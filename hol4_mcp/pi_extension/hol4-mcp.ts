/**
 * HOL4 MCP Extension for Pi
 *
 * Provides HOL4 theorem prover tools to the agent by connecting to the hol4-mcp server.
 * The server is spawned automatically on first tool use and cleaned up on exit.
 *
 * Tools are dynamically discovered from the MCP server, so changes to the server
 * are automatically reflected without updating this extension.
 */

import { spawn, type ChildProcess } from "node:child_process";
import type { ExtensionAPI } from "@mariozechner/pi-coding-agent";
import { Type, type TSchema } from "@sinclair/typebox";
import { Text } from "@mariozechner/pi-tui";

// Minimal MCP client - JSON-RPC 2.0 over stdio with NDJSON framing (FastMCP style)
class McpClient {
  private proc: ChildProcess | null = null;
  private buffer = "";
  private nextId = 1;
  private pending = new Map<number, { resolve: (v: any) => void; reject: (e: Error) => void }>();

  async connect(command: string, args: string[]): Promise<void> {
    this.proc = spawn(command, args, { stdio: ["pipe", "pipe", "pipe"] });

    this.proc.stdout!.on("data", (chunk) => {
      this.buffer += chunk.toString();
      this.processBuffer();
    });

    this.proc.on("error", (err) => {
      for (const { reject } of this.pending.values()) {
        reject(err);
      }
      this.pending.clear();
    });

    this.proc.on("close", () => {
      const err = new Error("MCP server closed");
      for (const { reject } of this.pending.values()) {
        reject(err);
      }
      this.pending.clear();
      this.proc = null;
    });

    // Initialize
    await this.request("initialize", {
      protocolVersion: "2024-11-05",
      capabilities: {},
      clientInfo: { name: "pi-hol4-mcp", version: "0.1.0" },
    });

    // Send initialized notification
    this.notify("notifications/initialized", {});
  }

  private processBuffer(): void {
    // NDJSON: one JSON object per line
    let newlineIdx: number;
    while ((newlineIdx = this.buffer.indexOf("\n")) !== -1) {
      const line = this.buffer.slice(0, newlineIdx).trim();
      this.buffer = this.buffer.slice(newlineIdx + 1);

      if (!line) continue;

      try {
        const msg = JSON.parse(line);
        if ("id" in msg && this.pending.has(msg.id)) {
          const { resolve, reject } = this.pending.get(msg.id)!;
          this.pending.delete(msg.id);
          if (msg.error) {
            reject(new Error(msg.error.message || JSON.stringify(msg.error)));
          } else {
            resolve(msg.result);
          }
        }
      } catch {
        // Ignore parse errors
      }
    }
  }

  private send(msg: object): void {
    if (!this.proc?.stdin) throw new Error("Not connected");
    // NDJSON: send JSON followed by newline
    const json = JSON.stringify(msg);
    this.proc.stdin.write(json + "\n");
  }

  private notify(method: string, params: object): void {
    this.send({ jsonrpc: "2.0", method, params });
  }

  request<T = any>(method: string, params: object, signal?: AbortSignal): Promise<T> {
    return new Promise((resolve, reject) => {
      const id = this.nextId++;
      
      // Handle abort signal
      if (signal) {
        if (signal.aborted) {
          reject(new Error("Aborted"));
          return;
        }
        const onAbort = () => {
          this.pending.delete(id);
          reject(new Error("Aborted"));
        };
        signal.addEventListener("abort", onAbort, { once: true });
        // Clean up listener when request completes
        const originalResolve = resolve;
        const originalReject = reject;
        resolve = (v) => {
          signal.removeEventListener("abort", onAbort);
          originalResolve(v);
        };
        reject = (e) => {
          signal.removeEventListener("abort", onAbort);
          originalReject(e);
        };
      }
      
      this.pending.set(id, { resolve, reject });
      this.send({ jsonrpc: "2.0", id, method, params });
    });
  }

  async listTools(signal?: AbortSignal): Promise<{ tools: Array<{ name: string; description?: string; inputSchema?: any }> }> {
    return this.request("tools/list", {}, signal);
  }

  async callTool(name: string, args: Record<string, unknown>, signal?: AbortSignal): Promise<{ content: Array<{ type: string; text?: string }>; isError?: boolean }> {
    return this.request("tools/call", { name, arguments: args }, signal);
  }

  close(): void {
    if (this.proc) {
      this.proc.kill();
      this.proc = null;
    }
  }

  /**
   * Send SIGINT to the MCP server process.
   * The server catches this and interrupts all HOL sessions.
   */
  interrupt(): boolean {
    if (this.proc?.pid) {
      try {
        process.kill(this.proc.pid, "SIGINT");
        return true;
      } catch {
        return false;
      }
    }
    return false;
  }

  get isConnected(): boolean {
    return this.proc !== null;
  }
}

// Convert MCP JSON Schema to TypeBox schema
function jsonSchemaToTypebox(schema: any): TSchema {
  if (!schema || typeof schema !== "object") {
    return Type.Any();
  }

  switch (schema.type) {
    case "string":
      return Type.String({ description: schema.description });
    case "number":
    case "integer":
      return Type.Number({ description: schema.description });
    case "boolean":
      return Type.Boolean({ description: schema.description });
    case "array":
      return Type.Array(jsonSchemaToTypebox(schema.items || {}), { description: schema.description });
    case "object": {
      const properties: Record<string, TSchema> = {};
      const required = new Set(schema.required || []);

      for (const [key, value] of Object.entries(schema.properties || {})) {
        const propSchema = jsonSchemaToTypebox(value);
        properties[key] = required.has(key) ? propSchema : Type.Optional(propSchema);
      }
      return Type.Object(properties, { description: schema.description });
    }
    default:
      return Type.Any({ description: schema.description });
  }
}

export default function hol4McpExtension(pi: ExtensionAPI) {
  let client: McpClient | null = null;
  let connecting: Promise<McpClient> | null = null;

  async function getClient(): Promise<McpClient> {
    if (client?.isConnected) return client;
    if (connecting) return connecting;

    connecting = (async () => {
      // Pass HOL_TACTIC_TIMEOUT via --tactic-timeout if set
      const spawnArgs = ["--transport", "stdio"];
      const tt = process.env.HOL_TACTIC_TIMEOUT;
      if (tt) spawnArgs.push("--tactic-timeout", tt);
      const c = new McpClient();
      await c.connect("hol4-mcp", spawnArgs);
      client = c;
      return c;
    })();

    try {
      return await connecting;
    } finally {
      connecting = null;
    }
  }

  async function restartClient(): Promise<McpClient> {
    client?.close();
    client = null;
    connecting = null;
    return getClient();
  }

  async function cleanup() {
    client?.close();
    client = null;
  }

  // Register a single entry-point tool that lazily connects to MCP server
  // This avoids errors on startup if hol4-mcp isn't installed
  pi.registerTool({
    name: "hol4_mcp",
    label: "HOL4 MCP",
    description: `HOL4 theorem prover tools. Actions:
- action='list': Discover available tools from hol4-mcp server
- action='call': Invoke a tool (requires tool_name, optional args)
- action='interrupt': Send interrupt to all HOL sessions (use when ESC pressed or tactic hangs)
- action='restart': Kill and restart the MCP server (use if server is in bad state)`,
    parameters: Type.Object({
      action: Type.Union([
        Type.Literal("list"),
        Type.Literal("call"),
        Type.Literal("interrupt"),
        Type.Literal("restart"),
      ], { description: "Action: 'list', 'call', 'interrupt', or 'restart'" }),
      tool_name: Type.Optional(Type.String({ description: "Tool name (required for 'call')" })),
      args: Type.Optional(Type.Record(Type.String(), Type.Unknown(), { description: "Tool arguments as object (for 'call')" })),
    }),

    async execute(toolCallId, params, signal, onUpdate, ctx) {
      try {
        // Handle restart action - doesn't need existing client
        if (params.action === "restart") {
          await restartClient();
          return {
            content: [{ type: "text", text: "MCP server restarted. All HOL sessions have been terminated." }],
            details: {},
          };
        }

        const mcpClient = await getClient();

        if (params.action === "list") {
          const { tools } = await mcpClient.listTools(signal);
          const toolList = tools.map(t => `- ${t.name}: ${t.description || "(no description)"}`).join("\n");
          return {
            content: [{ type: "text", text: `Available HOL4 MCP tools:\n\n${toolList}` }],
            details: { tools },
          };
        }

        if (params.action === "interrupt") {
          // Get list of sessions and interrupt each one
          const sessionsResult = await mcpClient.callTool("hol_sessions", {}, signal);
          const sessionsText = sessionsResult.content
            .filter((c): c is { type: "text"; text: string } => c.type === "text")
            .map(c => c.text)
            .join("\n");
          
          // Parse session names from output (first column after header)
          const lines = sessionsText.split("\n");
          const interrupted: string[] = [];
          for (const line of lines.slice(2)) { // Skip header and separator
            const sessionName = line.split(/\s+/)[0];
            if (sessionName && !sessionName.startsWith("-")) {
              try {
                await mcpClient.callTool("hol_interrupt", { session: sessionName });
                interrupted.push(sessionName);
              } catch {
                // Session may have died
              }
            }
          }
          
          if (interrupted.length === 0) {
            return {
              content: [{ type: "text", text: "No active sessions to interrupt." }],
              details: {},
            };
          }
          
          return {
            content: [{ type: "text", text: `Sent interrupt to sessions: ${interrupted.join(", ")}` }],
            details: { interrupted },
          };
        }

        if (params.action === "call") {
          if (!params.tool_name) {
            return { content: [{ type: "text", text: "Error: tool_name required for 'call' action" }], details: {}, isError: true };
          }

          // Parse args if it's a JSON string (LLM sometimes passes stringified JSON)
          let args = params.args || {};
          if (typeof args === "string") {
            try {
              args = JSON.parse(args);
            } catch {
              return { content: [{ type: "text", text: `Error: Invalid JSON in args: ${args}` }], details: {}, isError: true };
            }
          }

          const result = await mcpClient.callTool(params.tool_name, args as Record<string, unknown>, signal);
          const textContent = result.content
            .filter((c): c is { type: "text"; text: string } => c.type === "text" && typeof c.text === "string")
            .map((c) => c.text)
            .join("\n");

          return {
            content: [{ type: "text", text: textContent || "(no output)" }],
            details: { mcpResult: result, tool_name: params.tool_name, args },
            isError: result.isError === true,
          };
        }

        return { content: [{ type: "text", text: "Unknown action" }], details: {}, isError: true };
      } catch (err) {
        const message = err instanceof Error ? err.message : String(err);
        
        // If aborted (ESC pressed), send SIGINT to MCP server
        // The server catches this and interrupts all HOL sessions
        if (message === "Aborted" && client?.isConnected) {
          client.interrupt();
          return { 
            content: [{ type: "text", text: "Interrupted (sent SIGINT to HOL sessions)." }], 
            details: {},
            isError: true,
          };
        }
        
        return { content: [{ type: "text", text: `HOL4 MCP error: ${message}` }], details: {}, isError: true };
      }
    },

    renderCall(args, theme) {
      if (args.action === "list") {
        return new Text(theme.fg("toolTitle", theme.bold("hol4 ")) + theme.fg("accent", "list"), 0, 0);
      }
      if (args.action === "interrupt") {
        return new Text(theme.fg("toolTitle", theme.bold("hol4 ")) + theme.fg("warning", "interrupt"), 0, 0);
      }
      if (args.action === "restart") {
        return new Text(theme.fg("toolTitle", theme.bold("hol4 ")) + theme.fg("warning", "restart"), 0, 0);
      }
      
      const toolName = args.tool_name || "?";
      let text = theme.fg("toolTitle", theme.bold("hol4 ")) + theme.fg("accent", toolName);
      
      // Parse args if string (LLM sometimes sends JSON string)
      let toolArgs = args.args;
      if (typeof toolArgs === "string") {
        try { toolArgs = JSON.parse(toolArgs); } catch { toolArgs = null; }
      }
      
      if (toolArgs && typeof toolArgs === "object") {
        const argParts: string[] = [];
        for (const [k, v] of Object.entries(toolArgs)) {
          const val = typeof v === "string" ? v : JSON.stringify(v);
          argParts.push(`${k}=${val}`);
        }
        if (argParts.length > 0) {
          text += "\n" + theme.fg("dim", "  " + argParts.join(", "));
        }
      }
      
      return new Text(text, 0, 0);
    },

    renderResult(result, { expanded }, theme) {
      const details = result.details as { tool_name?: string; args?: any; mcpResult?: any } | undefined;
      const text = result.content[0];
      const output = text?.type === "text" ? text.text : "(no output)";
      const isError = result.isError === true;
      const icon = isError ? theme.fg("error", "✗") : theme.fg("success", "✓");
      
      if (expanded) {
        return new Text(`${icon} ${output}`, 0, 0);
      }
      
      // Collapsed: show first few lines
      const lines = output.split("\n");
      const preview = lines.slice(0, 5).join("\n");
      const truncated = lines.length > 5;
      let collapsed = `${icon} ${preview}`;
      if (truncated) {
        collapsed += "\n" + theme.fg("muted", `... (${lines.length - 5} more lines, Ctrl+O to expand)`);
      }
      return new Text(collapsed, 0, 0);
    },
  });

  pi.on("session_shutdown", async () => {
    await cleanup();
  });
}

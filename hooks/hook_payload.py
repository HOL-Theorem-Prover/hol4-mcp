#!/usr/bin/env python3
"""
Payload helpers shared by the hooks in this directory.

Not itself a hook: `install_hooks.py` discovers only files named
`h<N>_<name>.py`, so this module is never wired into settings.json.

Two things every hook needs and none should reimplement:

- `output_text(payload)` — a PostToolUse tool result as searchable text. The
  MCP result schema is not canonical, so several field names are tried and
  every string leaf is collected. Strings are kept RAW: escaping non-ASCII
  would hide the goal-display markers hooks match on (H16's `⅋ᵣ`), and
  re-encoding a dict as JSON would turn its newlines into `\\n`, breaking
  line-anchored patterns.
- `latest_user_message(payload)` — the text of the newest turn the user typed
  in the session transcript, for the consent-gated PreToolUse hooks. Tool
  results and harness-written lines (the compaction summary, request copies,
  hook and goal echoes, task notifications) ride the transcript as
  `role=user` too; those are plumbing, not prompts, and are skipped.
- `visible_command(command)` — a Bash command with its quoted strings,
  `#` comments and heredoc bodies blanked and its backslash-newlines joined,
  so a hook that matches command names sees only text the shell would
  execute. What the shell WOULD run inside a string is kept: a quoted single
  word (unquoted), `$(...)` and backtick substitutions, the argument of
  `-c`/`eval`, and the substitutions of an unquoted heredoc.
- `soft_block(...)` / `pregranted(...)` / `session_overrides(...)` — the
  soft-hook protocol: a situation is blocked ONCE per session window with
  the full message; an identical retry passes with a prominent override
  note and a log entry; a consent phrase in ANY user turn of the session
  pre-grants. The hard hooks (H14 `git ok`, H27 `wip ok`) do not use these —
  they read the latest user message only.
"""
import json
import os
import re
import sys
import time

STATE_ROOT = os.path.expanduser("~/.claude/hook-state")
SOFT_WINDOW_S = 30 * 60


def session_state_dir(payload):
    return os.path.join(STATE_ROOT, payload.get("session_id") or "nosession")


def _load_json(path, default):
    try:
        with open(path, encoding="utf-8") as fh:
            return json.load(fh)
    except Exception:
        return default


def _save_json(path, obj):
    try:
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w", encoding="utf-8") as fh:
            json.dump(obj, fh)
    except OSError:
        pass


def emit_context(text, event="PreToolUse"):
    """Allow the call and put `text` in front of the model (and the user)."""
    print(json.dumps({
        "hookSpecificOutput": {"hookEventName": event, "additionalContext": text},
        "systemMessage": text,
    }))


def granted(payload, phrase_re):
    """True if the phrase appears in ANY real user turn of the session, None
    if the transcript is unreadable (fail open)."""
    msgs = user_messages(payload)
    if msgs is None:
        return None
    return any(phrase_re.search(m) for m in msgs)


def pregranted(payload, hook, phrase_re, phrase, note):
    """Allow with a note when the user pre-granted `phrase` earlier in the
    session; False (nothing printed) otherwise."""
    if not granted(payload, phrase_re):
        return False
    emit_context(f"[{hook}: {note} — pre-granted by your `{phrase}`]")
    return True


def soft_block(payload, hook, fingerprint, lines, override_note, window_s=SOFT_WINDOW_S):
    """Block the situation `fingerprint` once; an identical retry inside the
    window passes with an override note and is logged. Returns the exit code."""
    path = os.path.join(session_state_dir(payload), "soft_blocks.json")
    state = _load_json(path, {})
    blocks = state.setdefault("blocks", {})
    key = f"{hook}:{fingerprint}"
    now = time.time()
    ts = blocks.get(key)
    if ts is not None and 0 <= now - float(ts) < window_s:
        state.setdefault("overrides", []).append(
            {"hook": hook, "ts": now, "what": override_note})
        _save_json(path, state)
        emit_context(f"⚠ {hook} OVERRIDDEN by repeat: {override_note}")
        return 0
    blocks[key] = now
    _save_json(path, state)
    for ln in lines:
        print(ln, file=sys.stderr)
    print("", file=sys.stderr)
    print("Blocked once. If, having read this, you still judge the call right, repeat",
          file=sys.stderr)
    print("it unchanged: it passes with a note and is logged as your decision (the",
          file=sys.stderr)
    print("session's overrides are listed at the next git commit).", file=sys.stderr)
    return 2


def session_overrides(payload):
    """The overrides logged this session, oldest first."""
    path = os.path.join(session_state_dir(payload), "soft_blocks.json")
    return list(_load_json(path, {}).get("overrides", []))


def overrides_summary(payload):
    """One line per hook: `H30 ×3 (what)`, or '' when nothing was overridden."""
    counts = {}
    for o in session_overrides(payload):
        h = o.get("hook", "?")
        counts.setdefault(h, [0, o.get("what", "")])
        counts[h][0] += 1
    if not counts:
        return ""
    return "; ".join(f"{h} ×{n} ({what})" for h, (n, what) in sorted(counts.items()))

_HEREDOC = re.compile(r"(?<!<)<<(?!<)-?\s*(?:(['\"])(\w+)\1|\\?(\w+))")
_KEEP_ARG_OF = ("-c", "-lc", "-ec", "-lec", "eval")
# A quoted single word is the word itself to the shell: `git "push"`.
_SINGLE_WORD = re.compile(r"[\w./:@=+,%-]+\Z")
_WORD_BREAK = " \t\n;|&()"


def _substitutions(s):
    """The `$(...)` and `` `...` `` segments of `s`, space-joined."""
    out, i = [], 0
    while i < len(s):
        if s.startswith("$(", i):
            depth, j = 0, i
            while j < len(s):
                if s[j] == "(":
                    depth += 1
                elif s[j] == ")":
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            out.append(s[i:j + 1])
            i = j + 1
        elif s[i] == "`":
            j = s.find("`", i + 1)
            j = len(s) - 1 if j < 0 else j
            out.append(s[i:j + 1])
            i = j + 1
        else:
            i += 1
    return " ".join(out)


def _heredoc_bodies(s, i, pending, out):
    """Blank the bodies of the heredocs in `pending`, which start at `s[i]`;
    returns the index after the last terminator line."""
    for quoted, tag in pending:
        while i < len(s):
            end = s.find("\n", i)
            end = len(s) if end < 0 else end
            line, nl = s[i:end], s[end:end + 1]
            i = end + len(nl)
            if line.lstrip("\t") == tag:
                out.append(line + nl)
                break
            out.append(("" if quoted else _substitutions(line)) + nl)
    return i


def _closing(s, i, open_, close):
    """The index after the `close` matching the `open_` at `s[i]`."""
    depth, j = 0, i
    while j < len(s):
        if s[j] == open_:
            depth += 1
        elif s[j] == close:
            depth -= 1
            if depth == 0:
                return j + 1
        j += 1
    return len(s)


def _arithmetic_end(s, i, at_word_start):
    """The index after the arithmetic expression starting at `s[i]` —
    `$((..))`, `$[..]`, a `((..))` command or a `let` line, where `<<` is
    a shift, not a heredoc — or None when none starts there."""
    if s.startswith("$((", i):
        return _closing(s, i + 1, "(", ")")
    if s.startswith("$[", i):
        return _closing(s, i + 1, "[", "]")
    if at_word_start and s.startswith("((", i):
        return _closing(s, i, "(", ")")
    if at_word_start and re.match(r"let[ \t]", s[i:i + 4]):
        m = re.compile(r"[\n;&|]").search(s, i)
        return m.start() if m else len(s)
    return None


def _prev_token(s, i):
    j = i
    while j > 0 and s[j - 1] in " \t":
        j -= 1
    k = j
    while k > 0 and s[k - 1] not in " \t\n;|&(":
        k -= 1
    return s[k:j]


def visible_command(command):
    """`command` with quoted strings, comments and heredoc bodies blanked
    (see module doc)."""
    s = command
    out, i, pending = [], 0, []
    while i < len(s):
        c = s[i]
        if c == "\n":
            out.append(c)
            i = _heredoc_bodies(s, i + 1, pending, out)
            pending = []
            continue
        if c == "\\" and i + 1 < len(s):
            # A backslash-newline joins the lines.
            out.append("" if s[i + 1] == "\n" else s[i:i + 2])
            i += 2
            continue
        at_word_start = i == 0 or s[i - 1] in _WORD_BREAK
        j = _arithmetic_end(s, i, at_word_start)
        if j is not None:
            out.append(s[i:j])
            i = j
            continue
        m = _HEREDOC.match(s, i)
        if m:
            pending.append((m.group(1) is not None, m.group(2) or m.group(3)))
            out.append(m.group(0))
            i = m.end()
            continue
        if c == "#" and at_word_start:
            end = s.find("\n", i)
            i = len(s) if end < 0 else end
            continue
        # `$'...'` (ANSI-C quoting) escapes with backslashes, as "..." does.
        ansi = s.startswith("$'", i)
        if c in "'\"" or ansi:
            keep = _prev_token(s, i) in _KEEP_ARG_OF
            q, start = ("'", i + 2) if ansi else (c, i + 1)
            j = start
            while j < len(s) and s[j] != q:
                j += 2 if (q == '"' or ansi) and s[j] == "\\" else 1
            body = s[start:j]
            if keep:
                out.append(q + body + q)
            elif _SINGLE_WORD.match(body):
                out.append(body)
            else:
                out.append(q + (_substitutions(visible_command(body))
                                if q == '"' else "") + q)
            i = j + 1
            continue
        out.append(c)
        i += 1
    return "".join(out)

RESULT_KEYS = ("tool_output", "tool_response", "tool_result",
               "result", "output", "response")


def _strings(v):
    """Every string leaf of a JSON-shaped value, in order."""
    if v is None:
        return []
    if isinstance(v, str):
        return [v]
    if isinstance(v, dict):
        return [s for x in v.values() for s in _strings(x)]
    if isinstance(v, (list, tuple)):
        return [s for x in v for s in _strings(x)]
    return [str(v)]


def output_text(payload):
    """A PostToolUse tool result flattened to one searchable string."""
    return "\n".join(s for key in RESULT_KEYS for s in _strings(payload.get(key)))


def _is_tool_result_only(content):
    """True if `content` is a list whose every element is a tool_result block.
    Such events are tool plumbing, not user prompts."""
    if not isinstance(content, list) or not content:
        return False
    return all(isinstance(c, dict) and c.get("type") == "tool_result"
               for c in content)


def _text_of(content):
    if isinstance(content, str):
        return content
    if isinstance(content, list):
        return "".join((c.get("text", "") if isinstance(c, dict) else str(c))
                       for c in content)
    return str(content)


# Claude Code writes these as `role=user` lines too, but the user typed none of
# them: the compaction summary, skill bodies, hook and goal echoes, task
# notifications, subagent hand-backs and slash-command output. Their text
# quotes earlier turns verbatim, consent phrases included.
_HARNESS_FLAGS = ("isMeta", "isCompactSummary", "isVisibleInTranscriptOnly")


def _user_turn_text(line):
    """Text of a transcript line that is a turn the user typed, else None."""
    try:
        event = json.loads(line)
    except Exception:
        return None
    if event.get("type") not in (None, "user"):           # e.g. api-request-blob
        return None
    if any(event.get(flag) for flag in _HARNESS_FLAGS):
        return None
    origin = event.get("origin")
    if isinstance(origin, dict) and origin.get("kind") not in (None, "human"):
        return None
    content = None
    if event.get("role") == "user":                       # flat
        content = event.get("content", "")
    msg = event.get("message")
    if content is None and isinstance(msg, dict) and msg.get("role") == "user":
        content = msg.get("content", "")                  # nested
    if content is None and event.get("type") == "user":   # type field
        content = event.get("content", "") or event.get("text", "")
    if content is None or _is_tool_result_only(content):
        return None
    text = _text_of(content)
    head = text.lstrip()
    if head.startswith("<local-command-stdout>"):    # a slash command's output
        return None
    if head.startswith("<command-name>"):
        # A slash command is a turn, so it ends an earlier message's one-shot
        # consent, but its arguments are command input that grants nothing.
        return ""
    return text


def user_messages(payload):
    """Texts of every real user turn, oldest first, or None if unreadable."""
    path = payload.get("transcript_path", "")
    if not path:
        return None
    try:
        with open(path, "r", encoding="utf-8") as f:
            lines = f.readlines()
    except (FileNotFoundError, OSError):
        return None
    out = []
    for line in lines:
        line = line.strip()
        if not line:
            continue
        text = _user_turn_text(line)
        if text is not None:
            out.append(text)
    return out


def latest_user_message(payload):
    """Text of the newest real user turn, or None if unreadable (fail open)."""
    msgs = user_messages(payload)
    return msgs[-1] if msgs else None

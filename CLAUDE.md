# Development Notes

## Virtual environment

Use `uv` for venv and dependency management:

```bash
uv pip install --python .venv/bin/python <package>
uv pip install --python .venv/bin/python -e .
```

## Running tests

```bash
.venv/bin/python -m pytest tests/ -q
```

## FastMCP

This project requires FastMCP >= 3.0. In 3.x, `@mcp.tool()` returns the
original function unchanged (no `.fn` unwrapping). Do not use `.fn` on tools.

#!/usr/bin/env python3
"""Detect and fix mismatched Unicode smart quotes in a file.

Thin CLI shim — the implementation lives in hol4_mcp.quote_check (so the
MCP server can run the same diagnosis in parse-error paths).

Usage: python3 check_quotes.py <file> [--fix]
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))

from hol4_mcp.quote_check import main

sys.exit(main(sys.argv[1:]))

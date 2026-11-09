#!/usr/bin/env python3
"""Capture stable UserPromptSubmit text for consent-aware HOL4 hooks."""

from __future__ import annotations

import json
import sys

from runtime import load_prompts, save_prompts


MAX_PROMPTS = 64
MAX_PROMPT_CHARS = 100_000


def main() -> int:
    try:
        payload = json.load(sys.stdin)
        prompt = payload.get("prompt")
        if not isinstance(prompt, str):
            return 0
        prompts = load_prompts(payload)
        prompts.append(prompt[:MAX_PROMPT_CHARS])
        save_prompts(payload, prompts[-MAX_PROMPTS:])
    except Exception:
        # A prompt-history convenience must never prevent a user turn.
        return 0
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

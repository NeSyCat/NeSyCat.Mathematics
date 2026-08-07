#!/usr/bin/env python3
"""Implementation for grind-stop.sh. Reads the Stop hook JSON from stdin,
decrements the .claude/grind-mode counter, and either re-blocks (re-prompts
the agent to keep grinding) or lets the stop proceed once exhausted. Never
raises past main()."""
import json
import os
import sys


def main():
    if len(sys.argv) < 2:
        return
    state_file = sys.argv[1]

    try:
        data = json.load(sys.stdin)
    except Exception:
        data = {}

    stop_hook_active = bool(data.get("stop_hook_active", False))

    try:
        with open(state_file, "r", encoding="utf-8") as fh:
            remaining = int(fh.read().strip())
    except Exception:
        # State file unreadable/corrupt: fail safe, remove it, stay silent.
        try:
            os.remove(state_file)
        except OSError:
            pass
        return

    # Loop-safety escape hatch: already re-invoked with nothing left to do.
    if stop_hook_active and remaining <= 0:
        try:
            os.remove(state_file)
        except OSError:
            pass
        return

    new_remaining = remaining - 1

    if new_remaining >= 0:
        try:
            with open(state_file, "w", encoding="utf-8") as fh:
                fh.write(str(new_remaining))
        except Exception:
            return
        out = {
            "decision": "block",
            "reason": (
                f"GRIND MODE ({new_remaining} left): re-read FORMALIZE.md and "
                "continue the work loop — pick the next item per PROGRESS.md, "
                "implement, check, commit. Do not stop to ask questions. "
                "Disarm anytime: scripts/grind-mode.sh off"
            ),
        }
        print(json.dumps(out))
    else:
        try:
            os.remove(state_file)
        except OSError:
            pass
        return


if __name__ == "__main__":
    try:
        main()
    except Exception:
        pass

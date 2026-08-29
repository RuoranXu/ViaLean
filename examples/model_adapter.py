#!/usr/bin/env python3
"""Minimal vialean.guidance.v1 command adapter.

Replace score_actions() with a call to a local model runtime. The transport itself
uses only Python's standard library and writes no diagnostics to stdout.
"""

import json
import sys
from typing import Any


def score_actions(request: dict[str, Any]) -> dict[str, Any]:
    """Deterministic fallback scorer; replace this body with local inference."""
    family_bonus = {
        "structural": 0.90,
        "equality_local": 0.88,
        "witness_local": 0.84,
        "local_cut": 0.76,
        "library_cut": 0.62,
    }
    scored = []
    for action in request.get("actions", []):
        prior = float(action.get("prior", 0.5))
        score = family_bonus.get(action.get("family"), prior)
        scored.append({"id": str(action["id"]), "score": max(0.0, min(1.0, score))})
    return {
        "value": 0.5 if not scored else max(item["score"] for item in scored),
        "actions": scored,
        "rationale": "example adapter; replace score_actions with local model inference",
    }


def main() -> None:
    request = json.load(sys.stdin)
    if request.get("protocol") != "vialean.guidance.v1":
        raise ValueError("unsupported ViaLean protocol")
    json.dump(score_actions(request), sys.stdout, separators=(",", ":"))
    sys.stdout.write("\n")


if __name__ == "__main__":
    main()
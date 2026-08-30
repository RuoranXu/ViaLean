#!/usr/bin/env python3
"""Minimal command adapter for both ViaLean model protocols.

Replace score_actions() / continue_search() with a local runtime or API call. The
transport uses only Python's standard library and keeps stdout JSON-only.
"""

import json
import sys
from typing import Any


def score_actions(request: dict[str, Any]) -> dict[str, Any]:
    """Deterministic policy fallback; replace with model inference."""
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
        "rationale": "example policy; replace score_actions with local inference",
    }


def continue_search(request: dict[str, Any]) -> dict[str, Any]:
    """Offer Lean code first, plus an optional symbolic fallback selected from feedback."""
    failed = {
        str(event.get("action_id"))
        for event in request.get("search_feedback", [])
        if event.get("outcome") == "failed"
    }
    frontier = request.get("frontier", [])
    for probe in frontier:
        if probe.get("executable") and str(probe.get("id")) not in failed:
            return {
                "lean_candidates": [{"code": "by simp_all"}],
                "continue": [{"probe_id": str(probe["id"])}],
                "rationale": "try concise Lean code, then use a diverse symbolic counterfactual",
            }

    actions = request.get("actions", [])
    preferred = sorted(
        enumerate(actions),
        key=lambda pair: (pair[1].get("family") != "structural", pair[0]),
    )
    for index, action in preferred:
        if str(action.get("id")) not in failed:
            return {
                "lean_candidates": [{"code": "by simp_all"}],
                "continue": [{"id": str(action["id"])}],
                "rationale": "try concise Lean code, then use an action not failed in feedback",
            }
    return {"continue": [], "rationale": "all executable probes and actions were attempted"}


def main() -> None:
    request = json.load(sys.stdin)
    protocol = request.get("protocol")
    if protocol == "vialean.guidance.v1":
        response = score_actions(request)
    elif protocol == "vialean.interactive.v1":
        response = continue_search(request)
    else:
        raise ValueError("unsupported ViaLean protocol")
    json.dump(response, sys.stdout, separators=(",", ":"))
    sys.stdout.write("\n")


if __name__ == "__main__":
    main()

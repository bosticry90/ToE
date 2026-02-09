from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools.bridge_ledger_generate import build_bridge_ledger_payload


def _repo_root_from_test_file(p: Path) -> Path:
    p = p.resolve()
    if p.is_file():
        p = p.parent
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def test_bridge_ledger_is_deterministic() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))

    l1 = build_bridge_ledger_payload(repo_root=repo_root)
    l2 = build_bridge_ledger_payload(repo_root=repo_root)

    assert json.dumps(l1, sort_keys=True) == json.dumps(l2, sort_keys=True)
    assert l1.get("schema_version") == 1

    items = list(l1.get("items", []))
    assert [it.get("ticket_id") for it in items] == [
        "BRIDGE_TICKET_0001",
        "BRIDGE_TICKET_0002",
        "BRIDGE_TICKET_0003",
        "BRIDGE_TICKET_0004",
        "BRIDGE_TICKET_TOYH_0001",
        "BRIDGE_TICKET_TOYH_0002",
        "BRIDGE_FEASIBILITY_TOYG_0001",
        "BRIDGE_TICKET_TOYG_0001",
        "BRIDGE_TICKET_TOYG_0002",
        "BRIDGE_TICKET_TOYG_0003",
        "BRIDGE_TICKET_TOYH_0003",
        "BRIDGE_TICKET_TOYH_0004",
        "BRIDGE_TICKET_TOYHG_0001",
    ]

    for it in items:
        assert it.get("bridge_class")
        assert it.get("evidence_strength")
        evidence = it.get("evidence", {})
        nodes = list(evidence.get("pytest_nodes", []))
        assert nodes, f"Expected pytest_nodes for ticket_id={it.get('ticket_id')}"
        assert it.get("ticket_path")
        assert it.get("ticket_sha256")

    assert l1.get("artifact_sha256")

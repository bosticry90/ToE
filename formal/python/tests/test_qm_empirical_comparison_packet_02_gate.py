from __future__ import annotations

import json
import re
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QM_EMPIRICAL_COMPARISON_PACKET_02_v0.md"
PROTOCOL_PATH = REPO_ROOT / "formal" / "docs" / "release" / "FOUNDATIONAL_EMPIRICAL_COMPARISON_PROTOCOL_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "qm_empirical_comparison_packet_02_v0.json"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"

EXPECTED_ARTIFACT_ID = "qm_empirical_comparison_packet_02_v0"
EXPECTED_GATE = "ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED"
ALLOWED_DECISIONS = {"RETAIN_v0", "PRUNE_v0", "INCONCLUSIVE_v0"}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def test_qm_empirical_packet_02_gate() -> None:
    doc_text = _read(DOC_PATH)
    protocol_text = _read(PROTOCOL_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)

    artifact_json = json.loads(_read(ARTIFACT_PATH))
    payload = artifact_json.get("payload", {})

    assert artifact_json.get("artifact_id") == EXPECTED_ARTIFACT_ID
    assert payload.get("status") == "RUN_BOUNDED_v0_NONCLAIM"
    assert payload.get("decision") in ALLOWED_DECISIONS

    assert _extract_token(doc_text, "QM_EMPIRICAL_PACKET_02_STATUS_v0") == "RUN_BOUNDED_v0_NONCLAIM"
    assert _extract_token(doc_text, "QM_EMPIRICAL_PACKET_02_ARTIFACT_v0") == EXPECTED_ARTIFACT_ID
    assert _extract_token(doc_text, "QM_EMPIRICAL_PACKET_02_GATE_v0") == EXPECTED_GATE
    assert _extract_token(doc_text, "QM_EMPIRICAL_PACKET_02_DECISION_v0") in ALLOWED_DECISIONS
    assert _extract_token(doc_text, "QM_EMPIRICAL_PACKET_02_EVIDENCE_TIER_v0") == "INTERMEDIATE_v0"
    assert _extract_token(doc_text, "QM_EMPIRICAL_PACKET_02_DECISION_ELIGIBILITY_v0") == (
        "RETAIN_OR_PRUNE_ALLOWED_WITH_PROTOCOL_GUARDS"
    )

    assert payload.get("evidence_tier") == "INTERMEDIATE_v0"
    eligibility = payload.get("decision_eligibility")
    assert isinstance(eligibility, dict)
    assert eligibility.get("retain_allowed") is True
    assert eligibility.get("prune_allowed") is True
    assert eligibility.get("prune_guard_satisfied") is True

    if payload.get("decision") == "PRUNE_v0":
        uncertainty = str(payload.get("uncertainty_annotation", "")).lower()
        assert "scaffold" not in uncertainty

    assert _extract_token(protocol_text, "FOUNDATIONAL_EMPIRICAL_COMPARISON_PRUNE_GUARD_v0") == (
        "NO_DIRECT_PRUNE_WITH_SCAFFOLD_UNCERTAINTY"
    )
    assert _extract_token(protocol_text, "FOUNDATIONAL_EMPIRICAL_PACKET_02_DECISION_ELIGIBILITY_v0") == (
        "RETAIN_OR_PRUNE_ALLOWED_WITH_PROTOCOL_GUARDS"
    )

    for path_ref in (
        "formal/docs/paper/DERIVATION_TARGET_QM_EMPIRICAL_COMPARISON_PACKET_02_v0.md",
        "formal/python/tests/test_qm_empirical_comparison_packet_02_gate.py",
    ):
        assert path_ref in roadmap_text
        assert path_ref in state_text

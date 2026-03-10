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
RECORD_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QM_EMPIRICAL_PACKET_02_DECISION_RECORD_v0.md"
PACKET_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QM_EMPIRICAL_COMPARISON_PACKET_02_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "qm_empirical_comparison_packet_02_v0.json"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def test_qm_empirical_packet_02_decision_record_gate() -> None:
    record_text = _read(RECORD_DOC_PATH)
    packet_text = _read(PACKET_DOC_PATH)
    artifact = json.loads(_read(ARTIFACT_PATH))
    payload = artifact.get("payload", {})

    assert _extract_token(record_text, "QM_EMPIRICAL_PACKET_02_DECISION_RECORD_STATUS_v0") == "RUN_BOUNDED_v0_NONCLAIM"
    assert _extract_token(record_text, "QM_EMPIRICAL_PACKET_02_DECISION_RESULT_v0") == "RETAIN_v0"
    assert _extract_token(record_text, "QM_EMPIRICAL_PACKET_02_DECISION_BASIS_v0") == "CYCLE02_GUARD_SATISFIED_RETAIN"
    assert _extract_token(record_text, "QM_EMPIRICAL_PACKET_02_DECISION_GUARD_v0") == "PROTOCOL_COMPLIANT_INTERMEDIATE_TIER"

    assert _extract_token(packet_text, "QM_EMPIRICAL_PACKET_02_DECISION_v0") == "RETAIN_v0"
    assert payload.get("decision") == "RETAIN_v0"
    assert payload.get("evidence_tier") == "INTERMEDIATE_v0"

    eligibility = payload.get("decision_eligibility")
    assert isinstance(eligibility, dict)
    assert eligibility.get("retain_allowed") is True
    assert eligibility.get("prune_allowed") is True
    assert eligibility.get("prune_guard_satisfied") is True

    assert payload.get("decision_record_pointer") == (
        "formal/docs/paper/DERIVATION_TARGET_QM_EMPIRICAL_PACKET_02_DECISION_RECORD_v0.md"
    )

    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)
    for ref in (
        "formal/docs/paper/DERIVATION_TARGET_QM_EMPIRICAL_PACKET_02_DECISION_RECORD_v0.md",
        "formal/python/tests/test_qm_empirical_packet_02_decision_record_gate.py",
    ):
        assert ref in roadmap_text
        assert ref in state_text

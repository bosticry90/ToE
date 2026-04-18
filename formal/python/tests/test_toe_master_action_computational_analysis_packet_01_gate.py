from __future__ import annotations

import json
import re
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "toe_master_action_computational_analysis_packet_01_v0.json"
REPORT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "toe_master_action_computational_analysis_packet_01_20260417_v0.json"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-./]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def test_toe_master_action_computational_analysis_packet_01_gate() -> None:
    doc_text = _read(DOC_PATH)
    artifact = json.loads(_read(ARTIFACT_PATH))
    report = json.loads(_read(REPORT_PATH))
    payload = artifact.get("payload", {})
    numeric_summary = report.get("numeric_summary", {})

    assert artifact.get("artifact_id") == "toe_master_action_computational_analysis_packet_01_v0"
    assert payload.get("status") == "RUN_BOUNDED_v0_NONCLAIM"
    assert payload.get("authorization_class") == "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS"
    assert payload.get("decision") == "INCONCLUSIVE_v0"
    assert payload.get("implementation_stack") == "NUMPY_FIRST_REFERENCE_IMPLEMENTATION_ONLY"
    assert payload.get("observable_bundle") == [
        "operator_stability_observable_v0",
        "residual_consistency_observable_v0",
        "regime_limit_sensitivity_observable_v0",
    ]

    assert _extract_token(doc_text, "TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_STATUS_v0") == "RUN_BOUNDED_v0_NONCLAIM"
    assert _extract_token(doc_text, "TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_ARTIFACT_v0") == "toe_master_action_computational_analysis_packet_01_v0"
    assert _extract_token(doc_text, "TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_DECISION_v0") == "INCONCLUSIVE_v0"

    assert report.get("summary", {}).get("packet_decision") == "INCONCLUSIVE_v0"
    assert report.get("summary", {}).get("subordinate_disposition") == "REFINE_CANDIDATE_v0"
    assert report.get("criteria", {}).get("numpy_reference_stack_only") is True
    assert report.get("criteria", {}).get("operator_stability_pass") is True
    assert report.get("criteria", {}).get("residual_consistency_pass") is True
    assert report.get("criteria", {}).get("regime_limit_sensitivity_pass") is True
    assert round(float(numeric_summary.get("spectral_radius", 0.0)), 6) == 0.990685
    assert round(float(numeric_summary.get("residual_norm", 0.0)), 6) == 0.036644

    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)
    for ref in (
        "formal/docs/paper/DERIVATION_TARGET_TOE_MASTER_ACTION_COMPUTATIONAL_ANALYSIS_PACKET_01_v0.md",
        "formal/output/toe_master_action_computational_analysis_packet_01_v0.json",
        "formal/output/reports/toe_master_action_computational_analysis_packet_01_20260417_v0.json",
        "formal/output/reports/toe_master_action_computational_analysis_packet_01_decision_20260417_v0.json",
        "formal/python/tests/test_toe_master_action_computational_analysis_packet_01_gate.py",
    ):
        assert ref in roadmap_text
        assert ref in state_text or ref in inventory_text

    assert "INV-PHYS-TOE-MASTER-ACTION-COMP-ANALYSIS-PACKET01-v0" in inventory_text
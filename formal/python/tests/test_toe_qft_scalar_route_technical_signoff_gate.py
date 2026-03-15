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
SIGNOFF_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QFT_SCALAR_ROUTE_TECHNICAL_SIGNOFF_v0.md"
SIGNOFF_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "toe_qft_scalar_route_technical_signoff_checkpoint_v0.json"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-\.]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def test_scalar_technical_signoff_document_has_required_structure() -> None:
    text = _read(SIGNOFF_DOC_PATH)
    required_markers = [
        "Sign-off ID:",
        "## Technical Completeness Summary",
        "## Remaining Bounded Debts",
        "## Debt Classification Table",
        "## Claim Envelope (Honest Scope)",
        "SCALAR_ROUTE_TECHNICAL_SIGNOFF_STATUS_v0: SIGNED_OFF_BOUNDED_RIGOR_BASELINE_v0",
        "SCALAR_ROUTE_TECHNICAL_SIGNOFF_DEBT_CLASS_v0: BOUNDED_LINKAGE_RECOVERY_DEBT_v0",
        "SCALAR_ROUTE_TECHNICAL_SIGNOFF_GATE_v0: REQUIRED_TECHNICAL_SIGNOFF_SCHEMA_AND_PARITY",
        "SCALAR_ROUTE_TECHNICAL_SIGNOFF_ARTIFACT_v0: toe_qft_scalar_route_technical_signoff_checkpoint_v0",
    ]
    for marker in required_markers:
        assert marker in text, f"Technical signoff document missing marker: {marker}"


def test_scalar_technical_signoff_checkpoint_schema_is_pinned() -> None:
    artifact = _read_json(SIGNOFF_CHECKPOINT_PATH)

    assert artifact.get("artifact_id") == "toe_qft_scalar_route_technical_signoff_checkpoint_v0"
    assert artifact.get("phase") == "PHASE_2_SCALAR_TECHNICAL_SIGNOFF"
    assert artifact.get("status") == "SIGNED_OFF_BOUNDED_RIGOR_BASELINE_v0"

    payload = artifact.get("payload", {})
    assert payload.get("signoff_doc_path") == "formal/docs/paper/TOE_QFT_SCALAR_ROUTE_TECHNICAL_SIGNOFF_v0.md"
    assert payload.get("technical_record_path") == "formal/docs/paper/TOE_QFT_SCALAR_ROUTE_FULL_TECHNICAL_RECORD_v0.md"
    assert payload.get("technical_record_checkpoint_path") == (
        "formal/output/toe_qft_scalar_route_full_technical_record_checkpoint_v0.json"
    )

    classification = payload.get("classification", {})
    for key in [
        "non_blocking_for_scalar_paper",
        "blocking_for_stronger_claims",
        "deferred_to_later_lanes",
    ]:
        assert isinstance(classification.get(key), list) and classification.get(key), (
            f"Missing or empty classification list: {key}"
        )

    coverage = payload.get("coverage_summary", {})
    assert coverage.get("paper_may_rely_with_gap_flag") == 0
    assert coverage.get("lean_missing_linkage") == 0
    assert coverage.get("full_derived") == coverage.get("ledger_claims")


def test_scalar_technical_signoff_authority_surface_parity() -> None:
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    required_refs = [
        "formal/docs/paper/TOE_QFT_SCALAR_ROUTE_TECHNICAL_SIGNOFF_v0.md",
        "formal/output/toe_qft_scalar_route_technical_signoff_checkpoint_v0.json",
        "formal/python/tests/test_toe_qft_scalar_route_technical_signoff_gate.py",
    ]
    for ref in required_refs:
        assert ref in state_text, f"Missing signoff pointer in State_of_the_Theory.md: {ref}"
        assert ref in roadmap_text, f"Missing signoff pointer in PHYSICS_ROADMAP_v0.md: {ref}"

    state_status = _extract_token(state_text, "SCALAR_ROUTE_TECHNICAL_SIGNOFF_STATUS_v0")
    roadmap_status = _extract_token(roadmap_text, "SCALAR_ROUTE_TECHNICAL_SIGNOFF_STATUS_v0")
    state_debt = _extract_token(state_text, "SCALAR_ROUTE_TECHNICAL_SIGNOFF_DEBT_CLASS_v0")
    roadmap_debt = _extract_token(roadmap_text, "SCALAR_ROUTE_TECHNICAL_SIGNOFF_DEBT_CLASS_v0")

    assert state_status == roadmap_status == "SIGNED_OFF_BOUNDED_RIGOR_BASELINE_v0"
    assert state_debt == roadmap_debt == "BOUNDED_LINKAGE_RECOVERY_DEBT_v0"

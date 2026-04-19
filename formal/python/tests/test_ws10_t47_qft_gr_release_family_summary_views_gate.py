from __future__ import annotations

import json
from pathlib import Path

from formal.python.tests._archived_history_sentinel import split_active_and_archived
from formal.python.tools import ws10_t47_qft_gr_release_family_summary_views_report as tool


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md"
DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_IMPLEMENTATION_TRANCHE_47_DECLARATION_20260418_v0.md"
SUMMARY_VIEWS_PATH = REPO_ROOT / "formal" / "output" / "reports" / "qft_gr_sliceb_increment_family_summary_views_20260418_v0.json"
GATE_PATH = REPO_ROOT / "formal" / "python" / "tests" / "test_ws10_t47_qft_gr_release_family_summary_views_gate.py"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _active_text(path: Path) -> str:
    active, _ = split_active_and_archived(_read(path), path)
    return active


def test_ws10_t47_files_exist() -> None:
    for path in (PROGRAM_PATH, DECLARATION_PATH, SUMMARY_VIEWS_PATH, GATE_PATH):
        assert path.exists(), f"Missing required T47 file: {path}"


def test_ws10_t47_tokens_parity() -> None:
    state_text = _active_text(STATE_PATH)
    roadmap_text = _active_text(ROADMAP_PATH)
    parity_tokens = [
        "THEORY_RESTART_T47_REMEDIATION_PHASE_U_STATUS_v0: ACTIVE_QFT_GR_RELEASE_FAMILY_SUMMARY_VIEWS_NONLIVE_v0",
        "THEORY_RESTART_T47_REMEDIATION_PHASE_U_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_47_DECLARATION_20260418_v0.md",
        "THEORY_RESTART_T47_REMEDIATION_PHASE_U_PROGRAM_DOC_v0: formal/docs/release/WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md",
        "THEORY_RESTART_T47_REMEDIATION_PHASE_U_REPORT_TOOL_v0: formal/python/tools/ws10_t47_qft_gr_release_family_summary_views_report.py",
        "THEORY_RESTART_T47_REMEDIATION_PHASE_U_SUMMARY_JSON_v0: formal/output/reports/qft_gr_sliceb_increment_family_summary_views_20260418_v0.json",
        "THEORY_RESTART_T47_REMEDIATION_PHASE_U_GATE_v0: formal/python/tests/test_ws10_t47_qft_gr_release_family_summary_views_gate.py",
        "THEORY_RESTART_T47_REMEDIATION_PHASE_U_ENTRY_CRITERIA_v0: DERIVE_QFT_GR_SLICEB_SUMMARY_VIEWS_FROM_T43_REGISTRY_WITHOUT_CREATING_NEW_AUTHORITY",
        "THEORY_RESTART_T47_REMEDIATION_PHASE_U_NEXT_ACTION_v0: USE_QFT_GR_SUMMARY_VIEWS_AS_ACTIVE_REVIEW_SURFACE_AND_DEFER_RAW_CHAIN_TO_ARCHIVAL_TRACEABILITY",
    ]
    for token in parity_tokens:
        assert token in state_text, f"Missing state token: {token}"
        assert token in roadmap_text, f"Missing roadmap token: {token}"


def test_ws10_t47_program_tokens_present() -> None:
    text = _read(PROGRAM_PATH)
    required = [
        "formal/output/reports/qft_gr_sliceb_increment_family_summary_views_20260418_v0.json",
        "formal/python/tools/ws10_t47_qft_gr_release_family_summary_views_report.py",
        "formal/python/tests/test_ws10_t47_qft_gr_release_family_summary_views_gate.py",
        "WS10_REMEDIATION_PHASE_U_T47_STATUS_v0: ACTIVE_QFT_GR_RELEASE_FAMILY_SUMMARY_VIEWS_NONLIVE_v0",
        "WS10_REMEDIATION_PHASE_U_T47_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_47_DECLARATION_20260418_v0.md",
        "WS10_REMEDIATION_PHASE_U_T47_REPORT_TOOL_v0: formal/python/tools/ws10_t47_qft_gr_release_family_summary_views_report.py",
        "WS10_REMEDIATION_PHASE_U_T47_SUMMARY_JSON_v0: formal/output/reports/qft_gr_sliceb_increment_family_summary_views_20260418_v0.json",
        "WS10_REMEDIATION_PHASE_U_T47_GATE_v0: formal/python/tests/test_ws10_t47_qft_gr_release_family_summary_views_gate.py",
        "WS10_REMEDIATION_PHASE_U_T47_ENTRY_CRITERIA_v0: DERIVE_QFT_GR_SLICEB_SUMMARY_VIEWS_FROM_T43_REGISTRY_WITHOUT_CREATING_NEW_AUTHORITY",
        "WS10_REMEDIATION_PHASE_U_T47_NEXT_ACTION_v0: USE_QFT_GR_SUMMARY_VIEWS_AS_ACTIVE_REVIEW_SURFACE_AND_DEFER_RAW_CHAIN_TO_ARCHIVAL_TRACEABILITY",
        "WS10_REMEDIATION_PHASE_U_T47_ADJUDICATION_v0: QFT_GR_RELEASE_FAMILY_REVIEW_SURFACE_COMPRESSED_NONAUTHORITATIVE_v0",
    ]
    missing = [token for token in required if token not in text]
    assert not missing, "Missing remediation program Phase U T47 token(s): " + ", ".join(missing)


def test_ws10_t47_summary_views_match_tool_output() -> None:
    payload = _json(SUMMARY_VIEWS_PATH)
    expected = tool.build_report(captured_at_utc=payload.get("captured_at_utc"))
    assert payload == expected, "T47 release-family summary views drifted from generator output."


def test_ws10_t47_summary_view_semantics() -> None:
    payload = _json(SUMMARY_VIEWS_PATH)
    assert payload.get("status") == "DERIVED_NONAUTHORITATIVE_REVIEW_SURFACE_v0"
    assert payload.get("derived_from", {}).get("registry_file_count") == 279
    semantic_bands = payload.get("kind_span_views", {}).get("SEMANTIC_DELTA_DECISION_NOTE", {}).get("increment_bands")
    science_bands = payload.get("kind_span_views", {}).get("SCIENCE_VALIDATION_NOTE", {}).get("increment_bands")
    synthesis_missing = payload.get("kind_span_views", {}).get("SYNTHESIS_NOTE", {}).get("missing_end_increments")
    assert semantic_bands == [{"start": 5, "end": 68}]
    assert science_bands == [{"start": 50, "end": 68}]
    assert synthesis_missing == [6]
    review_focus = payload.get("review_focus", {})
    assert review_focus.get("synthesis_anchor_distribution", {}).get("all_synthesis_notes_anchor_at_increment01") is True
    assert review_focus.get("terminal_increment_band") == {"start_increment": 59, "end_increment": 68}
    assert payload.get("summary", {}).get("terminal_outcome") == "QFT_GR_SLICEB_RELEASE_FAMILY_SUMMARY_VIEWS_GENERATED_OVER_T43_REGISTRY"
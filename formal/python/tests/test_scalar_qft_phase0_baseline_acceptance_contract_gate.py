from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
CONTRACT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "lanes"
    / "SCALAR_QFT_PHASE0_BASELINE_ACCEPTANCE_CONTRACT_v0.md"
)
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "scalar_qft_phase0_baseline_acceptance_contract_v0.json"
)
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
OBLIGATION_MAP_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "lanes"
    / "STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md"
)

REQUIRED_SECTION_HEADERS = [
    "Document ID:",
    "## Baseline Snapshot",
    "## Success Criteria",
    "## Fail-Closed Conditions",
    "## Verification Command Set",
    "## Evidence Pointer Requirements",
    "## Phase Lock Rule",
]

REQUIRED_POINTERS = [
    "State_of_the_Theory.md",
    "formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md",
]

REQUIRED_BOUNDARY_TEXT = [
    "no parser claim",
    "no master-action promotion claim",
    "no seam closure claim",
    "no empirical claim",
]

REQUIRED_FAIL_CLOSED_TEXT = [
    "no net movement => tranche fails",
]

REQUIRED_LOCK_TEXT = "Phase 1 blocked until Phase 0 gate is GREEN."

PHASE0_TRANCHE_FILES = [
    "formal/docs/lanes/SCALAR_QFT_PHASE0_BASELINE_ACCEPTANCE_CONTRACT_v0.md",
    "formal/python/tests/test_scalar_qft_phase0_baseline_acceptance_contract_gate.py",
    "formal/output/reports/scalar_qft_phase0_baseline_acceptance_contract_v0.json",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _is_lean_theorem_path(path: str) -> bool:
    normalized = path.replace("\\", "/")
    return normalized.startswith("formal/toe_formal/ToeFormal/") and normalized.endswith(".lean")


def test_phase0_files_exist() -> None:
    for path in (CONTRACT_PATH, REPORT_PATH, STATE_PATH, OBLIGATION_MAP_PATH):
        assert path.exists(), f"Missing required Phase 0 surface: {path}"


def test_phase0_contract_contains_required_sections_and_rules() -> None:
    text = _read(CONTRACT_PATH)

    for section in REQUIRED_SECTION_HEADERS:
        assert section in text, f"Missing contract section: {section}"

    for pointer in REQUIRED_POINTERS:
        assert pointer in text, f"Missing required source pointer: {pointer}"

    for boundary_line in REQUIRED_BOUNDARY_TEXT:
        assert boundary_line in text, f"Missing non-claim boundary control: {boundary_line}"

    for fail_line in REQUIRED_FAIL_CLOSED_TEXT:
        assert fail_line in text, f"Missing fail-closed requirement: {fail_line}"

    assert REQUIRED_LOCK_TEXT in text, "Missing Phase 1 lock rule text."
    assert "No Lean theorem files modified in this tranche." in text


def test_phase0_report_schema_and_green_status() -> None:
    payload = _read_json(REPORT_PATH)

    expected_top_level_keys = {
        "report_id",
        "generated_at_utc",
        "contract_path",
        "gate_status",
        "baseline",
        "baseline_sources",
        "success_criteria_present",
        "fail_closed_conditions_present",
        "phase1_lock_rule_present",
        "non_claim_checks_present",
        "no_lean_theorem_files_modified_in_this_tranche",
        "missing_requirements",
    }

    missing_keys = expected_top_level_keys.difference(payload.keys())
    assert not missing_keys, f"Missing report key(s): {sorted(missing_keys)}"

    assert payload["report_id"] == "scalar_qft_phase0_baseline_acceptance_contract_v0"
    assert payload["contract_path"] == "formal/docs/lanes/SCALAR_QFT_PHASE0_BASELINE_ACCEPTANCE_CONTRACT_v0.md"
    assert payload["gate_status"] == "GREEN"

    baseline = payload["baseline"]
    assert baseline["theorem_gap_count"] == 7
    assert baseline["seam_gap_count"] == 3
    assert baseline["retained_assumption_rows"] == 6

    sources = payload["baseline_sources"]
    assert "State_of_the_Theory.md" in sources
    assert "formal/docs/lanes/STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md" in sources

    assert payload["success_criteria_present"] is True
    assert payload["fail_closed_conditions_present"] is True
    assert payload["phase1_lock_rule_present"] is True

    non_claim = payload["non_claim_checks_present"]
    assert non_claim["no_parser_claim"] is True
    assert non_claim["no_master_action_promotion_claim"] is True
    assert non_claim["no_seam_closure_claim"] is True
    assert non_claim["no_empirical_claim"] is True

    assert payload["missing_requirements"] == []


def test_phase0_gate_verifies_no_lean_theorem_files_in_tranche() -> None:
    payload = _read_json(REPORT_PATH)

    lean_paths = [p for p in PHASE0_TRANCHE_FILES if _is_lean_theorem_path(p)]
    assert lean_paths == [], f"Phase 0 tranche unexpectedly contains Lean theorem path(s): {lean_paths}"
    assert payload["no_lean_theorem_files_modified_in_this_tranche"] is True

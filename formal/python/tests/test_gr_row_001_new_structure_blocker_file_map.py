from __future__ import annotations

import json
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
MAP_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "GR_ROW_001_NEW_STRUCTURE_BLOCKER_FILE_MAP_20260418_v0.json"
)
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_gr_row_001_blocker_file_map_pins_active_new_structure_chain() -> None:
    payload = _read_json(MAP_PATH)

    assert payload["target_row"] == "ROW-PILLAR-GR-001"
    assert payload["authoritative_branch_classification"]["current_lane_class"] == "FROZEN_NEW_STRUCTURE_BRANCH"
    assert payload["authoritative_branch_classification"]["authoritative_next_step"] == (
        "RESUME_FROM_P78_P79_P80_DORMANT_PACKAGE_ONLY"
    )
    assert payload["authoritative_branch_classification"]["authoritative_next_action"] == (
        "KEEP_GR_ROW_001_FROZEN_AND_PREPARE_ONE_BOUNDED_SHARED_INTERFACE_DECLARATION_IF_RESTART_AUTHORIZED"
    )

    expected_active_chain = {
        "formal/output/reports/gr_row_001_higher_level_structure_review_20260412_v0.json",
        "formal/output/reports/gr_row_001_structural_gap_definition_20260412_v0.json",
        "formal/docs/release/GR_ROW_001_NEW_STRUCTURE_CONCEPT_PACKET_20260413_v0.json",
        "formal/output/reports/gr_row_001_new_structure_concept_packet_20260413_v0.json",
        "formal/docs/release/GR_ROW_001_SHARED_INTERFACE_DECLARATION_20260413_v0.json",
        "formal/output/reports/gr_row_001_shared_interface_declaration_20260413_v0.json",
        "formal/docs/release/GR_ROW_001_COMPARATOR_SPECIFICATION_20260413_v0.json",
        "formal/output/reports/gr_row_001_comparator_specification_20260413_v0.json",
    }
    actual_active_chain = set(payload["active_authority_chain"]["freeze_basis"]) | set(
        payload["active_authority_chain"]["dormant_design_package"]
    )
    missing = sorted(expected_active_chain - actual_active_chain)
    assert not missing, "GR blocker file map missing active chain file(s): " + ", ".join(missing)


def test_gr_row_001_blocker_file_map_marks_retry_chain_as_historical_only() -> None:
    payload = _read_json(MAP_PATH)
    historical = set(payload["historical_exhausted_retry_chain"])

    assert "formal/output/reports/gr_master_action_transport_attack_retry_packet_20260412_v0.json" in historical
    assert "formal/output/reports/gr_regime_limit_alignment_attack_retry_packet_20260412_v0.json" in historical
    assert payload["active_retry_language_audit"]["state_and_dormant_package_surfaces"] == (
        "NO_RETRY_PATH_LANGUAGE_DETECTED_IN_ACTIVE_NEXT_STEP_MIRRORS"
    )


def test_gr_row_001_blocker_file_map_is_pinned_in_state() -> None:
    state_text = _read(STATE_PATH)
    required_tokens = [
        "GR_ROW_001_BLOCKER_FILE_MAP_DECLARATION_v0: formal/docs/release/GR_ROW_001_NEW_STRUCTURE_BLOCKER_FILE_MAP_20260418_v0.json",
        "GR_ROW_001_BLOCKER_FILE_MAP_NEXT_STEP_RULE_v0: RESUME_FROM_P78_P79_P80_DORMANT_PACKAGE_ONLY",
        "GR_ROW_001_BLOCKER_FILE_MAP_ACTIVE_RETRY_LANGUAGE_AUDIT_v0: NO_RETRY_PATH_LANGUAGE_DETECTED_IN_ACTIVE_NEXT_STEP_MIRRORS",
        "GR_ROW_001_BLOCKER_FILE_MAP_GATE_v0: formal/python/tests/test_gr_row_001_new_structure_blocker_file_map.py",
    ]
    missing = [token for token in required_tokens if token not in state_text]
    assert not missing, "State_of_the_Theory.md missing GR blocker file map token(s): " + ", ".join(missing)
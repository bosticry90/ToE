from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_focused_gate_not_manifest_enrolled,
)
from formal.python.tools.minimal_global_toe_mathematical_obligation_index_report import (
    ALLOWED_MATURITY_STATES,
    DEFAULT_OUT as INDEX_PATH,
    OUTCOME_ID as INDEX_OUTCOME,
    QFT_GR_CALCULATION_TARGET,
    QFT_GR_FIRST_BREAK_ROW_ID,
    QFT_GR_FIRST_REQUIRED_CALCULATION,
    build_minimal_global_toe_mathematical_obligation_index,
)
from formal.python.tools.minimal_global_toe_mathematical_obligation_index_result_review_report import (
    DEFAULT_OUT as INDEX_REVIEW_PATH,
    NEXT_TARGET as SELECTION_TARGET,
    OUTCOME_ID as INDEX_REVIEW_OUTCOME,
    build_minimal_global_toe_mathematical_obligation_index_result_review,
)
from formal.python.tools.qft_gr_source_action_test_action_weak_pairing_domain_calculation_packet_report import (
    CALCULATION_RESULT,
    DEFAULT_OUT as CALCULATION_PACKET_PATH,
    NEXT_TARGET as CALCULATION_PACKET_REVIEW_TARGET,
    OUTCOME_ID as CALCULATION_PACKET_OUTCOME,
    build_qft_gr_source_action_test_action_weak_pairing_domain_calculation_packet,
)
from formal.python.tools.qft_gr_source_map_ladder_packet_from_candidate_source_to_admissible_source_result_review_report import (
    DEFAULT_OUT as LADDER_REVIEW_PATH,
    NEXT_TARGET as OBLIGATION_INDEX_TARGET,
    OUTCOME_ID as LADDER_REVIEW_OUTCOME,
    REVIEWED_COMMIT,
    build_qft_gr_source_map_ladder_packet_from_candidate_source_to_admissible_source_result_review,
)
from formal.python.tools.select_next_global_toe_work_target_from_mathematical_obligation_index_report import (
    DEFAULT_OUT as SELECTION_PATH,
    OUTCOME_ID as SELECTION_OUTCOME,
    build_select_next_global_toe_work_target_from_mathematical_obligation_index,
)


REPO_ROOT = find_repo_root(Path(__file__))
MANIFEST_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_SOURCE_MAP_LADDER_PACKET_DIRTY_FILE_MANIFEST_20260616_v0.txt"
)
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
SURFACES_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
)
TOE_FORMAL_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
FRONTIER_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CrossPillarClosureFrontier.lean"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _workstream(payload: dict, workstream_id: str) -> dict:
    for row in payload["workstreams"]:
        if row["workstream_id"] == workstream_id:
            return row
    raise AssertionError(f"Missing workstream: {workstream_id}")


def test_dirty_manifest_uses_relative_paths_only() -> None:
    text = _read(MANIFEST_PATH)
    assert "C:/" not in text
    assert "C:\\" not in text
    assert "formal/docs/release/" in text
    assert "formal/python/tools/" in text
    assert "formal/toe_formal/" in text


def test_ladder_result_review_binds_preserved_artifact() -> None:
    review = _json(LADDER_REVIEW_PATH)
    assert review["outcome_id"] == LADDER_REVIEW_OUTCOME
    assert review["accepted"] is True
    assert review["reviewed_commit"] == REVIEWED_COMMIT
    assert (
        review["reviewed_live_target_before_review"]
        == "review_qft_gr_source_map_ladder_packet_from_candidate_source_to_admissible_source_result"
    )
    assert review["selected_next_target"] == OBLIGATION_INDEX_TARGET
    assert review["first_ladder_break_row_id"] == QFT_GR_FIRST_BREAK_ROW_ID
    assert review["source_admissibility_claimed"] is False
    assert review["qft_gr_source_map_closure_claimed"] is False
    assert review["repair_loop_authorized"] is False
    generated = (
        build_qft_gr_source_map_ladder_packet_from_candidate_source_to_admissible_source_result_review()
    )
    assert generated == review


def test_minimal_obligation_index_is_small_and_calculation_oriented() -> None:
    index = _json(INDEX_PATH)
    assert index["outcome_id"] == INDEX_OUTCOME
    assert index["prepared"] is True
    assert index["global_maturity_matrix_deferred"] is True
    assert "UNKNOWN_OR_UNASSESSED" in ALLOWED_MATURITY_STATES
    assert index["central_field"] == "first_required_calculation"
    assert index["obligation_row_count"] <= 8
    rows = index["obligation_rows"]
    assert {row["unit_type"] for row in rows} >= {
        "pillar",
        "seam",
        "candidate_family",
        "computational_layer",
    }
    qft_gr = next(row for row in rows if row["unit_id"] == "QFT_GR")
    assert qft_gr["maturity_state"] == "BOUNDED_OBSTRUCTION"
    assert qft_gr["artifact_maturity"] == "preserved_packet_plus_review"
    assert qft_gr["formal_maturity"] == "first_break_recorded"
    assert qft_gr["scientific_maturity"] == "source_admissibility_blocked"
    assert qft_gr["first_unresolved_blocker"] == QFT_GR_FIRST_BREAK_ROW_ID
    assert qft_gr["first_required_calculation"] == QFT_GR_FIRST_REQUIRED_CALCULATION
    assert qft_gr["next_calculation_target"] == QFT_GR_CALCULATION_TARGET
    assert index["calculation_executed_by_this_index"] is False
    assert index["theory_closure_claimed"] is False
    assert build_minimal_global_toe_mathematical_obligation_index() == index


def test_index_review_and_selector_authorize_only_calculation_packet() -> None:
    review = _json(INDEX_REVIEW_PATH)
    assert review["outcome_id"] == INDEX_REVIEW_OUTCOME
    assert review["accepted"] is True
    assert review["selected_next_target"] == SELECTION_TARGET
    assert review["selection_only_authorized"] is True
    assert review["calculation_packet_not_yet_prepared_by_this_review"] is True
    assert build_minimal_global_toe_mathematical_obligation_index_result_review() == review

    selection = _json(SELECTION_PATH)
    assert selection["outcome_id"] == SELECTION_OUTCOME
    assert selection["selected"] is True
    assert selection["selected_next_target"] == QFT_GR_CALCULATION_TARGET
    assert selection["selected_target_is_calculation_packet"] is True
    assert selection["selected_target_executes_repair"] is False
    assert selection["qft_gr_first_required_calculation"] == QFT_GR_FIRST_REQUIRED_CALCULATION
    assert build_select_next_global_toe_work_target_from_mathematical_obligation_index() == selection


def test_calculation_packet_has_actual_mathematical_acceptance_content() -> None:
    packet = _json(CALCULATION_PACKET_PATH)
    assert packet["outcome_id"] == CALCULATION_PACKET_OUTCOME
    assert packet["prepared"] is True
    assert packet["calculation_result"] == CALCULATION_RESULT
    assert packet["selected_next_target"] == CALCULATION_PACKET_REVIEW_TARGET
    assert packet["weak_pairing_definition"]["well_defined_pairing"] == "blocked"
    outputs = packet["mathematical_acceptance_outputs"]
    assert outputs["definition_supplied"] is True
    assert outputs["lemma_or_proposition_stated"] is True
    assert outputs["well_definedness_proof_attempted"] is True
    assert outputs["counterexample_or_obstruction_recorded"] is True
    assert outputs["calculation_blocked_by_missing_formal_input"] is True
    assert "T : D -> R" in packet["weak_pairing_definition"]["distributional_requirement"]
    assert "integral_M" in packet["weak_pairing_definition"]["smooth_or_locally_integrable_template"]
    assert packet["well_defined_pairing"] == "blocked"
    assert packet["missing_mathematical_data_count"] >= 4
    assert all(
        row["status"] == "NOT_REACHED"
        for row in packet["calculation_progression"]
        if row["stage"] != "weak_pairing"
    )
    for key in [
        "source_admissibility_claimed",
        "Bianchi_compatibility_claimed",
        "semiclassical_einstein_equation_derived",
        "qft_gr_closure_claimed",
        "qft_gr_seam_closed",
        "empirical_validation_claimed",
        "public_submission_authorized",
        "master_action_promoted",
    ]:
        assert packet[key] is False, key
    assert (
        build_qft_gr_source_action_test_action_weak_pairing_domain_calculation_packet()
        == packet
    )


def test_registry_surfaces_and_imports_record_calculation_review_history() -> None:
    registry = _json(REGISTRY_PATH)
    calculation_packet = _workstream(registry, QFT_GR_CALCULATION_TARGET)
    assert calculation_packet["status"] == "paused"
    assert calculation_packet["selected_next_target"] == CALCULATION_PACKET_REVIEW_TARGET
    assert calculation_packet["report"] == (
        "formal/docs/release/"
        "QFT_GR_SOURCE_ACTION_TEST_ACTION_WEAK_PAIRING_DOMAIN_CALCULATION_PACKET_20260616_v0.json"
    )
    assert calculation_packet["outcome_id"] == CALCULATION_PACKET_OUTCOME

    calculation_review = _workstream(registry, CALCULATION_PACKET_REVIEW_TARGET)
    assert calculation_review["status"] == "paused"
    assert calculation_review["calculation_result"] == CALCULATION_RESULT

    joined = "\n".join(
        _read(path)
        for path in [SURFACES_PATH, TOE_FORMAL_PATH, FRONTIER_PATH, REGISTRY_PATH]
    )
    for token in [
        "QFTGRSourceActionTestActionWeakPairingDomainCalculationPacket",
        CALCULATION_PACKET_REVIEW_TARGET,
        CALCULATION_PACKET_OUTCOME,
        CALCULATION_RESULT,
        "no source admissibility",
        "no QFT-GR closure",
    ]:
        assert token in joined


def test_qft_gr_weak_pairing_calculation_gate_not_manifest_enrolled() -> None:
    assert_focused_gate_not_manifest_enrolled(
        "test_qft_gr_source_action_test_action_weak_pairing_domain_calculation_packet_gate.py"
    )

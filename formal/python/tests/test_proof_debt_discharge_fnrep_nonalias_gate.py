from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_current_target_consistent,
    assert_focused_gate_not_manifest_enrolled,
    assert_forbidden_promotions_closed,
    assert_frontier_matches_registry,
    assert_public_surfaces_match_registry,
    skip_if_not_current_target,
    workstream,
)


REPO_ROOT = find_repo_root(Path(__file__))
SOURCE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "FNRepNonAliasEquivalence01.lean"
)
DISCHARGE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "FNRepNonAliasEquivalence01Discharge.lean"
)
RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "FNRepNonAliasEquivalence01DischargeResultReview.lean"
)
PREP_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ProofDebtLedgerDischargeLane.lean"
)
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PROOF_DEBT_DISCHARGE_FNREP_NONALIAS_20260503_v0.json"
)
RESULT_REVIEW_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PROOF_DEBT_DISCHARGE_FNREP_NONALIAS_RESULT_REVIEW_20260503_v0.json"
)
LEDGER_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "LEAN_AXIOM_SPEC_BACKED_LEDGER_v0.md"
)
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
README_PATH = REPO_ROOT / "README.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STRICT_MAP_PATH = (
    REPO_ROOT / "formal" / "docs" / "lanes" / "STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md"
)
SEAM_REGISTRY_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md"
)
SEAM_INVENTORY_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md"
)
MATH_PHYSICS_INVENTORY_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
)

SOURCE_EVIDENCE = str(SOURCE_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
DISCHARGE_EVIDENCE = str(DISCHARGE_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
RESULT_REVIEW_EVIDENCE = str(RESULT_REVIEW_PATH.relative_to(REPO_ROOT)).replace(
    "\\", "/"
)
PREP_EVIDENCE = str(PREP_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
REPORT_EVIDENCE = str(REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
RESULT_REVIEW_REPORT_EVIDENCE = str(
    RESULT_REVIEW_REPORT_PATH.relative_to(REPO_ROOT)
).replace("\\", "/")
LEDGER_EVIDENCE = str(LEDGER_PATH.relative_to(REPO_ROOT)).replace("\\", "/")

SURFACE_ID = "fnrep_nonalias_default_nonalias_discharge_v0"
RESULT_REVIEW_SURFACE_ID = "fnrep_nonalias_default_nonalias_discharge_result_review_v0"
EXECUTION_TARGET = "execute_selected_proof_debt_discharge_item"
REVIEW_TARGET = "review_fnrep_nonalias_default_nonalias_discharge_result"
POST_REVIEW_TARGET = "select_next_post_proof_debt_discharge_bounded_attack"
PREPARED_TOKEN = "PROOF_DEBT_LEDGER_DISCHARGE_LANE_PREPARED"
RESULT_TOKEN = "FNREP_NONALIAS_DEFAULT_NONALIAS_DISCHARGED_LEAN_BACKED"
REVIEW_TOKEN = (
    "FNREP_NONALIAS_DEFAULT_NONALIAS_DISCHARGE_RESULT_REVIEW_CONSUMED_LEAN_BACKED"
)
REFINEMENT_TOKEN = "FNREP_NONALIAS_DEFAULT_NONALIAS_REFINED_NOT_DISCHARGED"
SELECTED_ITEM = f"{SOURCE_EVIDENCE}::defaultNonAlias"
ACTIVE_LANE = "proof_debt_ledger_discharge_lane"
RESULT_REVIEW_SLICE = "fnrep_nonalias_default_nonalias_discharge_result_review_v0"
POST_REVIEW_SLICE = "post_proof_debt_discharge_bounded_attack_selection_v0"
NONCLAIM_BOUNDARY = "fnrep_nonalias_default_nonalias_discharge_result_review_nonclaim_boundary"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def _registry() -> dict[str, Any]:
    return _json(REGISTRY_PATH)


def test_selected_default_nonalias_axiom_is_replaced_by_definitions() -> None:
    source = _read(SOURCE_PATH)

    assert "axiom defaultNonAlias" not in source
    for token in {
        "def defaultRep32",
        "def defaultNonAlias",
        "theorem defaultNonAlias_eq_zero_rep32_false",
        "theorem defaultNonAlias_tag_false",
        "def sampleRep32",
        "theorem diagnosticNonAlias_not_eligible",
    }:
        assert token in source


def test_discharge_surface_records_successful_lean_backed_result() -> None:
    text = _read(DISCHARGE_PATH)

    for token in {
        SURFACE_ID,
        EXECUTION_TARGET,
        PREPARED_TOKEN,
        RESULT_TOKEN,
        REPORT_EVIDENCE,
        REVIEW_TARGET,
        SELECTED_ITEM,
        "defaultRep32_and_defaultNonAlias_defs",
        "FNRepNonAliasDefaultDischargeStatus",
        "defaultNonAlias_discharge_eq_zero_rep32_false",
        "defaultNonAlias_roundtrip_to_defaultRep32",
        "defaultNonAlias_discharge_tag_false",
        "fnrep_nonalias_default_discharge_consumes_live_target_v0",
        "fnrep_nonalias_default_discharge_consumes_prepared_token_v0",
        "fnrep_nonalias_default_discharge_selected_item_v0",
        "fnrep_nonalias_default_discharge_lean_backed_v0",
        "fnrep_nonalias_default_discharge_result_token_v0",
        "fnrep_nonalias_default_discharge_axiom_removed_v0",
    }:
        assert token in text

    for theorem in {
        "fnrep_nonalias_default_discharge_no_pillar_completion_v0",
        "fnrep_nonalias_default_discharge_no_seam_closure_v0",
        "fnrep_nonalias_default_discharge_no_phase2_readiness_v0",
        "fnrep_nonalias_default_discharge_no_empirical_claim_v0",
        "fnrep_nonalias_default_discharge_master_action_not_promoted_v0",
    }:
        assert theorem in text


def test_discharge_report_and_ledger_record_axiom_count_drop() -> None:
    report = _json(REPORT_PATH)
    ledger = _read(LEDGER_PATH)

    assert report["schema_id"] == "PROOF_DEBT_DISCHARGE_FNREP_NONALIAS_20260503_v0"
    assert report["execution_status"] == "completed_successful_discharge"
    assert report["current_target"] == EXECUTION_TARGET
    assert report["consumed_prepared_lane_token"] == PREPARED_TOKEN
    assert report["selected_debt_item"] == SELECTED_ITEM
    assert report["discharge_surface"] == DISCHARGE_EVIDENCE
    assert report["result_token"] == RESULT_TOKEN
    assert report["refinement_token_not_used"] == REFINEMENT_TOKEN
    assert report["prior_authority"] == "SPEC_BACKED_DECLARATION_LEVEL_WITNESS"
    assert report["resulting_authority"] == "LEAN_BACKED_DEFINITION_AND_THEOREM"
    assert report["axiom_removed"] is True
    assert report["ledger_row_removed"] is True
    assert report["real_axiom_count_before"] == 61
    assert report["real_axiom_count_after"] == 60
    assert report["remaining_same_file_axiom"] == "sampleRep32"
    assert report["next_target"] == REVIEW_TARGET
    assert not any(report["nonclaim_boundaries"].values())

    assert "real_axiom_count_v0: 59" in ledger
    assert f"| `defaultNonAlias` | `{SOURCE_EVIDENCE}` |" not in ledger
    assert f"| `sampleRep32` | `{SOURCE_EVIDENCE}` |" not in ledger


def test_registry_rotates_to_fnrep_nonalias_discharge_result_review() -> None:
    assert_current_target_consistent()
    assert_frontier_matches_registry()
    assert_forbidden_promotions_closed()
    assert_public_surfaces_match_registry()
    payload = _registry()
    skip_if_not_current_target(payload, POST_REVIEW_TARGET)
    state = payload["current_target_state"]

    assert state["previous_live_next_target"] == REVIEW_TARGET
    assert state["live_next_target"] == POST_REVIEW_TARGET
    assert state["live_next_target_evidence"] == RESULT_REVIEW_EVIDENCE
    assert state["active_lane"] == ACTIVE_LANE

    active = workstream(ACTIVE_LANE, payload)
    assert active["status"] == "active"
    assert active["retained_blocker"] == NONCLAIM_BOUNDARY
    assert active["authorization_evidence"] == RESULT_REVIEW_EVIDENCE
    assert active["authorized_next_slice"] == POST_REVIEW_SLICE
    assert active["authorized_next_strict_target"] == POST_REVIEW_TARGET
    assert active["consumed_target"] == REVIEW_TARGET
    assert active["latest_surface"] == RESULT_REVIEW_SURFACE_ID
    assert active["execution_surface"] == DISCHARGE_EVIDENCE
    assert active["execution_report"] == REPORT_EVIDENCE
    assert active["review_surface"] == RESULT_REVIEW_EVIDENCE
    assert active["review_report"] == RESULT_REVIEW_REPORT_EVIDENCE
    assert active["consumed_prepared_lane_token"] == PREPARED_TOKEN
    assert active["discharge_result_token"] == RESULT_TOKEN
    assert active["result_token"] == REVIEW_TOKEN
    assert active["selected_debt_item"] == SELECTED_ITEM
    assert active["prior_authority"] == "SPEC_BACKED_DECLARATION_LEVEL_WITNESS"
    assert active["resulting_authority"] == "LEAN_BACKED_DEFINITION_AND_THEOREM"
    assert active["real_axiom_count_before"] == 61
    assert active["real_axiom_count_after"] == 60
    assert active["axiom_removed"] == "yes"
    assert active["debt_item_discharged"] == "yes"
    assert active["proof_debt_ledger"] == LEDGER_EVIDENCE
    assert active["pillar_completion_inferred"] == "no"
    assert active["seam_closure_claim"] == "no"
    assert active["phase2_readiness_claim"] == "no"
    assert active["empirical_adequacy_claim"] == "no"
    assert active["master_action_promotion_authorized"] == "no"

    qft_gr = workstream("qft_gr_source_map", payload)
    assert qft_gr["authorized_next_strict_target"] == POST_REVIEW_TARGET
    assert qft_gr["proof_debt_discharge_result_token"] == RESULT_TOKEN
    assert qft_gr["qft_gr_witness_search_plan_selected"] == "no"
    assert qft_gr["full_source_map_closure_authorized"] == "no"

    master_action = workstream("master_action_dependency_frontier", payload)
    assert master_action["authorized_next_strict_target"] == POST_REVIEW_TARGET
    assert master_action["master_action_current_citation_target"] == POST_REVIEW_TARGET
    assert master_action["proof_debt_discharge_result_token"] == RESULT_TOKEN
    assert master_action["master_action_promotion_authorized"] == "no"

    assert REVIEW_TARGET in payload["next_strict_target_coverage"]
    assert POST_REVIEW_TARGET in payload["next_strict_target_coverage"]
    assert NONCLAIM_BOUNDARY in payload["retained_blocker_coverage"]


def test_public_surfaces_track_fnrep_nonalias_discharge() -> None:
    for path in [
        README_PATH,
        STATE_PATH,
        ROADMAP_PATH,
        STRICT_MAP_PATH,
        SEAM_REGISTRY_PATH,
        SEAM_INVENTORY_PATH,
    ]:
        text = _read(path)
        assert REVIEW_TARGET in text
        assert POST_REVIEW_TARGET in text
        assert DISCHARGE_EVIDENCE in text
        assert REPORT_EVIDENCE in text
        assert RESULT_TOKEN in text
        assert SELECTED_ITEM in text

    inventory = _read(MATH_PHYSICS_INVENTORY_PATH)
    assert "INV-MATH-PROOF-DEBT-DISCHARGE-FNREP-NONALIAS-v0" in inventory
    assert DISCHARGE_EVIDENCE in inventory
    assert REPORT_EVIDENCE in inventory
    assert RESULT_TOKEN in inventory

    assert_focused_gate_not_manifest_enrolled(
        "test_proof_debt_discharge_fnrep_nonalias_gate.py"
    )

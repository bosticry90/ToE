from __future__ import annotations

"""Select the bounded targeted-recovery outcome and nonautomatic construction handoff."""

if __name__ == "__main__" and (__package__ is None or __package__ == ""):
    raise SystemExit("Run this tool as a module with .\\py.ps1 -m")

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_ROOT = REPO_ROOT / "formal/docs/release"
PROGRAM_ID = "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0"
STAGE_ID = "TARGETED_CCFT_RECOVERY_RESULT_AND_CONSTRUCTION_HANDOFF"
TARGET = "select_toe_post_targeted_ccft_recovery_construction_handoff_v0"
OUTCOME = "TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERED"
MANDATORY_EXIT_TARGET = "close_toe_targeted_ccft_closure_evidence_recovery_v0_after_bounded_result_v0"
CONSTRUCTION_PREPARATION_TARGET = "prepare_bounded_ccft_v0_theory_construction_program"
STAGE3_RESULT = RELEASE_ROOT / (
    "TOE_TARGETED_CCFT_CONTRACT_COMPLETENESS_AND_CONFLICT_ADJUDICATION_RESULT_v0.json"
)
AUTHORITY = RELEASE_ROOT / (
    "TOE_TARGETED_CCFT_RECOVERY_RESULT_AND_CONSTRUCTION_HANDOFF_"
    "STAGE_4_OPEN_AUTHORITY_v0.json"
)
MANIFEST = RELEASE_ROOT / (
    "bounded_program_manifests/TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0_MANIFEST_v1.json"
)
OPEN_EVENT = RELEASE_ROOT / (
    "bounded_program_events/TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0_ATTEMPT_04_OPEN_v0.json"
)
RESULT_PATH = RELEASE_ROOT / (
    "TOE_TARGETED_CCFT_RECOVERY_RESULT_AND_CONSTRUCTION_HANDOFF_RESULT_v0.json"
)


def _load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _write(path: Path, value: dict[str, Any]) -> None:
    if path.exists():
        raise ValueError(f"immutable result already exists: {path}")
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n",
        encoding="ascii",
        newline="\n",
    )


def _stage() -> dict[str, Any]:
    stage = _load(MANIFEST)["stages"][3]
    if stage["stage_number"] != 4 or stage["semantic_stage_id"] != STAGE_ID:
        raise ValueError("manifest Stage 4 mismatch")
    if stage["canonical_target"] != TARGET:
        raise ValueError("manifest Stage 4 target mismatch")
    return stage


def build_result(*, captured_at_utc: str) -> dict[str, Any]:
    stage3 = _load(STAGE3_RESULT)
    authority = _load(AUTHORITY)
    manifest = _load(MANIFEST)
    open_event = _load(OPEN_EVENT)
    summary = stage3["adjudication_summary"]
    if summary["exact_contracts_recovered"] != 4 or summary["conflicts_preserved"] != 3:
        raise ValueError("frozen Stage 3 counts do not satisfy the handoff authority")
    if authority["scientific_input_summary"]["positive_recovery_threshold_satisfied"] is not True:
        raise ValueError("positive recovery threshold was not authorized as satisfied")
    if manifest["mandatory_exit"]["target"] != MANDATORY_EXIT_TARGET:
        raise ValueError("manifest mandatory exit target mismatch")
    handoff = manifest["required_post_outcome_handoff"]
    if handoff["target"] != CONSTRUCTION_PREPARATION_TARGET:
        raise ValueError("manifest construction-preparation target mismatch")
    recovered = stage3["future_new_postulate_reduction_ledger"]
    if len(recovered) != 4:
        raise ValueError("postulate-reduction ledger must contain four recovered contracts")

    status_counts = summary["checklist_status_counts"]
    return {
        "artifact_id": "TOE_TARGETED_CCFT_RECOVERY_RESULT_AND_CONSTRUCTION_HANDOFF_RESULT_v0",
        "schema_id": "toe.targeted_ccft.recovery_result_and_construction_handoff.result.v0",
        "captured_at_utc": captured_at_utc,
        "program_id": PROGRAM_ID,
        "semantic_stage_id": STAGE_ID,
        "scientific_target": TARGET,
        "scope_hash": _stage()["canonical_scope_hash"],
        "attempt_sequence_number": 4,
        "open_event_binding": {
            "path": OPEN_EVENT.relative_to(REPO_ROOT).as_posix(),
            "sha256": _sha(OPEN_EVENT),
            "event_hash": open_event["event_hash"],
        },
        "stage_3_input_binding": {
            "path": STAGE3_RESULT.relative_to(REPO_ROOT).as_posix(),
            "sha256": _sha(STAGE3_RESULT),
            "exact_contracts_recovered": 4,
            "conflicts_preserved": 3,
            "single_content_discovery_pass_consumed": True,
            "selected_source_count": 96,
            "overflow_source_count_not_reviewed": 137,
        },
        "exactly_one_program_scientific_outcome": OUTCOME,
        "program_scientific_outcome": OUTCOME,
        "program_outcome_selection_basis": {
            "positive_threshold": 1,
            "exact_contracts_recovered": 4,
            "threshold_satisfied": True,
            "alternative_outcome_selected": False,
        },
        "recovered_partial_conflicting_and_absent_contract_summary": {
            "recovered_exact": status_counts["RECOVERED_EXACT_CLOSURE_CONTRACT"],
            "conflict_preserved": status_counts["CONFLICT_PRESERVED_NO_CONTRACT_RECOVERED"],
            "exact_application_blocked_by_conflict": status_counts["EXACT_EVIDENCE_APPLICATION_BLOCKED_BY_CONFLICT"],
            "exact_configuration_bound": status_counts["EXACT_EVIDENCE_CONFIGURATION_BOUND_NOT_GENERAL_CONTRACT"],
            "exact_incomplete_parameter_range": status_counts["EXACT_EVIDENCE_INCOMPLETE_PARAMETER_RANGE"],
            "only_nonexact_evidence": status_counts["ONLY_NONEXACT_EVIDENCE_NO_CONTRACT_RECOVERED"],
            "no_relevant_evidence": status_counts["NO_RELEVANT_EVIDENCE_NO_CONTRACT_RECOVERED"],
            "checklist_total": 18,
            "cp_nlse_governing_equation_resolved": False,
            "cp_nlse_interaction_dispersion_resolved": False,
            "lcrd_v3_model_closed": False,
        },
        "new_postulate_reduction_summary": {
            "contract_count": 4,
            "cp_nlse_contract_count": 1,
            "lcrd_v3_contract_count": 3,
            "contracts": recovered,
            "branch_or_model_selection_implied": False,
        },
        "historical_recovery_boundary": {
            "ccft_v0_historical_recovery_complete": True,
            "additional_archive_or_overflow_search_authorized": False,
            "second_targeted_pass_authorized": False,
            "repository_claim_exhaustion_established": False,
            "unreviewed_material_may_exist_but_does_not_reopen_recovery": True,
        },
        "branch_readiness_snapshot": {
            "CP_NLSE": {
                "strength": "COMPUTATIONAL_AND_NUMERICAL_SCAFFOLDING",
                "recovered_contract": "ONE_DIMENSIONAL_PERIODIC_DOMAIN_AND_BOUNDARY",
                "decisive_blocker": "GOVERNING_EQUATION_AND_NONLINEAR_DISPERSION_CONFLICT",
                "selected_for_ccft_v0": False,
            },
            "LCRD_V3": {
                "strength": "DISTINCTIVE_FOUR_FIELD_ROTOR_CURVATURE_STRUCTURE",
                "recovered_contracts": ["STATE_TUPLE", "Q_ROTOR_CLOSURE", "EVOLUTION_COUPLINGS"],
                "decisive_blocker": "DATA_NORMALIZATION_PARAMETER_AND_IMPLEMENTATION_CONTRACTS_INCOMPLETE",
                "selected_for_ccft_v0": False,
            },
            "combined_model_authorized": False,
            "branch_selected": "NONE",
        },
        "required_nonautomatic_construction_preparation_handoff": {
            "target": CONSTRUCTION_PREPARATION_TARGET,
            "preparation_authorized": False,
            "installation_authorized": False,
            "scientific_stage_authorized": False,
            "mandatory_exit_must_complete_first": True,
            "recommended_program_scope": "CCFT_V0_MINIMAL_MODEL_CONSTRUCTION_AND_THEOREM_DISCOVERY",
            "research_director_decision_packet_required_first": True,
            "branch_readiness_decision_required_before_equation_freeze": True,
            "required_provenance_labels": [
                "SOURCE_RECOVERED",
                "KNOWN_PHYSICS_BASELINE",
                "NEW_CCFT_POSTULATE",
                "NUMERICAL_CONVENTION",
                "MATHEMATICAL_CONTROL",
            ],
            "recommended_theorem_packet_lanes": [
                "PROVE",
                "DISPROVE",
                "CONSTRUCT",
                "FIND_COUNTEREXAMPLE",
                "SYMBOLIC_CHECK",
                "NUMERICAL_CHECK",
                "LEAN_FORMALIZE_WHERE_FEASIBLE",
            ],
            "recommended_cross_cutting_checks_not_installed_here": [
                "C_FINITE_APPROXIMATION",
                "C_IDENTIFIABILITY",
                "C_COMPLEXITY",
            ],
        },
        "immediate_successor": {
            "target": MANDATORY_EXIT_TARGET,
            "kind": "MANDATORY_PROGRAM_EXIT",
            "selected": True,
            "completed": False,
        },
        "nonclaim_boundary": {
            "cp_nlse_or_lcrd_branch_selected": False,
            "governing_equation_selected_repaired_or_postulated": False,
            "ccft_v0_model_selected_or_constructed": False,
            "construction_program_prepared_installed_or_opened": False,
            "theorem_discovery_lane_authorized_or_executed": False,
            "new_proof_counterexample_symbolic_or_numerical_result_created": False,
            "cross_cutting_checks_installed": False,
            "physical_operationalization_or_empirical_claim_established": False,
            "evidence_promoted": False,
            "repository_claim_exhaustion_established": False,
        },
        "lifecycle_result": "PASSED",
        "status": "STAGE_4_HANDOFF_RESULT_READY_FOR_INDEPENDENT_REVIEW_AND_ATOMIC_CLOSE",
    }


def execute(*, captured_at_utc: str) -> dict[str, Any]:
    result = build_result(captured_at_utc=captured_at_utc)
    _write(RESULT_PATH, result)
    return result


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--captured-at-utc", required=True)
    args = parser.parse_args(argv)
    result = execute(captured_at_utc=args.captured_at_utc)
    print(json.dumps({
        "program_scientific_outcome": result["program_scientific_outcome"],
        "exact_contracts_recovered": result["stage_3_input_binding"]["exact_contracts_recovered"],
        "immediate_successor": result["immediate_successor"]["target"],
    }, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "V01_ALPHA_TRANCHE_004_RETAINED_SOURCE_MAP_BLOCKER_DECLARATION_20260515_v0"
DECLARATION_ID = "V01_ALPHA_TRANCHE_004_RETAINED_SOURCE_MAP_BLOCKER_DECLARATION_v0"
OUTCOME_ID = (
    "V01_ALPHA_TRANCHE_004_RETAINED_SOURCE_MAP_BLOCKER_DECLARATION_PREPARED_AFTER_"
    "FAIL_CLOSED_WITNESS_CHAIN_ATTEMPT_WITH_NO_RELEASE_PROMOTION"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_ATTEMPT_RESULT_REVIEW_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_TRANCHE_004_RETAINED_SOURCE_MAP_BLOCKER_DECLARATION_20260515_v0.json"
)

EXPECTED_RESULT_REVIEW_ID = (
    "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_ATTEMPT_RESULT_REVIEW_v0"
)
EXPECTED_RESULT_REVIEW_OUTCOME = (
    "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_ATTEMPT_RESULT_REVIEW_"
    "ACCEPTS_FAIL_CLOSED_RETAINED_BLOCKER_AND_AUTHORIZES_RETAINED_BLOCKER_DECLARATION_"
    "PREPARATION_ONLY"
)
EXPECTED_RESULT_REVIEW_SELECTED_TARGET = (
    "prepare_v01_alpha_tranche_004_retained_source_map_blocker_declaration"
)

TRANCHE_001_STATUS = "documented_dependency_nonblocking"
TRANCHE_002_STATUS = "documented_dependency_nonblocking"
TRANCHE_003_STATUS = "documented_dependency_nonblocking"
SELECTED_TRANCHE_ID = "V01-ALPHA-DEP-REM-TRANCHE-004"
SELECTED_FINDING_ID = "V01-ALPHA-DEP-REM-004"
SELECTED_DEPENDENCY = (
    "qft_gr_source_map_eligibility_ladder_summary_source_map_not_authorized_v0"
)
SELECTED_DEPENDENCY_CLASS = "blocked_bridge_authorization_dependency"
CURRENT_BLOCKER = "full_source_map_semantic_closure_not_authorized"
BLOCKER_REASON = (
    "obligation_ladder_constructed_witness_chain_absent_source_map_closure_not_authorized"
)
PROJECT_AXIOMS_USED: list[str] = []
LEAN_AXIOMS_USED: list[str] = []

CONSTRUCTION_ATTEMPT_CLASSIFICATION = "construction_attempt_failed_retained_blocker"
DECLARATION_CLASSIFICATION = (
    "retained_source_map_authorization_release_blocker_declared_after_fail_closed_attempt"
)
NEXT_TARGET = "review_v01_alpha_tranche_004_retained_source_map_blocker_declaration_result"

REQUIRED_WITNESS_CHAIN_COMPONENTS = [
    "renormalization_validity_witness",
    "finite_stress_energy_tensor_witness",
    "conservation_witness",
    "bianchi_compatibility_witness",
    "einstein_coupling_witness",
    "weak_curvature_source_identification_witness",
    "poisson_recovery_witness",
    "newtonian_weak_field_recovery_witness",
    "semiclassical_einstein_equation_witness",
    "qft_gr_source_map_closure_witness",
]

REQUIRED_SOURCE_MAP_SEMANTIC_CLOSURE_CONDITIONS = [
    "positive_full_source_map_semantic_closure_authorization_readout",
    "witness_chain_complete_for_all_required_qft_gr_source_map_layers",
    "semantic_closure_proof_or_equivalent_reviewed_evidence",
    "no_reinterpretation_of_negative_authorization_marker_as_closure",
    "expert_review_acceptance_before_any_blocker_downgrade",
]

FORBIDDEN_EFFECTS = [
    "additional_construction_attempt_authorized",
    "additional_construction_attempt_executed",
    "source_map_authorization_status_adjudication_packet_preparation_authorized",
    "documented_nonblocking_status_authorized",
    "tranche_004_moved_to_documented_dependency_nonblocking",
    "source_map_closure_claimed",
    "source_map_semantic_closure_authorized",
    "qft_gr_seam_closed",
    "witness_chain_constructed",
    "partial_witness_chain_constructed",
    "source_map_witness_chain_evidence_constructed",
    "source_map_witness_chain_construction_successful",
    "blocker_movement_registered",
    "blocker_movement_authorized",
    "blocker_fully_remediated",
    "release_packet_assembled",
    "v01_alpha_marked_ready",
    "lean_theorem_debt_discharged",
    "axiom_spec_backed_debt_reduced",
    "axiom_spec_backed_debt_reduced_by_documentation",
    "proof_debt_reduced",
    "retained_assumptions_discharged",
    "theorem_discharge_authorized",
    "lane_reopen_authorized",
    "phase2_authorized",
    "seam_closure_authorized",
    "empirical_validation_authorized",
    "master_action_promotion_authorized",
    "claim_promotion_authorized",
    "computational_physics_execution_surface_opened",
]


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _release_blockers(result_review: dict[str, Any]) -> list[dict[str, Any]]:
    return list(result_review.get("release_blocking_obligations_carry_forward", []))


def _selected_obligation(rows: list[dict[str, Any]]) -> dict[str, Any]:
    for row in rows:
        if row.get("dependency_finding_id") == SELECTED_FINDING_ID:
            return dict(row)
    return {}


def _release_blockers_tracked(rows: list[dict[str, Any]]) -> bool:
    return (
        len(rows) == 3
        and [row.get("dependency_finding_id") for row in rows]
        == [
            "V01-ALPHA-DEP-REM-004",
            "V01-ALPHA-DEP-REM-005",
            "V01-ALPHA-DEP-REM-006",
        ]
        and all(row.get("modified_by_tranche_003") is False for row in rows)
        and all(
            row.get("status_carry_forward") == "tracked_unmodified_not_audited_in_tranche_003"
            for row in rows
        )
    )


def _future_tranches_005_006_tracked(result_review: dict[str, Any]) -> bool:
    rows = list(result_review.get("other_release_blocking_obligations", []))
    return (
        len(rows) == 2
        and [row.get("dependency_finding_id") for row in rows]
        == ["V01-ALPHA-DEP-REM-005", "V01-ALPHA-DEP-REM-006"]
        and all(row.get("modified_by_tranche_004") is False for row in rows)
        and all(
            row.get("status_carry_forward") == "tracked_unmodified_not_audited_in_tranche_004"
            for row in rows
        )
    )


def build_declaration(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    source_map = dict(result_review.get("source_map_authorization_status", {}))
    lean = dict(result_review.get("lean_audit_result", {}))
    release_blockers = _release_blockers(result_review)
    selected_obligation = _selected_obligation(release_blockers)
    missing_witnesses = list(result_review.get("missing_witness_components", []))
    unsatisfied_closure = list(
        result_review.get("unsatisfied_source_map_semantic_closure_conditions", [])
    )
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    retained_blocker_declaration = {
        "declaration_kind": "retained_source_map_authorization_release_blocker",
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_dependency_finding_id": SELECTED_FINDING_ID,
        "selected_dependency": SELECTED_DEPENDENCY,
        "attempt_result": CONSTRUCTION_ATTEMPT_CLASSIFICATION,
        "source_map_posture": CURRENT_BLOCKER,
        "retained_reason": BLOCKER_REASON,
        "witness_chain_constructed": False,
        "source_map_closure_authorized": False,
        "release_impact": "tranche_004_remains_release_blocking",
        "declaration_review_required_before_next_lane_routing": True,
    }

    release_impact = {
        "tranche_004_remains_release_blocking": True,
        "release_readiness_blocked_by_tranche_004": True,
        "release_assembly_allowed": False,
        "readiness_marking_allowed": False,
        "continue_to_tranches_005_006_before_declaration_review": False,
        "pause_release_readiness_decision_deferred_to_declaration_result_review": True,
    }

    acceptance_criteria = {
        "consumes_expected_result_review": result_review.get("review_id")
        == EXPECTED_RESULT_REVIEW_ID,
        "result_review_accepted": result_review.get("accepted") is True,
        "result_review_outcome_expected": result_review.get("outcome_id")
        == EXPECTED_RESULT_REVIEW_OUTCOME,
        "result_review_selected_this_declaration": result_review.get("selected_next_target")
        == EXPECTED_RESULT_REVIEW_SELECTED_TARGET,
        "attempt_result_preserved": result_review.get("construction_attempt_classification")
        == CONSTRUCTION_ATTEMPT_CLASSIFICATION
        and result_review.get("attempt_result", {}).get("classification")
        == CONSTRUCTION_ATTEMPT_CLASSIFICATION,
        "retained_blocker_preparation_authorized": result_review.get(
            "retained_source_map_blocker_declaration_preparation_authorized"
        )
        is True,
        "retained_blocker_review_had_not_prepared_declaration": result_review.get(
            "retained_source_map_blocker_declaration_prepared_by_review"
        )
        is False,
        "tranche_001_documented_nonblocking_preserved": result_review.get(
            "tranche_001_status"
        )
        == TRANCHE_001_STATUS,
        "tranche_002_documented_nonblocking_preserved": result_review.get(
            "tranche_002_status"
        )
        == TRANCHE_002_STATUS,
        "tranche_003_documented_nonblocking_preserved": result_review.get(
            "tranche_003_status"
        )
        == TRANCHE_003_STATUS,
        "tranche_004_selected_only": result_review.get("selected_tranche_id")
        == SELECTED_TRANCHE_ID
        and result_review.get("selected_remediation_finding_id") == SELECTED_FINDING_ID
        and result_review.get("selected_dependency") == SELECTED_DEPENDENCY,
        "selected_obligation_expected": selected_obligation.get("dependency")
        == SELECTED_DEPENDENCY
        and selected_obligation.get("dependency_class") == SELECTED_DEPENDENCY_CLASS,
        "current_blocker_preserved": result_review.get("current_blocker") == CURRENT_BLOCKER
        and source_map.get("authorization_status") == CURRENT_BLOCKER
        and source_map.get("full_source_map_semantic_closure_authorized") is False,
        "blocker_reason_preserved": result_review.get("blocker_reason") == BLOCKER_REASON
        and source_map.get("not_authorized_reason") == BLOCKER_REASON,
        "project_axioms_empty": result_review.get("project_axioms_used")
        == PROJECT_AXIOMS_USED
        and lean.get("project_axioms_used") == PROJECT_AXIOMS_USED
        and lean.get("project_axiom_count") == 0,
        "lean_audit_no_axioms_preserved": lean.get("parsed_axioms") == LEAN_AXIOMS_USED
        and lean.get("depends_on_no_axioms") is True,
        "missing_witnesses_preserved": missing_witnesses == REQUIRED_WITNESS_CHAIN_COMPONENTS
        and result_review.get("missing_witness_count") == 10,
        "semantic_closure_conditions_unsatisfied": unsatisfied_closure
        == REQUIRED_SOURCE_MAP_SEMANTIC_CLOSURE_CONDITIONS
        and result_review.get("unsatisfied_source_map_semantic_closure_condition_count") == 5,
        "declares_retained_release_blocker": retained_blocker_declaration[
            "declaration_kind"
        ]
        == "retained_source_map_authorization_release_blocker"
        and release_impact["tranche_004_remains_release_blocking"] is True,
        "no_additional_construction_attempt": forbidden_effect_status[
            "additional_construction_attempt_authorized"
        ]
        is False
        and forbidden_effect_status["additional_construction_attempt_executed"] is False,
        "no_witness_chain_construction": result_review.get("witness_chain_constructed")
        is False
        and result_review.get("partial_witness_chain_constructed") is False
        and forbidden_effect_status["witness_chain_constructed"] is False,
        "no_source_map_closure": result_review.get("source_map_closure_claimed") is False
        and result_review.get("source_map_semantic_closure_authorized") is False
        and forbidden_effect_status["source_map_closure_claimed"] is False,
        "no_qft_gr_seam_closure": result_review.get("qft_gr_seam_closed") is False
        and forbidden_effect_status["qft_gr_seam_closed"] is False,
        "tranche_004_not_moved_to_documented_nonblocking": result_review.get(
            "tranche_004_moved_to_documented_dependency_nonblocking"
        )
        is False
        and forbidden_effect_status["tranche_004_moved_to_documented_dependency_nonblocking"]
        is False
        and forbidden_effect_status["documented_nonblocking_status_authorized"] is False,
        "tranches_005_006_remain_tracked": _future_tranches_005_006_tracked(
            result_review
        ),
        "release_blockers_remain_tracked": _release_blockers_tracked(release_blockers),
        "no_blocker_movement": forbidden_effect_status["blocker_movement_registered"]
        is False
        and forbidden_effect_status["blocker_movement_authorized"] is False,
        "no_release_packet_assembly": forbidden_effect_status["release_packet_assembled"]
        is False
        and release_impact["release_assembly_allowed"] is False,
        "no_v01_readiness_marking": forbidden_effect_status["v01_alpha_marked_ready"]
        is False
        and release_impact["readiness_marking_allowed"] is False,
        "no_theorem_or_proof_debt_discharge": forbidden_effect_status[
            "lean_theorem_debt_discharged"
        ]
        is False
        and forbidden_effect_status["proof_debt_reduced"] is False
        and forbidden_effect_status["axiom_spec_backed_debt_reduced"] is False,
        "no_phase2_seam_empirical_or_master_action_authorization": all(
            forbidden_effect_status[key] is False
            for key in [
                "phase2_authorized",
                "seam_closure_authorized",
                "empirical_validation_authorized",
                "master_action_promotion_authorized",
            ]
        ),
        "forbidden_effects_all_false": all(
            value is False for value in forbidden_effect_status.values()
        ),
        "exactly_one_next_target_selected": NEXT_TARGET
        == "review_v01_alpha_tranche_004_retained_source_map_blocker_declaration_result",
    }
    accepted = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "declaration_id": DECLARATION_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "V01_ALPHA_TRANCHE_004_RETAINED_SOURCE_MAP_BLOCKER_DECLARATION_BLOCKED",
        "consumes_construction_attempt_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_construction_attempt_result_review_pointer": _ptr(result_review_path),
        "consumed_construction_attempt_result_review_schema_id": result_review.get(
            "schema_id"
        ),
        "declaration_scope": (
            "PREPARE_TRANCHE_004_RETAINED_SOURCE_MAP_BLOCKER_DECLARATION_ONLY_NO_"
            "ADDITIONAL_CONSTRUCTION_SOURCE_MAP_CLOSURE_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
        ),
        "tranche_001_status": TRANCHE_001_STATUS,
        "tranche_002_status": TRANCHE_002_STATUS,
        "tranche_003_status": TRANCHE_003_STATUS,
        "tranche_004_status": "retained_source_map_authorization_release_blocker_declared_pending_result_review",
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": SELECTED_FINDING_ID,
        "selected_dependency": SELECTED_DEPENDENCY,
        "selected_dependency_class": SELECTED_DEPENDENCY_CLASS,
        "selected_release_blocking_obligation": selected_obligation,
        "current_blocker": CURRENT_BLOCKER,
        "blocker_reason": BLOCKER_REASON,
        "source_map_authorization_status": source_map,
        "lean_audit_result": {
            "parsed_axioms": lean.get("parsed_axioms"),
            "project_axioms_used": lean.get("project_axioms_used"),
            "project_axiom_count": lean.get("project_axiom_count"),
            "depends_on_no_axioms": lean.get("depends_on_no_axioms"),
            "classification": lean.get("classification"),
        },
        "project_axioms_used": PROJECT_AXIOMS_USED,
        "construction_attempt_classification": CONSTRUCTION_ATTEMPT_CLASSIFICATION,
        "declaration_classification": DECLARATION_CLASSIFICATION,
        "retained_source_map_blocker_declaration_prepared": accepted,
        "retained_blocker_declaration": retained_blocker_declaration,
        "release_impact": release_impact,
        "required_witness_chain_components": REQUIRED_WITNESS_CHAIN_COMPONENTS,
        "missing_witness_components": missing_witnesses,
        "missing_witness_count": len(missing_witnesses),
        "required_source_map_semantic_closure_conditions": REQUIRED_SOURCE_MAP_SEMANTIC_CLOSURE_CONDITIONS,
        "unsatisfied_source_map_semantic_closure_conditions": unsatisfied_closure,
        "unsatisfied_source_map_semantic_closure_condition_count": len(unsatisfied_closure),
        "witness_chain_constructed": False,
        "partial_witness_chain_constructed": False,
        "source_map_witness_chain_evidence_constructed": False,
        "source_map_witness_chain_construction_successful": False,
        "source_map_closure_claimed": False,
        "source_map_semantic_closure_authorized": False,
        "qft_gr_seam_closed": False,
        "retained_blocker": True,
        "retained_blocker_reason": BLOCKER_REASON,
        "remains_release_blocking": True,
        "release_readiness_blocked_by_tranche_004": True,
        "tranche_004_moved_to_documented_dependency_nonblocking": False,
        "documented_nonblocking_status_authorized": False,
        "release_blocking_obligations_carry_forward": release_blockers,
        "release_blocking_obligation_count": len(release_blockers),
        "other_release_blocking_obligations": result_review.get(
            "other_release_blocking_obligations", []
        ),
        "other_release_blocking_obligation_count": result_review.get(
            "other_release_blocking_obligation_count", 0
        ),
        "additional_construction_attempt_authorized": False,
        "additional_construction_attempt_executed": False,
        "source_map_authorization_status_adjudication_packet_preparation_authorized": False,
        "documentation_alone_can_clear_blocker": False,
        "blocker_movement_authorized": False,
        "blocker_movement_registered": False,
        "blocker_fully_remediated": False,
        "release_packet_assembled": False,
        "v01_alpha_marked_ready": False,
        "lean_theorem_debt_discharged": False,
        "axiom_spec_backed_debt_reduced": False,
        "axiom_spec_backed_debt_reduced_by_documentation": False,
        "proof_debt_reduced": False,
        "retained_assumptions_discharged": False,
        "validation_claim_authorized": False,
        "forbidden_effect_status": forbidden_effect_status,
        "selected_next_target": NEXT_TARGET
        if accepted
        else "REMEDIATE_V01_ALPHA_TRANCHE_004_RETAINED_SOURCE_MAP_BLOCKER_DECLARATION",
        "selected_next_target_kind": "retained_source_map_blocker_declaration_result_review_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "REVIEW_TRANCHE_004_RETAINED_SOURCE_MAP_BLOCKER_DECLARATION_ONLY_NO_SOURCE_"
            "MAP_CLOSURE_BLOCKER_MOVEMENT_RELEASE_PROMOTION_OR_READINESS_MARKING"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": (
                    "The retained source-map blocker declaration must be reviewed before "
                    "choosing whether to pause release-readiness remediation or carry the "
                    "retained blocker while examining tranches 005 and 006."
                ),
            },
            {
                "target": "pause_v01_alpha_release_readiness_due_to_retained_tranche_004_blocker",
                "decision": "deferred_until_declaration_result_review",
                "reason": "Release-readiness pause is a review decision, not a declaration-preparation effect.",
            },
            {
                "target": "prepare_v01_alpha_dependency_remediation_next_tranche_selection_packet",
                "decision": "deferred_until_declaration_result_review",
                "reason": "Next-tranche routing must wait for declaration result review.",
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha tranche 004 retained source-map blocker declaration records "
            "that construction_attempt_failed_retained_blocker leaves tranche 004 release-"
            "blocking. It preserves full_source_map_semantic_closure_not_authorized, the "
            "absent witness-chain reason, project_axioms_used = [], no witness-chain "
            "construction, no source-map closure, no QFT-GR seam closure, no movement to "
            "documented/nonblocking, no release assembly, no readiness marking, no theorem/"
            "proof debt discharge, no Phase 2 authorization, no empirical validation, and "
            "no master-action promotion."
        ),
        "roadmap_update_required": True,
    }


def write_declaration(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_declaration(
        result_review_path=result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha tranche 004 retained source-map blocker declaration."
        )
    )
    parser.add_argument("--result-review", type=Path, default=DEFAULT_RESULT_REVIEW_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    result_review_path = (
        ns.result_review if ns.result_review.is_absolute() else (REPO_ROOT / ns.result_review)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_declaration(
        result_review_path=result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_tranche_004_retained_source_map_blocker_declaration_report: "
        f"accepted={payload['accepted']} classification={payload['declaration_classification']} "
        f"selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

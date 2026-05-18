from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_ATTEMPT_20260515_v0"
ATTEMPT_ID = "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_ATTEMPT_v0"
OUTCOME_ID = (
    "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_ATTEMPT_EXECUTED_"
    "WITH_NO_SOURCE_MAP_CLOSURE_OR_RELEASE_PROMOTION"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_RESULT_REVIEW_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_ATTEMPT_20260515_v0.json"
)

EXPECTED_RESULT_REVIEW_ID = (
    "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_RESULT_REVIEW_v0"
)
EXPECTED_RESULT_REVIEW_OUTCOME = (
    "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_RESULT_REVIEW_"
    "ACCEPTS_CONSTRUCTION_ROUTE_AND_SELECTS_BOUNDED_NEXT_ACTION_ONLY"
)
EXPECTED_RESULT_REVIEW_SELECTED_TARGET = (
    "execute_v01_alpha_tranche_004_source_map_witness_chain_construction_attempt"
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
NEXT_TARGET = "review_v01_alpha_tranche_004_source_map_witness_chain_construction_attempt_result"

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

ATTEMPT_EXECUTION_STEPS = [
    {
        "step_id": "attempt_001_bind_negative_readout_to_attempt",
        "result": "negative_authorization_readout_preserved",
        "constructed_witness_components": [],
    },
    {
        "step_id": "attempt_002_check_required_component_witnesses",
        "result": "no_reviewed_component_witnesses_available",
        "missing_witness_components": REQUIRED_WITNESS_CHAIN_COMPONENTS,
    },
    {
        "step_id": "attempt_003_check_semantic_closure_conditions",
        "result": "no_required_semantic_closure_conditions_satisfied",
        "unsatisfied_conditions": REQUIRED_SOURCE_MAP_SEMANTIC_CLOSURE_CONDITIONS,
    },
    {
        "step_id": "attempt_004_preserve_clean_lean_audit_surface",
        "result": "no_lean_axioms_project_axioms_empty",
        "project_axioms_used": PROJECT_AXIOMS_USED,
    },
    {
        "step_id": "attempt_005_fail_closed_pending_result_review",
        "result": CONSTRUCTION_ATTEMPT_CLASSIFICATION,
        "source_map_closure_claimed": False,
        "blocker_movement_registered": False,
    },
]

FORBIDDEN_EFFECTS = [
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


def build_attempt(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    source_map = dict(result_review.get("source_map_authorization_status", {}))
    lean = dict(result_review.get("lean_audit_result", {}))
    release_blockers = _release_blockers(result_review)
    selected_obligation = _selected_obligation(release_blockers)
    required_witnesses = list(result_review.get("required_witness_chain_components", []))
    required_closure = list(
        result_review.get("required_source_map_semantic_closure_conditions", [])
    )
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    attempt_result = {
        "classification": CONSTRUCTION_ATTEMPT_CLASSIFICATION,
        "witness_chain_constructed": False,
        "partial_witness_chain_constructed": False,
        "constructed_witness_components": [],
        "missing_witness_components": required_witnesses,
        "missing_witness_count": len(required_witnesses),
        "satisfied_source_map_semantic_closure_conditions": [],
        "unsatisfied_source_map_semantic_closure_conditions": required_closure,
        "unsatisfied_source_map_semantic_closure_condition_count": len(required_closure),
        "source_map_closure_claimed": False,
        "source_map_semantic_closure_authorized": False,
        "qft_gr_seam_closed": False,
        "retained_blocker": True,
        "retained_blocker_reason": BLOCKER_REASON,
        "requires_result_review_before_any_status_adjudication": True,
    }

    attempt_evidence = {
        "negative_authorization_readout_preserved": source_map.get("authorization_status")
        == CURRENT_BLOCKER
        and source_map.get("full_source_map_semantic_closure_authorized") is False,
        "source_map_not_authorized": source_map.get("source_map_not_authorized") is True,
        "prior_missing_witness_count": source_map.get("missing_witness_count"),
        "prior_supplied_only_layer_count": source_map.get("supplied_only_layer_count"),
        "reviewed_component_witnesses_found": 0,
        "reviewed_closure_conditions_satisfied": 0,
        "lean_axioms_used": lean.get("parsed_axioms"),
        "project_axioms_used": lean.get("project_axioms_used"),
        "project_axiom_count": lean.get("project_axiom_count"),
    }

    acceptance_criteria = {
        "consumes_expected_result_review": result_review.get("review_id")
        == EXPECTED_RESULT_REVIEW_ID,
        "result_review_accepted": result_review.get("accepted") is True,
        "result_review_outcome_expected": result_review.get("outcome_id")
        == EXPECTED_RESULT_REVIEW_OUTCOME,
        "result_review_selected_this_attempt": result_review.get("selected_next_target")
        == EXPECTED_RESULT_REVIEW_SELECTED_TARGET,
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
        "tranche_004_only_attempted_target": result_review.get("selected_tranche_id")
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
        "bounded_attempt_was_authorized": result_review.get(
            "source_map_witness_chain_construction_attempt_authorized"
        )
        is True,
        "bounded_attempt_executed_only": len(ATTEMPT_EXECUTION_STEPS) == 5
        and all(step["step_id"].startswith("attempt_") for step in ATTEMPT_EXECUTION_STEPS),
        "attempt_classified_fail_closed": attempt_result["classification"]
        == CONSTRUCTION_ATTEMPT_CLASSIFICATION
        and attempt_result["retained_blocker"] is True,
        "required_witness_chain_components_preserved": required_witnesses
        == REQUIRED_WITNESS_CHAIN_COMPONENTS
        and attempt_result["missing_witness_components"] == REQUIRED_WITNESS_CHAIN_COMPONENTS
        and attempt_result["missing_witness_count"] == 10,
        "required_source_map_semantic_closure_conditions_preserved": required_closure
        == REQUIRED_SOURCE_MAP_SEMANTIC_CLOSURE_CONDITIONS
        and attempt_result["unsatisfied_source_map_semantic_closure_conditions"]
        == REQUIRED_SOURCE_MAP_SEMANTIC_CLOSURE_CONDITIONS,
        "no_witness_chain_constructed": attempt_result["witness_chain_constructed"] is False
        and attempt_result["partial_witness_chain_constructed"] is False
        and attempt_result["constructed_witness_components"] == [],
        "no_source_map_closure_claimed": attempt_result["source_map_closure_claimed"]
        is False
        and attempt_result["source_map_semantic_closure_authorized"] is False,
        "no_qft_gr_seam_closure": attempt_result["qft_gr_seam_closed"] is False,
        "no_blocker_movement": forbidden_effect_status["blocker_movement_registered"]
        is False
        and forbidden_effect_status["blocker_movement_authorized"] is False,
        "release_blockers_remain_tracked": _release_blockers_tracked(release_blockers),
        "no_release_packet_assembly": forbidden_effect_status["release_packet_assembled"]
        is False,
        "no_v01_readiness_marking": forbidden_effect_status["v01_alpha_marked_ready"]
        is False,
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
        == "review_v01_alpha_tranche_004_source_map_witness_chain_construction_attempt_result",
    }
    accepted = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "attempt_id": ATTEMPT_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_ATTEMPT_BLOCKED",
        "consumes_construction_packet_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_construction_packet_result_review_pointer": _ptr(result_review_path),
        "consumed_construction_packet_result_review_schema_id": result_review.get(
            "schema_id"
        ),
        "attempt_scope": (
            "EXECUTE_BOUNDED_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_ATTEMPT_"
            "ONLY_NO_SOURCE_MAP_CLOSURE_BLOCKER_MOVEMENT_RELEASE_PROMOTION_OR_READINESS_MARKING"
        ),
        "tranche_001_status": TRANCHE_001_STATUS,
        "tranche_002_status": TRANCHE_002_STATUS,
        "tranche_003_status": TRANCHE_003_STATUS,
        "tranche_004_status": (
            "construction_attempt_failed_retained_blocker_pending_result_review"
        ),
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
        "source_map_witness_chain_construction_attempt_executed": accepted,
        "source_map_witness_chain_construction_attempt_authorized_by_prior_review": True,
        "construction_attempt_classification": CONSTRUCTION_ATTEMPT_CLASSIFICATION,
        "attempt_execution_steps": ATTEMPT_EXECUTION_STEPS,
        "attempt_evidence": attempt_evidence,
        "attempt_result": attempt_result,
        "required_witness_chain_components": required_witnesses,
        "required_source_map_semantic_closure_conditions": required_closure,
        "constructed_witness_components": [],
        "missing_witness_components": required_witnesses,
        "missing_witness_count": len(required_witnesses),
        "satisfied_source_map_semantic_closure_conditions": [],
        "unsatisfied_source_map_semantic_closure_conditions": required_closure,
        "unsatisfied_source_map_semantic_closure_condition_count": len(required_closure),
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
        "release_blocking_obligations_carry_forward": release_blockers,
        "release_blocking_obligation_count": len(release_blockers),
        "other_release_blocking_obligations": result_review.get(
            "other_release_blocking_obligations", []
        ),
        "other_release_blocking_obligation_count": result_review.get(
            "other_release_blocking_obligation_count", 0
        ),
        "source_map_authorization_status_adjudication_packet_preparation_authorized": False,
        "retained_source_map_blocker_declaration_preparation_authorized": False,
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
        else "REMEDIATE_V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_ATTEMPT",
        "selected_next_target_kind": "tranche_004_source_map_witness_chain_construction_attempt_result_review_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "REVIEW_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_ATTEMPT_RESULT_"
            "ONLY_NO_SOURCE_MAP_CLOSURE_BLOCKER_MOVEMENT_RELEASE_PROMOTION_OR_READINESS_MARKING"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": (
                    "The fail-closed construction attempt must be reviewed before any "
                    "status adjudication packet or retained-blocker declaration can be prepared."
                ),
            },
            {
                "target": "prepare_source_map_authorization_status_adjudication_packet",
                "decision": "deferred",
                "reason": "Status adjudication requires construction-attempt result review first.",
            },
            {
                "target": "prepare_v01_alpha_tranche_004_retained_source_map_blocker_declaration",
                "decision": "deferred",
                "reason": (
                    "The retained-blocker branch remains available after result review "
                    "accepts the failed attempt."
                ),
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha tranche 004 source-map witness-chain construction attempt "
            "executes only the bounded attempt authorized by the construction-packet result "
            "review. It finds no reviewed witness-chain components, satisfies no source-map "
            "semantic-closure conditions, classifies the result as construction_attempt_failed_"
            "retained_blocker, preserves project_axioms_used = [], and does not claim "
            "source-map closure, close the QFT-GR seam, move tranche 004, assemble release, "
            "mark readiness, discharge theorem/proof debt, authorize Phase 2, validate "
            "empirically, promote the master action, or make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_attempt(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_attempt(
        result_review_path=result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha tranche 004 source-map witness-chain construction attempt."
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
    payload = write_attempt(
        result_review_path=result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_tranche_004_source_map_witness_chain_construction_attempt_report: "
        f"accepted={payload['accepted']} classification={payload['construction_attempt_classification']} "
        f"selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

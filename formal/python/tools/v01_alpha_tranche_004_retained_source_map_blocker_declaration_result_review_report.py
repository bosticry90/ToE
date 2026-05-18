from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_TRANCHE_004_RETAINED_SOURCE_MAP_BLOCKER_DECLARATION_RESULT_REVIEW_"
    "20260515_v0"
)
REVIEW_ID = "V01_ALPHA_TRANCHE_004_RETAINED_SOURCE_MAP_BLOCKER_DECLARATION_RESULT_REVIEW_v0"
OUTCOME_ID = (
    "V01_ALPHA_TRANCHE_004_RETAINED_SOURCE_MAP_BLOCKER_DECLARATION_RESULT_REVIEW_"
    "ACCEPTS_RETAINED_RELEASE_BLOCKER_AND_SELECTS_REMEDIATION_CONTINUATION_OR_RELEASE_HOLD"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_TRANCHE_004_RETAINED_SOURCE_MAP_BLOCKER_DECLARATION_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_TRANCHE_004_RETAINED_SOURCE_MAP_BLOCKER_DECLARATION_RESULT_REVIEW_20260515_v0.json"
)

EXPECTED_DECLARATION_ID = "V01_ALPHA_TRANCHE_004_RETAINED_SOURCE_MAP_BLOCKER_DECLARATION_v0"
EXPECTED_DECLARATION_OUTCOME = (
    "V01_ALPHA_TRANCHE_004_RETAINED_SOURCE_MAP_BLOCKER_DECLARATION_PREPARED_AFTER_"
    "FAIL_CLOSED_WITNESS_CHAIN_ATTEMPT_WITH_NO_RELEASE_PROMOTION"
)
EXPECTED_DECLARATION_SELECTED_TARGET = (
    "review_v01_alpha_tranche_004_retained_source_map_blocker_declaration_result"
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
REVIEW_CLASSIFICATION = (
    "retained_source_map_authorization_release_blocker_accepted_carry_forward_to_tranche_005_selection"
)
ROUTING_DECISION = (
    "continue_to_tranche_005_selection_while_carrying_tranche_004_as_retained_release_blocker"
)
NEXT_TARGET = (
    "prepare_v01_alpha_dependency_remediation_next_tranche_selection_packet_after_tranche_004_"
    "retained_blocker_declaration"
)

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
    "next_tranche_selection_packet_prepared_by_review",
    "release_readiness_pause_registered_by_review",
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


def _release_blockers(declaration: dict[str, Any]) -> list[dict[str, Any]]:
    return list(declaration.get("release_blocking_obligations_carry_forward", []))


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


def _future_tranches_005_006_tracked(declaration: dict[str, Any]) -> bool:
    rows = list(declaration.get("other_release_blocking_obligations", []))
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


def build_result_review(
    *,
    declaration_path: Path = DEFAULT_DECLARATION_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    source_map = dict(declaration.get("source_map_authorization_status", {}))
    lean = dict(declaration.get("lean_audit_result", {}))
    retained = dict(declaration.get("retained_blocker_declaration", {}))
    release_impact = dict(declaration.get("release_impact", {}))
    release_blockers = _release_blockers(declaration)
    selected_obligation = _selected_obligation(release_blockers)
    missing_witnesses = list(declaration.get("missing_witness_components", []))
    unsatisfied_closure = list(
        declaration.get("unsatisfied_source_map_semantic_closure_conditions", [])
    )
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    routing_decision = {
        "selected_branch": ROUTING_DECISION,
        "retained_tranche_004_release_blocker_carry_forward_required": True,
        "continue_to_tranche_005_006_queue": True,
        "pause_release_readiness_due_to_retained_tranche_004_blocker": False,
        "release_readiness_remains_blocked_by_tranche_004": True,
        "release_hold_branch": "deferred_not_selected",
        "selection_reason": (
            "Tranche 004 is accepted as retained/release-blocking, but tranches 005 "
            "and 006 remain unprocessed. Continue the dependency remediation queue while "
            "carrying tranche 004 as an explicit retained release blocker."
        ),
    }

    acceptance_criteria = {
        "consumes_expected_declaration": declaration.get("declaration_id")
        == EXPECTED_DECLARATION_ID,
        "declaration_accepted": declaration.get("accepted") is True,
        "declaration_outcome_expected": declaration.get("outcome_id")
        == EXPECTED_DECLARATION_OUTCOME,
        "declaration_selected_this_review": declaration.get("selected_next_target")
        == EXPECTED_DECLARATION_SELECTED_TARGET,
        "attempt_result_preserved": declaration.get("construction_attempt_classification")
        == CONSTRUCTION_ATTEMPT_CLASSIFICATION
        and retained.get("attempt_result") == CONSTRUCTION_ATTEMPT_CLASSIFICATION,
        "declaration_classification_preserved": declaration.get("declaration_classification")
        == DECLARATION_CLASSIFICATION,
        "retained_release_blocker_declared": declaration.get("retained_blocker") is True
        and declaration.get("remains_release_blocking") is True
        and retained.get("declaration_kind") == "retained_source_map_authorization_release_blocker",
        "release_readiness_blocked_by_tranche_004": declaration.get(
            "release_readiness_blocked_by_tranche_004"
        )
        is True
        and release_impact.get("release_readiness_blocked_by_tranche_004") is True,
        "tranche_001_documented_nonblocking_preserved": declaration.get(
            "tranche_001_status"
        )
        == TRANCHE_001_STATUS,
        "tranche_002_documented_nonblocking_preserved": declaration.get(
            "tranche_002_status"
        )
        == TRANCHE_002_STATUS,
        "tranche_003_documented_nonblocking_preserved": declaration.get(
            "tranche_003_status"
        )
        == TRANCHE_003_STATUS,
        "tranche_004_selected_only": declaration.get("selected_tranche_id")
        == SELECTED_TRANCHE_ID
        and declaration.get("selected_remediation_finding_id") == SELECTED_FINDING_ID
        and declaration.get("selected_dependency") == SELECTED_DEPENDENCY,
        "selected_obligation_expected": selected_obligation.get("dependency")
        == SELECTED_DEPENDENCY
        and selected_obligation.get("dependency_class") == SELECTED_DEPENDENCY_CLASS,
        "current_blocker_preserved": declaration.get("current_blocker") == CURRENT_BLOCKER
        and source_map.get("authorization_status") == CURRENT_BLOCKER
        and source_map.get("full_source_map_semantic_closure_authorized") is False,
        "blocker_reason_preserved": declaration.get("blocker_reason") == BLOCKER_REASON
        and source_map.get("not_authorized_reason") == BLOCKER_REASON,
        "project_axioms_empty": declaration.get("project_axioms_used")
        == PROJECT_AXIOMS_USED
        and lean.get("project_axioms_used") == PROJECT_AXIOMS_USED
        and lean.get("project_axiom_count") == 0,
        "lean_audit_no_axioms_preserved": lean.get("parsed_axioms") == LEAN_AXIOMS_USED
        and lean.get("depends_on_no_axioms") is True,
        "missing_witnesses_preserved": missing_witnesses == REQUIRED_WITNESS_CHAIN_COMPONENTS
        and declaration.get("missing_witness_count") == 10,
        "semantic_closure_conditions_unsatisfied": unsatisfied_closure
        == REQUIRED_SOURCE_MAP_SEMANTIC_CLOSURE_CONDITIONS
        and declaration.get("unsatisfied_source_map_semantic_closure_condition_count") == 5,
        "no_witness_chain_construction": declaration.get("witness_chain_constructed")
        is False
        and declaration.get("partial_witness_chain_constructed") is False
        and forbidden_effect_status["witness_chain_constructed"] is False,
        "source_map_closure_remains_unauthorized": declaration.get(
            "source_map_closure_claimed"
        )
        is False
        and declaration.get("source_map_semantic_closure_authorized") is False
        and forbidden_effect_status["source_map_closure_claimed"] is False,
        "qft_gr_seam_closure_unauthorized": declaration.get("qft_gr_seam_closed")
        is False
        and forbidden_effect_status["qft_gr_seam_closed"] is False,
        "tranche_004_not_moved_to_documented_nonblocking": declaration.get(
            "tranche_004_moved_to_documented_dependency_nonblocking"
        )
        is False
        and forbidden_effect_status["tranche_004_moved_to_documented_dependency_nonblocking"]
        is False
        and forbidden_effect_status["documented_nonblocking_status_authorized"] is False,
        "tranches_005_006_remain_tracked": _future_tranches_005_006_tracked(
            declaration
        ),
        "release_blockers_remain_tracked": _release_blockers_tracked(release_blockers),
        "continuation_branch_selected": routing_decision["selected_branch"]
        == ROUTING_DECISION
        and routing_decision["continue_to_tranche_005_006_queue"] is True,
        "release_hold_branch_not_selected": routing_decision[
            "pause_release_readiness_due_to_retained_tranche_004_blocker"
        ]
        is False
        and forbidden_effect_status["release_readiness_pause_registered_by_review"] is False,
        "no_next_tranche_selection_packet_prepared_by_review": forbidden_effect_status[
            "next_tranche_selection_packet_prepared_by_review"
        ]
        is False,
        "no_additional_construction_attempt": forbidden_effect_status[
            "additional_construction_attempt_authorized"
        ]
        is False
        and forbidden_effect_status["additional_construction_attempt_executed"] is False,
        "no_blocker_movement": forbidden_effect_status["blocker_movement_registered"]
        is False
        and forbidden_effect_status["blocker_movement_authorized"] is False,
        "no_release_packet_assembly": forbidden_effect_status["release_packet_assembled"]
        is False
        and release_impact.get("release_assembly_allowed") is False,
        "no_v01_readiness_marking": forbidden_effect_status["v01_alpha_marked_ready"]
        is False
        and release_impact.get("readiness_marking_allowed") is False,
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
        == (
            "prepare_v01_alpha_dependency_remediation_next_tranche_selection_packet_after_tranche_004_"
            "retained_blocker_declaration"
        ),
    }
    accepted = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "review_id": REVIEW_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "V01_ALPHA_TRANCHE_004_RETAINED_SOURCE_MAP_BLOCKER_DECLARATION_RESULT_REVIEW_BLOCKED",
        "consumes_retained_blocker_declaration": EXPECTED_DECLARATION_ID,
        "consumes_retained_blocker_declaration_pointer": _ptr(declaration_path),
        "consumed_retained_blocker_declaration_schema_id": declaration.get("schema_id"),
        "review_scope": (
            "REVIEW_TRANCHE_004_RETAINED_SOURCE_MAP_BLOCKER_DECLARATION_RESULT_ONLY_NO_"
            "SOURCE_MAP_CLOSURE_BLOCKER_MOVEMENT_RELEASE_PROMOTION_OR_READINESS_MARKING"
        ),
        "tranche_001_status": TRANCHE_001_STATUS,
        "tranche_002_status": TRANCHE_002_STATUS,
        "tranche_003_status": TRANCHE_003_STATUS,
        "tranche_004_status": (
            "retained_source_map_authorization_release_blocker_accepted_carry_forward_"
            "pending_tranche_005_selection"
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
        "construction_attempt_classification": CONSTRUCTION_ATTEMPT_CLASSIFICATION,
        "declaration_classification": DECLARATION_CLASSIFICATION,
        "review_classification": REVIEW_CLASSIFICATION,
        "retained_blocker_declaration_result_accepted": accepted,
        "retained_blocker_declaration": retained,
        "routing_decision": routing_decision,
        "routing_decision_token": ROUTING_DECISION,
        "release_impact": release_impact,
        "release_readiness_blocked_by_tranche_004": True,
        "release_readiness_pause_selected": False,
        "continued_remediation_queue_selected": True,
        "retained_tranche_004_release_blocker_carry_forward_required": True,
        "next_tranche_selection_packet_prepared_by_review": False,
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
        "tranche_004_moved_to_documented_dependency_nonblocking": False,
        "documented_nonblocking_status_authorized": False,
        "release_blocking_obligations_carry_forward": release_blockers,
        "release_blocking_obligation_count": len(release_blockers),
        "other_release_blocking_obligations": declaration.get(
            "other_release_blocking_obligations", []
        ),
        "other_release_blocking_obligation_count": declaration.get(
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
        else "REMEDIATE_V01_ALPHA_TRANCHE_004_RETAINED_SOURCE_MAP_BLOCKER_DECLARATION_RESULT_REVIEW",
        "selected_next_target_kind": (
            "next_tranche_selection_packet_preparation_after_tranche_004_retained_blocker"
        ),
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_NEXT_TRANCHE_SELECTION_PACKET_AFTER_TRANCHE_004_RETAINED_BLOCKER_"
            "DECLARATION_ONLY_NO_REMEDIATION_EXECUTION_RELEASE_PROMOTION_OR_READINESS_MARKING"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": routing_decision["selection_reason"],
            },
            {
                "target": "pause_v01_alpha_release_readiness_due_to_retained_tranche_004_blocker",
                "decision": "deferred_not_selected",
                "reason": (
                    "Release readiness remains blocked, but unprocessed tranches 005 and 006 "
                    "can still be audited while tranche 004 is carried as retained."
                ),
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha tranche 004 retained source-map blocker declaration result "
            "review accepts the retained release blocker and selects continued dependency "
            "remediation queue preparation while carrying tranche 004 as retained/release-"
            "blocking. It does not claim source-map closure, construct the witness chain, "
            "close the QFT-GR seam, move tranche 004 to documented/nonblocking, assemble "
            "release, mark readiness, discharge theorem/proof debt, authorize Phase 2, "
            "validate empirically, or promote the master action."
        ),
        "roadmap_update_required": True,
    }


def write_result_review(
    *,
    declaration_path: Path = DEFAULT_DECLARATION_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_result_review(
        declaration_path=declaration_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha tranche 004 retained source-map blocker declaration "
            "result review."
        )
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    declaration_path = (
        ns.declaration if ns.declaration.is_absolute() else (REPO_ROOT / ns.declaration)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_result_review(
        declaration_path=declaration_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_tranche_004_retained_source_map_blocker_declaration_result_review_report: "
        f"accepted={payload['accepted']} decision={payload['routing_decision_token']} "
        f"selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

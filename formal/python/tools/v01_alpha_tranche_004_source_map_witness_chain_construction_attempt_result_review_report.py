from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_ATTEMPT_RESULT_REVIEW_"
    "20260515_v0"
)
REVIEW_ID = (
    "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_ATTEMPT_RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_ATTEMPT_RESULT_REVIEW_"
    "ACCEPTS_FAIL_CLOSED_RETAINED_BLOCKER_AND_AUTHORIZES_RETAINED_BLOCKER_DECLARATION_"
    "PREPARATION_ONLY"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_ATTEMPT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_ATTEMPT_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_ATTEMPT_RESULT_REVIEW_20260515_v0.json"
)

EXPECTED_ATTEMPT_ID = "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_ATTEMPT_v0"
EXPECTED_ATTEMPT_OUTCOME = (
    "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_ATTEMPT_EXECUTED_"
    "WITH_NO_SOURCE_MAP_CLOSURE_OR_RELEASE_PROMOTION"
)
EXPECTED_ATTEMPT_SELECTED_TARGET = (
    "review_v01_alpha_tranche_004_source_map_witness_chain_construction_attempt_result"
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
REVIEW_CLASSIFICATION = (
    "fail_closed_retained_source_map_blocker_accepted_pending_declaration_preparation"
)
NEXT_TARGET = "prepare_v01_alpha_tranche_004_retained_source_map_blocker_declaration"

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
    "retained_source_map_blocker_declaration_prepared_by_review",
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


def _release_blockers(attempt: dict[str, Any]) -> list[dict[str, Any]]:
    return list(attempt.get("release_blocking_obligations_carry_forward", []))


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


def _future_tranches_005_006_tracked(attempt: dict[str, Any]) -> bool:
    rows = list(attempt.get("other_release_blocking_obligations", []))
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
    attempt_path: Path = DEFAULT_ATTEMPT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    attempt = _read_json(attempt_path)
    source_map = dict(attempt.get("source_map_authorization_status", {}))
    lean = dict(attempt.get("lean_audit_result", {}))
    attempt_result = dict(attempt.get("attempt_result", {}))
    release_blockers = _release_blockers(attempt)
    selected_obligation = _selected_obligation(release_blockers)
    required_witnesses = list(attempt.get("required_witness_chain_components", []))
    missing_witnesses = list(attempt.get("missing_witness_components", []))
    required_closure = list(attempt.get("required_source_map_semantic_closure_conditions", []))
    unsatisfied_closure = list(
        attempt.get("unsatisfied_source_map_semantic_closure_conditions", [])
    )
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    review_decision = {
        "attempt_result_accepted": True,
        "accepted_classification": CONSTRUCTION_ATTEMPT_CLASSIFICATION,
        "retained_blocker_result_accepted": True,
        "tranche_004_remains_release_blocking": True,
        "tranche_004_documented_dependency_nonblocking_authorized": False,
        "retained_blocker_declaration_preparation_authorized": True,
        "retained_blocker_declaration_prepared_by_review": False,
        "selection_reason": (
            "The bounded construction attempt found no reviewed component witnesses and "
            "satisfied no source-map semantic-closure conditions. The only safe next step "
            "is a retained source-map blocker declaration packet."
        ),
    }

    acceptance_criteria = {
        "consumes_expected_attempt": attempt.get("attempt_id") == EXPECTED_ATTEMPT_ID,
        "attempt_accepted": attempt.get("accepted") is True,
        "attempt_outcome_expected": attempt.get("outcome_id") == EXPECTED_ATTEMPT_OUTCOME,
        "attempt_selected_this_review": attempt.get("selected_next_target")
        == EXPECTED_ATTEMPT_SELECTED_TARGET,
        "attempt_result_exactly_fail_closed": attempt.get("construction_attempt_classification")
        == CONSTRUCTION_ATTEMPT_CLASSIFICATION
        and attempt_result.get("classification") == CONSTRUCTION_ATTEMPT_CLASSIFICATION,
        "retained_blocker_preserved": attempt.get("retained_blocker") is True
        and attempt_result.get("retained_blocker") is True
        and attempt.get("retained_blocker_reason") == BLOCKER_REASON,
        "tranche_001_documented_nonblocking_preserved": attempt.get("tranche_001_status")
        == TRANCHE_001_STATUS,
        "tranche_002_documented_nonblocking_preserved": attempt.get("tranche_002_status")
        == TRANCHE_002_STATUS,
        "tranche_003_documented_nonblocking_preserved": attempt.get("tranche_003_status")
        == TRANCHE_003_STATUS,
        "tranche_004_only_reviewed_target": attempt.get("selected_tranche_id")
        == SELECTED_TRANCHE_ID
        and attempt.get("selected_remediation_finding_id") == SELECTED_FINDING_ID
        and attempt.get("selected_dependency") == SELECTED_DEPENDENCY,
        "selected_obligation_expected": selected_obligation.get("dependency")
        == SELECTED_DEPENDENCY
        and selected_obligation.get("dependency_class") == SELECTED_DEPENDENCY_CLASS,
        "current_blocker_preserved": attempt.get("current_blocker") == CURRENT_BLOCKER
        and source_map.get("authorization_status") == CURRENT_BLOCKER
        and source_map.get("full_source_map_semantic_closure_authorized") is False,
        "blocker_reason_preserved": attempt.get("blocker_reason") == BLOCKER_REASON
        and source_map.get("not_authorized_reason") == BLOCKER_REASON,
        "project_axioms_empty": attempt.get("project_axioms_used") == PROJECT_AXIOMS_USED
        and lean.get("project_axioms_used") == PROJECT_AXIOMS_USED
        and lean.get("project_axiom_count") == 0,
        "lean_audit_no_axioms_preserved": lean.get("parsed_axioms") == LEAN_AXIOMS_USED
        and lean.get("depends_on_no_axioms") is True,
        "no_witness_chain_constructed": attempt.get("witness_chain_constructed") is False
        and attempt.get("partial_witness_chain_constructed") is False
        and attempt_result.get("witness_chain_constructed") is False
        and attempt_result.get("partial_witness_chain_constructed") is False,
        "no_reviewed_component_witnesses": attempt.get("constructed_witness_components") == []
        and attempt_result.get("constructed_witness_components") == [],
        "missing_witnesses_preserved": missing_witnesses == REQUIRED_WITNESS_CHAIN_COMPONENTS
        and required_witnesses == REQUIRED_WITNESS_CHAIN_COMPONENTS
        and attempt.get("missing_witness_count") == 10
        and attempt_result.get("missing_witness_count") == 10,
        "source_map_closure_remains_unauthorized": attempt.get("source_map_closure_claimed")
        is False
        and attempt.get("source_map_semantic_closure_authorized") is False
        and attempt_result.get("source_map_closure_claimed") is False
        and attempt_result.get("source_map_semantic_closure_authorized") is False,
        "semantic_closure_conditions_unsatisfied": required_closure
        == REQUIRED_SOURCE_MAP_SEMANTIC_CLOSURE_CONDITIONS
        and unsatisfied_closure == REQUIRED_SOURCE_MAP_SEMANTIC_CLOSURE_CONDITIONS
        and attempt.get("unsatisfied_source_map_semantic_closure_condition_count") == 5,
        "qft_gr_seam_closure_unauthorized": attempt.get("qft_gr_seam_closed") is False
        and attempt_result.get("qft_gr_seam_closed") is False,
        "tranche_004_not_moved_to_documented_nonblocking": forbidden_effect_status[
            "tranche_004_moved_to_documented_dependency_nonblocking"
        ]
        is False
        and forbidden_effect_status["documented_nonblocking_status_authorized"] is False,
        "tranches_005_006_remain_tracked": _future_tranches_005_006_tracked(attempt),
        "release_blockers_remain_tracked": _release_blockers_tracked(release_blockers),
        "retained_blocker_declaration_preparation_selected_only": review_decision[
            "retained_blocker_declaration_preparation_authorized"
        ]
        is True
        and review_decision["retained_blocker_declaration_prepared_by_review"] is False,
        "no_status_adjudication_packet_preparation_by_review": forbidden_effect_status[
            "source_map_authorization_status_adjudication_packet_preparation_authorized"
        ]
        is False,
        "no_blocker_movement": forbidden_effect_status["blocker_movement_registered"]
        is False
        and forbidden_effect_status["blocker_movement_authorized"] is False,
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
        "no_retained_assumption_discharge": forbidden_effect_status[
            "retained_assumptions_discharged"
        ]
        is False,
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
        == "prepare_v01_alpha_tranche_004_retained_source_map_blocker_declaration",
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
        else (
            "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_ATTEMPT_"
            "RESULT_REVIEW_BLOCKED"
        ),
        "consumes_construction_attempt": EXPECTED_ATTEMPT_ID,
        "consumes_construction_attempt_pointer": _ptr(attempt_path),
        "consumed_construction_attempt_schema_id": attempt.get("schema_id"),
        "review_scope": (
            "REVIEW_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_ATTEMPT_RESULT_"
            "ONLY_NO_RETAINED_BLOCKER_DECLARATION_PREPARATION_BY_REVIEW_SOURCE_MAP_CLOSURE_"
            "BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
        ),
        "tranche_001_status": TRANCHE_001_STATUS,
        "tranche_002_status": TRANCHE_002_STATUS,
        "tranche_003_status": TRANCHE_003_STATUS,
        "tranche_004_status": (
            "fail_closed_retained_source_map_blocker_accepted_pending_declaration_preparation"
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
        "review_classification": REVIEW_CLASSIFICATION,
        "construction_attempt_classification": CONSTRUCTION_ATTEMPT_CLASSIFICATION,
        "construction_attempt_result_accepted": accepted,
        "review_decision": review_decision,
        "attempt_result": attempt_result,
        "required_witness_chain_components": required_witnesses,
        "constructed_witness_components": [],
        "missing_witness_components": missing_witnesses,
        "missing_witness_count": len(missing_witnesses),
        "required_source_map_semantic_closure_conditions": required_closure,
        "satisfied_source_map_semantic_closure_conditions": [],
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
        "other_release_blocking_obligations": attempt.get(
            "other_release_blocking_obligations", []
        ),
        "other_release_blocking_obligation_count": attempt.get(
            "other_release_blocking_obligation_count", 0
        ),
        "retained_source_map_blocker_declaration_preparation_authorized": accepted,
        "retained_source_map_blocker_declaration_prepared_by_review": False,
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
        else (
            "REMEDIATE_V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_"
            "ATTEMPT_RESULT_REVIEW"
        ),
        "selected_next_target_kind": "retained_source_map_blocker_declaration_preparation_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_TRANCHE_004_RETAINED_SOURCE_MAP_BLOCKER_DECLARATION_ONLY_NO_SOURCE_"
            "MAP_CLOSURE_BLOCKER_MOVEMENT_RELEASE_PROMOTION_OR_READINESS_MARKING"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": (
                    "The construction attempt failed closed with no witnesses and no closure "
                    "conditions satisfied, so the retained blocker must be declared before "
                    "any next-tranche or release-readiness routing."
                ),
            },
            {
                "target": "prepare_source_map_authorization_status_adjudication_packet",
                "decision": "deferred",
                "reason": (
                    "Status adjudication is not appropriate until the retained blocker "
                    "declaration is prepared and reviewed."
                ),
            },
            {
                "target": (
                    "prepare_v01_alpha_dependency_remediation_next_tranche_selection_packet"
                ),
                "decision": "deferred",
                "reason": (
                    "Next-tranche routing must wait until tranche 004's retained blocker "
                    "status is declared and reviewed."
                ),
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha tranche 004 source-map witness-chain construction attempt "
            "result review accepts construction_attempt_failed_retained_blocker and "
            "authorizes only retained source-map blocker declaration preparation. It "
            "preserves no witness-chain construction, no source-map closure, no QFT-GR "
            "seam closure, no tranche 004 movement to documented/nonblocking, no release "
            "assembly, no readiness marking, no theorem/proof debt discharge, no retained-"
            "assumption discharge, no Phase 2 authorization, no empirical validation, and "
            "no master-action promotion."
        ),
        "roadmap_update_required": True,
    }


def write_result_review(
    *,
    attempt_path: Path = DEFAULT_ATTEMPT_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_result_review(
        attempt_path=attempt_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha tranche 004 source-map witness-chain construction "
            "attempt result review."
        )
    )
    parser.add_argument("--attempt", type=Path, default=DEFAULT_ATTEMPT_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    attempt_path = ns.attempt if ns.attempt.is_absolute() else (REPO_ROOT / ns.attempt)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_result_review(
        attempt_path=attempt_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_tranche_004_source_map_witness_chain_construction_attempt_result_review_report: "
        f"accepted={payload['accepted']} classification={payload['review_classification']} "
        f"selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

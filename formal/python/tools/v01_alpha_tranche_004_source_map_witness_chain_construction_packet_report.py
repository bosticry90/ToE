from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_20260515_v0"
PACKET_ID = "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_v0"
OUTCOME_ID = (
    "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_PREPARED_"
    "WITH_NO_WITNESS_CONSTRUCTION_OR_SOURCE_MAP_CLOSURE"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_EVIDENCE_PACKET_RESULT_REVIEW_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_20260515_v0.json"
)

EXPECTED_RESULT_REVIEW_ID = (
    "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_EVIDENCE_PACKET_RESULT_REVIEW_v0"
)
EXPECTED_RESULT_REVIEW_OUTCOME = (
    "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_EVIDENCE_PACKET_RESULT_REVIEW_"
    "ACCEPTS_REQUIREMENTS_ONLY_AND_SELECTS_BOUNDED_NEXT_ACTION"
)
EXPECTED_RESULT_REVIEW_SELECTED_TARGET = (
    "prepare_v01_alpha_tranche_004_source_map_witness_chain_construction_packet"
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

REQUIRED_LEAN_THEORY_SURFACES = [
    {
        "surface_id": "source_map_eligibility_ladder_summary",
        "path": "formal/toe_formal/ToeFormal/Bridges/QFT_GR_SourceMapEligibilityLadderSummary.lean",
        "module": "ToeFormal.Bridges.QFTGRSourceMapEligibilityLadderSummary",
        "role": "negative authorization readout and construction-target witness inventory",
    },
    {
        "surface_id": "renormalized_expectation_value_semantics",
        "path": "formal/toe_formal/ToeFormal/Bridges/QFT_GR_RenormalizedExpectationValueSemantics.lean",
        "role": "candidate renormalization and finite stress-energy witness surface",
    },
    {
        "surface_id": "covariant_conservation_obligation_semantics",
        "path": "formal/toe_formal/ToeFormal/Bridges/QFT_GR_CovariantConservationObligationSemantics.lean",
        "role": "candidate conservation witness surface",
    },
    {
        "surface_id": "bianchi_compatibility_obligation_semantics",
        "path": "formal/toe_formal/ToeFormal/Bridges/QFT_GR_BianchiCompatibilityObligationSemantics.lean",
        "role": "candidate Bianchi compatibility witness surface",
    },
    {
        "surface_id": "einstein_coupling_obligation_semantics",
        "path": "formal/toe_formal/ToeFormal/Bridges/QFT_GR_EinsteinCouplingObligationSemantics.lean",
        "role": "candidate Einstein coupling witness surface",
    },
    {
        "surface_id": "poisson_recovery_obligation_semantics",
        "path": "formal/toe_formal/ToeFormal/Bridges/QFT_GR_PoissonRecoveryObligationSemantics.lean",
        "role": "candidate weak-curvature, Poisson, and Newtonian recovery witness surface",
    },
]

REQUIRED_DOCUMENTATION_SURFACES = [
    "formal/docs/release/V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_EVIDENCE_PACKET_RESULT_REVIEW_20260515_v0.json",
    "formal/docs/release/V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_EVIDENCE_PACKET_20260515_v0.json",
    "formal/docs/release/V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_20260515_v0.json",
    "formal/docs/release/TOE_V01_ALPHA_LEAN_DEPENDENCY_AUDIT_v0.md",
    "formal/docs/paper/PHYSICS_ROADMAP_v0.md",
]

CANDIDATE_CONSTRUCTION_ROUTE = [
    {
        "step_id": "route_001_bind_negative_readout_to_missing_witness_inventory",
        "purpose": "Keep the current negative authorization readout as the starting obligation.",
        "execution_authorized_by_packet": False,
    },
    {
        "step_id": "route_002_define_component_witness_obligations",
        "purpose": "Prepare construction obligations for each required witness-chain component.",
        "required_components": REQUIRED_WITNESS_CHAIN_COMPONENTS,
        "execution_authorized_by_packet": False,
    },
    {
        "step_id": "route_003_define_semantic_closure_obligation",
        "purpose": "Prepare the closure obligation that can only follow reviewed component witnesses.",
        "required_conditions": REQUIRED_SOURCE_MAP_SEMANTIC_CLOSURE_CONDITIONS,
        "execution_authorized_by_packet": False,
    },
    {
        "step_id": "route_004_require_clean_lean_and_review_surfaces",
        "purpose": "Require project-axiom-free Lean/theory evidence and documentation review surfaces.",
        "execution_authorized_by_packet": False,
    },
    {
        "step_id": "route_005_require_result_review_before_authorization_change",
        "purpose": "Prevent any source-map authorization change before bounded execution and result review.",
        "execution_authorized_by_packet": False,
    },
]

SUCCESS_CRITERIA = [
    "construction_route_identifies_all_required_witness_chain_components",
    "construction_route_identifies_required_source_map_semantic_closure_conditions",
    "lean_and_theory_surfaces_are_pinned_for_future_execution",
    "documentation_surfaces_are_pinned_for_future_review",
    "project_axioms_used_remains_empty",
    "packet_selects_result_review_before_any_construction_execution",
]

FAILURE_CRITERIA = [
    "any_required_witness_chain_component_is_omitted",
    "source_map_closure_is_claimed_by_preparation_packet",
    "witness_chain_construction_is_claimed_by_preparation_packet",
    "project_axioms_are_introduced_or_left_untracked",
    "packet_authorizes_release_readiness_or_blocker_movement",
    "packet_skips_result_review_before_construction_execution",
]

NEXT_TARGET = "review_v01_alpha_tranche_004_source_map_witness_chain_construction_packet_result"
POST_CONSTRUCTION_REVIEW_TARGET = (
    "review_v01_alpha_tranche_004_source_map_witness_chain_construction_result"
)

FORBIDDEN_EFFECTS = [
    "source_map_closure_claimed",
    "source_map_semantic_closure_authorized",
    "qft_gr_seam_closed",
    "witness_chain_constructed",
    "source_map_witness_chain_evidence_constructed",
    "source_map_witness_chain_evidence_construction_authorized",
    "source_map_witness_chain_construction_executed",
    "evidence_construction_executed",
    "remediation_execution_authorized",
    "remediation_executed",
    "broader_remediation_executed",
    "documentation_prepared",
    "policy_adjudication_executed",
    "expert_re_review_executed",
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


def build_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    source_map = dict(result_review.get("source_map_authorization_status", {}))
    lean = dict(result_review.get("lean_audit_result", {}))
    release_blockers = _release_blockers(result_review)
    selected_obligation = _selected_obligation(release_blockers)
    required_witnesses = list(
        result_review.get("required_witness_chain_components", REQUIRED_WITNESS_CHAIN_COMPONENTS)
    )
    required_closure = list(
        result_review.get(
            "required_source_map_semantic_closure_conditions",
            REQUIRED_SOURCE_MAP_SEMANTIC_CLOSURE_CONDITIONS,
        )
    )
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    construction_execution_boundaries = {
        "construction_execution_authorized_by_this_packet": False,
        "future_execution_requires_packet_result_review": True,
        "source_map_authorization_change_allowed_by_this_packet": False,
        "source_map_closure_claim_allowed_by_this_packet": False,
        "blocker_movement_allowed_by_this_packet": False,
        "release_readiness_allowed_by_this_packet": False,
        "theorem_debt_discharge_allowed_by_this_packet": False,
        "phase2_or_seam_closure_allowed_by_this_packet": False,
    }

    construction_packet_scope = {
        "scope_kind": "SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_PREPARATION_ONLY",
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_dependency_finding_id": SELECTED_FINDING_ID,
        "selected_dependency": SELECTED_DEPENDENCY,
        "current_blocker": CURRENT_BLOCKER,
        "blocker_reason": BLOCKER_REASON,
        "required_witness_chain_components": required_witnesses,
        "candidate_construction_route": CANDIDATE_CONSTRUCTION_ROUTE,
        "required_lean_theory_surfaces": REQUIRED_LEAN_THEORY_SURFACES,
        "required_documentation_surfaces": REQUIRED_DOCUMENTATION_SURFACES,
        "success_criteria": SUCCESS_CRITERIA,
        "failure_criteria": FAILURE_CRITERIA,
        "construction_execution_boundaries": construction_execution_boundaries,
        "post_construction_review_target": POST_CONSTRUCTION_REVIEW_TARGET,
    }

    acceptance_criteria = {
        "consumes_expected_result_review": result_review.get("review_id")
        == EXPECTED_RESULT_REVIEW_ID,
        "result_review_accepted": result_review.get("accepted") is True,
        "result_review_outcome_expected": result_review.get("outcome_id")
        == EXPECTED_RESULT_REVIEW_OUTCOME,
        "result_review_selected_this_packet": result_review.get("selected_next_target")
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
        "construction_route_prepared_only": construction_packet_scope["scope_kind"]
        == "SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_PREPARATION_ONLY"
        and construction_execution_boundaries["construction_execution_authorized_by_this_packet"]
        is False,
        "required_witness_chain_components_preserved": required_witnesses
        == REQUIRED_WITNESS_CHAIN_COMPONENTS
        and len(required_witnesses) == 10,
        "required_source_map_semantic_closure_conditions_preserved": required_closure
        == REQUIRED_SOURCE_MAP_SEMANTIC_CLOSURE_CONDITIONS,
        "candidate_route_defined": len(CANDIDATE_CONSTRUCTION_ROUTE) == 5
        and all(
            step["execution_authorized_by_packet"] is False
            for step in CANDIDATE_CONSTRUCTION_ROUTE
        ),
        "lean_theory_surfaces_defined": len(REQUIRED_LEAN_THEORY_SURFACES) >= 6,
        "documentation_surfaces_defined": len(REQUIRED_DOCUMENTATION_SURFACES) >= 5,
        "success_and_failure_criteria_defined": len(SUCCESS_CRITERIA) >= 6
        and len(FAILURE_CRITERIA) >= 6,
        "post_packet_review_selected": NEXT_TARGET
        == "review_v01_alpha_tranche_004_source_map_witness_chain_construction_packet_result",
        "post_construction_review_target_defined": POST_CONSTRUCTION_REVIEW_TARGET
        == "review_v01_alpha_tranche_004_source_map_witness_chain_construction_result",
        "release_blockers_remain_tracked": _release_blockers_tracked(release_blockers),
        "no_source_map_closure": forbidden_effect_status["source_map_closure_claimed"]
        is False
        and forbidden_effect_status["source_map_semantic_closure_authorized"] is False
        and construction_execution_boundaries["source_map_closure_claim_allowed_by_this_packet"]
        is False,
        "no_witness_chain_construction": forbidden_effect_status["witness_chain_constructed"]
        is False
        and forbidden_effect_status["source_map_witness_chain_evidence_constructed"]
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
        == "review_v01_alpha_tranche_004_source_map_witness_chain_construction_packet_result",
    }
    accepted = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_BLOCKED",
        "consumes_witness_chain_evidence_packet_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_witness_chain_evidence_packet_result_review_pointer": _ptr(
            result_review_path
        ),
        "consumed_witness_chain_evidence_packet_result_review_schema_id": result_review.get(
            "schema_id"
        ),
        "packet_scope": (
            "PREPARE_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_ONLY_"
            "NO_WITNESS_CONSTRUCTION_SOURCE_MAP_CLOSURE_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
        ),
        "tranche_001_status": TRANCHE_001_STATUS,
        "tranche_002_status": TRANCHE_002_STATUS,
        "tranche_003_status": TRANCHE_003_STATUS,
        "tranche_004_status": (
            "construction_packet_prepared_source_map_closure_still_unauthorized_pending_"
            "construction_packet_result_review"
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
        "source_map_witness_chain_construction_packet_prepared": accepted,
        "construction_packet_scope": construction_packet_scope,
        "required_witness_chain_components": required_witnesses,
        "required_source_map_semantic_closure_conditions": required_closure,
        "candidate_construction_route": CANDIDATE_CONSTRUCTION_ROUTE,
        "required_lean_theory_surfaces": REQUIRED_LEAN_THEORY_SURFACES,
        "required_documentation_surfaces": REQUIRED_DOCUMENTATION_SURFACES,
        "success_criteria": SUCCESS_CRITERIA,
        "failure_criteria": FAILURE_CRITERIA,
        "construction_execution_boundaries": construction_execution_boundaries,
        "post_packet_review_target": NEXT_TARGET,
        "post_construction_review_target": POST_CONSTRUCTION_REVIEW_TARGET,
        "documentation_alone_can_clear_blocker": False,
        "remains_release_blocking": True,
        "release_blocking_obligations_carry_forward": release_blockers,
        "release_blocking_obligation_count": len(release_blockers),
        "other_release_blocking_obligations": result_review.get(
            "other_release_blocking_obligations", []
        ),
        "other_release_blocking_obligation_count": result_review.get(
            "other_release_blocking_obligation_count", 0
        ),
        "source_map_closure_claimed": False,
        "source_map_semantic_closure_authorized": False,
        "qft_gr_seam_closed": False,
        "witness_chain_constructed": False,
        "source_map_witness_chain_evidence_constructed": False,
        "source_map_witness_chain_evidence_construction_authorized": False,
        "source_map_witness_chain_construction_executed": False,
        "evidence_construction_executed": False,
        "remediation_execution_authorized": False,
        "remediation_executed": False,
        "broader_remediation_executed": False,
        "documentation_prepared": False,
        "policy_adjudication_executed": False,
        "expert_re_review_executed": False,
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
        else "REMEDIATE_V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET",
        "selected_next_target_kind": "tranche_004_source_map_witness_chain_construction_packet_result_review_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "REVIEW_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_CONSTRUCTION_PACKET_ONLY_"
            "NO_CONSTRUCTION_EXECUTION_CLOSURE_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": "The construction packet must be reviewed before any bounded construction attempt.",
            },
            {
                "target": (
                    "execute_v01_alpha_tranche_004_source_map_witness_chain_construction"
                ),
                "decision": "deferred",
                "reason": "Construction execution requires packet result review first.",
            },
            {
                "target": "prepare_v01_alpha_tranche_004_retained_source_map_blocker_declaration",
                "decision": "deferred",
                "reason": "Retained-blocker declaration remains available if construction packet review fails closed.",
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha tranche 004 source-map witness-chain construction packet "
            "prepares only a bounded construction route. It preserves full_source_map_"
            "semantic_closure_not_authorized, preserves the absent witness-chain reason, "
            "preserves project_axioms_used = [], and does not construct the witness chain, "
            "claim source-map closure, close the QFT-GR seam, move tranche 004, assemble "
            "release, mark readiness, discharge theorem/proof debt, authorize Phase 2, "
            "validate empirically, promote the master action, or make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_packet(
        result_review_path=result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha tranche 004 source-map witness-chain construction packet."
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
    payload = write_packet(
        result_review_path=result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_tranche_004_source_map_witness_chain_construction_packet_report: "
        f"accepted={payload['accepted']} current_blocker={payload['current_blocker']} "
        f"selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

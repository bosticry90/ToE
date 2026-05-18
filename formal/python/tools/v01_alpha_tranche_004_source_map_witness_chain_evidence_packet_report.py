from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_EVIDENCE_PACKET_20260515_v0"
PACKET_ID = "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_EVIDENCE_PACKET_v0"
OUTCOME_ID = (
    "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_EVIDENCE_PACKET_PREPARED_"
    "WITH_NO_SOURCE_MAP_CLOSURE_OR_RELEASE_PROMOTION"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_REMEDIATION_PACKET_RESULT_REVIEW_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_EVIDENCE_PACKET_20260515_v0.json"
)

EXPECTED_RESULT_REVIEW_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_"
    "REMEDIATION_PACKET_RESULT_REVIEW_v0"
)
EXPECTED_RESULT_REVIEW_OUTCOME = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_"
    "REMEDIATION_PACKET_RESULT_REVIEW_ACCEPTS_REAL_BLOCKER_REMEDIATION_PLAN_AND_"
    "SELECTS_BOUNDED_NEXT_ACTION_ONLY"
)
EXPECTED_RESULT_REVIEW_SELECTED_TARGET = (
    "prepare_v01_alpha_tranche_004_source_map_witness_chain_evidence_packet"
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
LEAN_AXIOMS_USED: list[str] = []
PROJECT_AXIOMS_USED: list[str] = []

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

LEAN_SURFACES_INVOLVED = [
    {
        "kind": "audit_target",
        "module": "ToeFormal.Bridges.QFTGRSourceMapEligibilityLadderSummary",
        "name": (
            "ToeFormal.Bridges.QFTGRSourceMapEligibilityLadderSummary."
            "qft_gr_source_map_eligibility_ladder_summary_source_map_not_authorized_v0"
        ),
        "path": "formal/toe_formal/ToeFormal/Bridges/QFT_GR_SourceMapEligibilityLadderSummary.lean",
        "role": "negative source-map authorization marker and missing witness-chain readout",
    },
    {
        "kind": "release_marker",
        "module": "ToeFormal.Release.V01Tranche004SourceMapWitnessChainEvidencePacket",
        "path": "formal/toe_formal/ToeFormal/Release/V01Tranche004SourceMapWitnessChainEvidencePacket.lean",
        "role": "Lean-side non-claim marker for this preparation packet",
    },
]

DOCUMENTATION_SURFACES_INVOLVED = [
    "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_REMEDIATION_PACKET_RESULT_REVIEW_20260515_v0.json",
    "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_REMEDIATION_PACKET_20260515_v0.json",
    "formal/docs/release/V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_EVIDENCE_PACKET_20260515_v0.json",
    "formal/docs/release/TOE_V01_ALPHA_LEAN_DEPENDENCY_AUDIT_v0.md",
    "formal/docs/paper/PHYSICS_ROADMAP_v0.md",
]

NEXT_TARGET = "review_v01_alpha_tranche_004_source_map_witness_chain_evidence_packet_result"

FORBIDDEN_EFFECTS = [
    "source_map_closure_claimed",
    "source_map_semantic_closure_authorized",
    "witness_chain_constructed",
    "source_map_witness_chain_evidence_constructed",
    "source_map_witness_chain_evidence_construction_authorized",
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


def _known_available_evidence(
    result_review: dict[str, Any],
    result_review_path: Path,
) -> list[dict[str, Any]]:
    source_map = dict(result_review.get("source_map_authorization_status", {}))
    lean = dict(result_review.get("lean_audit_result", {}))
    return [
        {
            "evidence_id": "tranche_004_remediation_plan_result_review_accepted",
            "status": "available",
            "source": _ptr(result_review_path),
            "supports": "bounded witness-chain evidence packet preparation only",
        },
        {
            "evidence_id": "negative_source_map_authorization_readout",
            "status": "available",
            "authorization_status": source_map.get("authorization_status"),
            "not_authorized_reason": source_map.get("not_authorized_reason"),
            "supports": "retention of the source-map semantic-closure blocker",
        },
        {
            "evidence_id": "missing_witness_chain_inventory",
            "status": "available",
            "missing_witness_count": source_map.get("missing_witness_count"),
            "required_components": result_review.get(
                "required_witness_chain_evidence",
                REQUIRED_WITNESS_CHAIN_COMPONENTS,
            ),
            "supports": "definition of the evidence requirements",
        },
        {
            "evidence_id": "lean_dependency_audit_clean",
            "status": "available",
            "parsed_axioms": lean.get("parsed_axioms"),
            "project_axioms_used": lean.get("project_axioms_used"),
            "depends_on_no_axioms": lean.get("depends_on_no_axioms"),
            "supports": "the blocker is not a Lean axiom dependency hygiene issue",
        },
    ]


def _known_missing_evidence(result_review: dict[str, Any]) -> list[dict[str, Any]]:
    required_witnesses = result_review.get(
        "required_witness_chain_evidence",
        REQUIRED_WITNESS_CHAIN_COMPONENTS,
    )
    required_closure = result_review.get(
        "required_source_map_semantic_closure_evidence",
        REQUIRED_SOURCE_MAP_SEMANTIC_CLOSURE_CONDITIONS,
    )
    return [
        {
            "missing_evidence_id": "required_witness_chain_components_not_constructed",
            "status": "missing",
            "components": required_witnesses,
        },
        {
            "missing_evidence_id": "positive_source_map_semantic_closure_authorization",
            "status": "missing",
            "conditions": required_closure,
        },
        {
            "missing_evidence_id": "reviewed_semantic_closure_proof_or_equivalent",
            "status": "missing",
        },
        {
            "missing_evidence_id": "expert_re_review_acceptance_for_authorization_change",
            "status": "missing",
        },
        {
            "missing_evidence_id": "result_review_accepting_any_new_evidence_before_blocker_movement",
            "status": "missing",
        },
    ]


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
    required_witnesses = result_review.get(
        "required_witness_chain_evidence",
        REQUIRED_WITNESS_CHAIN_COMPONENTS,
    )
    required_closure = result_review.get(
        "required_source_map_semantic_closure_evidence",
        REQUIRED_SOURCE_MAP_SEMANTIC_CLOSURE_CONDITIONS,
    )
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    evidence_requirements_scope = {
        "scope_kind": "SOURCE_MAP_WITNESS_CHAIN_EVIDENCE_REQUIREMENTS_PREPARATION_ONLY",
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_dependency_finding_id": SELECTED_FINDING_ID,
        "selected_dependency": SELECTED_DEPENDENCY,
        "current_blocker": CURRENT_BLOCKER,
        "blocker_reason": BLOCKER_REASON,
        "known_available_evidence": _known_available_evidence(result_review, result_review_path),
        "known_missing_evidence": _known_missing_evidence(result_review),
        "required_witness_chain_components": required_witnesses,
        "required_source_map_semantic_closure_conditions": required_closure,
        "lean_surfaces_involved": LEAN_SURFACES_INVOLVED,
        "documentation_surfaces_involved": DOCUMENTATION_SURFACES_INVOLVED,
        "evidence_construction_authorized_by_this_packet": False,
        "source_map_closure_claimed_by_this_packet": False,
        "tranche_004_movement_authorized_by_this_packet": False,
        "release_blocking_status_after_packet": "remains_release_blocking",
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
        "prepares_requirements_only": evidence_requirements_scope["scope_kind"]
        == "SOURCE_MAP_WITNESS_CHAIN_EVIDENCE_REQUIREMENTS_PREPARATION_ONLY"
        and evidence_requirements_scope["evidence_construction_authorized_by_this_packet"]
        is False,
        "known_available_evidence_recorded": len(
            evidence_requirements_scope["known_available_evidence"]
        )
        >= 4,
        "known_missing_evidence_recorded": len(
            evidence_requirements_scope["known_missing_evidence"]
        )
        >= 5,
        "required_witness_chain_components_recorded": required_witnesses
        == REQUIRED_WITNESS_CHAIN_COMPONENTS
        and len(required_witnesses) == 10,
        "required_source_map_semantic_closure_conditions_recorded": required_closure
        == REQUIRED_SOURCE_MAP_SEMANTIC_CLOSURE_CONDITIONS
        and len(required_closure) == 5,
        "lean_surfaces_recorded": len(LEAN_SURFACES_INVOLVED) >= 2,
        "documentation_surfaces_recorded": len(DOCUMENTATION_SURFACES_INVOLVED) >= 5,
        "documentation_alone_cannot_clear": result_review.get(
            "documentation_alone_can_clear_blocker"
        )
        is False,
        "remains_release_blocking": evidence_requirements_scope[
            "release_blocking_status_after_packet"
        ]
        == "remains_release_blocking",
        "release_blockers_remain_tracked": _release_blockers_tracked(release_blockers),
        "no_source_map_closure": forbidden_effect_status["source_map_closure_claimed"]
        is False
        and forbidden_effect_status["source_map_semantic_closure_authorized"] is False,
        "no_witness_chain_construction": forbidden_effect_status[
            "witness_chain_constructed"
        ]
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
        == "review_v01_alpha_tranche_004_source_map_witness_chain_evidence_packet_result",
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
        else "V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_EVIDENCE_PACKET_BLOCKED",
        "consumes_remediation_packet_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_remediation_packet_result_review_pointer": _ptr(result_review_path),
        "consumed_remediation_packet_result_review_schema_id": result_review.get("schema_id"),
        "packet_scope": (
            "PREPARE_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_EVIDENCE_REQUIREMENTS_ONLY_"
            "NO_SOURCE_MAP_CLOSURE_WITNESS_CONSTRUCTION_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
        ),
        "tranche_001_status": TRANCHE_001_STATUS,
        "tranche_002_status": TRANCHE_002_STATUS,
        "tranche_003_status": TRANCHE_003_STATUS,
        "tranche_004_status": (
            "real_source_map_authorization_blocker_witness_chain_evidence_requirements_"
            "prepared_pending_result_review"
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
        "source_map_witness_chain_evidence_packet_prepared": accepted,
        "evidence_requirements_scope": evidence_requirements_scope,
        "known_available_evidence": evidence_requirements_scope["known_available_evidence"],
        "known_missing_evidence": evidence_requirements_scope["known_missing_evidence"],
        "required_witness_chain_components": required_witnesses,
        "required_source_map_semantic_closure_conditions": required_closure,
        "lean_surfaces_involved": LEAN_SURFACES_INVOLVED,
        "documentation_surfaces_involved": DOCUMENTATION_SURFACES_INVOLVED,
        "evidence_construction_authorized": False,
        "evidence_construction_executed": False,
        "documentation_alone_can_clear_blocker": False,
        "remains_release_blocking": True,
        "post_packet_review_target": NEXT_TARGET,
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
        "witness_chain_constructed": False,
        "source_map_witness_chain_evidence_constructed": False,
        "source_map_witness_chain_evidence_construction_authorized": False,
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
        else "REMEDIATE_V01_ALPHA_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_EVIDENCE_PACKET",
        "selected_next_target_kind": "tranche_004_source_map_witness_chain_evidence_packet_result_review_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "REVIEW_TRANCHE_004_SOURCE_MAP_WITNESS_CHAIN_EVIDENCE_PACKET_ONLY_"
            "NO_EVIDENCE_CONSTRUCTION_CLOSURE_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": (
                    "Review the prepared witness-chain evidence requirements before any "
                    "bounded evidence construction branch can be considered."
                ),
            },
            {
                "target": (
                    "execute_v01_alpha_dependency_remediation_tranche_004_bounded_source_map_"
                    "witness_chain_evidence_construction"
                ),
                "decision": "deferred",
                "reason": "Construction is not authorized by this preparation packet.",
            },
            {
                "target": "prepare_v01_alpha_tranche_004_retained_source_map_blocker_declaration",
                "decision": "deferred",
                "reason": "Retained-blocker declaration remains a later branch if evidence is unavailable.",
            },
            {
                "target": "prepare_v01_alpha_release_readiness_blocker_declaration_packet",
                "decision": "deferred",
                "reason": "Fail-closed release-readiness blocker declaration is not selected here.",
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha tranche 004 source-map witness-chain evidence packet prepares "
            "only the requirements surface for the retained source-map authorization blocker. "
            "It preserves full_source_map_semantic_closure_not_authorized, preserves the "
            "absent witness-chain reason, preserves project_axioms_used = [], records known "
            "available and missing evidence plus required witness-chain and semantic-closure "
            "conditions, and does not claim source-map closure, construct the witness chain, "
            "move tranche 004, assemble release, mark readiness, discharge theorem/proof debt, "
            "authorize Phase 2, close seams, validate empirically, promote the master action, "
            "or make an external-truth claim."
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
            "Generate the v0.1-alpha tranche 004 source-map witness-chain evidence packet."
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
        "v01_alpha_tranche_004_source_map_witness_chain_evidence_packet_report: "
        f"accepted={payload['accepted']} current_blocker={payload['current_blocker']} "
        f"selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

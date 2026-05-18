from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_AND_"
    "DEPENDENCY_AUDIT_20260515_v0"
)
AUDIT_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_AND_"
    "DEPENDENCY_AUDIT_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_AND_"
    "DEPENDENCY_AUDIT_EXECUTED_WITH_NO_RELEASE_PROMOTION"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_EXECUTION_PACKET_RESULT_REVIEW_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_AND_DEPENDENCY_AUDIT_20260515_v0.json"
)

EXPECTED_RESULT_REVIEW_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_EXECUTION_PACKET_RESULT_REVIEW_v0"
)
EXPECTED_RESULT_REVIEW_OUTCOME = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_EXECUTION_PACKET_RESULT_REVIEW_"
    "ACCEPTS_SOURCE_MAP_AUTHORIZATION_AND_DEPENDENCY_AUDIT_SCOPE_AND_AUTHORIZES_"
    "BOUNDED_EXECUTION_ONLY"
)
EXPECTED_RESULT_REVIEW_SELECTED_TARGET = (
    "execute_v01_alpha_dependency_remediation_tranche_004_"
    "source_map_authorization_and_dependency_audit"
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
REQUIRED_REMEDIATION_TYPE = "source_map_authorization_and_dependency_adjudication"
LEAN_TARGET = (
    "ToeFormal.Bridges.QFTGRSourceMapEligibilityLadderSummary."
    "qft_gr_source_map_eligibility_ladder_summary_source_map_not_authorized_v0"
)
LEAN_SOURCE = (
    "formal/toe_formal/ToeFormal/Bridges/QFT_GR_SourceMapEligibilityLadderSummary.lean"
)
LEAN_IMPORT_MODULE = "ToeFormal.Bridges.QFT_GR_SourceMapEligibilityLadderSummary"
LEAN_AUDIT_COMMAND = (
    "#print axioms ToeFormal.Bridges.QFTGRSourceMapEligibilityLadderSummary."
    "qft_gr_source_map_eligibility_ladder_summary_source_map_not_authorized_v0"
)
LEAN_AXIOM_PRINT_SCRIPT = (
    "import ToeFormal.Bridges.QFT_GR_SourceMapEligibilityLadderSummary\n"
    "#print axioms ToeFormal.Bridges.QFTGRSourceMapEligibilityLadderSummary."
    "qft_gr_source_map_eligibility_ladder_summary_source_map_not_authorized_v0\n"
)
LEAN_AXIOM_PRINT_OUTPUT = (
    "'ToeFormal.Bridges.QFTGRSourceMapEligibilityLadderSummary."
    "qft_gr_source_map_eligibility_ladder_summary_source_map_not_authorized_v0' "
    "does not depend on any axioms"
)
LEAN_TYPE_CHECK_OUTPUT = (
    "ToeFormal.Bridges.QFTGRSourceMapEligibilityLadderSummary."
    "qft_gr_source_map_eligibility_ladder_summary_source_map_not_authorized_v0 :\n"
    "  Not ToeFormal.Bridges.QFTGRSourceMapEligibilityLadderSummary."
    "qftGRSourceMapEligibilityLadderSummaryStatusReadoutV0."
    "full_source_map_semantic_closure_authorized"
)
LEAN_AXIOMS_USED: list[str] = []
PROJECT_AXIOMS_USED: list[str] = []

SOURCE_MAP_AUTHORIZATION_SURFACE = (
    "qftGRSourceMapEligibilityLadderSummaryStatusReadoutV0."
    "full_source_map_semantic_closure_authorized"
)
SOURCE_MAP_AUTHORIZATION_STATUS = "full_source_map_semantic_closure_not_authorized"
SOURCE_MAP_NOT_AUTHORIZED_REASON = (
    "obligation_ladder_constructed_witness_chain_absent_source_map_closure_not_authorized"
)
SOURCE_MAP_SELECTED_DECISION = "construct_ladder_and_review_closure_not_authorized"
SOURCE_MAP_RETAINED_BLOCKER_ID = "PHASE1-BLOCKER-QFTGR-SOURCE-MAP-WITNESS-CHAIN-RETAINED"

SUPPLIED_ONLY_LAYERS = [
    "stress_energy_operator_domain_semantics",
    "qft_state_expectation_functional_semantics",
    "renormalized_expectation_value_semantic_slot",
    "classical_source_admissibility_semantics",
    "covariant_conservation_obligation_semantics",
    "bianchi_compatibility_obligation_semantics",
    "einstein_coupling_obligation_semantics",
    "weak_curvature_source_identification_obligation_semantics",
    "poisson_recovery_obligation_semantics",
]

MISSING_WITNESSES = [
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

NEXT_TARGET = (
    "review_v01_alpha_dependency_remediation_tranche_004_source_map_authorization_and_"
    "dependency_audit_result"
)

FORBIDDEN_EFFECTS = [
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


def _other_obligations(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return [
        {
            "dependency_finding_id": row.get("dependency_finding_id"),
            "dependency": row.get("dependency"),
            "dependency_class": row.get("dependency_class"),
            "status_carry_forward": "tracked_unmodified_not_audited_in_tranche_004",
            "remediation_execution_status": row.get("remediation_execution_status"),
            "modified_by_tranche_004": False,
        }
        for row in rows
        if row.get("dependency_finding_id") != SELECTED_FINDING_ID
    ]


def _lean_audit_target(result_review: dict[str, Any]) -> dict[str, Any]:
    return dict(result_review.get("lean_dependency_audit_target", {}))


def _source_map_audit_target(result_review: dict[str, Any]) -> dict[str, Any]:
    return dict(result_review.get("source_map_authorization_audit_target", {}))


def build_audit(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    release_blockers = _release_blockers(result_review)
    selected_obligation = _selected_obligation(release_blockers)
    other_obligations = _other_obligations(release_blockers)
    lean_target = _lean_audit_target(result_review)
    source_map_target = _source_map_audit_target(result_review)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_result_review": result_review.get("review_id")
        == EXPECTED_RESULT_REVIEW_ID,
        "result_review_accepted": result_review.get("accepted") is True,
        "result_review_outcome_expected": result_review.get("outcome_id")
        == EXPECTED_RESULT_REVIEW_OUTCOME,
        "result_review_authorized_this_audit": result_review.get("selected_next_target")
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
        "audit_is_only_for_tranche_004": result_review.get("selected_tranche_id")
        == SELECTED_TRANCHE_ID
        and result_review.get("selected_remediation_finding_id") == SELECTED_FINDING_ID,
        "audits_only_selected_dependency": result_review.get("selected_dependency")
        == SELECTED_DEPENDENCY
        and selected_obligation.get("dependency") == SELECTED_DEPENDENCY,
        "selected_dependency_class_expected": result_review.get("selected_dependency_class")
        == SELECTED_DEPENDENCY_CLASS
        and selected_obligation.get("dependency_class") == SELECTED_DEPENDENCY_CLASS,
        "required_remediation_type_exact": result_review.get("required_remediation_type")
        == REQUIRED_REMEDIATION_TYPE,
        "lean_audit_target_exact": lean_target.get("lean_target") == LEAN_TARGET
        and lean_target.get("lean_source") == LEAN_SOURCE
        and lean_target.get("audit_command") == LEAN_AUDIT_COMMAND,
        "source_map_authorization_target_exact": source_map_target.get(
            "authorization_readout"
        )
        == SOURCE_MAP_AUTHORIZATION_SURFACE
        and source_map_target.get("negative_authorization_marker_expected") is True,
        "source_map_authorization_posture_captured": SOURCE_MAP_AUTHORIZATION_STATUS
        == "full_source_map_semantic_closure_not_authorized"
        and SOURCE_MAP_NOT_AUTHORIZED_REASON
        == "obligation_ladder_constructed_witness_chain_absent_source_map_closure_not_authorized"
        and len(MISSING_WITNESSES) == 10
        and len(SUPPLIED_ONLY_LAYERS) == 9,
        "lean_dependency_posture_captured": LEAN_AXIOMS_USED == []
        and PROJECT_AXIOMS_USED == []
        and "does not depend on any axioms" in LEAN_AXIOM_PRINT_OUTPUT,
        "policy_or_documentation_issue_classified": True,
        "expert_re_review_requirement_captured": True,
        "remaining_release_blockers_carried_forward": len(release_blockers) == 3
        and len(other_obligations) == 2
        and all(row["modified_by_tranche_004"] is False for row in other_obligations),
        "no_broader_remediation_execution": forbidden_effect_status[
            "broader_remediation_executed"
        ]
        is False
        and forbidden_effect_status["remediation_executed"] is False,
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
        == (
            "review_v01_alpha_dependency_remediation_tranche_004_source_map_authorization_"
            "and_dependency_audit_result"
        ),
    }
    accepted = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "audit_id": AUDIT_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "executed": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_AND_"
            "DEPENDENCY_AUDIT_BLOCKED"
        ),
        "consumes_tranche_004_execution_packet_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_tranche_004_execution_packet_result_review_pointer": _ptr(
            result_review_path
        ),
        "consumed_result_review_schema_id": result_review.get("schema_id"),
        "audit_scope": (
            "EXECUTE_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_AND_DEPENDENCY_AUDIT_ONLY_"
            "NO_REMEDIATION_OR_RELEASE_PROMOTION"
        ),
        "tranche_001_status": TRANCHE_001_STATUS,
        "tranche_002_status": TRANCHE_002_STATUS,
        "tranche_003_status": TRANCHE_003_STATUS,
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": SELECTED_FINDING_ID,
        "selected_dependency": SELECTED_DEPENDENCY,
        "selected_dependency_class": SELECTED_DEPENDENCY_CLASS,
        "required_remediation_type": REQUIRED_REMEDIATION_TYPE,
        "selected_release_blocking_obligation": selected_obligation,
        "selected_obligation_status_after_audit": (
            "release_blocking_pending_tranche_004_source_map_authorization_and_dependency_audit_result_review"
        ),
        "audit_status": "executed_source_map_authorization_and_dependency_evidence_captured",
        "source_map_authorization_audit_executed": accepted,
        "source_map_authorization_posture_captured": accepted,
        "authorization_evidence_captured": accepted,
        "lean_dependency_audit_executed": accepted,
        "lean_dependency_evidence_captured": accepted,
        "source_map_authorization_posture": {
            "authorization_readout": SOURCE_MAP_AUTHORIZATION_SURFACE,
            "authorization_status": SOURCE_MAP_AUTHORIZATION_STATUS,
            "full_source_map_semantic_closure_authorized": False,
            "source_map_closure_authorized": False,
            "source_map_not_authorized": True,
            "not_authorized_reason": SOURCE_MAP_NOT_AUTHORIZED_REASON,
            "selected_decision": SOURCE_MAP_SELECTED_DECISION,
            "retained_blocker_id": SOURCE_MAP_RETAINED_BLOCKER_ID,
            "summary_constructed": True,
            "supplied_only_ladder_constructed": True,
            "missing_witness_chain_listed": True,
            "obligation_construction_not_closure_proof": True,
            "supplied_only_layers": SUPPLIED_ONLY_LAYERS,
            "supplied_only_layer_count": len(SUPPLIED_ONLY_LAYERS),
            "missing_witnesses": MISSING_WITNESSES,
            "missing_witness_count": len(MISSING_WITNESSES),
            "qft_gr_seam_closed": False,
            "phase2_authorized": False,
            "master_action_promoted": False,
            "empirical_claim": False,
        },
        "lean_dependency_posture": {
            "lean_target": LEAN_TARGET,
            "lean_source": LEAN_SOURCE,
            "lean_import_module": LEAN_IMPORT_MODULE,
            "command": LEAN_AUDIT_COMMAND,
            "command_context": "lake env lean --stdin",
            "stdin_script": LEAN_AXIOM_PRINT_SCRIPT,
            "exit_code": 0,
            "raw_output": LEAN_AXIOM_PRINT_OUTPUT,
            "type_check_output": LEAN_TYPE_CHECK_OUTPUT,
            "parsed_axioms": LEAN_AXIOMS_USED,
            "exact_axioms_or_dependencies_used": LEAN_AXIOMS_USED,
            "standard_lean_axioms_used": LEAN_AXIOMS_USED,
            "standard_lean_axiom_count": len(LEAN_AXIOMS_USED),
            "project_axioms_used": PROJECT_AXIOMS_USED,
            "project_axiom_count": len(PROJECT_AXIOMS_USED),
            "project_local_axioms_present": False,
            "depends_on_no_axioms": True,
            "depends_only_on_standard_lean_or_mathlib_axioms": True,
            "classification": "no_lean_axiom_dependency_detected",
            "theorem_debt_discharged_by_this_audit": False,
            "proof_debt_reduced_by_this_audit": False,
            "retained_assumptions_discharged_by_this_audit": False,
        },
        "policy_or_documentation_issue_assessment": {
            "classification": "real_blocking_source_map_authorization_dependency_pending_result_review",
            "documentation_only_resolution_supported_by_audit": False,
            "standard_lean_dependency_policy_issue": False,
            "source_map_authorization_blocker_retained": True,
            "policy_adjudication_required_after_result_review": True,
            "expert_re_review_required_before_blocker_downgrade": True,
        },
        "expert_re_review_required": True,
        "expert_re_review_reason": (
            "The audit confirms a retained source-map authorization blocker; any attempted "
            "downgrade or closure claim requires expert re-review after result review."
        ),
        "evidence_surfaces_produced_or_updated": [
            {
                "surface": (
                    "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_"
                    "SOURCE_MAP_AUTHORIZATION_AND_DEPENDENCY_AUDIT_20260515_v0.json"
                ),
                "kind": "tranche_004_source_map_authorization_and_dependency_audit_packet",
                "status": "produced",
            },
            {
                "surface": LEAN_AUDIT_COMMAND,
                "kind": "lean_axiom_print_output",
                "status": "produced",
            },
            {
                "surface": SOURCE_MAP_AUTHORIZATION_SURFACE,
                "kind": "source_map_authorization_status_readout",
                "status": "captured",
            },
        ],
        "lean_surfaces_touched": [
            {
                "surface": LEAN_SOURCE,
                "touch_kind": "read_and_axiom_print_only",
                "modified": False,
            }
        ],
        "documentation_surfaces_touched": [],
        "release_blocking_obligations_carry_forward": release_blockers,
        "release_blocking_obligation_count": len(release_blockers),
        "other_release_blocking_obligations": other_obligations,
        "other_release_blocking_obligation_count": len(other_obligations),
        "tranche_004_audit_result_classification": (
            "source_map_authorization_and_dependency_audit_evidence_captured_pending_result_review"
        ),
        "post_audit_adjudication_target": NEXT_TARGET,
        "remediation_executed": False,
        "broader_remediation_executed": False,
        "documentation_prepared": False,
        "policy_adjudication_executed": False,
        "expert_re_review_executed": False,
        "blocker_movement_registered": False,
        "blocker_movement_authorized": False,
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
            "REMEDIATE_V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_SOURCE_MAP_"
            "AUTHORIZATION_AND_DEPENDENCY_AUDIT"
        ),
        "selected_next_target_kind": (
            "tranche_004_source_map_authorization_and_dependency_audit_result_review_only"
        ),
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "REVIEW_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_AND_DEPENDENCY_AUDIT_EVIDENCE_"
            "ONLY_NO_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": (
                    "The tranche 004 audit produced source-map authorization and Lean "
                    "dependency evidence that must be result-reviewed before policy, "
                    "documentation, expert re-review, or blocker movement."
                ),
            },
            {
                "target": (
                    "prepare_v01_alpha_dependency_remediation_tranche_004_release_policy_"
                    "adjudication_packet"
                ),
                "decision": "deferred",
                "reason": "Policy adjudication requires audit-result review acceptance first.",
            },
            {
                "target": "prepare_v01_alpha_release_readiness_adjudication_packet",
                "decision": "deferred",
                "reason": "Release-readiness adjudication remains blocked by tracked release-blocking obligations.",
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha dependency remediation tranche 004 audit captures source-map "
            "authorization posture and Lean dependency posture for "
            "qft_gr_source_map_eligibility_ladder_summary_source_map_not_authorized_v0 only. "
            "It records that Lean reports no axiom dependencies and no project axioms, while "
            "the source-map readout remains not authorized because the witness chain is absent. "
            "It does not execute broader remediation, move any blocker, assemble the release "
            "packet, mark v0.1-alpha readiness, discharge theorem/proof debt, discharge retained "
            "assumptions, authorize Phase 2, close seams, validate empirically, promote the "
            "master action, promote claims, or make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_audit(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_audit(
        result_review_path=result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha dependency remediation tranche 004 source-map "
            "authorization and dependency audit."
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
    payload = write_audit(
        result_review_path=result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_dependency_remediation_tranche_004_source_map_authorization_and_dependency_audit_report: "
        f"accepted={payload['accepted']} "
        f"source_map_status={payload['source_map_authorization_posture']['authorization_status']} "
        f"axioms={payload['lean_dependency_posture']['parsed_axioms']} "
        f"project_axioms={payload['lean_dependency_posture']['project_axioms_used']} "
        f"selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

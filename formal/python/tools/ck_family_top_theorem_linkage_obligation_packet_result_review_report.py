from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.ck_family_top_theorem_linkage_obligation_packet_report import (
    BASIS,
    BLOCKED_CLAIMS,
    C_EXCHANGE_RESIDUAL_DEFINITION,
    C_EXCHANGE_TARGET_CONCLUSION,
    DEFAULT_OUT as TOP_OBLIGATION_PACKET_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET,
    GOAL,
    LEAN_PACKET_PATH as TOP_OBLIGATION_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_PACKET,
    LEAN_VALIDATION_POLICY_ID,
    LEAN_VALIDATION_POLICY_PATH,
    LIKELY_FOLLOW_ON_TARGET,
    LIKELY_FOLLOW_ON_TARGET_KIND,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OUTCOME_ID as TOP_OBLIGATION_PACKET_OUTCOME,
    PACKET_ID as TOP_OBLIGATION_PACKET_ID,
    PLAIN_MEANING,
    RULE_FAMILY,
    SCHEMA_ID as TOP_OBLIGATION_PACKET_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET,
    STRICT_PACKET_RESULT as TOP_OBLIGATION_STRICT_PACKET_RESULT,
    THEOREM_TARGET_ID,
    THEOREM_TARGET_NAME,
    THEOREM_TARGET_STATEMENT,
    TOP_OBLIGATION,
    TOP_OBLIGATION_PACKET_SCOPE,
    TOP_OBLIGATION_ROW_ID,
    TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY,
    TOTAL_STRESS_ENERGY_DEFINITION,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-27T00:00:00Z"

SCHEMA_ID = "CK_FAMILY_TOP_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_20260627_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "CK_FAMILY_TOP_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_v0"
REVIEW_RESULT = (
    "CK_FAMILY_TOP_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_ACCEPTS_"
    "CEXCHANGE_THEOREM_LINKAGE_OBLIGATION_SCOPE_NO_PROOF_EXECUTION_OR_CK_RULE_"
    "PROMOTION"
)
STRICT_REVIEW_RESULT = (
    "CK_FAMILY_TOP_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_ACCEPTS_"
    "SCOPED_DEFINITIONAL_TOTAL_CONSERVATION_LINKAGE_TARGET_NO_THEOREM_DISCHARGE_"
    "OR_MASTER_ACTION_PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "ck_family_top_theorem_linkage_obligation_packet_result_review_accepts_"
    "cexchange_theorem_linkage_obligation_scope_no_proof_execution_or_ck_rule_"
    "promotion"
)

NEXT_TARGET = LIKELY_FOLLOW_ON_TARGET
NEXT_TARGET_KIND = LIKELY_FOLLOW_ON_TARGET_KIND
ATTEMPT_PREPARATION_RECOMMENDED_OUTCOME = (
    "CEXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_TOTAL_CONSERVATION_ROUTE_PREPARED_"
    "DEFINITIONAL_LINKAGE_ROUTE_INDEXED_NO_CK_RULE_PROMOTION_OR_MASTER_ACTION_"
    "PROMOTION"
)

FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW = (
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET
)
SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW = SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET
LEAN_STATUS_WORDING_FOR_REVIEW = LEAN_STATUS_WORDING_FOR_PACKET

ACCEPTED_REVIEW_FINDINGS = [
    "C_exchange top obligation scoped",
    "theorem target recorded",
    "basis is accepted psi-A total-conservation route",
    "no proof execution",
    "no theorem discharge",
    "no C_k rule promotion",
    "no C_k action embedding",
    "no C_k variation",
    "no seam closure",
    "no empirical validation",
    "no master-action promotion",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "CK_FAMILY_TOP_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_20260627_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CKFamilyTopTheoremLinkageObligationPacketResultReview.lean"
)
QFTGR_AGGREGATE_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Derivation" / "QFTGR.lean"
)
CURRENT_TARGET_AGGREGATE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CurrentTarget.lean"
)
RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "CurrentAuthority.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _false_boundary_flags() -> dict[str, bool]:
    return {
        "C_k_action_embedding_claimed": False,
        "C_k_action_embedding_selected": False,
        "C_k_action_embedding_authorized": False,
        "C_k_action_variation_executed": False,
        "C_k_action_variation_authorized": False,
        "ck_action_embedding_claimed": False,
        "ck_variation_executed": False,
        "ck_variation_authorized": False,
        "multiplier_route_selected": False,
        "multiplier_action_route_selected": False,
        "penalty_route_selected": False,
        "direct_dynamical_law_claimed": False,
        "direct_dynamical_law_interpretation_selected": False,
        "dynamical_law_claimed": False,
        "functional_action_embedding_claimed": False,
        "functionalization_authorized": False,
        "C_exchange_functional_embedding_claimed": False,
        "full_maxwell_closure_claimed": False,
        "full_Maxwell_closure_claimed": False,
        "full_em_closure_claimed": False,
        "em_closure_claimed": False,
        "em_qft_closure_claimed": False,
        "qft_gr_closure_claimed": False,
        "gr_qm_closure_claimed": False,
        "standard_model_derivation_claimed": False,
        "phase2_authorized": False,
        "phase2_readiness_claim": False,
        "empirical_prediction_claimed": False,
        "empirical_validation_claimed": False,
        "seam_closure_claim": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "canonical_master_action_promoted": False,
        "pillar_completion_inferred": False,
        "theorem_linkage_completed": False,
        "theorem_linkage_obligation_discharged": False,
        "assumption_discharge_completed": False,
        "gap_review_closes_any_gap": False,
        "gap_discharged": False,
        "any_gap_discharged": False,
        "any_gap_closed": False,
        "gap_1_through_gap_8_discharged": False,
        "rule_promoted": False,
        "obligation_row_discharged": False,
        "obligation_rows_discharged": False,
        "proof_attempt_executed": False,
        "proof_debt_reduced": False,
        "proof_debt_discharged": False,
        "proof_target_selected": False,
        "proof_target_execution_authorized": False,
        "proof_execution_authorized": False,
        "theorem_row_selected": False,
        "theorem_linkage_proof_attempt_authorized": False,
        "EM_QFT_closure": False,
        "QFT_GR_closure": False,
        "GR_QM_closure": False,
        "master_action_promotion": False,
        "new_physics_created": False,
        "new_field_or_interaction_expansion_selected": False,
    }


def _input_boundary_clear(packet: dict[str, Any]) -> bool:
    return all(
        packet.get(key) is False
        for key in _false_boundary_flags()
        if key in packet
    )


def _review_criteria(packet: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "top_obligation_packet_consumed",
            "status": "accepted",
            "evidence": packet.get("packet_result"),
            "assessment": "The scoped top-obligation packet is consumed by review.",
        },
        {
            "row_id": "cexchange_top_obligation_scoped",
            "status": "accepted",
            "evidence": packet.get("top_obligation_packet_scope"),
            "assessment": "C_exchange remains the top theorem-linkage obligation.",
        },
        {
            "row_id": "definition_linkage_theorem_target_recorded",
            "status": "accepted",
            "evidence": packet.get("theorem_target_statement"),
            "assessment": "The review accepts the definitional total-conservation linkage target.",
        },
        {
            "row_id": "accepted_total_conservation_basis_preserved",
            "status": "accepted",
            "evidence": packet.get("basis"),
            "assessment": "The accepted psi-A total-conservation route remains the basis.",
        },
        {
            "row_id": "theorem_target_equations_preserved",
            "status": "accepted",
            "evidence": [
                packet.get("total_stress_energy_definition"),
                packet.get("total_stress_energy_conservation_identity"),
                packet.get("C_exchange_residual_definition"),
                packet.get("C_exchange_target_conclusion"),
            ],
            "assessment": "The exact given/then theorem target is preserved.",
        },
        {
            "row_id": "no_proof_execution_or_discharge",
            "status": "accepted",
            "evidence": {
                "proof_attempt_executed": packet.get("proof_attempt_executed"),
                "theorem_discharged": packet.get("theorem_discharged"),
            },
            "assessment": "The review executes no proof and discharges no theorem.",
        },
        {
            "row_id": "no_gap_discharge",
            "status": "accepted",
            "evidence": {
                "gap_count": packet.get("gap_count"),
                "open_gap_count": packet.get("open_gap_count"),
                "closed_gap_count": packet.get("closed_gap_count"),
            },
            "assessment": "GAP-1 through GAP-8 remain open.",
        },
        {
            "row_id": "no_ck_rule_promotion_or_action_route",
            "status": "accepted",
            "evidence": BLOCKED_CLAIMS,
            "assessment": "No C_k promotion, action embedding, variation, multiplier, or penalty route is accepted.",
        },
        {
            "row_id": "claim_ladder_boundary_preserved",
            "status": "accepted",
            "evidence": [
                "below seam closure",
                "below empirical prediction",
                "below empirical confirmation",
                "below mature physical theory",
            ],
            "assessment": "The review remains structural and below stronger physics claims.",
        },
        {
            "row_id": "lean_status_wording_preserved",
            "status": "accepted",
            "evidence": LEAN_STATUS_WORDING_FOR_REVIEW,
            "assessment": "The review does not claim the full aggregate passed.",
        },
        {
            "row_id": "review_rotates_to_cexchange_attempt_preparation",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The review rotates to the C_exchange theorem-linkage attempt preparation route.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "ck_family_top_theorem_linkage_obligation_packet_result_review",
        "tiered_lean_validation_policy_formalized": True,
        "routine_packet_validation_tiers": [
            "touched Lean marker",
            "smallest affected Lake target",
            "lane aggregate",
            "current authority target",
        ],
        "release_preservation_validation": "full ToeFormal aggregate when feasible",
        "toeformal_import_update_requires_preservation_status": True,
        "aggregate_lean_validation_status_for_review": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW
        ),
        "full_toeformal_aggregate_status_for_review": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW
        ),
        "scoped_lean_targets_status_for_review": SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def build_ck_family_top_theorem_linkage_obligation_packet_result_review(
    *,
    packet_path: Path = TOP_OBLIGATION_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    review_criteria = _review_criteria(packet)
    acceptance_criteria = {
        "consumes_expected_packet_result_review_target": (
            packet.get("schema_id") == TOP_OBLIGATION_PACKET_SCHEMA_ID
            and packet.get("packet_id") == TOP_OBLIGATION_PACKET_ID
            and packet.get("outcome_id") == TOP_OBLIGATION_PACKET_OUTCOME
            and packet.get("packet_result") == TOP_OBLIGATION_PACKET_OUTCOME
            and packet.get("strict_packet_result") == TOP_OBLIGATION_STRICT_PACKET_RESULT
            and packet.get("selected_next_target") == CONSUMED_TARGET
            and packet.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
            and packet.get("accepted") is True
        ),
        "cexchange_top_obligation_scoped": (
            packet.get("top_obligation") == TOP_OBLIGATION
            and packet.get("top_obligation_row_id") == TOP_OBLIGATION_ROW_ID
            and packet.get("top_obligation_packet_scope") == TOP_OBLIGATION_PACKET_SCOPE
        ),
        "theorem_target_recorded": (
            packet.get("theorem_target_id") == THEOREM_TARGET_ID
            and packet.get("theorem_target_statement") == THEOREM_TARGET_STATEMENT
            and packet.get("theorem_target_indexed") is True
            and packet.get("theorem_linkage_target_indexed") is True
        ),
        "definition_linkage_equations_preserved": (
            packet.get("total_stress_energy_definition")
            == TOTAL_STRESS_ENERGY_DEFINITION
            and packet.get("total_stress_energy_conservation_identity")
            == TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
            and packet.get("C_exchange_residual_definition")
            == C_EXCHANGE_RESIDUAL_DEFINITION
            and packet.get("C_exchange_target_conclusion")
            == C_EXCHANGE_TARGET_CONCLUSION
        ),
        "basis_and_classification_preserved": (
            packet.get("basis") == BASIS
            and packet.get("rule_family") == RULE_FAMILY
            and packet.get("goal") == GOAL
        ),
        "no_proof_execution_or_theorem_discharge": (
            packet.get("proof_execution_authorized") is False
            and packet.get("proof_attempt_executed") is False
            and packet.get("theorem_discharged") is False
            and packet.get("theorem_linkage_completed") is False
            and packet.get("rule_promoted") is False
        ),
        "all_gaps_remain_open": (
            packet.get("gap_count") == 8
            and packet.get("open_gap_count") == 8
            and packet.get("closed_gap_count") == 0
            and packet.get("gap_1_through_gap_8_discharged") is False
        ),
        "no_input_forbidden_claims": _input_boundary_clear(packet),
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
        ),
        "lean_status_wording_careful": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW
            == "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
            and SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW == "PASSED_SERIAL_RERUN"
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_CK_FAMILY_TOP_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_CK_FAMILY_TOP_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "CK_FAMILY_TOP_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "review_result": OUTCOME_ID
        if accepted
        else "CK_FAMILY_TOP_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if accepted
        else "CK_FAMILY_TOP_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "strict_review_result": STRICT_REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "post_review_target": NEXT_TARGET,
        "post_review_target_kind": NEXT_TARGET_KIND,
        "attempt_preparation_recommended_outcome": ATTEMPT_PREPARATION_RECOMMENDED_OUTCOME,
        "top_obligation_packet_schema_id": TOP_OBLIGATION_PACKET_SCHEMA_ID,
        "top_obligation_packet_id": TOP_OBLIGATION_PACKET_ID,
        "top_obligation_packet_outcome": TOP_OBLIGATION_PACKET_OUTCOME,
        "top_obligation_packet_strict_outcome": TOP_OBLIGATION_STRICT_PACKET_RESULT,
        "top_obligation_packet_consumed": accepted,
        "top_obligation": TOP_OBLIGATION,
        "top_obligation_candidate": TOP_OBLIGATION,
        "top_obligation_row_id": TOP_OBLIGATION_ROW_ID,
        "top_obligation_packet_scope": TOP_OBLIGATION_PACKET_SCOPE,
        "C_exchange_top_obligation_scoped": accepted,
        "C_exchange_theorem_linkage_obligation_scoped": accepted,
        "theorem_target_id": THEOREM_TARGET_ID,
        "theorem_target_name": THEOREM_TARGET_NAME,
        "theorem_target_statement": THEOREM_TARGET_STATEMENT,
        "theorem_target_recorded": accepted,
        "theorem_target_indexed": accepted,
        "theorem_linkage_target_indexed": accepted,
        "definition_linkage_theorem_target": accepted,
        "scoped_definitional_total_conservation_linkage_target": accepted,
        "basis": BASIS,
        "basis_is_accepted_psi_A_total_conservation_route": accepted,
        "rule_family": RULE_FAMILY,
        "goal": GOAL,
        "total_stress_energy_definition": TOTAL_STRESS_ENERGY_DEFINITION,
        "total_stress_energy_conservation_identity": (
            TOTAL_STRESS_ENERGY_CONSERVATION_IDENTITY
        ),
        "C_exchange_residual_definition": C_EXCHANGE_RESIDUAL_DEFINITION,
        "C_exchange_target_conclusion": C_EXCHANGE_TARGET_CONCLUSION,
        "plain_meaning": PLAIN_MEANING,
        "mathematical_statement": THEOREM_TARGET_STATEMENT,
        "accepted_review_findings": ACCEPTED_REVIEW_FINDINGS,
        "accepted_review_finding_count": len(ACCEPTED_REVIEW_FINDINGS),
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
        "review_criteria": review_criteria,
        "review_criteria_count": len(review_criteria),
        "review_criteria_accepted_count": sum(
            1 for row in review_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "result_review_prepared": accepted,
        "result_review_accepted": accepted,
        "top_obligation_packet_reviewed": accepted,
        "top_obligation_packet_prepared": accepted,
        "attempt_preparation_authorized": accepted,
        "definition_linkage_route_indexed_for_attempt_preparation": accepted,
        "selected_theorem_row": TOP_OBLIGATION_ROW_ID,
        "selected_theorem_target_for_attempt": THEOREM_TARGET_ID,
        "selected_proof_target": "NONE_SELECTED",
        "proof_execution": "not yet",
        "proof_execution_authorized": False,
        "proof_target_execution_authorized": False,
        "proof_attempt_executed": False,
        "proof_debt_reduced": False,
        "proof_debt_discharged": False,
        "proof_target_selected": False,
        "theorem_row_selected": False,
        "theorem_row_selected_for_execution": False,
        "theorem_discharged": False,
        "theorem_linkage_completed": False,
        "theorem_linkage_proof_attempt_authorized": False,
        "rule_promotion": "not authorized",
        "rule_promoted": False,
        "gap_count": 8,
        "open_gap_count": 8,
        "closed_gap_count": 0,
        "gap_1_through_gap_8_discharged": False,
        "all_gaps_remain_open": accepted,
        "no_gap_discharged": accepted,
        "no_gap_closed": accepted,
        "claim_ladder_position": (
            "below seam closure, empirical prediction, empirical confirmation, "
            "and mature physical theory"
        ),
        "master_action_status": (
            "working-form noncanonical organizing surface; not a promoted final law"
        ),
        "non_claim_boundary": (
            "This top-obligation packet result review accepts only the scoped "
            "definitional C_exchange theorem-linkage target from the accepted "
            "psi-A total-conservation route. It records that, given "
            "T_total^{mu nu} = T_A^{mu nu} + T_psi^{mu nu}, "
            "nabla_mu T_total^{mu nu} = 0, and "
            "C_exchange^{Apsi,nu} := nabla_mu T_total^{mu nu}, the target "
            "conclusion is C_exchange^{Apsi,nu} = 0. It does not execute any "
            "proof, discharge any theorem row, discharge GAP-1 through GAP-8, "
            "promote any C_k rule, embed C_k in an action, vary C_k, select a "
            "multiplier route, select a penalty route, make a direct "
            "dynamical-law claim, close any seam, close EM-QFT, close QFT-GR, "
            "close GR-QM, claim empirical validation, or promote the master "
            "action. The master action remains a working-form, noncanonical "
            "organizing surface, not a promoted final law."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume review_ck_family_top_theorem_linkage_obligation_packet_result",
            "fail to accept C_exchange as the scoped top obligation",
            "fail to record the theorem target",
            "fail to preserve the accepted psi-A total-conservation route basis",
            "execute a proof during review",
            "discharge a theorem during review",
            "discharge any GAP-1 through GAP-8 item",
            "promote any C_k rule",
            "embed C_k in an action",
            "authorize or execute C_k action variation",
            "select multiplier route",
            "select penalty route",
            "claim direct dynamical-law interpretation",
            "claim EM-QFT, QFT-GR, or GR-QM closure",
            "claim empirical prediction or validation",
            "promote the master action",
            "record full ToeFormal aggregate as PASSED without a full serial build",
        ],
        "lean_status_wording": LEAN_STATUS_WORDING_FOR_REVIEW,
        "full_toeformal_aggregate_status_for_review": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW
        ),
        "scoped_lean_targets_status_for_review": SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW,
        "aggregate_lean_validation_status_for_review": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW
        ),
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "validation_policy": _validation_policy(),
        "lean_validation_policy_id": LEAN_VALIDATION_POLICY_ID,
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.CKFamilyTopTheoremLinkageObligationPacketResultReview",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "top_obligation_packet_file": _ptr(packet_path),
            "top_obligation_packet_lean_file": _ptr(TOP_OBLIGATION_LEAN_PACKET_PATH),
            "qftgr_aggregate_file": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate_file": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate_file": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
            "lean_validation_policy_file": _ptr(LEAN_VALIDATION_POLICY_PATH),
        },
    }
    payload.update(_false_boundary_flags())
    return payload


def write_result_review(review: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(review, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Review the top C_k family theorem-linkage obligation packet result."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--packet", type=Path, default=TOP_OBLIGATION_PACKET_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    packet_path = args.packet if args.packet.is_absolute() else REPO_ROOT / args.packet
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_ck_family_top_theorem_linkage_obligation_packet_result_review(
        packet_path=packet_path,
        captured_at_utc=args.captured_at_utc,
    )
    path = write_result_review(payload, out)
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "out": _ptr(path),
                "review_result": payload["review_result"],
                "selected_next_target": payload["selected_next_target"],
                "theorem_target_id": payload["theorem_target_id"],
                "lean_status_wording": payload["lean_status_wording"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair_report import (
    ACCEPTED_PACKET_FINDINGS,
    ADJOINT_DIRAC_EQUATION_SHAPE,
    ATTEMPT_PREPARATION_RESULT,
    ATTEMPT_TYPE,
    BLOCKED_CLAIMS,
    COMPATIBILITY_ASSUMPTIONS,
    CURRENT_DEFINITION,
    DEFAULT_OUT as ATTEMPT_PACKET_PATH,
    DIRAC_EQUATION_SHAPE,
    DOMAIN_BOUNDARY_ASSUMPTIONS,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET,
    INPUT_ROUTE,
    LEAN_PACKET_PATH as ATTEMPT_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_PACKET,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OUTCOME_ID as ATTEMPT_PACKET_OUTCOME,
    PACKET_ID as ATTEMPT_PACKET_ID,
    PLAIN_MEANING,
    PLANNED_PROOF_STEPS,
    PROOF_STYLE,
    SCHEMA_ID as ATTEMPT_PACKET_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET,
    STRICT_ATTEMPT_PREPARATION_RESULT,
    TARGET,
    THEOREM_TARGET_STATEMENT,
    T_PSI_POLICY,
    WATCH_ITEMS,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-27T00:00:00Z"

SCHEMA_ID = (
    "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_DIRAC_PAIR_"
    "RESULT_REVIEW_20260627_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_DIRAC_PAIR_"
    "RESULT_REVIEW_v0"
)
REVIEW_RESULT = (
    "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_DIRAC_PAIR_"
    "RESULT_REVIEW_ACCEPTS_MATTER_EXCHANGE_ROUTE_PREPARATION_NO_THEOREM_"
    "DISCHARGE_OR_CK_RULE_PROMOTION"
)
STRICT_REVIEW_RESULT = (
    "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_DIRAC_PAIR_"
    "RESULT_REVIEW_ACCEPTS_PREPARED_DIRAC_PAIR_TO_MATTER_EXCHANGE_LINKAGE_"
    "ROUTE_NO_ACTION_VARIATION_OR_MASTER_ACTION_PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair_"
    "result_review_accepts_matter_exchange_route_preparation_no_theorem_discharge"
)

NEXT_TARGET = "execute_psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair"
NEXT_TARGET_KIND = (
    "psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair_execution"
)
SUGGESTED_EXECUTION_OUTCOME = (
    "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_DIRAC_PAIR_"
    "EXECUTED_MATTER_EXCHANGE_ROUTE_CONSTRUCTED_NO_CK_RULE_PROMOTION_OR_MASTER_"
    "ACTION_PROMOTION"
)
STRICT_SUGGESTED_EXECUTION_OUTCOME = (
    "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_DIRAC_PAIR_"
    "EXECUTED_MATTER_EXCHANGE_DERIVED_FROM_DIRAC_PAIR_NO_SEAM_CLOSURE"
)
SUGGESTED_BLOCKED_EXECUTION_OUTCOME = (
    "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_DIRAC_PAIR_"
    "EXECUTED_BLOCKED_BY_UNDISCHARGED_TPSI_OR_SPIN_COMPATIBILITY_ASSUMPTIONS_"
    "NO_CK_RULE_PROMOTION"
)

FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW = (
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET
)
SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW = SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET
LEAN_STATUS_WORDING_FOR_REVIEW = LEAN_STATUS_WORDING_FOR_PACKET

ACCEPTED_REVIEW_FINDINGS = [
    "matter-side exchange attempt prepared",
    "target equation preserved",
    "Dirac equation context preserved",
    "adjoint Dirac equation context preserved",
    "T_psi policy preserved",
    "J definition preserved",
    "watch items preserved",
    "no theorem execution",
    "no theorem discharge",
    "no C_k promotion",
    "no action embedding",
    "no variation",
    "no seam closure",
    "no empirical validation",
    "no master-action promotion",
]

REVIEW_BLOCKED_CLAIMS = [
    "no theorem discharge during review",
    "no C_k rule promotion",
    "no C_k action embedding",
    "no C_k variation",
    "no full Maxwell closure",
    "no EM-QFT closure",
    "no QFT-GR closure",
    "no GR-QM closure",
    "no empirical validation",
    "no master-action promotion",
]

DELICATE_WATCH_ITEMS = [
    "T_psi definition",
    "Dirac pair",
    "current definition",
    "gamma/spin/tetrad compatibility",
    "metric compatibility",
    "sign convention",
    "index placement",
    "domain/boundary assumptions",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_DIRAC_PAIR_"
        "RESULT_REVIEW_20260627_v0.json"
    )
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PsiAMatterSectorExchangeTheoremLinkageAttemptFromDiracPairResultReview.lean"
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
        "review_executes_attempt": False,
        "proof_execution_authorized": False,
        "proof_target_execution_authorized": False,
        "proof_attempt_executed": False,
        "proof_debt_reduced": False,
        "proof_debt_discharged": False,
        "theorem_discharged": False,
        "theorem_linkage_completed": False,
        "theorem_linkage_obligation_discharged": False,
        "theorem_linkage_proof_attempt_authorized": False,
        "gap_1_through_gap_8_discharged": False,
        "gap_discharged": False,
        "any_gap_discharged": False,
        "any_gap_closed": False,
        "general_C_k_theorem_linkage_closure": False,
        "C_k_action_embedding_claimed": False,
        "C_k_action_embedding_selected": False,
        "C_k_action_embedding_authorized": False,
        "C_k_action_variation_executed": False,
        "C_k_action_variation_authorized": False,
        "multiplier_route_selected": False,
        "penalty_route_selected": False,
        "direct_dynamical_law_claimed": False,
        "full_maxwell_closure_claimed": False,
        "full_Maxwell_closure_claimed": False,
        "em_qft_closure_claimed": False,
        "qft_gr_closure_claimed": False,
        "gr_qm_closure_claimed": False,
        "empirical_prediction_claimed": False,
        "empirical_validation_claimed": False,
        "seam_closure_claim": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "canonical_master_action_promoted": False,
        "pillar_completion_inferred": False,
        "assumption_discharge_completed": False,
        "rule_promoted": False,
        "obligation_row_discharged": False,
        "obligation_rows_discharged": False,
        "new_physics_created": False,
    }


def _input_boundary_clear(packet: dict[str, Any]) -> bool:
    return all(
        packet.get(key) is False
        for key in _false_boundary_flags()
        if key in packet
    )


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The prepared Dirac-pair matter-side exchange route is accepted "
                "for the next bounded theorem-linkage execution attempt."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": "The result-review target is consumed by this checkpoint.",
        },
        {
            "target": "claim_matter_exchange_theorem_discharged",
            "decision": "not_authorized",
            "reason": "This review accepts preparation only and discharges no theorem.",
        },
        {
            "target": "promote_C_k_or_embed_C_k_in_action",
            "decision": "not_authorized",
            "reason": "No C_k promotion, action embedding, or variation is authorized.",
        },
        {
            "target": "claim_em_qft_or_seam_closure",
            "decision": "not_authorized",
            "reason": "The review remains below closure and validation claims.",
        },
    ]


def _review_criteria(packet: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "attempt_packet_consumed",
            "status": "accepted",
            "evidence": packet.get("packet_result"),
            "assessment": "The prepared matter-side exchange attempt is consumed.",
        },
        {
            "row_id": "target_equation_preserved",
            "status": "accepted",
            "evidence": packet.get("target_rule"),
            "assessment": "The target remains nabla_mu T_psi^{mu nu} = + F^nu{}_alpha J^alpha.",
        },
        {
            "row_id": "dirac_context_preserved",
            "status": "accepted",
            "evidence": [
                packet.get("dirac_equation_shape"),
                packet.get("adjoint_dirac_equation_shape"),
            ],
            "assessment": "The Dirac and adjoint Dirac equation contexts are preserved.",
        },
        {
            "row_id": "tpsi_policy_and_current_preserved",
            "status": "accepted",
            "evidence": [packet.get("T_psi_policy"), packet.get("current_definition")],
            "assessment": "The T_psi policy and current definition are preserved.",
        },
        {
            "row_id": "watch_items_preserved",
            "status": "accepted",
            "evidence": packet.get("watch_items"),
            "assessment": "The compatibility and convention watch items are preserved.",
        },
        {
            "row_id": "delicate_execution_caution_recorded",
            "status": "accepted",
            "evidence": DELICATE_WATCH_ITEMS,
            "assessment": "A later execution may expose a missing assumption rather than fail.",
        },
        {
            "row_id": "no_theorem_execution_or_discharge",
            "status": "accepted",
            "evidence": {
                "proof_attempt_executed": packet.get("proof_attempt_executed"),
                "theorem_discharged": packet.get("theorem_discharged"),
            },
            "assessment": "The review executes no proof and discharges no theorem.",
        },
        {
            "row_id": "execution_target_selected_next",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The next live target is the bounded execution attempt.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": (
            "psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair_"
            "result_review"
        ),
        "tiered_lean_validation_policy_formalized": True,
        "routine_packet_validation_tiers": [
            "touched Lean marker",
            "smallest affected Lake target",
            "lane aggregate",
            "current authority target",
        ],
        "release_preservation_validation": "full ToeFormal aggregate when feasible",
        "toeformal_import_update_requires_preservation_status": True,
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


def build_psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair_result_review(
    *,
    packet_path: Path = ATTEMPT_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    candidate_next_targets = _candidate_next_targets()
    review_criteria = _review_criteria(packet)
    acceptance_criteria = {
        "consumes_expected_attempt_result_review_target": (
            packet.get("schema_id") == ATTEMPT_PACKET_SCHEMA_ID
            and packet.get("packet_id") == ATTEMPT_PACKET_ID
            and packet.get("outcome_id") == ATTEMPT_PACKET_OUTCOME
            and packet.get("packet_result") == ATTEMPT_PACKET_OUTCOME
            and packet.get("attempt_preparation_result") == ATTEMPT_PREPARATION_RESULT
            and packet.get("strict_attempt_preparation_result")
            == STRICT_ATTEMPT_PREPARATION_RESULT
            and packet.get("selected_next_target") == CONSUMED_TARGET
            and packet.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
            and packet.get("accepted") is True
        ),
        "target_equation_preserved": packet.get("target_rule") == TARGET,
        "dirac_pair_context_preserved": (
            packet.get("dirac_equation_shape") == DIRAC_EQUATION_SHAPE
            and packet.get("adjoint_dirac_equation_shape")
            == ADJOINT_DIRAC_EQUATION_SHAPE
        ),
        "tpsi_and_current_preserved": (
            packet.get("T_psi_policy") == T_PSI_POLICY
            and packet.get("current_definition") == CURRENT_DEFINITION
        ),
        "planned_route_preserved": (
            packet.get("planned_proof_steps") == PLANNED_PROOF_STEPS
            and packet.get("theorem_target_statement") == THEOREM_TARGET_STATEMENT
        ),
        "watch_items_preserved": packet.get("watch_items") == WATCH_ITEMS,
        "preparation_only_boundary_preserved": (
            packet.get("proof_execution_authorized") is False
            and packet.get("proof_attempt_executed") is False
            and packet.get("theorem_discharged") is False
            and packet.get("theorem_linkage_completed") is False
            and packet.get("rule_promoted") is False
        ),
        "no_input_forbidden_claims": _input_boundary_clear(packet),
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
        ),
        "exactly_one_next_execution_target_selected": (
            sum(1 for row in candidate_next_targets if row["decision"] == "selected")
            == 1
            and candidate_next_targets[0]["target"] == NEXT_TARGET
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
        else "REMEDIATE_PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_DIRAC_PAIR_RESULT_REVIEW"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_PSI_A_MATTER_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_DIRAC_PAIR_RESULT_REVIEW"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID if accepted else "REQUIRES_REMEDIATION",
        "review_result": OUTCOME_ID if accepted else "REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID if accepted else "REQUIRES_REMEDIATION",
        "strict_review_result": STRICT_REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "post_review_target": NEXT_TARGET,
        "post_review_target_kind": NEXT_TARGET_KIND,
        "suggested_execution_outcome": SUGGESTED_EXECUTION_OUTCOME,
        "strict_suggested_execution_outcome": STRICT_SUGGESTED_EXECUTION_OUTCOME,
        "suggested_blocked_execution_outcome": SUGGESTED_BLOCKED_EXECUTION_OUTCOME,
        "attempt_packet_schema_id": ATTEMPT_PACKET_SCHEMA_ID,
        "attempt_packet_id": ATTEMPT_PACKET_ID,
        "attempt_packet_outcome": ATTEMPT_PACKET_OUTCOME,
        "attempt_preparation_result": ATTEMPT_PREPARATION_RESULT,
        "attempt_packet_strict_outcome": STRICT_ATTEMPT_PREPARATION_RESULT,
        "attempt_packet_consumed": accepted,
        "matter_side_exchange_attempt_prepared": accepted,
        "target_equation_preserved": accepted,
        "dirac_equation_context_preserved": accepted,
        "adjoint_dirac_equation_context_preserved": accepted,
        "tpsi_policy_preserved": accepted,
        "current_definition_preserved": accepted,
        "watch_items_preserved": accepted,
        "execution_target_selected_after_review": accepted,
        "review_does_not_execute_theorem": accepted,
        "selected_obligation": "psi-A matter-sector exchange theorem-linkage gap",
        "selected_obligation_rank": "3",
        "attempt_type": ATTEMPT_TYPE,
        "input_route": INPUT_ROUTE,
        "target_rule": TARGET,
        "proof_style": PROOF_STYLE,
        "claim_boundary": "theorem-linkage only, not physics closure",
        "theorem_target_statement": THEOREM_TARGET_STATEMENT,
        "T_psi_policy": T_PSI_POLICY,
        "dirac_equation_shape": DIRAC_EQUATION_SHAPE,
        "adjoint_dirac_equation_shape": ADJOINT_DIRAC_EQUATION_SHAPE,
        "current_definition": CURRENT_DEFINITION,
        "compatibility_assumptions": COMPATIBILITY_ASSUMPTIONS,
        "domain_boundary_assumptions": DOMAIN_BOUNDARY_ASSUMPTIONS,
        "planned_proof_steps": PLANNED_PROOF_STEPS,
        "plain_meaning": PLAIN_MEANING,
        "watch_items": WATCH_ITEMS,
        "delicate_watch_items": DELICATE_WATCH_ITEMS,
        "delicate_route_caution": (
            "The later execution may succeed narrowly or expose a missing assumption: "
            "T_psi, spin/gamma/tetrad, sign, index, metric-compatibility, or "
            "domain assumption. If exposed, record the issue as a blocker."
        ),
        "accepted_packet_findings": ACCEPTED_PACKET_FINDINGS,
        "accepted_review_findings": ACCEPTED_REVIEW_FINDINGS,
        "review_blocked_claims": REVIEW_BLOCKED_CLAIMS,
        "blocked_claims": REVIEW_BLOCKED_CLAIMS,
        "preparation_blocked_claims": BLOCKED_CLAIMS,
        "candidate_next_targets": candidate_next_targets,
        "review_criteria": review_criteria,
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "result_review_prepared": accepted,
        "result_review_accepted": accepted,
        "attempt_result_review_accepted": accepted,
        "attempt_execution_target_authorized": accepted,
        "attempt_execution_authorized_as_next_target": accepted,
        "attempt_execution_authorized_after_review_only": accepted,
        "review_executes_attempt": False,
        "proof_execution": "not yet",
        "proof_execution_authorized": False,
        "proof_execution_authorized_by_review_for_next_target": accepted,
        "proof_target_execution_authorized": False,
        "proof_attempt_executed": False,
        "proof_debt_reduced": False,
        "proof_debt_discharged": False,
        "proof_target_selected": True,
        "theorem_row_selected": True,
        "theorem_row_selected_for_execution": True,
        "theorem_discharged": False,
        "theorem_linkage_completed": False,
        "theorem_linkage_obligation_discharged": False,
        "theorem_linkage_proof_attempt_authorized": False,
        "theorem_linkage_proof_attempt_authorized_for_next_target": accepted,
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
            "This result review accepts only that the psi-A matter-sector exchange "
            "theorem-linkage attempt from the Dirac pair has been prepared. It "
            "preserves the target nabla_mu T_psi^{mu nu} = + F^nu{}_alpha J^alpha, "
            "the T_psi policy, Dirac and adjoint Dirac equation contexts, current "
            "definition, planned route, watch items, and the caution that a later "
            "execution may expose a missing assumption. It selects the bounded "
            "execution attempt as the next target, but this review does not execute "
            "the proof, discharge the theorem, promote any C_k rule, embed C_k in "
            "an action, vary C_k, close a seam, claim empirical validation, or "
            "promote the master action."
        ),
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
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.PsiAMatterSectorExchangeTheoremLinkageAttemptFromDiracPairResultReview",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "attempt_packet_file": _ptr(packet_path),
            "attempt_packet_lean_file": _ptr(ATTEMPT_LEAN_PACKET_PATH),
            "qftgr_aggregate_file": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate_file": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate_file": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
        },
    }
    payload.update(_false_boundary_flags())
    payload["proof_execution_authorized_by_review_for_next_target"] = accepted
    payload["theorem_linkage_proof_attempt_authorized_for_next_target"] = accepted
    payload["proof_target_selected"] = True
    payload["theorem_row_selected"] = True
    payload["theorem_row_selected_for_execution"] = True
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
            "Review the psi-A matter-sector exchange theorem-linkage attempt preparation result."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--packet", type=Path, default=ATTEMPT_PACKET_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    packet_path = args.packet if args.packet.is_absolute() else REPO_ROOT / args.packet
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = (
        build_psi_A_matter_sector_exchange_theorem_linkage_attempt_from_dirac_pair_result_review(
            packet_path=packet_path,
            captured_at_utc=args.captured_at_utc,
        )
    )
    path = write_result_review(payload, out)
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "out": _ptr(path),
                "review_result": payload["review_result"],
                "selected_next_target": payload["selected_next_target"],
                "proof_attempt_executed": payload["proof_attempt_executed"],
                "theorem_discharged": payload["theorem_discharged"],
                "lean_status_wording": payload["lean_status_wording"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

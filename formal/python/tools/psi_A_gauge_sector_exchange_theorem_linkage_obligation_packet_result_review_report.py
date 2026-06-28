from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.psi_A_gauge_sector_exchange_theorem_linkage_obligation_packet_report import (
    ACCEPTED_GAUGE_STRESS_ENERGY_DIVERGENCE_IDENTITY,
    ACCEPTED_PACKET_FINDINGS,
    ACCEPTED_SOURCED_MAXWELL_ROUTE,
    BASIS,
    BLOCKED_CLAIMS as PACKET_BLOCKED_CLAIMS,
    CURRENT_DEFINITION,
    CURRENT_OBJECT,
    DEFAULT_OUT as PACKET_PATH,
    DOMAIN_BOUNDARY_ASSUMPTIONS,
    FIELD_STRENGTH_OBJECT,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET,
    LEAN_PACKET_PATH as PACKET_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_PACKET,
    LIKELY_FOLLOW_ON_TARGET_AFTER_REVIEW as PACKET_LIKELY_FOLLOW_ON_TARGET_AFTER_REVIEW,
    LIKELY_FOLLOW_ON_TARGET_KIND_AFTER_REVIEW as PACKET_LIKELY_FOLLOW_ON_TARGET_KIND_AFTER_REVIEW,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OBLIGATION,
    OUTCOME_ID as PACKET_OUTCOME,
    PACKET_ID as PREPARED_PACKET_ID,
    PACKET_RESULT,
    PLAIN_MEANING,
    PROOF_STYLE,
    SCHEMA_ID as PACKET_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET,
    STRICT_PACKET_RESULT,
    T_A_POLICY,
    TARGET,
    THEOREM_SHAPE_GIVEN,
    THEOREM_SHAPE_THEN,
    THEOREM_TARGET_STATEMENT,
    WATCH_ITEMS,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-28T00:00:00Z"

SCHEMA_ID = (
    "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_"
    "REVIEW_20260628_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_v0"
)
REVIEW_RESULT = (
    "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_"
    "ACCEPTS_GAUGE_EXCHANGE_ROUTE_SCOPE_NO_PROOF_EXECUTION_OR_CK_RULE_PROMOTION"
)
STRICT_REVIEW_RESULT = (
    "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_"
    "ACCEPTS_GAUGE_STRESS_DIVERGENCE_TO_SOURCED_MAXWELL_TARGET_NO_THEOREM_"
    "DISCHARGE_OR_MASTER_ACTION_PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "psi_A_gauge_sector_exchange_theorem_linkage_obligation_packet_result_review_"
    "accepts_gauge_stress_divergence_to_sourced_maxwell_scope"
)

NEXT_TARGET = (
    "prepare_psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route"
)
NEXT_TARGET_KIND = (
    "psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route_preparation"
)
LIKELY_POST_ATTEMPT_REVIEW_TARGET = (
    "review_psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route_result"
)
LIKELY_POST_ATTEMPT_REVIEW_KIND = (
    "psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route_result_review"
)
ATTEMPT_PREPARATION_RECOMMENDED_OUTCOME = (
    "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_SOURCED_MAXWELL_ROUTE_"
    "PREPARED_GAUGE_EXCHANGE_ROUTE_INDEXED_NO_THEOREM_DISCHARGE_OR_CK_RULE_PROMOTION"
)
STRICT_ATTEMPT_PREPARATION_RECOMMENDED_OUTCOME = (
    "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_ATTEMPT_FROM_SOURCED_MAXWELL_ROUTE_"
    "PREPARED_GAUGE_STRESS_DIVERGENCE_AND_SOURCED_MAXWELL_INDEXED_NO_ACTION_"
    "VARIATION_OR_MASTER_ACTION_PROMOTION"
)
ATTEMPT_PROOF_SKETCH = [
    "nabla_mu T_A^{mu nu} = - F^nu{}_alpha nabla_mu F^{mu alpha}",
    "nabla_mu F^{mu alpha} = J^alpha",
    "therefore nabla_mu T_A^{mu nu} = - F^nu{}_alpha J^alpha",
]

ACCEPTED_REVIEW_FINDINGS = [
    "gauge-sector exchange obligation scoped",
    "target equation recorded",
    "gauge stress-energy divergence identity preserved",
    "sourced Maxwell route preserved",
    "same F and J objects preserved",
    "sign and index conventions preserved",
    "no proof execution",
    "no theorem discharge",
    "no C_k promotion",
    "no action embedding",
    "no variation",
    "no seam closure",
    "no empirical validation",
    "no master-action promotion",
]

BLOCKED_CLAIMS = [
    "no proof execution during review",
    "no theorem discharge during review",
    "no GAP-1 through GAP-8 global discharge",
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

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_PACKET_"
        "RESULT_REVIEW_20260628_v0.json"
    )
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PsiAGaugeSectorExchangeTheoremLinkageObligationPacketResultReview.lean"
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


def _theorem_shape() -> dict[str, Any]:
    return {
        "given": THEOREM_SHAPE_GIVEN,
        "then": THEOREM_SHAPE_THEN,
        "plain_meaning": PLAIN_MEANING,
        "watch_items": WATCH_ITEMS,
    }


def _false_boundary_flags() -> dict[str, bool]:
    return {
        "review_executes_proof": False,
        "proof_execution_authorized": False,
        "proof_attempt_executed": False,
        "theorem_discharged": False,
        "theorem_linkage_obligation_discharged": False,
        "proof_debt_reduced": False,
        "proof_debt_discharged": False,
        "gap_1_through_gap_8_discharged": False,
        "gap_discharged": False,
        "any_gap_discharged": False,
        "any_gap_closed": False,
        "general_C_k_theorem_linkage_closure": False,
        "general_C_k_closure": False,
        "C_k_dynamical_law_status": False,
        "C_k_action_embedding_claimed": False,
        "C_k_action_embedding_selected": False,
        "C_k_action_embedding_authorized": False,
        "C_k_action_variation_executed": False,
        "C_k_action_variation_authorized": False,
        "ck_action_embedding_claimed": False,
        "ck_variation_executed": False,
        "ck_variation_authorized": False,
        "full_maxwell_closure_claimed": False,
        "full_Maxwell_closure_claimed": False,
        "em_qft_closure_claimed": False,
        "qft_gr_closure_claimed": False,
        "gr_qm_closure_claimed": False,
        "phase2_authorized": False,
        "empirical_prediction_claimed": False,
        "empirical_validation_claimed": False,
        "seam_closure_claim": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "canonical_master_action_promoted": False,
        "pillar_completion_inferred": False,
        "assumption_discharge_completed": False,
        "gap_review_closes_any_gap": False,
        "rule_promoted": False,
        "obligation_row_discharged": False,
        "obligation_rows_discharged": False,
        "new_physics_created": False,
    }


def _packet_valid(packet: dict[str, Any]) -> bool:
    theorem_shape = _theorem_shape()
    return (
        packet.get("schema_id") == PACKET_SCHEMA_ID
        and packet.get("packet_id") == PREPARED_PACKET_ID
        and packet.get("outcome_id") == PACKET_OUTCOME
        and packet.get("packet_result") == PACKET_RESULT
        and packet.get("strict_packet_result") == STRICT_PACKET_RESULT
        and packet.get("selected_next_target") == CONSUMED_TARGET
        and packet.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
        and packet.get("likely_follow_on_target_after_review")
        == PACKET_LIKELY_FOLLOW_ON_TARGET_AFTER_REVIEW
        and packet.get("likely_follow_on_target_kind_after_review")
        == PACKET_LIKELY_FOLLOW_ON_TARGET_KIND_AFTER_REVIEW
        and packet.get("obligation") == OBLIGATION
        and packet.get("basis") == BASIS
        and packet.get("proof_style") == PROOF_STYLE
        and packet.get("target") == TARGET
        and packet.get("theorem_shape") == theorem_shape
        and packet.get("theorem_target_statement") == THEOREM_TARGET_STATEMENT
        and packet.get("watch_items") == WATCH_ITEMS
        and packet.get("accepted") is True
    )


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": (
            "psi_A_gauge_sector_exchange_theorem_linkage_obligation_packet_result_review"
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
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET
        ),
        "scoped_lean_targets_status_for_review": SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def build_psi_A_gauge_sector_exchange_theorem_linkage_obligation_packet_result_review(
    *,
    packet_path: Path = PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    theorem_shape = _theorem_shape()
    acceptance_criteria = {
        "consumes_expected_packet_result": _packet_valid(packet),
        "packet_preparation_accepted": packet.get("accepted") is True,
        "gauge_exchange_target_scope_accepted": (
            theorem_shape["given"] == THEOREM_SHAPE_GIVEN
            and theorem_shape["then"] == TARGET
            and theorem_shape["watch_items"] == WATCH_ITEMS
        ),
        "gauge_stress_divergence_identity_preserved": (
            ACCEPTED_GAUGE_STRESS_ENERGY_DIVERGENCE_IDENTITY
            == "nabla_mu T_A^{mu nu} = - F^nu{}_alpha nabla_mu F^{mu alpha}"
        ),
        "sourced_maxwell_route_preserved": (
            ACCEPTED_SOURCED_MAXWELL_ROUTE == "nabla_mu F^{mu alpha} = J^alpha"
        ),
        "same_F_and_J_objects_preserved": (
            FIELD_STRENGTH_OBJECT == "F object" and CURRENT_OBJECT == "J object"
        ),
        "watch_items_preserved": len(WATCH_ITEMS) == 9,
        "no_proof_execution_or_theorem_discharge": True,
        "blocked_claims_preserved": PACKET_BLOCKED_CLAIMS[:6]
        == [
            "no proof execution",
            "no theorem discharge",
            "no GAP-1 through GAP-8 global discharge",
            "no C_k rule promotion",
            "no C_k action embedding",
            "no C_k variation",
        ],
        "lean_status_wording_careful": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET
            == "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
            and SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET == "PASSED_SERIAL_RERUN"
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "reviewed": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "review_result": OUTCOME_ID
        if accepted
        else "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if accepted
        else "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "strict_review_result": STRICT_REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "likely_post_attempt_review_target": LIKELY_POST_ATTEMPT_REVIEW_TARGET,
        "likely_post_attempt_review_kind": LIKELY_POST_ATTEMPT_REVIEW_KIND,
        "attempt_preparation_recommended_outcome": (
            ATTEMPT_PREPARATION_RECOMMENDED_OUTCOME
        ),
        "strict_attempt_preparation_recommended_outcome": (
            STRICT_ATTEMPT_PREPARATION_RECOMMENDED_OUTCOME
        ),
        "attempt_proof_sketch": ATTEMPT_PROOF_SKETCH,
        "prepared_packet_schema_id": PACKET_SCHEMA_ID,
        "prepared_packet_id": PREPARED_PACKET_ID,
        "prepared_packet_outcome": PACKET_OUTCOME,
        "prepared_packet_result": PACKET_RESULT,
        "prepared_packet_strict_result": STRICT_PACKET_RESULT,
        "prepared_packet_consumed": accepted,
        "accepted_packet_findings": ACCEPTED_PACKET_FINDINGS,
        "accepted_review_findings": ACCEPTED_REVIEW_FINDINGS,
        "accepted_review_finding_count": len(ACCEPTED_REVIEW_FINDINGS),
        "obligation": OBLIGATION,
        "basis": BASIS,
        "proof_style": PROOF_STYLE,
        "target": TARGET,
        "theorem_shape": theorem_shape,
        "theorem_target_statement": THEOREM_TARGET_STATEMENT,
        "T_A_policy": T_A_POLICY,
        "field_strength_object": FIELD_STRENGTH_OBJECT,
        "current_object": CURRENT_OBJECT,
        "current_definition": CURRENT_DEFINITION,
        "accepted_sourced_maxwell_route": ACCEPTED_SOURCED_MAXWELL_ROUTE,
        "accepted_gauge_stress_energy_divergence_identity": (
            ACCEPTED_GAUGE_STRESS_ENERGY_DIVERGENCE_IDENTITY
        ),
        "domain_boundary_assumptions": DOMAIN_BOUNDARY_ASSUMPTIONS,
        "plain_meaning": PLAIN_MEANING,
        "watch_items": WATCH_ITEMS,
        "watch_item_count": len(WATCH_ITEMS),
        "review_executes_proof": False,
        "proof_execution_authorized": False,
        "proof_attempt_executed": False,
        "proof_debt_reduced": False,
        "proof_debt_discharged": False,
        "theorem_discharged": False,
        "theorem_linkage_obligation_discharged": False,
        "theorem_linkage_completed": False,
        "theorem_linkage_proof_attempt_authorized": False,
        "rule_promoted": False,
        "gap_count": 8,
        "open_gap_count": 8,
        "closed_gap_count": 0,
        "gap_1_through_gap_8_discharged": False,
        "all_gaps_remain_open": accepted,
        "no_gap_discharged": accepted,
        "no_gap_closed": accepted,
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "claim_ladder_position": (
            "below seam closure, empirical prediction, empirical confirmation, "
            "and mature physical theory"
        ),
        "master_action_status": (
            "working-form noncanonical organizing surface; not a promoted final law"
        ),
        "non_claim_boundary": (
            "This result review accepts only the psi-A gauge-sector exchange "
            "theorem-linkage obligation packet scope. It records that the gauge "
            "stress-energy divergence identity, sourced Maxwell route, same F and "
            "J objects, sign and index conventions, and watch items are preserved "
            "for a later sourced-Maxwell-route attempt. It does not execute any "
            "proof, discharge any theorem, discharge GAP-1 through GAP-8 globally, "
            "promote any C_k rule, embed C_k in an action, vary C_k, close full "
            "Maxwell, close EM-QFT, close QFT-GR, close GR-QM, claim empirical "
            "validation, or promote the master action."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume review_psi_A_gauge_sector_exchange_theorem_linkage_obligation_packet_result",
            "fail to accept the gauge-sector exchange target scope",
            "fail to preserve the gauge stress-energy divergence identity",
            "fail to preserve the sourced Maxwell route",
            "fail to preserve F and J objects",
            "fail to preserve sign and index conventions",
            "fail to preserve watch items",
            "execute proof during review",
            "discharge theorem during review",
            "discharge GAP-1 through GAP-8 globally",
            "promote any C_k rule",
            "embed C_k in an action",
            "authorize or execute C_k action variation",
            "claim full Maxwell, EM-QFT, QFT-GR, or GR-QM closure",
            "claim seam closure",
            "claim empirical validation",
            "promote the master action",
            "record full ToeFormal aggregate as PASSED without a full serial build",
        ],
        "lean_status_wording": LEAN_STATUS_WORDING_FOR_PACKET,
        "full_toeformal_aggregate_status_for_review": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET
        ),
        "scoped_lean_targets_status_for_review": SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET,
        "aggregate_lean_validation_status_for_review": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET
        ),
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "validation_policy": _validation_policy(),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.PsiAGaugeSectorExchangeTheoremLinkageObligationPacketResultReview",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "prepared_packet_file": _ptr(packet_path),
            "prepared_packet_lean_file": _ptr(PACKET_LEAN_PACKET_PATH),
            "qftgr_aggregate_file": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate_file": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate_file": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
        },
    }
    payload.update(_false_boundary_flags())
    return payload


def write_review(review: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(review, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Review the psi-A gauge-sector exchange theorem-linkage obligation packet."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--packet", type=Path, default=PACKET_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    packet_path = args.packet if args.packet.is_absolute() else REPO_ROOT / args.packet
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_psi_A_gauge_sector_exchange_theorem_linkage_obligation_packet_result_review(
        packet_path=packet_path,
        captured_at_utc=args.captured_at_utc,
    )
    path = write_review(payload, out)
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "out": _ptr(path),
                "review_result": payload["review_result"],
                "selected_next_target": payload["selected_next_target"],
                "proof_attempt_executed": payload["proof_attempt_executed"],
                "theorem_discharged": payload["theorem_discharged"],
                "rule_promoted": payload["rule_promoted"],
                "lean_status_wording": payload["lean_status_wording"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

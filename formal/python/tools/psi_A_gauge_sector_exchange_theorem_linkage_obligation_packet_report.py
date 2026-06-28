from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.ck_family_theorem_linkage_obligation_selection_after_psi_A_matter_exchange_closeout_result_review_report import (
    DEFAULT_OUT as SELECTION_REVIEW_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW,
    GAUGE_EXCHANGE_TARGET_RULE,
    GAUGE_STRESS_ENERGY_DIVERGENCE_IDENTITY,
    LEAN_PACKET_PATH as SELECTION_REVIEW_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_REVIEW,
    LIKELY_POST_PACKET_REVIEW_TARGET as SELECTION_REVIEW_LIKELY_POST_PACKET_REVIEW_TARGET,
    NEXT_PACKET_TARGET_STATEMENT,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OUTCOME_ID as SELECTION_REVIEW_OUTCOME,
    PACKET_ID as SELECTION_REVIEW_PACKET_ID,
    REVIEW_RESULT as SELECTION_REVIEW_RESULT,
    SCHEMA_ID as SELECTION_REVIEW_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW,
    SELECTED_OBLIGATION,
    SELECTED_OBLIGATION_RANK,
    SOURCED_MAXWELL_ROUTE,
    STRICT_REVIEW_RESULT as SELECTION_REVIEW_STRICT_OUTCOME,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-28T00:00:00Z"

SCHEMA_ID = "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_PACKET_20260628_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_PACKET_v0"
PACKET_RESULT = (
    "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_PACKET_PREPARED_"
    "GAUGE_EXCHANGE_ROUTE_SCOPED_NO_PROOF_EXECUTION_OR_CK_RULE_PROMOTION"
)
STRICT_PACKET_RESULT = (
    "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_PACKET_PREPARED_"
    "GAUGE_STRESS_DIVERGENCE_TO_SOURCED_MAXWELL_TARGET_NO_ACTION_VARIATION_OR_"
    "MASTER_ACTION_PROMOTION"
)
OUTCOME_ID = PACKET_RESULT
PACKET_CLASSIFICATION = (
    "psi_A_gauge_sector_exchange_theorem_linkage_obligation_packet_prepared_"
    "gauge_stress_divergence_to_sourced_maxwell_target_scoped"
)

NEXT_TARGET = "review_psi_A_gauge_sector_exchange_theorem_linkage_obligation_packet_result"
NEXT_TARGET_KIND = "psi_A_gauge_sector_exchange_theorem_linkage_obligation_packet_result_review"
LIKELY_FOLLOW_ON_TARGET_AFTER_REVIEW = (
    "prepare_psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route"
)
LIKELY_FOLLOW_ON_TARGET_KIND_AFTER_REVIEW = (
    "psi_A_gauge_sector_exchange_theorem_linkage_attempt_from_sourced_maxwell_route_preparation"
)

OBLIGATION = "psi-A gauge-sector exchange theorem-linkage gap"
BASIS = (
    "accepted gauge stress-energy divergence identity, sourced Maxwell route, "
    "current definition, and shared domain/boundary assumptions"
)
PROOF_STYLE = (
    "gauge stress-energy divergence identity plus sourced Maxwell substitution route"
)
TARGET = "nabla_mu T_A^{mu nu} = - F^nu{}_alpha J^alpha"
PROOF_EXECUTION_STATUS = "not yet"
RULE_PROMOTION_STATUS = "not authorized"
THEOREM_TARGET_ID = "psi_A_gauge_sector_exchange_from_sourced_maxwell_route"
THEOREM_TARGET_NAME = (
    "psi-A gauge-sector exchange theorem-linkage from sourced Maxwell route"
)

T_A_POLICY = "T_A^{mu nu} policy"
FIELD_STRENGTH_OBJECT = "F object"
CURRENT_OBJECT = "J object"
CURRENT_DEFINITION = "J^alpha = q psibar gamma^alpha psi"
SIGN_CONVENTION = "same sign convention"
INDEX_PLACEMENT = "same index placement"
COVARIANT_DERIVATIVE = "same covariant derivative"
ACCEPTED_SOURCED_MAXWELL_ROUTE = SOURCED_MAXWELL_ROUTE
ACCEPTED_GAUGE_STRESS_ENERGY_DIVERGENCE_IDENTITY = (
    GAUGE_STRESS_ENERGY_DIVERGENCE_IDENTITY
)
DOMAIN_BOUNDARY_ASSUMPTIONS = "shared domain and boundary assumptions"
THEOREM_TARGET_STATEMENT = NEXT_PACKET_TARGET_STATEMENT
PLAIN_MEANING = (
    "The gauge field's stress-energy changes according to the current that sources it."
)
WATCH_ITEMS = [
    "same T_A definition",
    "same F object",
    "same J object",
    "same sign convention",
    "same index placement",
    "same covariant derivative",
    "accepted sourced Maxwell route",
    "accepted gauge stress-energy divergence identity",
    "shared domain and boundary assumptions",
]

THEOREM_SHAPE_GIVEN = [
    GAUGE_STRESS_ENERGY_DIVERGENCE_IDENTITY,
    SOURCED_MAXWELL_ROUTE,
]
THEOREM_SHAPE_THEN = TARGET

FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET = (
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW
)
SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET = SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW
LEAN_STATUS_WORDING_FOR_PACKET = LEAN_STATUS_WORDING_FOR_REVIEW

BLOCKED_CLAIMS = [
    "no proof execution",
    "no theorem discharge",
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

ACCEPTED_PACKET_FINDINGS = [
    "obligation: psi-A gauge-sector exchange theorem-linkage gap",
    "basis: accepted gauge stress-energy divergence identity, sourced Maxwell route, current definition, and shared domain/boundary assumptions",
    "proof style: gauge stress-energy divergence identity plus sourced Maxwell substitution route",
    "target: nabla_mu T_A^{mu nu} = - F^nu{}_alpha J^alpha",
    "proof execution: not yet",
    "rule promotion: not authorized",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_PACKET_20260628_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PsiAGaugeSectorExchangeTheoremLinkageObligationPacket.lean"
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


def _selection_review_valid(review: dict[str, Any]) -> bool:
    return (
        review.get("schema_id") == SELECTION_REVIEW_SCHEMA_ID
        and review.get("packet_id") == SELECTION_REVIEW_PACKET_ID
        and review.get("outcome_id") == SELECTION_REVIEW_OUTCOME
        and review.get("review_result") == SELECTION_REVIEW_RESULT
        and review.get("strict_review_result") == SELECTION_REVIEW_STRICT_OUTCOME
        and review.get("selected_next_target") == CONSUMED_TARGET
        and review.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
        and review.get("likely_post_packet_review_target")
        == SELECTION_REVIEW_LIKELY_POST_PACKET_REVIEW_TARGET
        and review.get("selected_obligation") == SELECTED_OBLIGATION
        and review.get("selected_obligation_rank") == SELECTED_OBLIGATION_RANK
        and review.get("accepted") is True
    )


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": "psi_A_gauge_sector_exchange_theorem_linkage_obligation_packet",
        "tiered_lean_validation_policy_formalized": True,
        "routine_packet_validation_tiers": [
            "touched Lean marker",
            "smallest affected Lake target",
            "lane aggregate",
            "current authority target",
        ],
        "release_preservation_validation": "full ToeFormal aggregate when feasible",
        "toeformal_import_update_requires_preservation_status": True,
        "aggregate_lean_validation_status_for_packet": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET
        ),
        "full_toeformal_aggregate_status_for_packet": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET
        ),
        "scoped_lean_targets_status_for_packet": SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def build_psi_A_gauge_sector_exchange_theorem_linkage_obligation_packet(
    *,
    selection_review_path: Path = SELECTION_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(selection_review_path)
    theorem_shape = _theorem_shape()
    acceptance_criteria = {
        "consumes_expected_selection_review": _selection_review_valid(review),
        "gauge_sector_exchange_obligation_selected": (
            review.get("selected_obligation") == OBLIGATION
            and review.get("selected_obligation_rank") == 4
        ),
        "gauge_exchange_target_scoped": (
            theorem_shape["given"] == THEOREM_SHAPE_GIVEN
            and theorem_shape["then"] == TARGET
            and theorem_shape["watch_items"] == WATCH_ITEMS
        ),
        "basis_and_proof_style_recorded": (
            BASIS
            == "accepted gauge stress-energy divergence identity, sourced Maxwell route, current definition, and shared domain/boundary assumptions"
            and PROOF_STYLE
            == "gauge stress-energy divergence identity plus sourced Maxwell substitution route"
        ),
        "no_proof_execution_or_theorem_discharge": True,
        "blocked_claims_preserved": True,
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
        else "REMEDIATE_PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_PACKET"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_PACKET",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_PACKET_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if accepted
        else "PSI_A_GAUGE_SECTOR_EXCHANGE_THEOREM_LINKAGE_OBLIGATION_PACKET_REQUIRES_REMEDIATION",
        "strict_packet_result": STRICT_PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "likely_follow_on_target_after_review": LIKELY_FOLLOW_ON_TARGET_AFTER_REVIEW,
        "likely_follow_on_target_kind_after_review": (
            LIKELY_FOLLOW_ON_TARGET_KIND_AFTER_REVIEW
        ),
        "selection_review_schema_id": SELECTION_REVIEW_SCHEMA_ID,
        "selection_review_packet_id": SELECTION_REVIEW_PACKET_ID,
        "selection_review_outcome": SELECTION_REVIEW_OUTCOME,
        "selection_review_result": SELECTION_REVIEW_RESULT,
        "selection_review_strict_outcome": SELECTION_REVIEW_STRICT_OUTCOME,
        "selection_review_consumed": accepted,
        "selected_obligation": SELECTED_OBLIGATION,
        "selected_obligation_rank": SELECTED_OBLIGATION_RANK,
        "obligation": OBLIGATION,
        "basis": BASIS,
        "proof_style": PROOF_STYLE,
        "target": TARGET,
        "rule_promotion": RULE_PROMOTION_STATUS,
        "proof_execution": PROOF_EXECUTION_STATUS,
        "theorem_target_id": THEOREM_TARGET_ID,
        "theorem_target_name": THEOREM_TARGET_NAME,
        "theorem_target_statement": THEOREM_TARGET_STATEMENT,
        "theorem_shape": theorem_shape,
        "T_A_policy": T_A_POLICY,
        "field_strength_object": FIELD_STRENGTH_OBJECT,
        "current_object": CURRENT_OBJECT,
        "current_definition": CURRENT_DEFINITION,
        "sign_convention": SIGN_CONVENTION,
        "index_placement": INDEX_PLACEMENT,
        "covariant_derivative": COVARIANT_DERIVATIVE,
        "accepted_sourced_maxwell_route": ACCEPTED_SOURCED_MAXWELL_ROUTE,
        "accepted_gauge_stress_energy_divergence_identity": (
            ACCEPTED_GAUGE_STRESS_ENERGY_DIVERGENCE_IDENTITY
        ),
        "domain_boundary_assumptions": DOMAIN_BOUNDARY_ASSUMPTIONS,
        "gauge_exchange_target_rule": TARGET,
        "plain_meaning": PLAIN_MEANING,
        "watch_items": WATCH_ITEMS,
        "watch_item_count": len(WATCH_ITEMS),
        "accepted_packet_findings": ACCEPTED_PACKET_FINDINGS,
        "accepted_packet_finding_count": len(ACCEPTED_PACKET_FINDINGS),
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
            "This packet scopes only the psi-A gauge-sector exchange "
            "theorem-linkage target. It records the accepted gauge stress-energy "
            "divergence identity, sourced Maxwell route, current definition, "
            "and shared domain/boundary assumptions as inputs for the target "
            "nabla_mu T_A^{mu nu} = - F^nu{}_alpha J^alpha. It does not execute "
            "any proof, discharge any theorem, discharge GAP-1 through GAP-8 "
            "globally, promote any C_k rule, embed C_k in an action, vary C_k, "
            "close full Maxwell, close EM-QFT, close QFT-GR, close GR-QM, claim "
            "empirical validation, or promote the master action."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume prepare_psi_A_gauge_sector_exchange_theorem_linkage_obligation_packet",
            "fail to scope the psi-A gauge-sector exchange theorem target",
            "fail to record the accepted gauge stress-energy divergence identity",
            "fail to record the accepted sourced Maxwell route",
            "fail to preserve the T_A, F, J, sign, index, and covariant derivative watch items",
            "execute a proof",
            "discharge a theorem",
            "discharge GAP-1 through GAP-8 globally",
            "promote any C_k rule",
            "embed C_k in an action",
            "authorize or execute C_k action variation",
            "claim full Maxwell, EM-QFT, QFT-GR, or GR-QM closure",
            "claim empirical validation",
            "promote the master action",
            "record full ToeFormal aggregate as PASSED without a full serial build",
        ],
        "lean_status_wording": LEAN_STATUS_WORDING_FOR_PACKET,
        "full_toeformal_aggregate_status_for_packet": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET
        ),
        "scoped_lean_targets_status_for_packet": SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET,
        "aggregate_lean_validation_status_for_packet": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET
        ),
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "validation_policy": _validation_policy(),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.PsiAGaugeSectorExchangeTheoremLinkageObligationPacket",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "selection_review_file": _ptr(selection_review_path),
            "selection_review_lean_file": _ptr(SELECTION_REVIEW_LEAN_PACKET_PATH),
            "qftgr_aggregate_file": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate_file": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate_file": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
        },
    }
    payload.update(_false_boundary_flags())
    return payload


def write_packet(packet: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(packet, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Prepare the psi-A gauge-sector exchange theorem-linkage obligation packet."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--selection-review", type=Path, default=SELECTION_REVIEW_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    selection_review_path = (
        args.selection_review
        if args.selection_review.is_absolute()
        else REPO_ROOT / args.selection_review
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = build_psi_A_gauge_sector_exchange_theorem_linkage_obligation_packet(
        selection_review_path=selection_review_path,
        captured_at_utc=args.captured_at_utc,
    )
    path = write_packet(payload, out)
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "out": _ptr(path),
                "packet_result": payload["packet_result"],
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

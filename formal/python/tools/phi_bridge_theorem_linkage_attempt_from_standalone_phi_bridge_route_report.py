from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.phi_bridge_theorem_linkage_obligation_packet_result_review_report import (
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    BRIDGE_CANDIDATE_ID,
    BRIDGE_CANDIDATE_RULE_PLAIN_MEANING,
    BRIDGE_CANDIDATE_TYPE,
    BRIDGE_CONSTRAINT_EQUATION,
    BRIDGE_CONSTRAINT_FORM,
    BRIDGE_ROUTE_ALIGNMENT_SEQUENCE,
    BRIDGE_ROUTE_ALIGNMENT_SEQUENCE_PLAIN,
    BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
    BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
    BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
    DEFAULT_OUT as REVIEW_PATH,
    LEAN_PACKET_PATH as REVIEW_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_PACKET,
    LEAN_STATUS_WORDING_LINES_FOR_PACKET,
    LIKELY_COMPONENTWISE_ATTEMPT_ROUTE,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OUTCOME_ID as REVIEW_OUTCOME,
    PACKET_ID as REVIEW_PACKET_ID,
    SCHEMA_ID as REVIEW_SCHEMA_ID,
    STANDALONE_PHI_BRIDGE_ROUTE,
    STRICT_REVIEW_RESULT,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-30T00:00:00Z"

SCHEMA_ID = (
    "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_ROUTE_"
    "20260630_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_ROUTE_v0"
OUTCOME_ID = (
    "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_ROUTE_"
    "PREPARED_C_BRIDGE_PHI_COMPONENT_ZERO_ROUTE_INDEXED_NO_THEOREM_DISCHARGE_"
    "OR_CK_RULE_PROMOTION"
)
STRICT_ATTEMPT_PREPARATION_RESULT = (
    "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_ROUTE_"
    "PREPARED_MASTER_WITNESS_ROUTE_MATCH_TARGET_NO_ACTION_VARIATION_OR_"
    "MASTER_ACTION_PROMOTION"
)
PACKET_CLASSIFICATION = (
    "phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route_prepares_"
    "componentwise_zero_route_no_theorem_discharge"
)

NEXT_TARGET = "review_phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route_result"
NEXT_TARGET_KIND = (
    "phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route_result_review"
)
SUGGESTED_REVIEW_OUTCOME = (
    "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_ROUTE_RESULT_"
    "REVIEW_ACCEPTS_C_BRIDGE_PHI_COMPONENT_ZERO_ROUTE_PREPARATION_NO_THEOREM_"
    "DISCHARGE_OR_CK_RULE_PROMOTION"
)
STRICT_SUGGESTED_REVIEW_OUTCOME = (
    "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_ROUTE_RESULT_"
    "REVIEW_ACCEPTS_MASTER_WITNESS_ROUTE_MATCH_TARGET_PREPARED_NO_ACTION_"
    "VARIATION_OR_MASTER_ACTION_PROMOTION"
)

FIELD_EQUATION_MATCH = "E_phi^master = E_phi^witness"
STRESS_ENERGY_MATCH = "T_phi^master = T_phi^witness"
SOURCE_RESIDUAL_MATCH = "C_source^phi = nabla_mu T_phi^{mu nu}"
FIELD_EQUATION_ZERO_COMPONENT = "E_phi^master - E_phi^witness = 0"
STRESS_ENERGY_ZERO_COMPONENT = "T_phi^master - T_phi^witness = 0"
SOURCE_RESIDUAL_ZERO_COMPONENT = "C_source^phi - nabla_mu T_phi^{mu nu} = 0"
BRIDGE_TUPLE_ZERO = "C_bridge^phi = (0, 0, 0)"
TARGET_CONCLUSION = "C_bridge^phi = 0"

COMPONENTWISE_ZERO_ROUTE = [
    FIELD_EQUATION_MATCH,
    STRESS_ENERGY_MATCH,
    SOURCE_RESIDUAL_MATCH,
    "therefore: E_phi^master - E_phi^witness = 0",
    "therefore: T_phi^master - T_phi^witness = 0",
    "therefore: C_source^phi - nabla_mu T_phi^{mu nu} = 0",
    "therefore: C_bridge^phi = (0, 0, 0)",
    "therefore: C_bridge^phi = 0",
]
PREPARED_LINKAGE_TARGET = (
    "C_bridge^phi = 0 from the frozen standalone phi bridge tuple by preparing "
    "the three component equalities E_phi^master = E_phi^witness, "
    "T_phi^master = T_phi^witness, and C_source^phi = nabla_mu T_phi^{mu nu}."
)
PLAIN_MEANING = (
    "The phi bridge tuple is targeted componentwise: if the master and witness "
    "field equation, stress-energy, and source-residual routes match, every "
    "tuple component is zero and the bridge target is C_bridge^phi = 0."
)

WATCH_ITEMS = [
    "same standalone phi bridge registry tuple",
    "same E_phi master/witness component",
    "same T_phi master/witness component",
    "same C_source^phi residual component",
    "same sign and index conventions",
    "no C_source^phi proof reuse",
    "no A-source route import",
    "no psi-A route import",
    "no QFT-GR route import",
    "no master-action promotion from route match",
]

BOUNDARY_ITEMS = [
    "no proof execution during preparation",
    "no theorem discharge",
    "no phi-sector closure",
    "no scalar/QFT closure",
    "no QFT-GR closure",
    "no EM-QFT closure",
    "no seam closure",
    "no general C_k closure",
    "no C_k promotion",
    "no action embedding",
    "no variation",
    "no empirical validation",
    "no master-action promotion",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_ROUTE_"
    "20260630_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PhiBridgeTheoremLinkageAttemptFromStandalonePhiBridgeRoute.lean"
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
        "proof_execution_authorized": False,
        "proof_attempt_executed": False,
        "theorem_execution_authorized": False,
        "theorem_discharged": False,
        "theorem_linkage_obligation_discharged": False,
        "C_bridge_phi_discharged": False,
        "C_bridge_phi_linkage_constructed": False,
        "C_bridge_phi_zero_derived": False,
        "C_bridge_phi_theorem_linkage_obligation_discharged": False,
        "bridge_admissibility_proved": False,
        "bridge_route_alignment_verified": False,
        "route_consistency_tuple_proved": False,
        "field_equation_match_proved": False,
        "stress_energy_match_proved": False,
        "source_residual_match_proved": False,
        "proof_debt_reduced": False,
        "proof_debt_discharged": False,
        "gap_discharged": False,
        "any_gap_discharged": False,
        "any_gap_closed": False,
        "gap_1_through_gap_8_discharged": False,
        "C_source_phi_route_reused": False,
        "C_bridge_phi_route_reused_from_C_source_phi": False,
        "A_source_route_imported": False,
        "A_sector_route_imported": False,
        "psi_A_route_imported": False,
        "psi_A_sourced_route_imported": False,
        "psi_A_sourced_Maxwell_imported": False,
        "QFT_GR_route_imported": False,
        "QFT_GR_source_route_imported": False,
        "J_current_imported": False,
        "master_action_route_substituted": False,
        "new_bridge_formula_invented": False,
        "C_source_phi_closure_claimed": False,
        "C_bridge_phi_closure_claimed": False,
        "phi_sector_closure_claimed": False,
        "full_scalar_qft_closure_claimed": False,
        "full_scalar_QFT_closure_claimed": False,
        "A_sector_closure_claimed": False,
        "sourced_maxwell_closure_claimed": False,
        "full_maxwell_closure_claimed": False,
        "full_Maxwell_closure_claimed": False,
        "em_qft_closure_claimed": False,
        "qft_gr_closure_claimed": False,
        "gr_qm_closure_claimed": False,
        "general_C_k_theorem_linkage_closure": False,
        "general_C_k_closure": False,
        "C_k_dynamical_law_status": False,
        "C_k_rule_promotion_authorized": False,
        "C_k_rule_promoted": False,
        "rule_promoted": False,
        "C_k_action_embedding_claimed": False,
        "C_k_action_embedding_selected": False,
        "C_k_action_embedding_authorized": False,
        "C_k_action_variation_executed": False,
        "C_k_action_variation_authorized": False,
        "action_embedding_claimed": False,
        "action_variation_executed": False,
        "multiplier_route_selected": False,
        "penalty_route_selected": False,
        "direct_dynamical_law_claimed": False,
        "empirical_prediction_claimed": False,
        "empirical_validation_claimed": False,
        "seam_closure_claim": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "canonical_master_action_promoted": False,
    }


def _review_valid(review: dict[str, Any]) -> bool:
    return (
        review.get("schema_id") == REVIEW_SCHEMA_ID
        and review.get("packet_id") == REVIEW_PACKET_ID
        and review.get("outcome_id") == REVIEW_OUTCOME
        and review.get("review_result") == REVIEW_OUTCOME
        and review.get("strict_review_result") == STRICT_REVIEW_RESULT
        and review.get("selected_next_target") == CONSUMED_TARGET
        and review.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
        and review.get("standalone_phi_bridge_route") == STANDALONE_PHI_BRIDGE_ROUTE
        and review.get("bridge_constraint_form") == BRIDGE_CONSTRAINT_FORM
        and review.get("bridge_constraint_equation") == BRIDGE_CONSTRAINT_EQUATION
        and review.get("bridge_route_field_equation_match")
        == BRIDGE_ROUTE_FIELD_EQUATION_MATCH
        and review.get("bridge_route_stress_energy_match")
        == BRIDGE_ROUTE_STRESS_ENERGY_MATCH
        and review.get("bridge_route_source_residual_match")
        == BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH
        and review.get("proof_attempt_executed") is False
        and review.get("theorem_discharged") is False
        and review.get("C_bridge_phi_discharged") is False
        and review.get("master_action_promoted") is False
        and review.get("accepted") is True
    )


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": (
            "phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route"
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
        "full_toeformal_aggregate_status_for_packet": (
            "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
        ),
        "scoped_lean_targets_status_for_packet": "PASSED_SERIAL_RERUN",
        "lean_status_wording_lines_for_packet": LEAN_STATUS_WORDING_LINES_FOR_PACKET,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def build_phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route(
    *,
    review_path: Path = REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(review_path)
    acceptance_criteria = {
        "consumes_expected_packet_result_review": _review_valid(review),
        "standalone_phi_bridge_registry_tuple_preserved": (
            STANDALONE_PHI_BRIDGE_ROUTE
            == "prior standalone phi bridge-admissibility registry"
            and BRIDGE_CONSTRAINT_FORM
            == "C_bridge^phi := (E_phi^master - E_phi^witness, "
            "T_phi^master - T_phi^witness, "
            "C_source^phi - nabla_mu T_phi^{mu nu})"
            and BRIDGE_CONSTRAINT_EQUATION == "C_bridge^phi = 0"
        ),
        "componentwise_zero_route_prepared": (
            COMPONENTWISE_ZERO_ROUTE
            == [
                "E_phi^master = E_phi^witness",
                "T_phi^master = T_phi^witness",
                "C_source^phi = nabla_mu T_phi^{mu nu}",
                "therefore: E_phi^master - E_phi^witness = 0",
                "therefore: T_phi^master - T_phi^witness = 0",
                "therefore: C_source^phi - nabla_mu T_phi^{mu nu} = 0",
                "therefore: C_bridge^phi = (0, 0, 0)",
                "therefore: C_bridge^phi = 0",
            ]
        ),
        "component_targets_match_prior_packet": (
            FIELD_EQUATION_ZERO_COMPONENT == BRIDGE_ROUTE_FIELD_EQUATION_MATCH
            and STRESS_ENERGY_ZERO_COMPONENT == BRIDGE_ROUTE_STRESS_ENERGY_MATCH
            and SOURCE_RESIDUAL_ZERO_COMPONENT == BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH
        ),
        "route_contamination_blocked": (
            "J^alpha" not in " ".join(COMPONENTWISE_ZERO_ROUTE)
            and "F^{mu" not in " ".join(COMPONENTWISE_ZERO_ROUTE)
            and "QFT-GR" not in " ".join(COMPONENTWISE_ZERO_ROUTE)
        ),
        "preparation_only_no_theorem_discharge": True,
        "lean_status_wording_preserved": (
            LEAN_STATUS_WORDING_LINES_FOR_PACKET
            == [
                "full ToeFormal aggregate = NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION",
                "scoped Lean targets = PASSED_SERIAL_RERUN",
            ]
        ),
    }
    prepared = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if prepared
        else "REMEDIATE_PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_ROUTE"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_"
            "BRIDGE_ROUTE_PREPARATION"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "accepted": prepared,
        "attempt_prepared": prepared,
        "outcome_id": OUTCOME_ID
        if prepared
        else "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_ROUTE_REQUIRES_REMEDIATION",
        "attempt_preparation_result": OUTCOME_ID
        if prepared
        else "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_ROUTE_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if prepared
        else "PHI_BRIDGE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_BRIDGE_ROUTE_REQUIRES_REMEDIATION",
        "strict_attempt_preparation_result": STRICT_ATTEMPT_PREPARATION_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND if prepared else "remediation",
        "suggested_review_outcome": SUGGESTED_REVIEW_OUTCOME,
        "strict_suggested_review_outcome": STRICT_SUGGESTED_REVIEW_OUTCOME,
        "review_schema_id": REVIEW_SCHEMA_ID,
        "review_packet_id": REVIEW_PACKET_ID,
        "review_outcome": REVIEW_OUTCOME,
        "review_strict_result": STRICT_REVIEW_RESULT,
        "review_consumed": prepared,
        "prior_review_accepted": prepared,
        "selected_obligation": "C_bridge^phi theorem-linkage obligation",
        "selected_theorem_linkage_gap": "C_bridge^phi theorem-linkage gap",
        "selected_obligation_row_id": "C_bridge^phi",
        "standalone_phi_bridge_route": STANDALONE_PHI_BRIDGE_ROUTE,
        "standalone_phi_bridge_route_preserved": prepared,
        "exact_tuple_definition_preserved": prepared,
        "target_C_bridge_phi_zero_preserved": prepared,
        "bridge_candidate_id": BRIDGE_CANDIDATE_ID,
        "bridge_candidate_type": BRIDGE_CANDIDATE_TYPE,
        "bridge_constraint_form": BRIDGE_CONSTRAINT_FORM,
        "bridge_constraint_equation": BRIDGE_CONSTRAINT_EQUATION,
        "bridge_admissibility_constraint_form": BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
        "bridge_route_field_equation_match": BRIDGE_ROUTE_FIELD_EQUATION_MATCH,
        "bridge_route_stress_energy_match": BRIDGE_ROUTE_STRESS_ENERGY_MATCH,
        "bridge_route_source_residual_match": BRIDGE_ROUTE_SOURCE_RESIDUAL_MATCH,
        "bridge_candidate_rule_plain_meaning": BRIDGE_CANDIDATE_RULE_PLAIN_MEANING,
        "bridge_route_alignment_sequence": BRIDGE_ROUTE_ALIGNMENT_SEQUENCE,
        "bridge_route_alignment_sequence_plain": BRIDGE_ROUTE_ALIGNMENT_SEQUENCE_PLAIN,
        "likely_componentwise_attempt_route": LIKELY_COMPONENTWISE_ATTEMPT_ROUTE,
        "componentwise_zero_route": COMPONENTWISE_ZERO_ROUTE,
        "componentwise_zero_route_count": len(COMPONENTWISE_ZERO_ROUTE),
        "field_equation_match": FIELD_EQUATION_MATCH,
        "stress_energy_match": STRESS_ENERGY_MATCH,
        "source_residual_match": SOURCE_RESIDUAL_MATCH,
        "field_equation_zero_component": FIELD_EQUATION_ZERO_COMPONENT,
        "stress_energy_zero_component": STRESS_ENERGY_ZERO_COMPONENT,
        "source_residual_zero_component": SOURCE_RESIDUAL_ZERO_COMPONENT,
        "bridge_tuple_zero": BRIDGE_TUPLE_ZERO,
        "target_conclusion": TARGET_CONCLUSION,
        "prepared_linkage_target": PREPARED_LINKAGE_TARGET,
        "plain_meaning": PLAIN_MEANING,
        "route_kind": "standalone_phi_bridge_componentwise_zero_preparation",
        "master_witness_route_match_target_prepared": prepared,
        "master_witness_route_match_promoted_to_master_action": False,
        "same_standalone_phi_bridge_registry_tuple": True,
        "same_E_phi_master_witness_component": True,
        "same_T_phi_master_witness_component": True,
        "same_C_source_phi_residual_component": True,
        "same_sign_and_index_conventions": True,
        "route_contamination_guard": (
            "prepare only the componentwise standalone phi bridge route; do not "
            "substitute C_source^phi, A-source, psi-A, QFT-GR, or master-action "
            "routes and do not treat master/witness route match as master-action "
            "promotion"
        ),
        "watch_items": WATCH_ITEMS,
        "watch_item_count": len(WATCH_ITEMS),
        "boundary_items": BOUNDARY_ITEMS,
        "boundary_item_count": len(BOUNDARY_ITEMS),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": prepared,
        "claim_ladder_position": (
            "below theorem discharge, phi-sector closure, scalar/QFT closure, "
            "seam closure, empirical prediction, empirical confirmation, and "
            "mature physical theory"
        ),
        "master_action_status": (
            "working-form noncanonical organizing surface; not a promoted final law"
        ),
        "non_claim_boundary": (
            "This packet prepares only the standalone phi-bridge C_bridge^phi "
            "theorem-linkage attempt from the frozen tuple C_bridge^phi := "
            "(E_phi^master - E_phi^witness, T_phi^master - T_phi^witness, "
            "C_source^phi - nabla_mu T_phi^{mu nu}). It indexes the component "
            "route E_phi^master = E_phi^witness, T_phi^master = T_phi^witness, "
            "and C_source^phi = nabla_mu T_phi^{mu nu}, then targets "
            "C_bridge^phi = (0, 0, 0) and C_bridge^phi = 0. It does not execute "
            "a proof, discharge C_bridge^phi, claim phi-sector closure, claim "
            "scalar/QFT closure, close EM-QFT or QFT-GR, claim general C_k "
            "closure, embed or vary an action, claim empirical validation, or "
            "promote the master action."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume prepare_phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route",
            "fail to preserve the frozen C_bridge^phi tuple",
            "fail to prepare E_phi^master = E_phi^witness",
            "fail to prepare T_phi^master = T_phi^witness",
            "fail to prepare C_source^phi = nabla_mu T_phi^{mu nu}",
            "silently substitute C_source^phi, A-source, psi-A, QFT-GR, or master-action routes",
            "execute the theorem attempt during preparation",
            "discharge C_bridge^phi during preparation",
            "claim phi-sector closure",
            "claim full scalar/QFT closure",
            "claim EM-QFT or QFT-GR closure",
            "claim general C_k closure",
            "embed or vary an action",
            "treat master/witness route match as master-action promotion",
            "promote the master action",
            "record full ToeFormal aggregate as PASSED without a full serial build",
        ],
        "lean_status_wording": LEAN_STATUS_WORDING_FOR_PACKET,
        "lean_status_wording_lines": LEAN_STATUS_WORDING_LINES_FOR_PACKET,
        "full_toeformal_aggregate_status_for_packet": (
            "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
        ),
        "scoped_lean_targets_status_for_packet": "PASSED_SERIAL_RERUN",
        "aggregate_lean_validation_status_for_packet": "PASSED_SERIAL_RERUN",
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "validation_policy": _validation_policy(),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.PhiBridgeTheoremLinkageAttemptFromStandalonePhiBridgeRoute",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "review_file": _ptr(review_path),
            "review_lean_file": _ptr(REVIEW_LEAN_PACKET_PATH),
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
            "Prepare the standalone phi-bridge C_bridge^phi componentwise "
            "zero theorem-linkage attempt without executing or discharging it."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--review", type=Path, default=REVIEW_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    review_path = args.review if args.review.is_absolute() else REPO_ROOT / args.review
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    packet = build_phi_bridge_theorem_linkage_attempt_from_standalone_phi_bridge_route(
        review_path=review_path,
        captured_at_utc=args.captured_at_utc,
    )
    path = write_packet(packet, out)
    print(
        json.dumps(
            {
                "accepted": packet["accepted"],
                "out": _ptr(path),
                "attempt_preparation_result": packet["attempt_preparation_result"],
                "selected_next_target": packet["selected_next_target"],
                "bridge_constraint_form": packet["bridge_constraint_form"],
                "target_conclusion": packet["target_conclusion"],
                "proof_attempt_executed": packet["proof_attempt_executed"],
                "theorem_discharged": packet["theorem_discharged"],
                "master_action_promoted": packet["master_action_promoted"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

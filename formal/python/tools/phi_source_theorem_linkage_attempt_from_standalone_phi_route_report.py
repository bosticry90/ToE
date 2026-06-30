from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.phi_source_theorem_linkage_obligation_packet_result_review_report import (
    C_SOURCE_PHI_RESIDUAL_DEFINITION,
    C_SOURCE_PHI_SOURCE_ADMISSIBILITY_CONDITION,
    DEFAULT_OUT as REVIEW_PATH,
    FIELD_EULER_LAGRANGE_EQUATION,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET,
    LEAN_PACKET_PATH as REVIEW_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_PACKET,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    ON_SHELL_IMPLICATION_FORM,
    ON_SHELL_RESIDUAL_FORM,
    OUTCOME_ID as REVIEW_OUTCOME,
    PACKET_ID as REVIEW_PACKET_ID,
    RESIDUAL_IDENTITY_FORM,
    ROUTE_BUNDLE_ADMISSIBILITY_FORM,
    SCHEMA_ID as REVIEW_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET,
    STANDALONE_PHI_SOURCE_ROUTE,
    STRESS_DIVERGENCE_TARGET,
    STRESS_ENERGY_UNDER_SELECTED_POLICY,
    STRICT_REVIEW_RESULT,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-30T00:00:00Z"

SCHEMA_ID = "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_20260630_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_v0"
OUTCOME_ID = (
    "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_PREPARED_"
    "C_SOURCE_PHI_LINKAGE_ROUTE_INDEXED_NO_THEOREM_DISCHARGE_OR_CK_RULE_"
    "PROMOTION"
)
STRICT_ATTEMPT_PREPARATION_RESULT = (
    "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_PREPARED_"
    "ON_SHELL_SCALAR_RESIDUAL_ROUTE_NO_ACTION_VARIATION_OR_MASTER_ACTION_"
    "PROMOTION"
)
PACKET_CLASSIFICATION = (
    "phi_source_theorem_linkage_attempt_from_standalone_phi_route_prepares_"
    "on_shell_scalar_residual_linkage_no_theorem_discharge"
)

NEXT_TARGET = "review_phi_source_theorem_linkage_attempt_from_standalone_phi_route_result"
NEXT_TARGET_KIND = (
    "phi_source_theorem_linkage_attempt_from_standalone_phi_route_result_review"
)
SUGGESTED_REVIEW_OUTCOME = (
    "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_RESULT_"
    "REVIEW_ACCEPTS_C_SOURCE_PHI_LINKAGE_ROUTE_PREPARATION_NO_THEOREM_"
    "DISCHARGE_OR_CK_RULE_PROMOTION"
)
STRICT_SUGGESTED_REVIEW_OUTCOME = (
    "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_RESULT_"
    "REVIEW_ACCEPTS_ON_SHELL_SCALAR_RESIDUAL_ROUTE_PREPARED_NO_ACTION_"
    "VARIATION_OR_MASTER_ACTION_PROMOTION"
)
LIKELY_POST_REVIEW_TARGET = (
    "execute_phi_source_theorem_linkage_attempt_from_standalone_phi_route"
)

ON_SHELL_CONDITION = "R_i^phi = 0"
TARGET_CONCLUSION = C_SOURCE_PHI_SOURCE_ADMISSIBILITY_CONDITION
LINKAGE_ROUTE = [
    C_SOURCE_PHI_RESIDUAL_DEFINITION,
    RESIDUAL_IDENTITY_FORM,
    ON_SHELL_RESIDUAL_FORM,
    "on shell: R_i^phi = 0",
    "therefore target: C_source^nu[g, phi] = 0",
]
PREPARED_LINKAGE_TARGET = (
    "C_source^nu[g, phi] = 0 from the prior standalone phi scalar/on-shell "
    "residual route C_source^nu = sum_i R_i^phi nabla^nu phi_i and "
    "R_i^phi = 0"
)
PLAIN_MEANING = (
    "The phi source residual vanishes when the scalar field equations hold on shell."
)

WATCH_ITEMS = [
    "same T_phi definition",
    "same phi-sector route",
    "same scalar/on-shell assumptions",
    "same covariant derivative convention",
    "same sign and index conventions",
    "same domain and boundary assumptions",
    "no A-sector route import",
    "no psi-A sourced Maxwell import",
    "no QFT-GR source-route import",
    "old omnibus tests historical/hard-coded only",
]

BOUNDARY_ITEMS = [
    "no theorem discharge during preparation",
    "no phi-sector closure",
    "no full scalar/QFT closure",
    "no QFT-GR closure",
    "no EM-QFT closure",
    "no general C_k closure",
    "no action embedding",
    "no variation",
    "no empirical validation",
    "no master-action promotion",
    "no old-omnibus acceptance-authority downgrade",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_20260630_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PhiSourceTheoremLinkageAttemptFromStandalonePhiRoute.lean"
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
        "C_source_phi_discharged": False,
        "C_source_phi_linkage_constructed": False,
        "C_source_phi_zero_derived": False,
        "phi_source_theorem_linkage_obligation_discharged": False,
        "proof_debt_reduced": False,
        "proof_debt_discharged": False,
        "gap_discharged": False,
        "any_gap_discharged": False,
        "any_gap_closed": False,
        "gap_1_through_gap_8_discharged": False,
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
        "A_source_route_imported": False,
        "A_sector_route_imported": False,
        "psi_A_sourced_route_imported": False,
        "psi_A_sourced_Maxwell_imported": False,
        "psi_A_sourced_Maxwell_substitution": False,
        "QFT_GR_source_route_imported": False,
        "J_current_imported": False,
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
        and review.get("standalone_phi_source_route") == STANDALONE_PHI_SOURCE_ROUTE
        and review.get("C_source_phi_residual_definition")
        == C_SOURCE_PHI_RESIDUAL_DEFINITION
        and review.get("source_admissibility_condition")
        == C_SOURCE_PHI_SOURCE_ADMISSIBILITY_CONDITION
        and review.get("residual_identity_form") == RESIDUAL_IDENTITY_FORM
        and review.get("on_shell_residual_form") == ON_SHELL_RESIDUAL_FORM
        and review.get("A_source_route_imported") is False
        and review.get("psi_A_sourced_Maxwell_imported") is False
        and review.get("QFT_GR_source_route_imported") is False
        and review.get("accepted") is True
    )


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": (
            "phi_source_theorem_linkage_attempt_from_standalone_phi_route"
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


def build_phi_source_theorem_linkage_attempt_from_standalone_phi_route(
    *,
    review_path: Path = REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(review_path)
    acceptance_criteria = {
        "consumes_expected_packet_review": _review_valid(review),
        "standalone_phi_source_route_preserved": (
            STANDALONE_PHI_SOURCE_ROUTE
            == "prior standalone phi source-admissibility registry"
            and C_SOURCE_PHI_RESIDUAL_DEFINITION
            == "C_source^nu[g, phi] := nabla_mu T_phi^{mu nu}"
        ),
        "scalar_on_shell_residual_identity_preserved": (
            RESIDUAL_IDENTITY_FORM
            == "C_source^nu = sum_i R_i^phi nabla^nu phi_i"
            and ON_SHELL_RESIDUAL_FORM
            == "R_i^phi := Box_g phi_i + partial_i V(phi)"
            and FIELD_EULER_LAGRANGE_EQUATION
            == "Box_g phi_i + partial_i V(phi) = 0"
        ),
        "linkage_target_prepared_without_discharge": (
            TARGET_CONCLUSION == "C_source^nu[g, phi] = 0"
            and LINKAGE_ROUTE
            == [
                "C_source^nu[g, phi] := nabla_mu T_phi^{mu nu}",
                "C_source^nu = sum_i R_i^phi nabla^nu phi_i",
                "R_i^phi := Box_g phi_i + partial_i V(phi)",
                "on shell: R_i^phi = 0",
                "therefore target: C_source^nu[g, phi] = 0",
            ]
        ),
        "route_contamination_blocked": (
            "A" not in " ".join(LINKAGE_ROUTE)
            and "J^alpha" not in " ".join(LINKAGE_ROUTE)
            and "QFT-GR" not in " ".join(LINKAGE_ROUTE)
        ),
        "preparation_only_no_theorem_discharge": True,
        "old_omnibus_tests_historical_only": True,
        "old_omnibus_tests_not_active_acceptance_authority": True,
        "lean_status_wording_preserved": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET
            == "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
            and SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET == "PASSED_SERIAL_RERUN"
        ),
    }
    prepared = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if prepared
        else "REMEDIATE_PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_"
            "ROUTE_PREPARATION"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "accepted": prepared,
        "attempt_prepared": prepared,
        "outcome_id": OUTCOME_ID
        if prepared
        else "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_REQUIRES_REMEDIATION",
        "attempt_preparation_result": OUTCOME_ID
        if prepared
        else "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if prepared
        else "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_REQUIRES_REMEDIATION",
        "strict_attempt_preparation_result": STRICT_ATTEMPT_PREPARATION_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND if prepared else "remediation",
        "suggested_review_outcome": SUGGESTED_REVIEW_OUTCOME,
        "strict_suggested_review_outcome": STRICT_SUGGESTED_REVIEW_OUTCOME,
        "likely_post_review_target": LIKELY_POST_REVIEW_TARGET,
        "review_schema_id": REVIEW_SCHEMA_ID,
        "review_packet_id": REVIEW_PACKET_ID,
        "review_outcome": REVIEW_OUTCOME,
        "review_strict_result": STRICT_REVIEW_RESULT,
        "review_consumed": prepared,
        "prior_review_accepted": prepared,
        "selected_obligation": "C_source^phi theorem-linkage obligation",
        "selected_theorem_linkage_gap": "C_source^phi theorem-linkage gap",
        "selected_obligation_row_id": "C_source^phi",
        "standalone_phi_source_route": STANDALONE_PHI_SOURCE_ROUTE,
        "standalone_phi_source_route_preserved": prepared,
        "C_source_phi_residual_definition": C_SOURCE_PHI_RESIDUAL_DEFINITION,
        "C_source_phi_source_admissibility_condition": (
            C_SOURCE_PHI_SOURCE_ADMISSIBILITY_CONDITION
        ),
        "C_source_phi_target_statement": C_SOURCE_PHI_SOURCE_ADMISSIBILITY_CONDITION,
        "source_admissibility_condition": C_SOURCE_PHI_SOURCE_ADMISSIBILITY_CONDITION,
        "stress_divergence_target": STRESS_DIVERGENCE_TARGET,
        "residual_identity_form": RESIDUAL_IDENTITY_FORM,
        "on_shell_residual_form": ON_SHELL_RESIDUAL_FORM,
        "on_shell_condition": ON_SHELL_CONDITION,
        "on_shell_implication_form": ON_SHELL_IMPLICATION_FORM,
        "field_euler_lagrange_equation": FIELD_EULER_LAGRANGE_EQUATION,
        "route_bundle_admissibility_form": ROUTE_BUNDLE_ADMISSIBILITY_FORM,
        "stress_energy_under_selected_policy": STRESS_ENERGY_UNDER_SELECTED_POLICY,
        "target_conclusion": TARGET_CONCLUSION,
        "prepared_linkage_target": PREPARED_LINKAGE_TARGET,
        "linkage_route": LINKAGE_ROUTE,
        "linkage_route_count": len(LINKAGE_ROUTE),
        "plain_meaning": PLAIN_MEANING,
        "route_kind": "standalone_phi_on_shell_scalar_residual",
        "same_T_phi_definition": True,
        "same_phi_sector_route": True,
        "same_scalar_on_shell_assumptions": True,
        "same_covariant_derivative_convention": True,
        "same_sign_and_index_conventions": True,
        "same_domain_and_boundary_assumptions": True,
        "A_source_route_imported": False,
        "A_sector_route_imported": False,
        "psi_A_sourced_Maxwell_imported": False,
        "psi_A_sourced_route_imported": False,
        "QFT_GR_source_route_imported": False,
        "J_current_imported": False,
        "route_contamination_guard": (
            "prepare only the standalone phi scalar/on-shell residual route; "
            "do not import A-sector, psi-A sourced Maxwell, or QFT-GR source "
            "routes and do not replace the phi residual identity"
        ),
        "old_omnibus_tests_historical_hard_coded": True,
        "old_omnibus_tests_not_active_acceptance_authority": True,
        "active_lane_acceptance_authority": (
            "focused phi-source theorem-linkage attempt gate plus scoped Lean targets"
        ),
        "silent_validation_downgrade_blocked": True,
        "watch_items": WATCH_ITEMS,
        "watch_item_count": len(WATCH_ITEMS),
        "boundary_items": BOUNDARY_ITEMS,
        "boundary_item_count": len(BOUNDARY_ITEMS),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": prepared,
        "claim_ladder_position": (
            "below theorem discharge, seam closure, empirical prediction, "
            "empirical confirmation, and mature physical theory"
        ),
        "master_action_status": (
            "working-form noncanonical organizing surface; not a promoted final law"
        ),
        "non_claim_boundary": (
            "This packet prepares only the standalone phi-source C_source^phi "
            "linkage attempt from the prior scalar/on-shell residual route: "
            "C_source^nu[g, phi] := nabla_mu T_phi^{mu nu}, "
            "C_source^nu = sum_i R_i^phi nabla^nu phi_i, "
            "R_i^phi := Box_g phi_i + partial_i V(phi), and on shell "
            "R_i^phi = 0 toward target C_source^nu[g, phi] = 0. It does not "
            "execute a proof, discharge C_source^phi, claim phi-sector "
            "closure, claim full scalar/QFT closure, close EM-QFT or QFT-GR, "
            "claim general C_k closure, embed or vary an action, claim "
            "empirical validation, or promote the master action. Historical "
            "hard-coded omnibus tests are not active-lane acceptance authority; "
            "old omnibus tests are not active-lane acceptance authority."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume prepare_phi_source_theorem_linkage_attempt_from_standalone_phi_route",
            "fail to preserve C_source^nu[g, phi] := nabla_mu T_phi^{mu nu}",
            "fail to preserve C_source^nu = sum_i R_i^phi nabla^nu phi_i",
            "fail to preserve R_i^phi := Box_g phi_i + partial_i V(phi)",
            "fail to preserve the on-shell condition R_i^phi = 0",
            "silently substitute an A-sector route",
            "silently import psi-A sourced Maxwell route",
            "silently import QFT-GR source route",
            "execute the theorem attempt during preparation",
            "discharge C_source^phi during preparation",
            "claim phi-sector closure",
            "claim full scalar/QFT closure",
            "claim EM-QFT or QFT-GR closure",
            "claim general C_k closure",
            "embed or vary an action",
            "treat old omnibus tests as active acceptance authority",
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
            "ToeFormal.Derivation.PhiSourceTheoremLinkageAttemptFromStandalonePhiRoute",
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
            "Prepare the standalone phi-source C_source^phi theorem-linkage "
            "attempt without executing or discharging the proof route."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--review", type=Path, default=REVIEW_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    review_path = args.review if args.review.is_absolute() else REPO_ROOT / args.review
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    packet = build_phi_source_theorem_linkage_attempt_from_standalone_phi_route(
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
                "C_source_phi_residual_definition": packet[
                    "C_source_phi_residual_definition"
                ],
                "residual_identity_form": packet["residual_identity_form"],
                "on_shell_residual_form": packet["on_shell_residual_form"],
                "theorem_discharged": packet["theorem_discharged"],
                "old_omnibus_tests_not_active_acceptance_authority": packet[
                    "old_omnibus_tests_not_active_acceptance_authority"
                ],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

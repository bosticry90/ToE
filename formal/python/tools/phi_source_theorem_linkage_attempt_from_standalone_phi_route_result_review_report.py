from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.phi_source_theorem_linkage_attempt_from_standalone_phi_route_report import (
    BOUNDARY_ITEMS as ATTEMPT_BOUNDARY_ITEMS,
    C_SOURCE_PHI_RESIDUAL_DEFINITION,
    C_SOURCE_PHI_SOURCE_ADMISSIBILITY_CONDITION,
    DEFAULT_OUT as ATTEMPT_PATH,
    FIELD_EULER_LAGRANGE_EQUATION,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET,
    LEAN_PACKET_PATH as ATTEMPT_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_PACKET,
    LINKAGE_ROUTE,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    ON_SHELL_CONDITION,
    ON_SHELL_RESIDUAL_FORM,
    OUTCOME_ID as ATTEMPT_OUTCOME,
    PACKET_ID as ATTEMPT_PACKET_ID,
    PLAIN_MEANING as ATTEMPT_PLAIN_MEANING,
    PREPARED_LINKAGE_TARGET,
    RESIDUAL_IDENTITY_FORM,
    ROUTE_BUNDLE_ADMISSIBILITY_FORM,
    SCHEMA_ID as ATTEMPT_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET,
    STANDALONE_PHI_SOURCE_ROUTE,
    STRESS_DIVERGENCE_TARGET,
    STRESS_ENERGY_UNDER_SELECTED_POLICY,
    STRICT_ATTEMPT_PREPARATION_RESULT,
    TARGET_CONCLUSION,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-30T00:00:00Z"

SCHEMA_ID = (
    "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_RESULT_REVIEW_"
    "20260630_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_RESULT_REVIEW_v0"
)
REVIEW_RESULT = (
    "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_RESULT_"
    "REVIEW_ACCEPTS_C_SOURCE_PHI_LINKAGE_ROUTE_PREPARATION_NO_THEOREM_"
    "DISCHARGE_OR_CK_RULE_PROMOTION"
)
STRICT_REVIEW_RESULT = (
    "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_RESULT_"
    "REVIEW_ACCEPTS_ON_SHELL_SCALAR_RESIDUAL_ROUTE_PREPARED_NO_ACTION_"
    "VARIATION_OR_MASTER_ACTION_PROMOTION"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "phi_source_theorem_linkage_attempt_from_standalone_phi_route_result_"
    "review_accepts_prepared_on_shell_scalar_residual_route_no_theorem_discharge"
)

NEXT_TARGET = "execute_phi_source_theorem_linkage_attempt_from_standalone_phi_route"
NEXT_TARGET_KIND = "phi_source_theorem_linkage_attempt_from_standalone_phi_route_execution"
SUGGESTED_EXECUTION_OUTCOME = (
    "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_EXECUTED_"
    "C_SOURCE_PHI_LINKAGE_CONSTRUCTED_NO_CK_RULE_PROMOTION_OR_MASTER_ACTION_"
    "PROMOTION"
)
STRICT_SUGGESTED_EXECUTION_OUTCOME = (
    "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_EXECUTED_"
    "C_SOURCE_PHI_ZERO_FROM_ON_SHELL_SCALAR_RESIDUAL_NO_SEAM_CLOSURE"
)

EXECUTION_ROUTE_TO_AUTHORIZE = [
    C_SOURCE_PHI_RESIDUAL_DEFINITION,
    RESIDUAL_IDENTITY_FORM,
    "R_i^phi = 0",
    "therefore: C_source^nu[g, phi] = 0",
]
PLAIN_MEANING = (
    "If the scalar field obeys its own field equation, then the scalar source "
    "residual vanishes."
)

ACCEPTED_REVIEW_FINDINGS = [
    "standalone phi-source theorem-linkage attempt prepared",
    "C_source^nu[g, phi] definition preserved",
    "scalar/on-shell residual identity preserved",
    "R_i^phi definition preserved",
    "on-shell condition preserved",
    "target C_source^nu[g, phi] = 0 prepared",
    "no theorem execution during review",
    "no theorem discharge during review",
    "no phi-sector closure",
    "no full scalar/QFT closure",
    "no QFT-GR closure",
    "no EM-QFT closure",
    "no general C_k closure",
    "no action embedding",
    "no variation",
    "no empirical validation",
    "no master-action promotion",
]

BLOCKED_CLAIMS = [
    "no theorem execution during review",
    "no theorem discharge during review",
    "no phi-sector closure",
    "no full scalar/QFT closure",
    "no QFT-GR closure",
    "no EM-QFT closure",
    "no general C_k closure",
    "no action embedding",
    "no variation",
    "no empirical validation",
    "no master-action promotion",
]

ROUTE_PURITY_WATCH_ITEMS = [
    "no A-sector route import",
    "no psi-A sourced Maxwell import",
    "no QFT-GR source-route import",
    "no silent replacement of the phi residual identity",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_RESULT_REVIEW_20260630_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PhiSourceTheoremLinkageAttemptFromStandalonePhiRouteResultReview.lean"
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
        "review_executes_theorem": False,
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
        "A_source_route_imported": False,
        "A_sector_route_imported": False,
        "psi_A_sourced_route_imported": False,
        "psi_A_sourced_Maxwell_imported": False,
        "psi_A_sourced_Maxwell_substitution": False,
        "QFT_GR_source_route_imported": False,
        "J_current_imported": False,
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


def _attempt_valid(attempt: dict[str, Any]) -> bool:
    return (
        attempt.get("schema_id") == ATTEMPT_SCHEMA_ID
        and attempt.get("packet_id") == ATTEMPT_PACKET_ID
        and attempt.get("outcome_id") == ATTEMPT_OUTCOME
        and attempt.get("attempt_preparation_result") == ATTEMPT_OUTCOME
        and attempt.get("strict_attempt_preparation_result")
        == STRICT_ATTEMPT_PREPARATION_RESULT
        and attempt.get("selected_next_target") == CONSUMED_TARGET
        and attempt.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
        and attempt.get("standalone_phi_source_route") == STANDALONE_PHI_SOURCE_ROUTE
        and attempt.get("C_source_phi_residual_definition")
        == C_SOURCE_PHI_RESIDUAL_DEFINITION
        and attempt.get("residual_identity_form") == RESIDUAL_IDENTITY_FORM
        and attempt.get("on_shell_residual_form") == ON_SHELL_RESIDUAL_FORM
        and attempt.get("on_shell_condition") == ON_SHELL_CONDITION
        and attempt.get("target_conclusion") == TARGET_CONCLUSION
        and attempt.get("A_source_route_imported") is False
        and attempt.get("psi_A_sourced_Maxwell_imported") is False
        and attempt.get("QFT_GR_source_route_imported") is False
        and attempt.get("old_omnibus_tests_not_active_acceptance_authority") is True
        and attempt.get("accepted") is True
    )


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": (
            "phi_source_theorem_linkage_attempt_from_standalone_phi_route_result_review"
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


def build_phi_source_theorem_linkage_attempt_from_standalone_phi_route_result_review(
    *,
    attempt_path: Path = ATTEMPT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    attempt = _read_json(attempt_path)
    route_text = " ".join(EXECUTION_ROUTE_TO_AUTHORIZE)
    acceptance_criteria = {
        "consumes_expected_attempt_preparation": _attempt_valid(attempt),
        "C_source_phi_definition_preserved": (
            C_SOURCE_PHI_RESIDUAL_DEFINITION
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
        "on_shell_target_prepared_without_discharge": (
            ON_SHELL_CONDITION == "R_i^phi = 0"
            and TARGET_CONCLUSION == "C_source^nu[g, phi] = 0"
            and EXECUTION_ROUTE_TO_AUTHORIZE
            == [
                "C_source^nu[g, phi] := nabla_mu T_phi^{mu nu}",
                "C_source^nu = sum_i R_i^phi nabla^nu phi_i",
                "R_i^phi = 0",
                "therefore: C_source^nu[g, phi] = 0",
            ]
        ),
        "route_contamination_blocked": (
            "J^alpha" not in route_text
            and "nabla_mu F" not in route_text
            and "QFT-GR" not in route_text
        ),
        "review_only_no_theorem_execution": True,
        "review_only_no_theorem_discharge": True,
        "old_omnibus_tests_historical_only": True,
        "old_omnibus_tests_not_active_acceptance_authority": True,
        "blocked_claims_preserved": ATTEMPT_BOUNDARY_ITEMS[1:4]
        == [
            "no phi-sector closure",
            "no full scalar/QFT closure",
            "no QFT-GR closure",
        ],
        "lean_status_wording_preserved": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_PACKET
            == "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
            and SCOPED_LEAN_TARGETS_STATUS_FOR_PACKET == "PASSED_SERIAL_RERUN"
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else (
            "REMEDIATE_PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_"
            "ROUTE_RESULT_REVIEW"
        )
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": (
            "ACTIVE_PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_"
            "ROUTE_RESULT_REVIEW"
        ),
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "reviewed": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_RESULT_"
            "REVIEW_REQUIRES_REMEDIATION"
        ),
        "review_result": OUTCOME_ID
        if accepted
        else (
            "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_RESULT_"
            "REVIEW_REQUIRES_REMEDIATION"
        ),
        "packet_result": OUTCOME_ID
        if accepted
        else (
            "PHI_SOURCE_THEOREM_LINKAGE_ATTEMPT_FROM_STANDALONE_PHI_ROUTE_RESULT_"
            "REVIEW_REQUIRES_REMEDIATION"
        ),
        "strict_review_result": STRICT_REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND if accepted else "remediation",
        "suggested_execution_outcome": SUGGESTED_EXECUTION_OUTCOME,
        "strict_suggested_execution_outcome": STRICT_SUGGESTED_EXECUTION_OUTCOME,
        "attempt_schema_id": ATTEMPT_SCHEMA_ID,
        "attempt_packet_id": ATTEMPT_PACKET_ID,
        "attempt_preparation_result": ATTEMPT_OUTCOME,
        "attempt_strict_preparation_result": STRICT_ATTEMPT_PREPARATION_RESULT,
        "attempt_preparation_consumed": accepted,
        "accepted_review_findings": ACCEPTED_REVIEW_FINDINGS,
        "accepted_review_finding_count": len(ACCEPTED_REVIEW_FINDINGS),
        "blocked_claims": BLOCKED_CLAIMS,
        "blocked_claim_count": len(BLOCKED_CLAIMS),
        "route_purity_watch_items": ROUTE_PURITY_WATCH_ITEMS,
        "route_purity_watch_item_count": len(ROUTE_PURITY_WATCH_ITEMS),
        "selected_obligation": "C_source^phi theorem-linkage obligation",
        "selected_theorem_linkage_gap": "C_source^phi theorem-linkage gap",
        "selected_obligation_row_id": "C_source^phi",
        "standalone_phi_source_route": STANDALONE_PHI_SOURCE_ROUTE,
        "standalone_phi_source_route_preserved": accepted,
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
        "field_euler_lagrange_equation": FIELD_EULER_LAGRANGE_EQUATION,
        "route_bundle_admissibility_form": ROUTE_BUNDLE_ADMISSIBILITY_FORM,
        "stress_energy_under_selected_policy": STRESS_ENERGY_UNDER_SELECTED_POLICY,
        "target_conclusion": TARGET_CONCLUSION,
        "prepared_linkage_target": PREPARED_LINKAGE_TARGET,
        "linkage_route": LINKAGE_ROUTE,
        "execution_route_to_authorize": EXECUTION_ROUTE_TO_AUTHORIZE,
        "execution_route_to_authorize_count": len(EXECUTION_ROUTE_TO_AUTHORIZE),
        "plain_meaning": PLAIN_MEANING,
        "attempt_plain_meaning": ATTEMPT_PLAIN_MEANING,
        "route_kind": "standalone_phi_on_shell_scalar_residual",
        "exact_registry_statement_frozen": True,
        "scalar_on_shell_residual_identity_preserved": True,
        "R_i_phi_definition_preserved": True,
        "on_shell_condition_preserved": True,
        "target_C_source_phi_zero_prepared": True,
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
            "review only the prepared standalone phi scalar/on-shell residual "
            "route; do not import A-sector, psi-A sourced Maxwell, or QFT-GR "
            "source routes and do not replace the phi residual identity"
        ),
        "old_omnibus_tests_historical_hard_coded": True,
        "old_omnibus_tests_not_active_acceptance_authority": True,
        "active_lane_acceptance_authority": (
            "focused phi-source theorem-linkage attempt result-review gate plus "
            "scoped Lean targets"
        ),
        "silent_validation_downgrade_blocked": True,
        "boundary_items": BLOCKED_CLAIMS,
        "boundary_item_count": len(BLOCKED_CLAIMS),
        "acceptance_criteria": acceptance_criteria,
        "record_validated": accepted,
        "claim_ladder_position": (
            "below theorem discharge, seam closure, empirical prediction, "
            "empirical confirmation, and mature physical theory"
        ),
        "master_action_status": (
            "working-form noncanonical organizing surface; not a promoted final law"
        ),
        "non_claim_boundary": (
            "This result review accepts only that the standalone phi-source "
            "C_source^phi linkage attempt was prepared from C_source^nu[g, phi] "
            ":= nabla_mu T_phi^{mu nu}, C_source^nu = sum_i R_i^phi nabla^nu "
            "phi_i, R_i^phi := Box_g phi_i + partial_i V(phi), and the "
            "on-shell condition R_i^phi = 0 toward the target C_source^nu[g, "
            "phi] = 0. It authorizes only the bounded execution target. It does "
            "not execute or discharge the theorem, does not claim phi-sector "
            "closure, does not claim full scalar/QFT closure, does not close "
            "QFT-GR or EM-QFT, does not claim general C_k closure, does not "
            "embed or vary an action, does not claim empirical validation, and "
            "does not promote the master action. Historical hard-coded omnibus "
            "tests are not active-lane acceptance authority."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume review_phi_source_theorem_linkage_attempt_from_standalone_phi_route_result",
            "fail to accept the prepared standalone phi scalar/on-shell residual route",
            "lose C_source^nu[g, phi] := nabla_mu T_phi^{mu nu}",
            "lose C_source^nu = sum_i R_i^phi nabla^nu phi_i",
            "lose R_i^phi := Box_g phi_i + partial_i V(phi)",
            "lose the on-shell condition R_i^phi = 0",
            "silently substitute an A-sector route",
            "silently import psi-A sourced Maxwell route",
            "silently import QFT-GR source route",
            "execute or discharge the theorem during review",
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
            "ToeFormal.Derivation.PhiSourceTheoremLinkageAttemptFromStandalonePhiRouteResultReview",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "attempt_file": _ptr(attempt_path),
            "attempt_lean_file": _ptr(ATTEMPT_LEAN_PACKET_PATH),
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
            "Review the standalone phi-source C_source^phi theorem-linkage "
            "attempt preparation without executing the theorem."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--attempt", type=Path, default=ATTEMPT_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    attempt_path = (
        args.attempt if args.attempt.is_absolute() else REPO_ROOT / args.attempt
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = (
        build_phi_source_theorem_linkage_attempt_from_standalone_phi_route_result_review(
            attempt_path=attempt_path,
            captured_at_utc=args.captured_at_utc,
        )
    )
    path = write_review(payload, out)
    print(
        json.dumps(
            {
                "accepted": payload["accepted"],
                "out": _ptr(path),
                "review_result": payload["review_result"],
                "selected_next_target": payload["selected_next_target"],
                "C_source_phi_residual_definition": payload[
                    "C_source_phi_residual_definition"
                ],
                "residual_identity_form": payload["residual_identity_form"],
                "on_shell_condition": payload["on_shell_condition"],
                "theorem_discharged": payload["theorem_discharged"],
                "old_omnibus_tests_not_active_acceptance_authority": payload[
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

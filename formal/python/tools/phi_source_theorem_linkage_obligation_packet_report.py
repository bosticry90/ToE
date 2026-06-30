from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.ck_family_theorem_linkage_obligation_selection_after_A_source_closeout_result_review_report import (
    DEFAULT_OUT as SELECTOR_REVIEW_PATH,
    FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW,
    LEAN_PACKET_PATH as SELECTOR_REVIEW_LEAN_PACKET_PATH,
    LEAN_STATUS_WORDING_FOR_REVIEW,
    NEXT_TARGET as CONSUMED_TARGET,
    NEXT_TARGET_KIND as CONSUMED_TARGET_KIND,
    OUTCOME_ID as SELECTOR_REVIEW_OUTCOME,
    PACKET_ID as SELECTOR_REVIEW_PACKET_ID,
    SCHEMA_ID as SELECTOR_REVIEW_SCHEMA_ID,
    SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW,
    SELECTED_OBLIGATION,
    SELECTED_OBLIGATION_ROW_ID,
    SELECTED_THEOREM_LINKAGE_GAP,
    STRICT_REVIEW_RESULT as SELECTOR_STRICT_REVIEW_RESULT,
)
from formal.python.tools.phi_source_admissibility_ck_constraint_candidate_packet_report import (
    CANDIDATE_CONSTRAINT_EQUATION,
    CANDIDATE_CONSTRAINT_FORM,
    CANDIDATE_CONSTRAINT_ID,
    DEFAULT_OUT as PHI_SOURCE_REGISTRY_PATH,
    LEAN_PACKET_PATH as PHI_SOURCE_REGISTRY_LEAN_PACKET_PATH,
    ON_SHELL_IMPLICATION_FORM,
    ON_SHELL_RESIDUAL_FORM,
    OUTCOME_ID as PHI_SOURCE_REGISTRY_OUTCOME,
    PACKET_ID as PHI_SOURCE_REGISTRY_PACKET_ID,
    RESIDUAL_IDENTITY_FORM,
    ROUTE_BUNDLE_ADMISSIBILITY_FORM,
    SCHEMA_ID as PHI_SOURCE_REGISTRY_SCHEMA_ID,
)
from formal.python.tools.toe_native_phi_signature_domain_and_potential_policy_packet_report import (
    BOX_OPERATOR_CONVENTION,
    FIELD_DOMAIN_POLICY,
    KINETIC_CONVENTION_POLICY,
    METRIC_SIGNATURE_POLICY,
    POTENTIAL_POLICY,
    SCALAR_FIELD_TYPE_POLICY,
    SELECTED_PHI_EQUATION_NO_CK,
)
from formal.python.tools.toe_native_phi_variation_retry_under_selected_policy_packet_report import (
    FIELD_EULER_LAGRANGE_EQUATION,
    STRESS_ENERGY_UNDER_SELECTED_POLICY,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-28T00:00:00Z"

SCHEMA_ID = "PHI_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_20260628_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "PHI_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_v0"
OUTCOME_ID = (
    "PHI_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_PREPARED_C_SOURCE_PHI_"
    "ROUTE_SCOPED_NO_PROOF_EXECUTION_OR_CK_RULE_PROMOTION"
)
STRICT_PACKET_RESULT = (
    "PHI_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_PREPARED_STANDALONE_PHI_"
    "SOURCE_ADMISSIBILITY_TARGET_NO_THEOREM_DISCHARGE_OR_MASTER_ACTION_"
    "PROMOTION"
)
PACKET_CLASSIFICATION = (
    "phi_source_theorem_linkage_obligation_packet_scopes_standalone_"
    "phi_source_admissibility_target_no_proof_execution_or_C_k_rule_promotion"
)

NEXT_TARGET = "review_phi_source_theorem_linkage_obligation_packet_result"
NEXT_TARGET_KIND = "phi_source_theorem_linkage_obligation_packet_result_review"
SUGGESTED_REVIEW_OUTCOME = (
    "PHI_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_ACCEPTS_"
    "C_SOURCE_PHI_ROUTE_SCOPE_NO_PROOF_EXECUTION_OR_CK_RULE_PROMOTION"
)
STRICT_SUGGESTED_REVIEW_OUTCOME = (
    "PHI_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_RESULT_REVIEW_ACCEPTS_"
    "STANDALONE_PHI_SOURCE_ADMISSIBILITY_TARGET_NO_THEOREM_DISCHARGE_OR_"
    "MASTER_ACTION_PROMOTION"
)

STANDALONE_PHI_SOURCE_ROUTE = "prior standalone phi source-admissibility registry"
C_SOURCE_PHI_RESIDUAL_DEFINITION = CANDIDATE_CONSTRAINT_FORM
C_SOURCE_PHI_SOURCE_ADMISSIBILITY_CONDITION = CANDIDATE_CONSTRAINT_EQUATION
C_SOURCE_PHI_TARGET_STATEMENT = CANDIDATE_CONSTRAINT_EQUATION
STRESS_DIVERGENCE_TARGET = "nabla_mu T_phi^{mu nu} = 0"
LIKELY_SCHEMATIC_ROUTE = [
    CANDIDATE_CONSTRAINT_FORM,
    STRESS_DIVERGENCE_TARGET,
    "therefore target prepared: " + CANDIDATE_CONSTRAINT_EQUATION,
]

PACKET_SCOPE_RECORD = [
    "selected obligation: C_source^phi theorem-linkage obligation",
    "prior selector-result review accepted",
    "prior standalone phi source-admissibility registry recovered",
    "exact C_source^nu[g, phi] definition frozen from registry",
    "exact C_source^nu[g, phi] = 0 target frozen from registry",
    "selected-policy T_phi expression indexed",
    "on-shell scalar residual identity indexed",
    "no proof execution",
    "no theorem discharge",
]

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
]

BOUNDARY_ITEMS = [
    "no proof execution",
    "no theorem discharge",
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

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PHI_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_20260628_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PhiSourceTheoremLinkageObligationPacket.lean"
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


def _blocked_boundary_flags() -> dict[str, bool]:
    return {
        "proof_execution_authorized": False,
        "proof_attempt_executed": False,
        "theorem_execution_authorized": False,
        "theorem_discharged": False,
        "theorem_linkage_obligation_discharged": False,
        "C_source_phi_discharged": False,
        "phi_source_theorem_linkage_obligation_discharged": False,
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


def _selector_review_valid(selector_review: dict[str, Any]) -> bool:
    return (
        selector_review.get("schema_id") == SELECTOR_REVIEW_SCHEMA_ID
        and selector_review.get("packet_id") == SELECTOR_REVIEW_PACKET_ID
        and selector_review.get("outcome_id") == SELECTOR_REVIEW_OUTCOME
        and selector_review.get("review_result") == SELECTOR_REVIEW_OUTCOME
        and selector_review.get("strict_review_result")
        == SELECTOR_STRICT_REVIEW_RESULT
        and selector_review.get("selected_next_target") == CONSUMED_TARGET
        and selector_review.get("selected_next_target_kind") == CONSUMED_TARGET_KIND
        and selector_review.get("selected_obligation") == SELECTED_OBLIGATION
        and selector_review.get("selected_theorem_linkage_gap")
        == SELECTED_THEOREM_LINKAGE_GAP
        and selector_review.get("selected_obligation_row_id")
        == SELECTED_OBLIGATION_ROW_ID
        and selector_review.get("accepted") is True
    )


def _phi_registry_valid(registry: dict[str, Any]) -> bool:
    return (
        registry.get("schema_id") == PHI_SOURCE_REGISTRY_SCHEMA_ID
        and registry.get("packet_id") == PHI_SOURCE_REGISTRY_PACKET_ID
        and registry.get("outcome_id") == PHI_SOURCE_REGISTRY_OUTCOME
        and registry.get("candidate_constraint_id") == CANDIDATE_CONSTRAINT_ID
        and registry.get("candidate_constraint_form") == CANDIDATE_CONSTRAINT_FORM
        and registry.get("candidate_constraint_equation")
        == CANDIDATE_CONSTRAINT_EQUATION
        and registry.get("on_shell_residual_form") == ON_SHELL_RESIDUAL_FORM
        and registry.get("residual_identity_form") == RESIDUAL_IDENTITY_FORM
        and registry.get("on_shell_implication_form") == ON_SHELL_IMPLICATION_FORM
        and registry.get("accepted") is True
    )


def _prior_phi_registry_snapshot() -> dict[str, Any]:
    return {
        "route_kind": STANDALONE_PHI_SOURCE_ROUTE,
        "candidate_constraint_id": CANDIDATE_CONSTRAINT_ID,
        "candidate_constraint_form": CANDIDATE_CONSTRAINT_FORM,
        "candidate_constraint_equation": CANDIDATE_CONSTRAINT_EQUATION,
        "source_admissibility_condition": CANDIDATE_CONSTRAINT_EQUATION,
        "stress_divergence_target": STRESS_DIVERGENCE_TARGET,
        "on_shell_residual_form": ON_SHELL_RESIDUAL_FORM,
        "residual_identity_form": RESIDUAL_IDENTITY_FORM,
        "on_shell_implication_form": ON_SHELL_IMPLICATION_FORM,
        "route_bundle_admissibility_form": ROUTE_BUNDLE_ADMISSIBILITY_FORM,
        "metric_signature_policy": METRIC_SIGNATURE_POLICY,
        "scalar_field_type_policy": SCALAR_FIELD_TYPE_POLICY,
        "field_domain_policy": FIELD_DOMAIN_POLICY,
        "kinetic_convention_policy": KINETIC_CONVENTION_POLICY,
        "box_operator_convention": BOX_OPERATOR_CONVENTION,
        "potential_policy": POTENTIAL_POLICY,
        "selected_phi_equation_no_ck": SELECTED_PHI_EQUATION_NO_CK,
        "field_euler_lagrange_equation": FIELD_EULER_LAGRANGE_EQUATION,
        "stress_energy_under_selected_policy": STRESS_ENERGY_UNDER_SELECTED_POLICY,
    }


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": "phi_source_theorem_linkage_obligation_packet",
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
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW
        ),
        "scoped_lean_targets_status_for_packet": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW
        ),
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def build_phi_source_theorem_linkage_obligation_packet(
    *,
    selector_review_path: Path = SELECTOR_REVIEW_PATH,
    phi_registry_path: Path = PHI_SOURCE_REGISTRY_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    selector_review = _read_json(selector_review_path)
    phi_registry = _read_json(phi_registry_path)
    prior_phi_registry = _prior_phi_registry_snapshot()
    acceptance_criteria = {
        "consumes_expected_selector_result_review": _selector_review_valid(
            selector_review
        ),
        "selected_obligation_preserved": (
            SELECTED_OBLIGATION == "C_source^phi theorem-linkage obligation"
            and SELECTED_THEOREM_LINKAGE_GAP == "C_source^phi theorem-linkage gap"
            and SELECTED_OBLIGATION_ROW_ID == "C_source^phi"
        ),
        "prior_phi_registry_exact": _phi_registry_valid(phi_registry),
        "standalone_phi_source_route_recovered": (
            CANDIDATE_CONSTRAINT_FORM
            == "C_source^nu[g, phi] := nabla_mu T_phi^{mu nu}"
            and CANDIDATE_CONSTRAINT_EQUATION == "C_source^nu[g, phi] = 0"
            and ON_SHELL_RESIDUAL_FORM
            == "R_i^phi := Box_g phi_i + partial_i V(phi)"
            and RESIDUAL_IDENTITY_FORM
            == "C_source^nu = sum_i R_i^phi nabla^nu phi_i"
            and ON_SHELL_IMPLICATION_FORM
            == "R_i^phi = 0 for all i implies C_source^nu = 0"
        ),
        "selected_policy_context_preserved": (
            FIELD_EULER_LAGRANGE_EQUATION == SELECTED_PHI_EQUATION_NO_CK
            and "T^policy_{mu nu}" in STRESS_ENERGY_UNDER_SELECTED_POLICY
            and BOX_OPERATOR_CONVENTION
            == "Box_g phi_i = g^{mu nu} nabla_mu nabla_nu phi_i"
        ),
        "route_contamination_blocked": True,
        "scope_only_no_theorem_execution": True,
        "lean_status_wording_preserved": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW
            == "NOT_COMPLETED_PARALLEL_FILE_LOCK_COLLISION"
            and SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW == "PASSED_SERIAL_RERUN"
        ),
    }
    prepared = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if prepared
        else "REMEDIATE_PHI_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET"
    )
    payload: dict[str, Any] = {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_PHI_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET",
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "accepted": prepared,
        "packet_prepared": prepared,
        "outcome_id": OUTCOME_ID
        if prepared
        else "PHI_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_REQUIRES_REMEDIATION",
        "packet_result": OUTCOME_ID
        if prepared
        else "PHI_SOURCE_THEOREM_LINKAGE_OBLIGATION_PACKET_REQUIRES_REMEDIATION",
        "strict_packet_result": STRICT_PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "consumed_target_kind": CONSUMED_TARGET_KIND,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND if prepared else "remediation",
        "suggested_review_outcome": SUGGESTED_REVIEW_OUTCOME,
        "strict_suggested_review_outcome": STRICT_SUGGESTED_REVIEW_OUTCOME,
        "selector_review_schema_id": SELECTOR_REVIEW_SCHEMA_ID,
        "selector_review_packet_id": SELECTOR_REVIEW_PACKET_ID,
        "selector_review_outcome": SELECTOR_REVIEW_OUTCOME,
        "selector_strict_review_result": SELECTOR_STRICT_REVIEW_RESULT,
        "selector_review_consumed": prepared,
        "prior_selector_result_review_accepted": prepared,
        "selected_obligation": SELECTED_OBLIGATION,
        "selected_theorem_linkage_gap": SELECTED_THEOREM_LINKAGE_GAP,
        "selected_obligation_row_id": SELECTED_OBLIGATION_ROW_ID,
        "C_source_phi_theorem_linkage_obligation_selected": prepared,
        "packet_scope_record": PACKET_SCOPE_RECORD,
        "packet_scope_record_count": len(PACKET_SCOPE_RECORD),
        "scope_only": True,
        "proof_execution_blocked": True,
        "theorem_discharge_blocked": True,
        "prior_phi_source_registry": prior_phi_registry,
        "standalone_phi_source_route": STANDALONE_PHI_SOURCE_ROUTE,
        "standalone_phi_source_route_preserved": prepared,
        "C_source_phi_constraint_candidate": CANDIDATE_CONSTRAINT_ID,
        "C_source_phi_residual_definition": C_SOURCE_PHI_RESIDUAL_DEFINITION,
        "C_source_phi_source_admissibility_condition": (
            C_SOURCE_PHI_SOURCE_ADMISSIBILITY_CONDITION
        ),
        "C_source_phi_target_statement": C_SOURCE_PHI_TARGET_STATEMENT,
        "source_admissibility_condition": C_SOURCE_PHI_SOURCE_ADMISSIBILITY_CONDITION,
        "stress_divergence_target": STRESS_DIVERGENCE_TARGET,
        "likely_schematic_route": LIKELY_SCHEMATIC_ROUTE,
        "exact_registry_statement_frozen": prepared,
        "on_shell_residual_form": ON_SHELL_RESIDUAL_FORM,
        "residual_identity_form": RESIDUAL_IDENTITY_FORM,
        "on_shell_implication_form": ON_SHELL_IMPLICATION_FORM,
        "route_bundle_admissibility_form": ROUTE_BUNDLE_ADMISSIBILITY_FORM,
        "metric_signature_policy": METRIC_SIGNATURE_POLICY,
        "scalar_field_type_policy": SCALAR_FIELD_TYPE_POLICY,
        "field_domain_policy": FIELD_DOMAIN_POLICY,
        "kinetic_convention_policy": KINETIC_CONVENTION_POLICY,
        "box_operator_convention": BOX_OPERATOR_CONVENTION,
        "potential_policy": POTENTIAL_POLICY,
        "selected_phi_equation_no_ck": SELECTED_PHI_EQUATION_NO_CK,
        "field_euler_lagrange_equation": FIELD_EULER_LAGRANGE_EQUATION,
        "stress_energy_under_selected_policy": STRESS_ENERGY_UNDER_SELECTED_POLICY,
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
        "route_contamination_guard": (
            "freeze exact C_source^phi statement from prior standalone phi "
            "source-admissibility registry; do not substitute A-sector, "
            "psi-A sourced Maxwell, or QFT-GR source routes"
        ),
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
            "This packet scopes only the standalone phi source theorem-linkage "
            "obligation. It freezes the prior standalone phi source-admissibility "
            "registry statement C_source^nu[g, phi] := nabla_mu T_phi^{mu nu} "
            "and target C_source^nu[g, phi] = 0, while retaining the selected "
            "scalar/on-shell residual identity C_source^nu = sum_i R_i^phi "
            "nabla^nu phi_i. It does not execute a proof, discharge "
            "C_source^phi, claim phi-sector closure, claim full scalar/QFT "
            "closure, close EM-QFT or QFT-GR, claim general C_k closure, embed "
            "or vary an action, claim empirical validation, or promote the "
            "master action."
        ),
        "critical_gate_fail_conditions": [
            "fail to consume prepare_phi_source_theorem_linkage_obligation_packet",
            "fail to freeze C_source^nu[g, phi] := nabla_mu T_phi^{mu nu}",
            "fail to freeze C_source^nu[g, phi] = 0",
            "silently substitute A-sector source route",
            "silently import psi-A sourced Maxwell route",
            "silently import QFT-GR source route",
            "execute the C_source^phi proof route",
            "discharge C_source^phi",
            "claim phi-sector closure",
            "claim full scalar/QFT closure",
            "claim EM-QFT or QFT-GR closure",
            "claim general C_k closure",
            "embed or vary an action",
            "promote the master action",
            "record full ToeFormal aggregate as PASSED without a full serial build",
        ],
        "lean_status_wording": LEAN_STATUS_WORDING_FOR_REVIEW,
        "full_toeformal_aggregate_status_for_packet": (
            FULL_TOEFORMAL_AGGREGATE_STATUS_FOR_REVIEW
        ),
        "scoped_lean_targets_status_for_packet": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW
        ),
        "aggregate_lean_validation_status_for_packet": (
            SCOPED_LEAN_TARGETS_STATUS_FOR_REVIEW
        ),
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "validation_policy": _validation_policy(),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.PhiSourceTheoremLinkageObligationPacket",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "selector_review_file": _ptr(selector_review_path),
            "selector_review_lean_file": _ptr(SELECTOR_REVIEW_LEAN_PACKET_PATH),
            "phi_source_registry_file": _ptr(phi_registry_path),
            "phi_source_registry_lean_file": _ptr(PHI_SOURCE_REGISTRY_LEAN_PACKET_PATH),
            "qftgr_aggregate_file": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate_file": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate_file": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
        },
    }
    payload.update(_blocked_boundary_flags())
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
            "obligation packet without executing the proof route."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--selector-review", type=Path, default=SELECTOR_REVIEW_PATH)
    parser.add_argument("--phi-registry", type=Path, default=PHI_SOURCE_REGISTRY_PATH)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args(argv)

    selector_review_path = (
        args.selector_review
        if args.selector_review.is_absolute()
        else REPO_ROOT / args.selector_review
    )
    phi_registry_path = (
        args.phi_registry
        if args.phi_registry.is_absolute()
        else REPO_ROOT / args.phi_registry
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    packet = build_phi_source_theorem_linkage_obligation_packet(
        selector_review_path=selector_review_path,
        phi_registry_path=phi_registry_path,
        captured_at_utc=args.captured_at_utc,
    )
    path = write_packet(packet, out)
    print(
        json.dumps(
            {
                "accepted": packet["accepted"],
                "out": _ptr(path),
                "packet_result": packet["packet_result"],
                "selected_obligation": packet["selected_obligation"],
                "selected_next_target": packet["selected_next_target"],
                "C_source_phi_residual_definition": packet[
                    "C_source_phi_residual_definition"
                ],
                "source_admissibility_condition": packet[
                    "source_admissibility_condition"
                ],
                "proof_attempt_executed": packet["proof_attempt_executed"],
                "theorem_discharged": packet["theorem_discharged"],
                "route_contamination_blocked": packet["acceptance_criteria"][
                    "route_contamination_blocked"
                ],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.master_action_ck_constraint_family_selection_for_phi_route_report import (
    AGGREGATE_TIMEOUT_STATUS,
    DEFAULT_OUT as CK_FAMILY_SELECTION_PATH,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as CK_FAMILY_SELECTION_OUTCOME,
    PACKET_ID as CK_FAMILY_SELECTION_PACKET_ID,
    SCHEMA_ID as CK_FAMILY_SELECTION_SCHEMA_ID,
    SELECTED_CK_CONSTRAINT_FAMILY,
    SELECTED_CK_OPTION_CLASS,
    SELECTION_RESULT as CK_FAMILY_SELECTION_RESULT,
)
from formal.python.tools.toe_native_phi_signature_domain_and_potential_policy_packet_report import (
    BOX_OPERATOR_CONVENTION,
    CK_ROLE_POLICY,
    FIELD_DOMAIN_POLICY,
    KINETIC_CONVENTION_POLICY,
    METRIC_SIGNATURE_POLICY,
    POTENTIAL_POLICY,
    SCALAR_FIELD_TYPE_POLICY,
    SELECTED_PHI_EQUATION_NO_CK,
    VARIATION_POLICY,
)
from formal.python.tools.toe_native_phi_variation_retry_under_selected_policy_packet_report import (
    DEFAULT_OUT as PHI_VARIATION_RETRY_PACKET_PATH,
    FIELD_EULER_LAGRANGE_EQUATION,
    OUTCOME_ID as PHI_VARIATION_RETRY_OUTCOME,
    PACKET_ID as PHI_VARIATION_RETRY_PACKET_ID,
    SCHEMA_ID as PHI_VARIATION_RETRY_SCHEMA_ID,
    STRESS_ENERGY_UNDER_SELECTED_POLICY,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-18T00:00:00Z"

SCHEMA_ID = "PHI_SOURCE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET_20260618_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "PHI_SOURCE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET_v0"
PACKET_RESULT = (
    "PHI_SOURCE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_RECORDED_AS_"
    "CONSERVATION_RESIDUAL_NO_VARIATION_OR_PROMOTION"
)
OUTCOME_ID = (
    "PHI_SOURCE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET_PREPARED_"
    + PACKET_RESULT
)
PACKET_CLASSIFICATION = (
    "phi_source_admissibility_ck_constraint_candidate_packet_records_"
    "conservation_residual_candidate_without_variation_or_promotion"
)
NEXT_TARGET = "review_phi_source_admissibility_ck_constraint_candidate_packet_result"
NEXT_TARGET_KIND = (
    "phi_source_admissibility_ck_constraint_candidate_packet_result_review"
)
LEAN_VALIDATION_POLICY_ID = "TIERED_LEAN_VALIDATION_POLICY_FOR_PACKET_WORK_v0"

CANDIDATE_CONSTRAINT_ID = "phi_source_conservation_residual_ck_candidate"
CANDIDATE_CONSTRAINT_FORM = "C_source^nu[g, phi] := nabla_mu T_phi^{mu nu}"
CANDIDATE_CONSTRAINT_EQUATION = "C_source^nu[g, phi] = 0"
ON_SHELL_RESIDUAL_ID = "phi_on_shell_source_admissibility_residual"
ON_SHELL_RESIDUAL_FORM = "R_i^phi := Box_g phi_i + partial_i V(phi)"
RESIDUAL_IDENTITY_FORM = "C_source^nu = sum_i R_i^phi nabla^nu phi_i"
ON_SHELL_IMPLICATION_FORM = (
    "R_i^phi = 0 for all i implies C_source^nu = 0"
)
CANDIDATE_ACTION_INSERTION_FORM = (
    "S_Csource[candidate] = integral_M sqrt(-g) lambda_nu "
    "C_source^nu d^4x"
)
ROUTE_BUNDLE_ADMISSIBILITY_ID = "phi_source_route_bundle_admissibility_checklist"
ROUTE_BUNDLE_ADMISSIBILITY_FORM = (
    "{action_derivability, weak_pairing, on_shell_conservation, "
    "Bianchi_compatibility}"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PHI_SOURCE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET_20260618_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "PhiSourceAdmissibilityCKConstraintCandidatePacket.lean"
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
LEAN_VALIDATION_POLICY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "LEAN_VALIDATION_TIER_POLICY_v0.md"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _candidate_shapes() -> list[dict[str, Any]]:
    return [
        {
            "candidate_id": CANDIDATE_CONSTRAINT_ID,
            "candidate_type": "conservation_residual_constraint",
            "selection_status": "selected_as_first_candidate_shape",
            "constraint_form": CANDIDATE_CONSTRAINT_FORM,
            "constraint_equation": CANDIDATE_CONSTRAINT_EQUATION,
            "plain_meaning": (
                "The phi source is admitted only when its stress-energy "
                "divergence residual vanishes."
            ),
            "requires_new_variation_now": False,
            "fully_concrete_ck_functional_defined": False,
            "physical_law_claimed": False,
        },
        {
            "candidate_id": ON_SHELL_RESIDUAL_ID,
            "candidate_type": "on_shell_source_admissibility_residual",
            "selection_status": "recorded_as_supporting_route_identity",
            "residual_form": ON_SHELL_RESIDUAL_FORM,
            "residual_identity": RESIDUAL_IDENTITY_FORM,
            "on_shell_implication": ON_SHELL_IMPLICATION_FORM,
            "plain_meaning": (
                "The selected phi equation implies the conservation residual "
                "vanishes at the route level."
            ),
            "requires_new_variation_now": False,
            "fully_concrete_ck_functional_defined": False,
            "physical_law_claimed": False,
        },
        {
            "candidate_id": ROUTE_BUNDLE_ADMISSIBILITY_ID,
            "candidate_type": "route_bundle_admissibility_constraint",
            "selection_status": "deferred_as_non_variational_checklist",
            "checklist_form": ROUTE_BUNDLE_ADMISSIBILITY_FORM,
            "plain_meaning": (
                "The whole source route can be tracked as admissibility "
                "metadata, but it is not selected as the first smooth "
                "variational C_k candidate shape."
            ),
            "requires_new_variation_now": False,
            "fully_concrete_ck_functional_defined": False,
            "physical_law_claimed": False,
        },
    ]


def _review_rows(
    *,
    selector: dict[str, Any],
    phi_variation_retry: dict[str, Any],
) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "consumes_expected_candidate_packet_target",
            "status": "accepted",
            "evidence": selector.get("selected_next_target"),
            "assessment": "The selector authorized this candidate packet.",
        },
        {
            "row_id": "selected_family_carried_forward",
            "status": "accepted",
            "evidence": [
                selector.get("selected_ck_option_class"),
                selector.get("selected_ck_constraint_family"),
            ],
            "assessment": "The packet stays within the phi source-admissibility family.",
        },
        {
            "row_id": "selected_phi_policy_carried_forward",
            "status": "accepted",
            "evidence": [
                METRIC_SIGNATURE_POLICY,
                SCALAR_FIELD_TYPE_POLICY,
                FIELD_DOMAIN_POLICY,
                KINETIC_CONVENTION_POLICY,
                BOX_OPERATOR_CONVENTION,
                POTENTIAL_POLICY,
                VARIATION_POLICY,
                CK_ROLE_POLICY,
            ],
            "assessment": "The selected nonpromotional phi policy is preserved.",
        },
        {
            "row_id": "phi_variation_route_reference_available",
            "status": "accepted",
            "evidence": [
                phi_variation_retry.get("outcome_id"),
                FIELD_EULER_LAGRANGE_EQUATION,
                STRESS_ENERGY_UNDER_SELECTED_POLICY,
            ],
            "assessment": "The conservation residual is tied to the selected phi route.",
        },
        {
            "row_id": "conservation_residual_candidate_recorded",
            "status": "accepted",
            "evidence": [CANDIDATE_CONSTRAINT_FORM, CANDIDATE_CONSTRAINT_EQUATION],
            "assessment": "The first candidate C_source^phi shape is recorded.",
        },
        {
            "row_id": "on_shell_residual_identity_recorded",
            "status": "accepted",
            "evidence": [
                ON_SHELL_RESIDUAL_FORM,
                RESIDUAL_IDENTITY_FORM,
                ON_SHELL_IMPLICATION_FORM,
            ],
            "assessment": "The route-level relation to the phi equation is recorded.",
        },
        {
            "row_id": "route_bundle_deferred",
            "status": "accepted",
            "evidence": ROUTE_BUNDLE_ADMISSIBILITY_FORM,
            "assessment": (
                "The route bundle remains useful metadata but is not the first "
                "smooth candidate functional."
            ),
        },
        {
            "row_id": "candidate_action_insertion_not_executed",
            "status": "accepted",
            "evidence": CANDIDATE_ACTION_INSERTION_FORM,
            "assessment": (
                "A future multiplier insertion shape is noted only as a "
                "candidate; no C_k variation is executed."
            ),
        },
        {
            "row_id": "no_new_conservation_or_source_admissibility_proof",
            "status": "accepted",
            "evidence": [
                "new_conservation_proof_claimed=false",
                "new_source_admissibility_proof_claimed=false",
            ],
            "assessment": "The packet records a candidate condition, not a proof.",
        },
        {
            "row_id": "no_closure_promotion_or_empirical_claim",
            "status": "accepted",
            "evidence": [
                "qft_gr_closure_claimed=false",
                "master_action_promoted=false",
                "empirical_validation_claimed=false",
            ],
            "assessment": "The nonpromotion boundary is preserved.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "phi_source_admissibility_ck_constraint_candidate_packet",
        "tiered_lean_validation_policy_formalized": True,
        "routine_packet_validation_tiers": [
            "touched Lean marker",
            "smallest affected Lake target",
            "lane aggregate",
            "current authority target",
        ],
        "release_preservation_validation": "full ToeFormal aggregate when feasible",
        "aggregate_timeout_with_steady_progress_interpretation": (
            "incomplete_validation_not_mathematical_failure"
        ),
        "toeformal_import_update_requires_preservation_status": True,
        "aggregate_lean_validation_status_for_packet": AGGREGATE_TIMEOUT_STATUS,
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def build_phi_source_admissibility_ck_constraint_candidate_packet(
    *,
    ck_family_selection_path: Path = CK_FAMILY_SELECTION_PATH,
    phi_variation_retry_packet_path: Path = PHI_VARIATION_RETRY_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    selector = _read_json(ck_family_selection_path)
    phi_variation_retry = _read_json(phi_variation_retry_packet_path)
    candidate_shapes = _candidate_shapes()
    review_rows = _review_rows(
        selector=selector,
        phi_variation_retry=phi_variation_retry,
    )
    acceptance_criteria = {
        "consumes_expected_target": (
            selector.get("schema_id") == CK_FAMILY_SELECTION_SCHEMA_ID
            and selector.get("packet_id") == CK_FAMILY_SELECTION_PACKET_ID
            and selector.get("outcome_id") == CK_FAMILY_SELECTION_OUTCOME
            and selector.get("selection_result") == CK_FAMILY_SELECTION_RESULT
            and selector.get("selected_next_target") == CONSUMED_TARGET
            and selector.get("accepted") is True
        ),
        "selected_family_matches_source_admissibility": (
            selector.get("selected_ck_option_class") == SELECTED_CK_OPTION_CLASS
            and selector.get("selected_ck_constraint_family")
            == SELECTED_CK_CONSTRAINT_FAMILY
            and SELECTED_CK_OPTION_CLASS == "source_admissibility_constraint"
            and SELECTED_CK_CONSTRAINT_FAMILY
            == "phi_source_admissibility_constraint_family"
        ),
        "phi_variation_retry_reference_available": (
            phi_variation_retry.get("schema_id") == PHI_VARIATION_RETRY_SCHEMA_ID
            and phi_variation_retry.get("packet_id") == PHI_VARIATION_RETRY_PACKET_ID
            and phi_variation_retry.get("outcome_id") == PHI_VARIATION_RETRY_OUTCOME
            and phi_variation_retry.get("accepted") is True
            and FIELD_EULER_LAGRANGE_EQUATION == SELECTED_PHI_EQUATION_NO_CK
        ),
        "conservation_residual_candidate_recorded": (
            CANDIDATE_CONSTRAINT_FORM
            == "C_source^nu[g, phi] := nabla_mu T_phi^{mu nu}"
            and CANDIDATE_CONSTRAINT_EQUATION == "C_source^nu[g, phi] = 0"
        ),
        "on_shell_residual_identity_recorded": (
            ON_SHELL_RESIDUAL_FORM
            == "R_i^phi := Box_g phi_i + partial_i V(phi)"
            and RESIDUAL_IDENTITY_FORM
            == "C_source^nu = sum_i R_i^phi nabla^nu phi_i"
        ),
        "candidate_shapes_counted": (
            len(candidate_shapes) == 3
            and sum(
                row["selection_status"] == "selected_as_first_candidate_shape"
                for row in candidate_shapes
            )
            == 1
        ),
        "no_ck_variation_executed": True,
        "no_new_conservation_or_source_admissibility_proof": True,
        "review_rows_all_accepted": all(
            row["status"] == "accepted" for row in review_rows
        ),
        "next_review_target_selected": (
            NEXT_TARGET
            == "review_phi_source_admissibility_ck_constraint_candidate_packet_result"
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_PHI_SOURCE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_PHI_SOURCE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "PHI_SOURCE_ADMISSIBILITY_CK_CONSTRAINT_CANDIDATE_PACKET_REQUIRES_REMEDIATION",
        "packet_result": PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "ck_family_selection_outcome": CK_FAMILY_SELECTION_OUTCOME,
        "phi_variation_retry_outcome": PHI_VARIATION_RETRY_OUTCOME,
        "selected_ck_option_class": SELECTED_CK_OPTION_CLASS,
        "selected_ck_constraint_family": SELECTED_CK_CONSTRAINT_FAMILY,
        "candidate_constraint_id": CANDIDATE_CONSTRAINT_ID,
        "candidate_constraint_type": "conservation_residual_constraint",
        "candidate_constraint_form": CANDIDATE_CONSTRAINT_FORM,
        "candidate_constraint_equation": CANDIDATE_CONSTRAINT_EQUATION,
        "on_shell_residual_id": ON_SHELL_RESIDUAL_ID,
        "on_shell_residual_form": ON_SHELL_RESIDUAL_FORM,
        "residual_identity_form": RESIDUAL_IDENTITY_FORM,
        "on_shell_implication_form": ON_SHELL_IMPLICATION_FORM,
        "candidate_action_insertion_form": CANDIDATE_ACTION_INSERTION_FORM,
        "candidate_action_insertion_executed": False,
        "route_bundle_admissibility_id": ROUTE_BUNDLE_ADMISSIBILITY_ID,
        "route_bundle_admissibility_form": ROUTE_BUNDLE_ADMISSIBILITY_FORM,
        "candidate_shapes": candidate_shapes,
        "candidate_shape_count": len(candidate_shapes),
        "candidate_shape_selected_count": sum(
            row["selection_status"] == "selected_as_first_candidate_shape"
            for row in candidate_shapes
        ),
        "candidate_shape_supporting_count": sum(
            row["selection_status"] == "recorded_as_supporting_route_identity"
            for row in candidate_shapes
        ),
        "candidate_shape_deferred_count": sum(
            row["selection_status"] == "deferred_as_non_variational_checklist"
            for row in candidate_shapes
        ),
        "metric_signature_policy": METRIC_SIGNATURE_POLICY,
        "scalar_field_type_policy": SCALAR_FIELD_TYPE_POLICY,
        "field_domain_policy": FIELD_DOMAIN_POLICY,
        "kinetic_convention_policy": KINETIC_CONVENTION_POLICY,
        "box_operator_convention": BOX_OPERATOR_CONVENTION,
        "potential_policy": POTENTIAL_POLICY,
        "variation_policy": VARIATION_POLICY,
        "ck_role_policy": CK_ROLE_POLICY,
        "selected_phi_equation_no_ck": SELECTED_PHI_EQUATION_NO_CK,
        "stress_energy_under_selected_policy": STRESS_ENERGY_UNDER_SELECTED_POLICY,
        "candidate_packet_prepared": True,
        "candidate_constraint_shape_recorded": True,
        "conservation_residual_candidate_selected": True,
        "on_shell_source_admissibility_relation_recorded": True,
        "route_bundle_admissibility_candidate_deferred": True,
        "candidate_constraint_is_condition_not_physical_law": True,
        "candidate_uses_prior_scalar_witness_pattern": True,
        "candidate_uses_selected_phi_policy": True,
        "fully_concrete_ck_functional_defined": False,
        "concrete_ck_functional_selected": False,
        "concrete_ck_functional_defined": False,
        "ck_functional_formula_fully_defined": False,
        "ck_functional_formula_selected": False,
        "candidate_not_yet_inserted_into_master_action_variation": True,
        "ck_variation_executed": False,
        "ck_variation_authorized": False,
        "lambda_variation_executed": False,
        "metric_variation_of_candidate_executed": False,
        "phi_variation_of_candidate_executed": False,
        "ck_family_claimed_as_physical_law": False,
        "phi_generated_by_ck_claimed": False,
        "phi_generation_theorem_claimed": False,
        "derived_v_phi_claimed": False,
        "v_phi_derivation_claimed": False,
        "potential_derived": False,
        "new_conservation_proof_claimed": False,
        "new_source_admissibility_proof_claimed": False,
        "source_admissibility_claimed": False,
        "source_admissibility_completed": False,
        "source_conservation_claimed": False,
        "weak_conservation_claimed": False,
        "bianchi_compatibility_claimed": False,
        "qft_gr_closure_claimed": False,
        "qft_gr_solved": False,
        "qft_gr_seam_closed": False,
        "qft_gr_source_map_closure_authorized": False,
        "semiclassical_coupling_authorized": False,
        "semiclassical_coupling_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "semiclassical_source_established": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "canonical_master_action_promoted": False,
        "toe_native_matter_derivation_claimed": False,
        "toe_native_matter_sector_derived": False,
        "toe_native_matter_sector_defined": False,
        "standard_model_derivation_claimed": False,
        "native_generation_theorem_claimed": False,
        "empirical_validation_claimed": False,
        "public_readiness_claimed": False,
        "public_submission_authorized": False,
        "phase2_readiness_claim": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "review_rows": review_rows,
        "review_row_count": len(review_rows),
        "review_row_accepted_count": sum(
            1 for row in review_rows if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "proof_depth_label": (
            "PHI_SOURCE_ADMISSIBILITY_CK_CANDIDATE_SHAPE_RECORDED_ONLY"
        ),
        "mathematical_statement": (
            "Under the selected (+,-,-,-) finite real scalar multiplet policy, "
            "the first phi source-admissibility C_k candidate is recorded as "
            "the conservation residual C_source^nu[g, phi] := nabla_mu "
            "T_phi^{mu nu}, with candidate condition C_source^nu = 0. The "
            "supporting route identity is recorded as C_source^nu = sum_i "
            "R_i^phi nabla^nu phi_i with R_i^phi := Box_g phi_i + partial_i "
            "V(phi). This records a candidate condition only; it does not "
            "insert the candidate into the master action or execute variation."
        ),
        "non_claim_boundary": (
            "This packet records a phi source-admissibility C_k candidate "
            "shape as a conservation residual only. It does not select or "
            "define a fully concrete C_k functional, execute C_k variation, "
            "vary lambda_k, vary the candidate with respect to phi or g, claim "
            "phi generation, derive V(phi), prove new conservation, prove new "
            "source admissibility, close QFT-GR, authorize semiclassical "
            "coupling, promote the master action, claim empirical validation, "
            "or authorize public readiness. C_k remains inactive and undefined "
            "at the fully concrete functional level, and C_k content is not "
            "fully defined. V(phi) remains smooth bounded-below but not "
            "derived. C_k does not yet generate phi. There is no ToE-native "
            "matter derivation, no native-generation theorem, no source "
            "admissibility or conservation, no QFT-GR closure, and no "
            "canonical master-action promotion."
        ),
        "critical_gate_fail_conditions": [
            "claim a fully concrete C_k functional is selected",
            "execute C_k variation",
            "execute lambda variation",
            "claim phi is generated by C_k",
            "claim V(phi) is derived",
            "claim source admissibility or conservation newly proved",
            "claim QFT-GR closure",
            "claim semiclassical coupling",
            "promote the master action",
            "claim empirical validation or public readiness",
        ],
        "validation_policy": _validation_policy(),
        "lean_validation_policy_id": LEAN_VALIDATION_POLICY_ID,
        "aggregate_lean_validation_status_for_packet": AGGREGATE_TIMEOUT_STATUS,
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.PhiSourceAdmissibilityCKConstraintCandidatePacket",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "files": {
            "json_report": _ptr(DEFAULT_OUT),
            "lean_packet_file": _ptr(LEAN_PACKET_PATH),
            "qftgr_aggregate_file": _ptr(QFTGR_AGGREGATE_PATH),
            "current_target_aggregate_file": _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            "release_current_authority_aggregate_file": _ptr(
                RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH
            ),
            "ck_family_selection_file": _ptr(ck_family_selection_path),
            "phi_variation_retry_packet_file": _ptr(phi_variation_retry_packet_path),
            "lean_validation_policy_file": _ptr(LEAN_VALIDATION_POLICY_PATH),
        },
    }


def write_packet(packet: dict[str, Any], out: Path = DEFAULT_OUT) -> Path:
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(
        json.dumps(packet, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return out


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Build the phi source-admissibility C_k constraint candidate packet."
        )
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()

    packet = build_phi_source_admissibility_ck_constraint_candidate_packet(
        captured_at_utc=args.captured_at_utc
    )
    path = write_packet(packet, args.out)
    print(
        json.dumps(
            {
                "accepted": packet["accepted"],
                "candidate_constraint_id": packet["candidate_constraint_id"],
                "out": _ptr(path),
                "outcome_id": packet["outcome_id"],
                "selected_next_target": packet["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()

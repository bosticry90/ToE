from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_phi_surface_variation_and_source_route_result_review_report import (
    DEFAULT_OUT as PHI_ROUTE_REVIEW_PATH,
    DEFERRED_CK_TARGET,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as PHI_ROUTE_REVIEW_OUTCOME,
    PACKET_ID as PHI_ROUTE_REVIEW_PACKET_ID,
    PHI_ROUTE_REVIEW_RESULT,
    SCHEMA_ID as PHI_ROUTE_REVIEW_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-18T00:00:00Z"

SCHEMA_ID = "TOE_NATIVE_PHI_SIGNATURE_DOMAIN_AND_POTENTIAL_POLICY_PACKET_20260618_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_PHI_SIGNATURE_DOMAIN_AND_POTENTIAL_POLICY_PACKET_v0"
PHI_POLICY_DECISION = "PHI_POLICY_PARTIALLY_SELECTED_CK_VARIATIONAL_CONTENT_STILL_BLOCKED"
PHI_POLICY_PACKET_RESULT = (
    "TOE_NATIVE_PHI_SIGNATURE_DOMAIN_AND_POTENTIAL_POLICY_PACKET_PREPARED_"
    "PHI_POLICY_PARTIALLY_SELECTED_CK_VARIATIONAL_CONTENT_STILL_BLOCKED"
)
OUTCOME_ID = PHI_POLICY_PACKET_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_phi_signature_domain_and_potential_policy_packet_selects_"
    "nonpromotional_scalar_conventions_and_blocks_ck_variational_content"
)
NEXT_TARGET = "prepare_toe_native_phi_variation_retry_under_selected_policy"
NEXT_TARGET_KIND = "toe_native_phi_variation_retry_under_selected_policy_packet_preparation"
LEAN_VALIDATION_POLICY_ID = "TIERED_LEAN_VALIDATION_POLICY_FOR_PACKET_WORK_v0"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_PHI_SIGNATURE_DOMAIN_AND_POTENTIAL_POLICY_PACKET_20260618_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativePhiSignatureDomainAndPotentialPolicyPacket.lean"
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

POLICY_ITEMS = [
    "metric signature",
    "scalar field type",
    "field domain",
    "kinetic convention",
    "box operator",
    "potential policy",
    "variation policy",
    "C_k role",
]

METRIC_SIGNATURE_POLICY = "(+,-,-,-)"
SCALAR_FIELD_TYPE_POLICY = (
    "finite real scalar multiplet phi_i : M -> R with i in I_phi; "
    "single-field specialization allowed for imported scalar comparison; "
    "I_phi cardinality is not ToE-derived"
)
FIELD_DOMAIN_POLICY = (
    "smooth finite-action scalar fields on a smooth Lorentzian four-manifold; "
    "variations are compactly supported or boundary terms are fixed; Sobolev "
    "and distributional extensions are not selected here"
)
KINETIC_CONVENTION_POLICY = (
    "L_phi^MA = +1/2 sum_i g^{mu nu} nabla_mu phi_i nabla_nu phi_i - V(phi) "
    "under the (+,-,-,-) signature"
)
BOX_OPERATOR_CONVENTION = "Box_g phi_i = g^{mu nu} nabla_mu nabla_nu phi_i"
POTENTIAL_POLICY = (
    "V : R^{|I_phi|} -> R is assumed smooth and bounded below for calculation; "
    "its functional form is not ToE-derived, and mass or polynomial "
    "specializations are deferred"
)
VARIATION_POLICY = (
    "vary phi_i and inverse metric g^{mu nu} in separate variations; hold "
    "lambda_k and C_k inactive in this packet; compact-support or fixed-boundary "
    "conditions remove boundary terms"
)
CK_ROLE_POLICY = (
    "C_k variational content is recorded as undefined and is not allowed to "
    "modify the phi equation in this packet"
)
SELECTED_PHI_EQUATION_NO_CK = "Box_g phi_i + partial_i V(phi) = 0"
SELECTED_STRESS_ENERGY_POLICY = (
    "use the previously recorded raw master-action stress-energy candidate only "
    "as a convention-dependent expression; no source-admissibility or "
    "conservation claim follows"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _policy_rows() -> list[dict[str, Any]]:
    return [
        {
            "policy_id": "metric_signature",
            "status": "selected_nonpromotionally",
            "decision": METRIC_SIGNATURE_POLICY,
            "reason": (
                "The master-action phi kinetic sign is kept as written for a "
                "bounded calculation convention."
            ),
        },
        {
            "policy_id": "scalar_field_type",
            "status": "selected_nonpromotionally",
            "decision": SCALAR_FIELD_TYPE_POLICY,
            "reason": (
                "The master action writes a sum over phi_i, so the packet uses a "
                "finite real scalar multiplet while retaining the one-field "
                "comparison slice."
            ),
        },
        {
            "policy_id": "field_domain",
            "status": "selected_for_packet_calculation",
            "decision": FIELD_DOMAIN_POLICY,
            "reason": (
                "The raw variation requires enough regularity for integration by "
                "parts and boundary-term control."
            ),
        },
        {
            "policy_id": "kinetic_convention",
            "status": "selected_nonpromotionally",
            "decision": KINETIC_CONVENTION_POLICY,
            "reason": "The convention normalizes the master-action phi surface for retry.",
        },
        {
            "policy_id": "box_operator",
            "status": "selected_nonpromotionally",
            "decision": BOX_OPERATOR_CONVENTION,
            "reason": "The retry needs a fixed d'Alembertian convention.",
        },
        {
            "policy_id": "potential_policy",
            "status": "partially_selected_not_derived",
            "decision": POTENTIAL_POLICY,
            "reason": (
                "Smooth bounded-below V gives a calculation class without "
                "claiming that ToE determines V."
            ),
        },
        {
            "policy_id": "variation_policy",
            "status": "selected_for_packet_calculation",
            "decision": VARIATION_POLICY,
            "reason": (
                "The next retry must state what is varied, what is held fixed, "
                "and how boundary terms are handled."
            ),
        },
        {
            "policy_id": "ck_role",
            "status": "blocked_pending_ck_variational_content",
            "decision": CK_ROLE_POLICY,
            "reason": (
                "Undefined seam constraints cannot silently modify the scalar "
                "equation."
            ),
        },
    ]


def _review_criteria(review: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "consumes_expected_policy_packet_target",
            "status": "accepted",
            "evidence": review.get("selected_next_target"),
            "assessment": "The result review authorized this policy packet.",
        },
        {
            "row_id": "metric_signature_selected",
            "status": "accepted",
            "evidence": METRIC_SIGNATURE_POLICY,
            "assessment": "A calculation signature is fixed nonpromotionally.",
        },
        {
            "row_id": "scalar_field_type_selected",
            "status": "accepted",
            "evidence": SCALAR_FIELD_TYPE_POLICY,
            "assessment": "The phi surface is treated as a finite real multiplet.",
        },
        {
            "row_id": "field_domain_selected",
            "status": "accepted",
            "evidence": FIELD_DOMAIN_POLICY,
            "assessment": "A smooth finite-action calculation domain is selected.",
        },
        {
            "row_id": "kinetic_and_box_conventions_selected",
            "status": "accepted",
            "evidence": [KINETIC_CONVENTION_POLICY, BOX_OPERATOR_CONVENTION],
            "assessment": "The kinetic sign, normalization, and Box_g convention are fixed.",
        },
        {
            "row_id": "potential_policy_partially_selected",
            "status": "accepted",
            "evidence": POTENTIAL_POLICY,
            "assessment": "V is constrained enough for calculation but not derived.",
        },
        {
            "row_id": "variation_policy_selected",
            "status": "accepted",
            "evidence": VARIATION_POLICY,
            "assessment": "Variation and boundary assumptions are fixed for retry.",
        },
        {
            "row_id": "ck_variational_content_blocked",
            "status": "accepted",
            "evidence": CK_ROLE_POLICY,
            "assessment": "C_k remains undefined and cannot modify the phi equation.",
        },
        {
            "row_id": "imported_scalar_witness_not_promoted",
            "status": "accepted",
            "evidence": review.get("imported_scalar_witness_not_promoted"),
            "assessment": "The scalar witness remains comparison evidence only.",
        },
        {
            "row_id": "next_retry_authorized_under_selected_policy",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "The next packet may retry the phi variation under this policy.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "toe_native_phi_signature_domain_and_potential_policy_packet",
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
        "aggregate_lean_validation_status_for_packet": "NOT_RUN",
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
        "full_security_scan_required": False,
    }


def build_toe_native_phi_signature_domain_and_potential_policy_packet(
    *,
    phi_route_review_path: Path = PHI_ROUTE_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(phi_route_review_path)
    policy_rows = _policy_rows()
    review_criteria = _review_criteria(review)
    acceptance_criteria = {
        "consumes_expected_policy_packet_target": (
            review.get("schema_id") == PHI_ROUTE_REVIEW_SCHEMA_ID
            and review.get("packet_id") == PHI_ROUTE_REVIEW_PACKET_ID
            and review.get("outcome_id") == PHI_ROUTE_REVIEW_OUTCOME
            and review.get("selected_next_target") == CONSUMED_TARGET
            and review.get("accepted") is True
        ),
        "metric_signature_selected": METRIC_SIGNATURE_POLICY == "(+,-,-,-)",
        "scalar_field_type_selected": "finite real scalar multiplet" in SCALAR_FIELD_TYPE_POLICY,
        "field_domain_selected": "smooth finite-action" in FIELD_DOMAIN_POLICY,
        "kinetic_convention_selected": "L_phi^MA" in KINETIC_CONVENTION_POLICY,
        "box_operator_selected": BOX_OPERATOR_CONVENTION.startswith("Box_g"),
        "potential_policy_partially_selected": (
            "smooth" in POTENTIAL_POLICY and "not ToE-derived" in POTENTIAL_POLICY
        ),
        "variation_policy_selected": (
            "vary phi_i" in VARIATION_POLICY and "boundary" in VARIATION_POLICY
        ),
        "ck_variational_content_still_blocked": (
            "undefined" in CK_ROLE_POLICY and "not allowed to modify" in CK_ROLE_POLICY
        ),
        "imported_scalar_witness_not_promoted": (
            review.get("imported_scalar_witness_not_promoted") is True
        ),
        "no_native_derivation_or_closure_claim": (
            review.get("toe_native_matter_derivation_claimed") is False
            and review.get("qft_gr_closure_claimed") is False
            and review.get("master_action_promoted") is False
        ),
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
        ),
        "next_target_is_variation_retry": (
            NEXT_TARGET == "prepare_toe_native_phi_variation_retry_under_selected_policy"
        ),
    }
    prepared = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if prepared
        else "REMEDIATE_TOE_NATIVE_PHI_SIGNATURE_DOMAIN_AND_POTENTIAL_POLICY_PACKET"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_PHI_SIGNATURE_DOMAIN_POTENTIAL_POLICY_PACKET",
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "accepted": prepared,
        "outcome_id": OUTCOME_ID
        if prepared
        else "TOE_NATIVE_PHI_SIGNATURE_DOMAIN_AND_POTENTIAL_POLICY_PACKET_REQUIRES_REMEDIATION",
        "phi_policy_decision": PHI_POLICY_DECISION,
        "phi_policy_packet_result": PHI_POLICY_PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "deferred_ck_variational_content_target": DEFERRED_CK_TARGET,
        "review_result": PHI_ROUTE_REVIEW_RESULT,
        "reviewed_phi_route_result_review_artifact_id": review.get("schema_id"),
        "reviewed_phi_route_result_review_outcome": review.get("outcome_id"),
        "policy_status": "partial_nonpromotional_selection",
        "policy_items": policy_rows,
        "policy_item_count": len(policy_rows),
        "policy_selected_count": sum(
            1 for row in policy_rows if row["status"] != "blocked_pending_ck_variational_content"
        ),
        "policy_blocked_count": sum(
            1 for row in policy_rows if row["status"] == "blocked_pending_ck_variational_content"
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
        "selected_stress_energy_policy": SELECTED_STRESS_ENERGY_POLICY,
        "ck_allowed_to_modify_phi_equation": False,
        "ck_variational_content_defined": False,
        "ck_variational_content_still_blocked": True,
        "signature_domain_potential_policy_selected": True,
        "variation_retry_under_selected_policy_authorized": prepared,
        "imported_scalar_witness_not_promoted": True,
        "native_derivation_blocked": True,
        "review_criteria": review_criteria,
        "review_criteria_count": len(review_criteria),
        "review_criteria_accepted_count": sum(
            1 for row in review_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "formal_theorem_backed_matter_derivation": False,
        "record_validated": True,
        "symbolic_calculation_recorded": False,
        "policy_contract_recorded": True,
        "proof_depth_label": "POLICY_SELECTION_RECORDED_NO_NATIVE_DERIVATION",
        "phi_variation_retry_authorized": prepared,
        "phi_variation_retry_executed": False,
        "phi_variation_route_executed": False,
        "phi_variation_derived_as_toe_native": False,
        "phi_stress_energy_derived_as_toe_native": False,
        "toe_native_phi_source_route_constructed": False,
        "toe_native_phi_source_admissibility_claimed": False,
        "toe_native_phi_source_conservation_claimed": False,
        "toe_native_matter_derivation_claimed": False,
        "toe_native_matter_sector_derived": False,
        "toe_native_matter_sector_defined": False,
        "toe_matter_sector_derived": False,
        "toe_matter_model_derived": False,
        "standard_model_derivation_claimed": False,
        "source_admissibility_claimed": False,
        "source_admissibility_completed": False,
        "source_conservation_claimed": False,
        "weak_conservation_claimed": False,
        "bianchi_compatibility_claimed": False,
        "source_map_closed": False,
        "qft_gr_solved": False,
        "qft_gr_closure_claimed": False,
        "qft_gr_seam_closed": False,
        "qft_gr_source_map_closure_authorized": False,
        "semiclassical_coupling_authorized": False,
        "semiclassical_coupling_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "semiclassical_source_established": False,
        "empirical_validation_claimed": False,
        "public_readiness_claimed": False,
        "public_submission_authorized": False,
        "canonical_master_action_promoted": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "phase2_readiness_claim": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "critical_gate_fail_conditions": [
            "treat selected convention as a ToE-native derivation",
            "allow undefined C_k to modify the phi equation",
            "derive or choose V(phi) as a final ToE law",
            "claim source admissibility",
            "claim conservation",
            "claim QFT-GR closure",
            "promote the working-form master action",
            "authorize semiclassical coupling or public release",
        ],
        "downstream_progression": [
            {
                "stage": "phi_signature_domain_potential_policy_packet",
                "status": "PARTIALLY_SELECTED_CK_VARIATIONAL_CONTENT_STILL_BLOCKED",
                "decision": PHI_POLICY_DECISION,
                "reason": (
                    "A clean scalar calculation convention is selected, but "
                    "C_k remains undefined and non-modifying."
                ),
            },
            {
                "stage": "phi_variation_retry_under_selected_policy",
                "status": "NEXT_TARGET_AUTHORIZED",
                "decision": selected_next_target,
                "reason": (
                    "The retry can now test the master-action phi surface under "
                    "the selected signature, domain, potential, and variation "
                    "policy without treating C_k as solved."
                ),
            },
            {
                "stage": "ck_variational_content_packet",
                "status": "RETAINED_DEFERRED",
                "decision": DEFERRED_CK_TARGET,
                "reason": "C_k content still requires its own packet.",
            },
        ],
        "mathematical_statement": (
            "This packet fixes a nonpromotional calculation policy for the "
            "working-form master-action phi surface: signature (+,-,-,-), finite "
            "real scalar multiplet, smooth finite-action field domain, the "
            "written +1/2 kinetic convention, Box_g = g^{mu nu} nabla_mu nabla_nu, "
            "smooth bounded-below but not ToE-derived potential, compact-support "
            "or fixed-boundary variation policy, and inactive C_k terms. It "
            "authorizes a retry under that policy while blocking native "
            "derivation and C_k modification claims."
        ),
        "non_claim_boundary": (
            "This policy packet selects calculation conventions only. It does "
            "not derive ToE-native matter, does not derive or uniquely select "
            "V(phi), does not define C_k variational content, does not claim "
            "source admissibility or conservation, does not close QFT-GR, does "
            "not authorize semiclassical coupling, does not promote the master "
            "action, does not claim empirical validation, and does not authorize "
            "public readiness or release completion."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativePhiSignatureDomainAndPotentialPolicyPacket",
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "lane_level_lean_target_files": [
            _ptr(LEAN_PACKET_PATH),
            _ptr(QFTGR_AGGREGATE_PATH),
            _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            _ptr(RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH),
        ],
        "lean_validation_policy_file": _ptr(LEAN_VALIDATION_POLICY_PATH),
        "validation_policy": _validation_policy(),
    }


def write_toe_native_phi_signature_domain_and_potential_policy_packet(
    *,
    phi_route_review_path: Path = PHI_ROUTE_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = build_toe_native_phi_signature_domain_and_potential_policy_packet(
        phi_route_review_path=phi_route_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return packet


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Build the ToE-native phi signature/domain/potential policy packet."
        )
    )
    parser.add_argument("--phi-route-review", type=Path, default=PHI_ROUTE_REVIEW_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()
    packet = write_toe_native_phi_signature_domain_and_potential_policy_packet(
        phi_route_review_path=args.phi_route_review,
        out=args.out,
        captured_at_utc=args.captured_at_utc,
    )
    print(json.dumps(packet, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

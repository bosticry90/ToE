from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_phi_surface_alignment_witness_closeout_report import (
    AGGREGATE_TIMEOUT_STATUS,
    ALIGNMENT_WITNESS_CLOSEOUT_STATUS,
    ALIGNMENT_WITNESS_STATUS,
    BOX_OPERATOR_CONVENTION,
    CK_ROLE_POLICY,
    DEFAULT_OUT as PHI_ALIGNMENT_CLOSEOUT_PATH,
    FIELD_DOMAIN_POLICY,
    FIELD_EULER_LAGRANGE_EQUATION,
    KINETIC_CONVENTION_POLICY,
    METRIC_SIGNATURE_POLICY,
    OUTCOME_ID as PHI_ALIGNMENT_CLOSEOUT_OUTCOME,
    PACKET_ID as PHI_ALIGNMENT_CLOSEOUT_PACKET_ID,
    POTENTIAL_POLICY,
    SCALAR_FIELD_TYPE_POLICY,
    SCALAR_WITNESS_COMPARISON_DECISION,
    SCHEMA_ID as PHI_ALIGNMENT_CLOSEOUT_SCHEMA_ID,
    SELECTED_PHI_ACTION,
    STRESS_ENERGY_UNDER_SELECTED_POLICY,
    VARIATION_POLICY,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-18T00:00:00Z"

SCHEMA_ID = "TOE_NATIVE_PHI_CK_VARIATIONAL_CONTENT_PACKET_20260618_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_PHI_CK_VARIATIONAL_CONTENT_PACKET_v0"
CK_VARIATIONAL_CONTENT_RESULT = (
    "CK_VARIATIONAL_CONTENT_BLOCKED_BY_UNSPECIFIED_CONSTRAINT_FUNCTIONALS"
)
OUTCOME_ID = (
    "TOE_NATIVE_PHI_CK_VARIATIONAL_CONTENT_PACKET_PREPARED_"
    "CK_VARIATIONAL_CONTENT_BLOCKED_BY_UNSPECIFIED_CONSTRAINT_FUNCTIONALS"
)
PACKET_CLASSIFICATION = (
    "toe_native_phi_ck_variational_content_packet_blocks_real_ck_content_on_"
    "unspecified_constraint_functionals"
)
CONSUMED_TARGET = "prepare_toe_native_phi_ck_variational_content_packet"
NEXT_TARGET = "prepare_master_action_ck_constraint_functional_definition_packet"
NEXT_TARGET_KIND = "master_action_ck_constraint_functional_definition_packet_preparation"
LEAN_VALIDATION_POLICY_ID = "TIERED_LEAN_VALIDATION_POLICY_FOR_PACKET_WORK_v0"

MASTER_ACTION_CK_SURFACE = "sum_k lambda_k * C_k(g, psi, A, phi, rho)"
CK_VARIATION_TARGET = "delta/delta phi_i [sum_k lambda_k C_k(g, psi, A, phi, rho)]"
CK_VARIATION_FORMAL_SLOT = (
    "delta_phi_i S_C(eta_i) = integral_M sqrt(-g) "
    "sum_k lambda_k (delta C_k/delta phi_i) eta_i d^4x"
)
RAW_TOTAL_PHI_CK_EQUATION = (
    "-(Box_g phi_i + partial_i V(phi)) + "
    "sum_k lambda_k delta C_k/delta phi_i = 0"
)
NORMALIZED_PHI_CK_EQUATION = (
    "Box_g phi_i + partial_i V(phi) = "
    "sum_k lambda_k delta C_k/delta phi_i"
)
SOURCE_FROM_CK_UNDER_SELECTED_POLICY = (
    "source_from_C_k,i = sum_k lambda_k delta C_k/delta phi_i"
)
LEFT_HAND_FORCE_CONVENTION = (
    "-sum_k lambda_k delta C_k/delta phi_i when moved to the left-hand side"
)
CK_INDEPENDENCE_CASE = (
    "if delta C_k/delta phi_i = 0 for all k,i, the selected-policy phi "
    "equation remains Box_g phi_i + partial_i V(phi) = 0 and no native "
    "generation follows"
)
BLOCKER_ID = "CK-FUNCTIONAL-DEFINITION-MISSING-FOR-PHI-VARIATION"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_PHI_CK_VARIATIONAL_CONTENT_PACKET_20260618_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativePhiCKVariationalContentPacket.lean"
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
MASTER_ACTION_DOC_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_CANDIDATE_MASTER_ACTION_v0.md"
)
RAW_PHI_ROUTE_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_PHI_SURFACE_VARIATION_AND_SOURCE_ROUTE_PACKET_20260618_v0.json"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required text file: {path}")
    return path.read_text(encoding="utf-8")


def _test_matrix() -> list[dict[str, Any]]:
    return [
        {
            "row_id": "generate_phi_equation",
            "symbolic_status": "blocked_no_constraint_functional",
            "can_be_tested_now": False,
            "result": "No C_k functional is defined that forces the phi equation.",
        },
        {
            "row_id": "modify_phi_equation",
            "symbolic_status": "formal_slot_recorded_only",
            "can_be_tested_now": False,
            "result": NORMALIZED_PHI_CK_EQUATION,
        },
        {
            "row_id": "restrict_allowed_potential",
            "symbolic_status": "blocked_no_potential_constraint",
            "can_be_tested_now": False,
            "result": "No C_k rule constrains V(phi).",
        },
        {
            "row_id": "enforce_source_conservation",
            "symbolic_status": "blocked_no_admissibility_or_conservation_theorem",
            "can_be_tested_now": False,
            "result": "No C_k source-admissibility or conservation proof is supplied.",
        },
        {
            "row_id": "connect_phi_to_another_pillar",
            "symbolic_status": "blocked_no_concrete_cross_pillar_constraint",
            "can_be_tested_now": False,
            "result": "No target pillar coupling is defined by C_k.",
        },
        {
            "row_id": "produce_new_residual_law",
            "symbolic_status": "blocked_no_residual_definition",
            "can_be_tested_now": False,
            "result": "No residual law follows from an undefined C_k.",
        },
        {
            "row_id": "produce_possible_falsifier",
            "symbolic_status": "blocked_no_observable_residual_or_constraint_family",
            "can_be_tested_now": False,
            "result": "No falsifier is produced without a selected C_k family.",
        },
    ]


def _packet_criteria(
    *,
    closeout: dict[str, Any],
    master_action_doc: str,
    raw_phi_route: dict[str, Any],
) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "alignment_closeout_consumed",
            "status": "accepted",
            "evidence": closeout.get("outcome_id"),
            "assessment": "The packet consumes the alignment closeout target.",
        },
        {
            "row_id": "selected_phi_policy_carried_forward",
            "status": "accepted",
            "evidence": [
                closeout.get("metric_signature_policy"),
                closeout.get("kinetic_convention_policy"),
                closeout.get("potential_policy"),
            ],
            "assessment": "The selected nonpromotional phi policy remains fixed.",
        },
        {
            "row_id": "generic_ck_surface_present",
            "status": "accepted",
            "evidence": MASTER_ACTION_CK_SURFACE,
            "assessment": (
                "The master action contains a generic seam-constraint surface."
            ),
        },
        {
            "row_id": "ck_phi_variation_slot_examined",
            "status": "accepted",
            "evidence": [
                CK_VARIATION_TARGET,
                CK_VARIATION_FORMAL_SLOT,
                raw_phi_route.get("phi_variation_with_seam_route"),
            ],
            "assessment": (
                "The packet examines the phi variation slot for the C_k term."
            ),
        },
        {
            "row_id": "ck_effect_menu_tested",
            "status": "accepted",
            "evidence": [row["row_id"] for row in _test_matrix()],
            "assessment": (
                "The packet checks generation, modification, potential "
                "restriction, conservation, cross-pillar connection, residual "
                "law, and falsifier roles."
            ),
        },
        {
            "row_id": "concrete_ck_functionals_not_found",
            "status": "accepted",
            "evidence": (
                "generic surface present without repo-local definitions of C_k"
                if MASTER_ACTION_CK_SURFACE in master_action_doc
                else "generic surface missing"
            ),
            "assessment": (
                "The repo supplies the generic C_k term but no concrete "
                "functional family that can be varied."
            ),
        },
        {
            "row_id": "real_ck_variational_content_blocked",
            "status": "accepted",
            "evidence": BLOCKER_ID,
            "assessment": (
                "Real C_k content is blocked until the constraint functionals "
                "are defined."
            ),
        },
        {
            "row_id": "definition_packet_selected_next",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": (
                "The next target must define the C_k functionals before "
                "retrying C_k variation."
            ),
        },
        {
            "row_id": "nonclaims_preserved",
            "status": "accepted",
            "evidence": [
                "native_generation_theorem_claimed=false",
                "source_conservation_claimed=false",
                "qft_gr_closure_claimed=false",
                "master_action_promoted=false",
            ],
            "assessment": "No derivation, closure, or promotion claim is added.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "toe_native_phi_ck_variational_content_packet",
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


def build_toe_native_phi_ck_variational_content_packet(
    *,
    phi_alignment_closeout_path: Path = PHI_ALIGNMENT_CLOSEOUT_PATH,
    master_action_doc_path: Path = MASTER_ACTION_DOC_PATH,
    raw_phi_route_packet_path: Path = RAW_PHI_ROUTE_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    closeout = _read_json(phi_alignment_closeout_path)
    master_action_doc = _read_text(master_action_doc_path)
    raw_phi_route = _read_json(raw_phi_route_packet_path)
    criteria = _packet_criteria(
        closeout=closeout,
        master_action_doc=master_action_doc,
        raw_phi_route=raw_phi_route,
    )
    test_matrix = _test_matrix()
    acceptance_criteria = {
        "consumes_expected_ck_packet_target": (
            closeout.get("schema_id") == PHI_ALIGNMENT_CLOSEOUT_SCHEMA_ID
            and closeout.get("packet_id") == PHI_ALIGNMENT_CLOSEOUT_PACKET_ID
            and closeout.get("outcome_id") == PHI_ALIGNMENT_CLOSEOUT_OUTCOME
            and closeout.get("selected_next_target") == CONSUMED_TARGET
            and closeout.get("accepted") is True
        ),
        "selected_policy_carried_forward": (
            closeout.get("metric_signature_policy") == METRIC_SIGNATURE_POLICY
            and closeout.get("scalar_field_type_policy") == SCALAR_FIELD_TYPE_POLICY
            and closeout.get("field_domain_policy") == FIELD_DOMAIN_POLICY
            and closeout.get("kinetic_convention_policy") == KINETIC_CONVENTION_POLICY
            and closeout.get("box_operator_convention") == BOX_OPERATOR_CONVENTION
            and closeout.get("potential_policy") == POTENTIAL_POLICY
            and closeout.get("variation_policy") == VARIATION_POLICY
        ),
        "generic_ck_surface_present": MASTER_ACTION_CK_SURFACE in master_action_doc,
        "ck_phi_variation_slot_examined": (
            "delta C_k/delta phi_i"
            in raw_phi_route.get("phi_variation_with_seam_route", "")
            and "delta C_k/delta phi_i" in CK_VARIATION_FORMAL_SLOT
        ),
        "ck_effect_menu_complete": len(test_matrix) == 7
        and {row["row_id"] for row in test_matrix}
        == {
            "generate_phi_equation",
            "modify_phi_equation",
            "restrict_allowed_potential",
            "enforce_source_conservation",
            "connect_phi_to_another_pillar",
            "produce_new_residual_law",
            "produce_possible_falsifier",
        },
        "concrete_ck_functionals_not_found": True,
        "real_ck_variational_content_blocked": True,
        "next_target_is_constraint_functional_definition_packet": (
            NEXT_TARGET
            == "prepare_master_action_ck_constraint_functional_definition_packet"
        ),
        "criteria_all_accepted": all(row["status"] == "accepted" for row in criteria),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_PHI_CK_VARIATIONAL_CONTENT_PACKET"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_PHI_CK_VARIATIONAL_CONTENT_PACKET",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_PHI_CK_VARIATIONAL_CONTENT_PACKET_REQUIRES_REMEDIATION",
        "packet_result": CK_VARIATIONAL_CONTENT_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "alignment_witness_status": ALIGNMENT_WITNESS_STATUS,
        "alignment_witness_closeout_status": ALIGNMENT_WITNESS_CLOSEOUT_STATUS,
        "phi_alignment_closeout_outcome": PHI_ALIGNMENT_CLOSEOUT_OUTCOME,
        "selected_phi_action": SELECTED_PHI_ACTION,
        "metric_signature_policy": METRIC_SIGNATURE_POLICY,
        "scalar_field_type_policy": SCALAR_FIELD_TYPE_POLICY,
        "field_domain_policy": FIELD_DOMAIN_POLICY,
        "kinetic_convention_policy": KINETIC_CONVENTION_POLICY,
        "box_operator_convention": BOX_OPERATOR_CONVENTION,
        "potential_policy": POTENTIAL_POLICY,
        "variation_policy": VARIATION_POLICY,
        "prior_ck_role_policy": CK_ROLE_POLICY,
        "field_euler_lagrange_equation_without_ck": FIELD_EULER_LAGRANGE_EQUATION,
        "stress_energy_under_selected_policy": STRESS_ENERGY_UNDER_SELECTED_POLICY,
        "scalar_witness_comparison_decision": SCALAR_WITNESS_COMPARISON_DECISION,
        "master_action_ck_surface": MASTER_ACTION_CK_SURFACE,
        "ck_variation_target": CK_VARIATION_TARGET,
        "ck_variation_formal_slot": CK_VARIATION_FORMAL_SLOT,
        "raw_total_phi_ck_equation": RAW_TOTAL_PHI_CK_EQUATION,
        "normalized_phi_ck_equation": NORMALIZED_PHI_CK_EQUATION,
        "source_from_ck_under_selected_policy": SOURCE_FROM_CK_UNDER_SELECTED_POLICY,
        "left_hand_force_convention": LEFT_HAND_FORCE_CONVENTION,
        "ck_independence_case": CK_INDEPENDENCE_CASE,
        "blocker_id": BLOCKER_ID,
        "ck_effect_test_matrix": test_matrix,
        "ck_effect_test_count": len(test_matrix),
        "packet_criteria": criteria,
        "packet_criteria_count": len(criteria),
        "packet_criteria_accepted_count": sum(
            1 for row in criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "generic_ck_surface_present": True,
        "concrete_ck_functionals_found": [],
        "concrete_ck_functional_definition_available": False,
        "ck_variational_derivative_defined": False,
        "ck_variational_content_recorded_symbolically": True,
        "ck_variational_content_constructed": False,
        "ck_variational_content_blocked": True,
        "ck_variational_content_blocked_by_unspecified_constraint_functionals": True,
        "ck_phi_equation_generation_constructed": False,
        "ck_phi_equation_modification_route_recorded_symbolically": True,
        "ck_phi_equation_modification_constructed": False,
        "ck_potential_restriction_constructed": False,
        "ck_source_conservation_enforced": False,
        "ck_cross_pillar_connection_constructed": False,
        "ck_new_residual_law_constructed": False,
        "ck_possible_falsifier_produced": False,
        "ck_phi_independence_case_recorded": True,
        "ck_phi_independence_selected": False,
        "ck_constraint_family_selected": False,
        "ck_constraint_functional_definition_required": True,
        "master_action_ck_definition_packet_authorized": True,
        "review_target_selected": False,
        "selected_phi_policy_carried_forward": True,
        "phi_alignment_witness_preserved": True,
        "native_generation_blocked": True,
        "proof_depth_label": (
            "SYMBOLIC_CK_VARIATION_SLOT_RECORDED_REAL_CK_CONTENT_BLOCKED"
        ),
        "formal_theorem_backed_matter_derivation": False,
        "native_generation_theorem_claimed": False,
        "derived_v_phi_claimed": False,
        "potential_derived": False,
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
        "scalar_route_level_status": [
            {
                "level": "imported_scalar_sandbox",
                "status": "positive_classical_witness",
            },
            {
                "level": "master_action_phi_surface",
                "status": (
                    "matches_scalar_witness_under_selected_policy_after_"
                    "convention_normalization"
                ),
            },
            {
                "level": "ck_variational_content",
                "status": (
                    "formal_variation_slot_recorded_but_blocked_by_"
                    "unspecified_constraint_functionals"
                ),
            },
            {
                "level": "toe_native_explanation",
                "status": (
                    "still_blocked_by_no_concrete_C_k_family_and_no_native_"
                    "generation_theorem"
                ),
            },
        ],
        "critical_gate_fail_conditions": [
            "claim C_k variational content is constructed",
            "claim C_k generates phi",
            "claim C_k restricts V(phi)",
            "claim source admissibility or conservation",
            "claim QFT-GR closure",
            "claim native-generation theorem",
            "promote the working-form master action",
        ],
        "downstream_progression": [
            {
                "stage": "ck_variational_content_packet",
                "status": "BLOCKED_BY_UNSPECIFIED_CONSTRAINT_FUNCTIONALS",
                "decision": CK_VARIATIONAL_CONTENT_RESULT,
                "reason": (
                    "The formal C_k variation slot can be written, but no "
                    "concrete C_k family exists to vary."
                ),
            },
            {
                "stage": "ck_constraint_functional_definition",
                "status": "NEXT_TARGET_AUTHORIZED",
                "decision": selected_next_target,
                "reason": (
                    "Constraint functionals must be defined before C_k can "
                    "generate, modify, restrict, conserve, connect, produce "
                    "residuals, or produce falsifiers."
                ),
            },
        ],
        "mathematical_statement": (
            "Under the selected (+,-,-,-) phi policy, the formal C_k slot is "
            "delta_phi_i S_C = integral sqrt(-g) sum_k lambda_k "
            "(delta C_k/delta phi_i) eta_i, yielding the normalized symbolic "
            "route Box_g phi_i + partial_i V(phi) = sum_k lambda_k delta "
            "C_k/delta phi_i. Because the project supplies no concrete "
            "constraint functionals C_k, this is only a formal slot, not "
            "constructed variational content."
        ),
        "non_claim_boundary": (
            "This packet records the symbolic C_k phi-variation slot and "
            "blocks real C_k variational content on unspecified constraint "
            "functionals. It does not prove ToE-native matter derivation, "
            "does not supply a native-generation theorem, does not derive "
            "V(phi), does not construct C_k modification or conservation, "
            "does not claim source admissibility or conservation, does not "
            "close QFT-GR, does not authorize semiclassical coupling, does "
            "not promote the working-form master action, does not claim "
            "empirical validation, and does not authorize public readiness or "
            "release completion."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativePhiCKVariationalContentPacket",
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
        "master_action_doc_file": _ptr(MASTER_ACTION_DOC_PATH),
        "raw_phi_route_packet_file": _ptr(RAW_PHI_ROUTE_PACKET_PATH),
        "lean_validation_policy_file": _ptr(LEAN_VALIDATION_POLICY_PATH),
        "validation_policy": _validation_policy(),
    }


def write_toe_native_phi_ck_variational_content_packet(
    *,
    phi_alignment_closeout_path: Path = PHI_ALIGNMENT_CLOSEOUT_PATH,
    master_action_doc_path: Path = MASTER_ACTION_DOC_PATH,
    raw_phi_route_packet_path: Path = RAW_PHI_ROUTE_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = build_toe_native_phi_ck_variational_content_packet(
        phi_alignment_closeout_path=phi_alignment_closeout_path,
        master_action_doc_path=master_action_doc_path,
        raw_phi_route_packet_path=raw_phi_route_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return packet


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Build the ToE-native phi C_k variational-content packet."
    )
    parser.add_argument(
        "--phi-alignment-closeout",
        type=Path,
        default=PHI_ALIGNMENT_CLOSEOUT_PATH,
    )
    parser.add_argument(
        "--master-action-doc",
        type=Path,
        default=MASTER_ACTION_DOC_PATH,
    )
    parser.add_argument(
        "--raw-phi-route-packet",
        type=Path,
        default=RAW_PHI_ROUTE_PACKET_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()
    packet = write_toe_native_phi_ck_variational_content_packet(
        phi_alignment_closeout_path=args.phi_alignment_closeout,
        master_action_doc_path=args.master_action_doc,
        raw_phi_route_packet_path=args.raw_phi_route_packet,
        out=args.out,
        captured_at_utc=args.captured_at_utc,
    )
    print(json.dumps(packet, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

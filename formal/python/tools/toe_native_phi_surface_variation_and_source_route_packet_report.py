from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_action_derivability_retry_with_provisional_matter_sector_report import (
    SCALAR_LAGRANGIAN as IMPORTED_SCALAR_LAGRANGIAN,
    STRESS_ENERGY_COVARIANT_EXPRESSION as IMPORTED_STRESS_ENERGY_COVARIANT_EXPRESSION,
)
from formal.python.tools.toe_native_matter_sector_calculation_route_selection_report import (
    DEFAULT_OUT as ROUTE_SELECTION_PATH,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as ROUTE_SELECTION_OUTCOME,
    ROUTE_SELECTION_RESULT,
    SCHEMA_ID as ROUTE_SELECTION_SCHEMA_ID,
    SELECTED_ROUTE_ID,
    SELECTED_SURFACE_SYMBOL,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-18T00:00:00Z"

SCHEMA_ID = "TOE_NATIVE_PHI_SURFACE_VARIATION_AND_SOURCE_ROUTE_PACKET_20260618_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_PHI_SURFACE_VARIATION_AND_SOURCE_ROUTE_PACKET_v0"
PHI_ROUTE_PACKET_RESULT = (
    "TOE_NATIVE_PHI_SURFACE_VARIATION_AND_SOURCE_ROUTE_PACKET_PREPARED_"
    "RAW_VARIATION_RECORDED_SOURCE_ROUTE_BLOCKED_FOR_NATIVE_DERIVATION"
)
OUTCOME_ID = PHI_ROUTE_PACKET_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_phi_surface_variation_and_source_route_packet_records_raw_"
    "master_action_phi_variation_and_blocks_native_source_derivation"
)
NEXT_TARGET = "review_toe_native_phi_surface_variation_and_source_route_result"
NEXT_TARGET_KIND = "toe_native_phi_surface_variation_and_source_route_result_review"
LEAN_VALIDATION_POLICY_ID = "TIERED_LEAN_VALIDATION_POLICY_FOR_PACKET_WORK_v0"

MASTER_ACTION_DOC_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_CANDIDATE_MASTER_ACTION_v0.md"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_PHI_SURFACE_VARIATION_AND_SOURCE_ROUTE_PACKET_20260618_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativePhiSurfaceVariationAndSourceRoutePacket.lean"
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

MASTER_ACTION_PHI_SURFACE_TERM = (
    "(1/2) * sum_i nabla_mu(phi_i) * nabla^mu(phi_i) - V(phi)"
)
MASTER_PHI_LAGRANGIAN = (
    "L_phi^MA = 1/2 sum_i g^{mu nu} nabla_mu phi_i nabla_nu phi_i - V(phi)"
)
MASTER_PHI_ACTION = (
    "S_phi^MA[g, phi] = integral_M sqrt(-g) L_phi^MA d^4x"
)
METRIC_SIGNATURE_DECISION = (
    "not_explicitly_fixed_in_master_action; the written +1/2 kinetic sign is "
    "compatible with a mostly-minus convention, while the imported scalar "
    "sandbox used an explicit -1/2 kinetic convention"
)
PHI_VARIATION_RAW_EQUATION = (
    "E_i^phi,MA = -Box_g phi_i - partial_i V(phi) + "
    "sum_k lambda_k delta C_k/delta phi_i = 0"
)
PHI_VARIATION_NO_SEAM_EQUATION = "Box_g phi_i + partial_i V(phi) = 0"
PHI_VARIATION_WITH_SEAM_ROUTE = (
    "Box_g phi_i + partial_i V(phi) = "
    "sum_k lambda_k delta C_k/delta phi_i, if the C_k variational "
    "derivatives exist with the stated sign convention"
)
METRIC_VARIATION_RAW_FORM = (
    "delta S_phi^MA(k) = integral_M sqrt(-g) "
    "[1/2 sum_i nabla_mu phi_i nabla_nu phi_i - "
    "1/2 g_{mu nu} L_phi^MA] k^{mu nu} d^4x"
)
MASTER_STRESS_ENERGY_CANDIDATE = (
    "T^MA_{mu nu} = -sum_i nabla_mu phi_i nabla_nu phi_i + "
    "g_{mu nu}(1/2 sum_i nabla_alpha phi_i nabla^alpha phi_i - V(phi))"
)
SEAM_STRESS_ENERGY_CONTRIBUTION = (
    "T^C_{mu nu} = -2/sqrt(-g) delta integral_M sqrt(-g) "
    "sum_k lambda_k C_k(g, psi, A, phi, rho) / delta g^{mu nu}"
)
SOURCE_ROUTE_STATUS_DECISION = (
    "raw_stress_energy_candidate_recorded_but_source_route_blocked_for_"
    "toe_native_status"
)
IMPORTED_SCALAR_COMPARISON_DECISION = (
    "matches_imported_scalar_witness_only_after_explicit_signature_and_"
    "kinetic_sign_normalization_and_after_setting_C_k_variations_to_zero"
)
TOE_NATIVE_STATUS_DECISION = (
    "declared_or_imported_master_action_surface_not_constraint_generated"
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


def _route_questions() -> list[dict[str, Any]]:
    return [
        {
            "question_id": "q1_master_action_scalar_term_defined",
            "status": "partially_defined",
            "answer": (
                "The phi surface term is syntactically present, but a full "
                "mathematical definition still requires field bundle/index-set, "
                "regularity, potential-domain, boundary, and seam-constraint "
                "policies."
            ),
            "evidence": MASTER_ACTION_PHI_SURFACE_TERM,
        },
        {
            "question_id": "q2_metric_signature_used",
            "status": "blocked_pending_explicit_convention",
            "answer": METRIC_SIGNATURE_DECISION,
            "evidence": "sqrt(-g) and the +1/2 phi kinetic sign in the master action",
        },
        {
            "question_id": "q3_exact_scalar_lagrangian",
            "status": "recorded",
            "answer": MASTER_PHI_LAGRANGIAN,
            "evidence": MASTER_ACTION_PHI_SURFACE_TERM,
        },
        {
            "question_id": "q4_phi_variation",
            "status": "raw_symbolic_variation_recorded",
            "answer": PHI_VARIATION_RAW_EQUATION,
            "evidence": PHI_VARIATION_NO_SEAM_EQUATION,
        },
        {
            "question_id": "q5_metric_variation",
            "status": "raw_symbolic_metric_variation_recorded",
            "answer": METRIC_VARIATION_RAW_FORM,
            "evidence": MASTER_STRESS_ENERGY_CANDIDATE,
        },
        {
            "question_id": "q6_imported_scalar_sandbox_reproduction",
            "status": "partial_after_convention_normalization_only",
            "answer": IMPORTED_SCALAR_COMPARISON_DECISION,
            "evidence": IMPORTED_SCALAR_LAGRANGIAN,
        },
        {
            "question_id": "q7_seam_constraint_modification",
            "status": "blocked_pending_C_k_definition",
            "answer": (
                "The seam terms can modify both the phi equation and the metric "
                "source through variational derivatives of C_k, but C_k is not "
                "specified enough to compute those terms."
            ),
            "evidence": [
                PHI_VARIATION_WITH_SEAM_ROUTE,
                SEAM_STRESS_ENERGY_CONTRIBUTION,
            ],
        },
        {
            "question_id": "q8_native_or_copied",
            "status": "not_native_derived",
            "answer": TOE_NATIVE_STATUS_DECISION,
            "evidence": (
                "No constraint-generation theorem, regime-emergence map, or "
                "uniqueness argument is supplied."
            ),
        },
        {
            "question_id": "q9_remaining_unproved",
            "status": "retained_blockers",
            "answer": (
                "signature, scalar index/domain, potential regularity, Green "
                "identity, boundary, C_k variational derivatives, source "
                "admissibility, conservation with seams, quantum expectation, "
                "and empirical content remain unproved."
            ),
            "evidence": "retained_phi_route_blocker_list",
        },
    ]


def _calculation_steps() -> list[dict[str, Any]]:
    return [
        {
            "step_id": "isolate_master_phi_surface",
            "mathematical_content": MASTER_PHI_ACTION,
            "claim": "candidate master-action phi surface isolated",
        },
        {
            "step_id": "record_signature_status",
            "mathematical_content": METRIC_SIGNATURE_DECISION,
            "claim": "signature is a blocker for exact scalar-sandbox comparison",
        },
        {
            "step_id": "vary_phi",
            "mathematical_content": PHI_VARIATION_RAW_EQUATION,
            "claim": "raw Euler-Lagrange route recorded under compact-support boundary policy",
        },
        {
            "step_id": "remove_seam_terms_for_reference_slice",
            "mathematical_content": PHI_VARIATION_NO_SEAM_EQUATION,
            "claim": "unconstrained master phi slice gives the sign-normalized scalar equation",
        },
        {
            "step_id": "vary_inverse_metric",
            "mathematical_content": METRIC_VARIATION_RAW_FORM,
            "claim": "raw inverse-metric variation recorded",
        },
        {
            "step_id": "read_raw_stress_energy_candidate",
            "mathematical_content": MASTER_STRESS_ENERGY_CANDIDATE,
            "claim": "stress-energy candidate is convention-dependent and not source-admissible yet",
        },
        {
            "step_id": "compare_imported_scalar_witness",
            "mathematical_content": IMPORTED_SCALAR_COMPARISON_DECISION,
            "claim": "comparison is partial and requires convention normalization",
        },
        {
            "step_id": "retain_native_derivation_blocker",
            "mathematical_content": TOE_NATIVE_STATUS_DECISION,
            "claim": "the master-action phi term is not generated by ToE principles in this packet",
        },
    ]


def _retained_blockers() -> list[dict[str, Any]]:
    return [
        {
            "blocker_id": "phi_metric_signature_convention_missing",
            "status": "retained",
            "reason": "The master action does not explicitly bind the scalar sign convention to a metric signature.",
        },
        {
            "blocker_id": "phi_field_content_and_index_set_missing",
            "status": "retained",
            "reason": "The number, bundle/type, and admitted domain of phi_i are not derived.",
        },
        {
            "blocker_id": "phi_potential_not_generated",
            "status": "retained",
            "reason": "V(phi) is named but not derived, constrained, or regularity-controlled.",
        },
        {
            "blocker_id": "seam_constraints_variational_content_missing",
            "status": "retained",
            "reason": "C_k has no concrete variational derivative with respect to phi or g.",
        },
        {
            "blocker_id": "source_admissibility_not_established",
            "status": "retained",
            "reason": "A raw metric variation formula is not a completed legal gravity source route.",
        },
        {
            "blocker_id": "native_generation_rule_missing",
            "status": "retained",
            "reason": "No theorem forces the phi scalar action from ToE-native rules.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "toe_native_phi_surface_variation_and_source_route_packet",
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


def build_toe_native_phi_surface_variation_and_source_route_packet(
    *,
    route_selection_path: Path = ROUTE_SELECTION_PATH,
    master_action_doc_path: Path = MASTER_ACTION_DOC_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    route_selection = _read_json(route_selection_path)
    master_action_doc = _read_text(master_action_doc_path)
    questions = _route_questions()
    steps = _calculation_steps()
    blockers = _retained_blockers()
    acceptance_criteria = {
        "consumes_expected_phi_packet_target": (
            route_selection.get("schema_id") == ROUTE_SELECTION_SCHEMA_ID
            and route_selection.get("outcome_id") == ROUTE_SELECTION_OUTCOME
            and route_selection.get("selected_next_target") == CONSUMED_TARGET
        ),
        "route_selection_selects_phi_surface": (
            route_selection.get("selected_surface_symbol") == SELECTED_SURFACE_SYMBOL
            and route_selection.get("selected_route_id") == SELECTED_ROUTE_ID
        ),
        "master_action_phi_surface_present": (
            MASTER_ACTION_PHI_SURFACE_TERM in master_action_doc
            and "sum_k lambda_k * C_k(g, psi, A, phi, rho)" in master_action_doc
        ),
        "scalar_lagrangian_recorded": MASTER_PHI_LAGRANGIAN.startswith("L_phi^MA"),
        "metric_signature_status_recorded": (
            "not_explicitly_fixed" in METRIC_SIGNATURE_DECISION
        ),
        "raw_phi_variation_recorded": "E_i^phi,MA" in PHI_VARIATION_RAW_EQUATION,
        "raw_metric_variation_recorded": "delta S_phi^MA" in METRIC_VARIATION_RAW_FORM,
        "raw_stress_energy_candidate_recorded": (
            "T^MA_{mu nu}" in MASTER_STRESS_ENERGY_CANDIDATE
        ),
        "seam_modification_blocked_pending_C_k": (
            "delta C_k/delta phi_i" in PHI_VARIATION_WITH_SEAM_ROUTE
            and "delta integral_M" in SEAM_STRESS_ENERGY_CONTRIBUTION
        ),
        "imported_scalar_comparison_is_partial": (
            "after_explicit_signature" in IMPORTED_SCALAR_COMPARISON_DECISION
        ),
        "questions_all_answered": len(questions) == 9,
        "retained_blockers_recorded": len(blockers) == 6,
        "no_toe_native_derivation_claim": True,
        "no_source_admissibility_or_conservation_claim": True,
        "no_qft_gr_or_semiclassical_closure": True,
        "no_master_action_promotion": True,
    }
    prepared = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if prepared
        else "REMEDIATE_TOE_NATIVE_PHI_SURFACE_VARIATION_AND_SOURCE_ROUTE_PACKET"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_PHI_ROUTE_PREPARATION_PACKET",
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "accepted": prepared,
        "outcome_id": OUTCOME_ID
        if prepared
        else "TOE_NATIVE_PHI_SURFACE_VARIATION_AND_SOURCE_ROUTE_PACKET_REQUIRES_REMEDIATION",
        "phi_route_packet_result": PHI_ROUTE_PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "route_selection_result": ROUTE_SELECTION_RESULT,
        "selected_surface_symbol": SELECTED_SURFACE_SYMBOL,
        "selected_route_id": SELECTED_ROUTE_ID,
        "master_action_doc": _ptr(master_action_doc_path),
        "master_action_phi_surface_term": MASTER_ACTION_PHI_SURFACE_TERM,
        "master_phi_action": MASTER_PHI_ACTION,
        "master_phi_lagrangian": MASTER_PHI_LAGRANGIAN,
        "metric_signature_decision": METRIC_SIGNATURE_DECISION,
        "phi_variation_raw_equation": PHI_VARIATION_RAW_EQUATION,
        "phi_variation_no_seam_equation": PHI_VARIATION_NO_SEAM_EQUATION,
        "phi_variation_with_seam_route": PHI_VARIATION_WITH_SEAM_ROUTE,
        "metric_variation_raw_form": METRIC_VARIATION_RAW_FORM,
        "master_stress_energy_candidate": MASTER_STRESS_ENERGY_CANDIDATE,
        "seam_stress_energy_contribution": SEAM_STRESS_ENERGY_CONTRIBUTION,
        "source_route_status_decision": SOURCE_ROUTE_STATUS_DECISION,
        "imported_scalar_lagrangian": IMPORTED_SCALAR_LAGRANGIAN,
        "imported_scalar_stress_energy_covariant_expression": (
            IMPORTED_STRESS_ENERGY_COVARIANT_EXPRESSION
        ),
        "imported_scalar_comparison_decision": IMPORTED_SCALAR_COMPARISON_DECISION,
        "toe_native_status_decision": TOE_NATIVE_STATUS_DECISION,
        "route_questions": questions,
        "route_question_count": len(questions),
        "calculation_steps": steps,
        "calculation_step_count": len(steps),
        "retained_blockers": blockers,
        "retained_blocker_count": len(blockers),
        "phi_surface_variation_route_prepared": prepared,
        "raw_phi_variation_formula_recorded": True,
        "raw_metric_variation_formula_recorded": True,
        "stress_energy_candidate_formula_recorded": True,
        "symbolic_calculation_recorded": True,
        "formal_theorem_backed_matter_derivation": False,
        "record_validated": True,
        "proof_depth_label": "SYMBOLIC_CALCULATION_RECORDED_STATUS_MARKER_VALIDATED",
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
        "accepted_outcomes_considered": [
            PHI_ROUTE_PACKET_RESULT,
            (
                "TOE_NATIVE_PHI_ROUTE_BLOCKED_BY_MISSING_SIGNATURE_OR_"
                "FIELD_DOMAIN_POLICY"
            ),
            "TOE_NATIVE_PHI_ROUTE_BLOCKED_BY_MISSING_SEAM_VARIATIONAL_CONTENT",
        ],
        "critical_gate_fail_conditions": [
            "ToE-native matter derivation",
            "ToE-native phi source admissibility",
            "ToE-native phi source conservation",
            "Standard Model derivation",
            "QFT-GR closure",
            "semiclassical coupling",
            "canonical master-action promotion",
            "empirical validation",
            "public readiness",
            "imported scalar witness promoted as native derivation",
        ],
        "downstream_progression": [
            {
                "stage": "phi_surface_route_packet",
                "status": "RAW_VARIATION_RECORDED_NATIVE_ROUTE_BLOCKED",
                "decision": PHI_ROUTE_PACKET_RESULT,
                "reason": (
                    "The master-action phi term can be varied symbolically, but "
                    "its source status is blocked by signature, C_k, and native "
                    "generation gaps."
                ),
            },
            {
                "stage": "phi_route_result_review",
                "status": "NEXT_TARGET_AUTHORIZED",
                "decision": selected_next_target,
                "reason": (
                    "The packet should be reviewed before any native-source "
                    "comparison, conservation, or source-admissibility claim."
                ),
            },
        ],
        "mathematical_statement": (
            "For the working-form master-action phi surface "
            + MASTER_PHI_LAGRANGIAN
            + ", compactly supported phi variation records "
            + PHI_VARIATION_RAW_EQUATION
            + ". In the no-seam reference slice this reduces to "
            + PHI_VARIATION_NO_SEAM_EQUATION
            + ". Inverse-metric variation records "
            + METRIC_VARIATION_RAW_FORM
            + " and the raw candidate "
            + MASTER_STRESS_ENERGY_CANDIDATE
            + ". These formulas do not by themselves derive ToE-native matter "
            "or a legal gravity source because signature, C_k, source "
            "admissibility, conservation, and native-generation obligations "
            "remain open."
        ),
        "non_claim_boundary": (
            "This packet records a raw symbolic variation/source route for the "
            "candidate master-action phi surface only. It does not claim a "
            "ToE-native matter derivation, does not promote the imported scalar "
            "sandbox to native status, does not establish source admissibility "
            "or conservation, does not close QFT-GR, does not authorize "
            "semiclassical coupling, does not derive the Standard Model, does "
            "not promote the master action, and does not claim empirical "
            "validation, public readiness, or release authorization."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativePhiSurfaceVariationAndSourceRoutePacket",
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
        "acceptance_criteria": acceptance_criteria,
    }


def write_toe_native_phi_surface_variation_and_source_route_packet(
    *,
    route_selection_path: Path = ROUTE_SELECTION_PATH,
    master_action_doc_path: Path = MASTER_ACTION_DOC_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_toe_native_phi_surface_variation_and_source_route_packet(
        route_selection_path=route_selection_path,
        master_action_doc_path=master_action_doc_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the ToE-native phi surface variation/source route packet."
    )
    parser.add_argument("--route-selection", type=Path, default=ROUTE_SELECTION_PATH)
    parser.add_argument("--master-action-doc", type=Path, default=MASTER_ACTION_DOC_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    route_selection_path = (
        args.route_selection
        if args.route_selection.is_absolute()
        else REPO_ROOT / args.route_selection
    )
    master_action_doc_path = (
        args.master_action_doc
        if args.master_action_doc.is_absolute()
        else REPO_ROOT / args.master_action_doc
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = write_toe_native_phi_surface_variation_and_source_route_packet(
        route_selection_path=route_selection_path,
        master_action_doc_path=master_action_doc_path,
        out=out,
        captured_at_utc=args.captured_at_utc,
    )
    print(
        "toe_native_phi_surface_variation_and_source_route_packet_report: "
        f"wrote {out} outcome={payload['outcome_id']} "
        f"next={payload['selected_next_target']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

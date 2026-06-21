from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.master_action_surface_selection_after_phi_ck_triad_report import (
    DEFAULT_OUT as SURFACE_SELECTION_PATH,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as SURFACE_SELECTION_OUTCOME,
    PACKET_ID as SURFACE_SELECTION_PACKET_ID,
    SCHEMA_ID as SURFACE_SELECTION_SCHEMA_ID,
    SELECTED_MASTER_ACTION_SURFACE,
    SELECTED_ROUTE_ID,
    SELECTED_SURFACE_SYMBOL,
    SELECTION_RESULT,
)
from formal.python.tools.phi_ck_source_bridge_transport_rule_family_closeout_report import (
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_RULE_DISPLAY_FORM,
    TRANSPORT_RULE_DISPLAY_FORM,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-21T00:00:00Z"

SCHEMA_ID = "TOE_NATIVE_A_SURFACE_VARIATION_AND_SOURCE_ROUTE_PACKET_20260621_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_A_SURFACE_VARIATION_AND_SOURCE_ROUTE_PACKET_v0"
A_SURFACE_ROUTE_PACKET_RESULT = (
    "TOE_NATIVE_A_SURFACE_VARIATION_AND_SOURCE_ROUTE_PACKET_PREPARED_"
    "RAW_GAUGE_VARIATION_RECORDED_SOURCE_ROUTE_BLOCKED_PENDING_"
    "GAUGE_GROUP_CURRENT_DOMAIN_AND_CK_CONTENT"
)
OUTCOME_ID = A_SURFACE_ROUTE_PACKET_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_A_surface_variation_and_source_route_packet_records_raw_"
    "gauge_route_and_blocks_source_route_pending_gauge_group_current_domain_"
    "and_ck_content"
)
NEXT_TARGET = "review_toe_native_A_surface_variation_and_source_route_result"
NEXT_TARGET_KIND = "toe_native_A_surface_variation_and_source_route_result_review"
LEAN_VALIDATION_POLICY_ID = "TIERED_LEAN_VALIDATION_POLICY_FOR_PACKET_WORK_v0"

MASTER_ACTION_DOC_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_CANDIDATE_MASTER_ACTION_v0.md"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_A_SURFACE_VARIATION_AND_SOURCE_ROUTE_PACKET_20260621_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativeASurfaceVariationAndSourceRoutePacket.lean"
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

MASTER_ACTION_A_SURFACE_TERM = "- (1/4) * F_{mu nu} * F^{mu nu}"
MASTER_A_ACTION = "S_A[g, A] = integral_M dVol_g [-1/4 F_{mu nu} F^{mu nu}]"
MASTER_A_LAGRANGIAN = "L_A^MA = -1/4 F_{mu nu} F^{mu nu}"
RAW_GAUGE_ROUTE = "A_mu -> F_{mu nu}"
RAW_VARIATION_ROUTE = "delta S_A / delta A_nu -> nabla_mu F^{mu nu}"
SOURCE_FORM_ROUTE_SHAPE = "nabla_mu F^{mu nu} = J^nu"
SOURCE_FORM_ROUTE_STATUS = (
    "route_shape_only_not_derived_pending_gauge_group_current_domain_and_ck_content"
)
GAUGE_ROUTE_STATUS_DECISION = (
    "raw_gauge_variation_recorded_but_source_route_blocked_for_native_status"
)
TOE_NATIVE_STATUS_DECISION = (
    "A_surface_has_recognizable_gauge_action_route_but_native_current_source_"
    "route_not_derived"
)
PHI_CK_TRIAD_CONTEXT = [
    SOURCE_RULE_DISPLAY_FORM,
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    TRANSPORT_RULE_DISPLAY_FORM,
]


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
            "question_id": "q1_master_action_gauge_term_defined",
            "status": "surface_indexed",
            "answer": (
                "The master action contains the gauge surface term, but it has "
                "not selected the gauge group, A-domain, F-definition, current "
                "semantics, or C_k analogues needed for a native source route."
            ),
            "evidence": MASTER_ACTION_A_SURFACE_TERM,
        },
        {
            "question_id": "q2_raw_gauge_route",
            "status": "raw_route_shape_recorded",
            "answer": RAW_GAUGE_ROUTE,
            "evidence": MASTER_A_ACTION,
        },
        {
            "question_id": "q3_raw_variation_route",
            "status": "raw_variation_shape_recorded",
            "answer": RAW_VARIATION_ROUTE,
            "evidence": MASTER_A_LAGRANGIAN,
        },
        {
            "question_id": "q4_source_form_route",
            "status": "route_shape_only_not_derived",
            "answer": SOURCE_FORM_ROUTE_SHAPE,
            "evidence": SOURCE_FORM_ROUTE_STATUS,
        },
        {
            "question_id": "q5_current_domain",
            "status": "blocked_pending_current_policy",
            "answer": (
                "A coupled current J^nu is not admitted until matter-current "
                "derivation or external-current policy and domain rules are "
                "selected."
            ),
            "evidence": "matter-current J^nu derived=false; external-current policy selected=false",
        },
        {
            "question_id": "q6_ck_analogues",
            "status": "blocked_pending_C_k_analogues",
            "answer": (
                "The phi source/bridge/transport triad is retained only as a "
                "template; no A-specific C_k source, bridge, transport, gauge, "
                "or current-conservation analogue is constructed here."
            ),
            "evidence": PHI_CK_TRIAD_CONTEXT,
        },
        {
            "question_id": "q7_remaining_unproved",
            "status": "retained_blockers",
            "answer": (
                "Gauge group, A bundle/domain, F definition, D_mu convention, "
                "current semantics, gauge fixing, boundary terms, stress-energy, "
                "source admissibility, current conservation, and C_k analogues "
                "remain open."
            ),
            "evidence": "retained_A_surface_route_blocker_list",
        },
    ]


def _calculation_steps() -> list[dict[str, Any]]:
    return [
        {
            "step_id": "isolate_master_A_surface",
            "mathematical_content": MASTER_A_ACTION,
            "claim": "candidate master-action A gauge surface isolated",
        },
        {
            "step_id": "record_raw_A_to_F_route",
            "mathematical_content": RAW_GAUGE_ROUTE,
            "claim": "raw gauge-potential to field-strength route recorded",
        },
        {
            "step_id": "record_raw_variation_shape",
            "mathematical_content": RAW_VARIATION_ROUTE,
            "claim": "raw Euler-Lagrange source-route shape recorded, not derived",
        },
        {
            "step_id": "record_future_current_route_shape",
            "mathematical_content": SOURCE_FORM_ROUTE_SHAPE,
            "claim": "current/source equation recorded as expected shape only",
        },
        {
            "step_id": "retain_gauge_structure_blockers",
            "mathematical_content": (
                "gauge group, A-domain, F-definition, D_mu convention, gauge "
                "fixing, and boundary controls are not selected"
            ),
            "claim": "native gauge variation remains blocked by missing structure",
        },
        {
            "step_id": "retain_source_route_blockers",
            "mathematical_content": (
                "J^nu, source admissibility, current conservation, stress-energy, "
                "and C_k analogues are not derived"
            ),
            "claim": "native current/source route remains blocked",
        },
    ]


def _retained_blockers() -> list[dict[str, Any]]:
    return [
        {
            "blocker_id": "gauge_group_not_selected",
            "status": "retained",
            "reason": "The packet does not select U(1), nonabelian Yang-Mills, or another gauge group.",
        },
        {
            "blocker_id": "bundle_domain_for_A_not_selected",
            "status": "retained",
            "reason": "The admissible bundle, regularity class, and domain for A_mu are not fixed.",
        },
        {
            "blocker_id": "definition_of_F_not_selected",
            "status": "retained",
            "reason": "F is named by the surface term, but abelian/nonabelian curvature conventions are not selected.",
        },
        {
            "blocker_id": "covariant_derivative_D_mu_convention_not_selected",
            "status": "retained",
            "reason": "The derivative convention for charged matter and gauge curvature is not fixed.",
        },
        {
            "blocker_id": "matter_current_J_nu_not_derived",
            "status": "retained",
            "reason": "No matter-sector variation derives a current J^nu in this packet.",
        },
        {
            "blocker_id": "external_current_policy_not_selected",
            "status": "retained",
            "reason": "The repo has not selected whether an external current is admissible for this route.",
        },
        {
            "blocker_id": "gauge_fixing_not_selected",
            "status": "retained",
            "reason": "No gauge-fixing convention or gauge-equivalence handling is selected.",
        },
        {
            "blocker_id": "boundary_terms_not_controlled",
            "status": "retained",
            "reason": "Boundary terms from the raw variation are not controlled by a selected boundary policy.",
        },
        {
            "blocker_id": "stress_energy_T_A_not_derived",
            "status": "retained",
            "reason": "The gauge stress-energy route is not varied or admitted as a legal source.",
        },
        {
            "blocker_id": "source_admissibility_not_proved",
            "status": "retained",
            "reason": "The packet records source-route shape only and proves no source-admissibility condition.",
        },
        {
            "blocker_id": "current_conservation_not_proved",
            "status": "retained",
            "reason": "No continuity equation or gauge-current conservation witness is proved.",
        },
        {
            "blocker_id": "C_k_analogues_not_constructed",
            "status": "retained",
            "reason": "No A-specific source, bridge, transport, gauge, or current C_k rule is constructed.",
        },
        {
            "blocker_id": "EM_closure_not_claimed",
            "status": "retained",
            "reason": "The packet does not derive Maxwell or Yang-Mills equations or close EM.",
        },
        {
            "blocker_id": "QFT_GR_closure_not_claimed",
            "status": "retained",
            "reason": "The packet does not close QFT-GR or establish a gravitational source route.",
        },
        {
            "blocker_id": "master_action_promotion_not_claimed",
            "status": "retained",
            "reason": "The working-form master action remains unpromoted and non-canonical.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "toe_native_A_surface_variation_and_source_route_packet",
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


def build_toe_native_a_surface_variation_and_source_route_packet(
    *,
    surface_selection_path: Path = SURFACE_SELECTION_PATH,
    master_action_doc_path: Path = MASTER_ACTION_DOC_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    surface_selection = _read_json(surface_selection_path)
    master_action_doc = _read_text(master_action_doc_path)
    questions = _route_questions()
    steps = _calculation_steps()
    blockers = _retained_blockers()
    acceptance_criteria = {
        "consumes_expected_A_packet_target": (
            surface_selection.get("schema_id") == SURFACE_SELECTION_SCHEMA_ID
            and surface_selection.get("packet_id") == SURFACE_SELECTION_PACKET_ID
            and surface_selection.get("outcome_id") == SURFACE_SELECTION_OUTCOME
            and surface_selection.get("selection_result") == SELECTION_RESULT
            and surface_selection.get("selected_next_target") == CONSUMED_TARGET
            and surface_selection.get("accepted") is True
        ),
        "surface_selection_selects_A_surface": (
            surface_selection.get("selected_master_action_surface")
            == SELECTED_MASTER_ACTION_SURFACE
            and surface_selection.get("selected_surface_symbol")
            == SELECTED_SURFACE_SYMBOL
            and surface_selection.get("selected_route_id") == SELECTED_ROUTE_ID
        ),
        "master_action_A_surface_present": (
            MASTER_ACTION_A_SURFACE_TERM in master_action_doc
            and "intended as EM/gauge-field surface" in master_action_doc
            and "sum_k lambda_k * C_k(g, psi, A, phi, rho)" in master_action_doc
        ),
        "raw_A_to_F_route_recorded": RAW_GAUGE_ROUTE == "A_mu -> F_{mu nu}",
        "raw_variation_shape_recorded": "nabla_mu F^{mu nu}" in RAW_VARIATION_ROUTE,
        "source_form_route_shape_only": (
            SOURCE_FORM_ROUTE_SHAPE == "nabla_mu F^{mu nu} = J^nu"
            and "route_shape_only" in SOURCE_FORM_ROUTE_STATUS
        ),
        "questions_all_answered": len(questions) == 7,
        "retained_blockers_recorded": len(blockers) == 15,
        "no_gauge_group_or_current_domain_selected": True,
        "no_source_admissibility_or_current_conservation_claim": True,
        "no_ck_analogues_or_em_closure": True,
        "no_qft_gr_or_master_action_promotion": True,
    }
    prepared = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if prepared
        else "REMEDIATE_TOE_NATIVE_A_SURFACE_VARIATION_AND_SOURCE_ROUTE_PACKET"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_A_SURFACE_ROUTE_PREPARATION_PACKET",
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "accepted": prepared,
        "outcome_id": OUTCOME_ID
        if prepared
        else "TOE_NATIVE_A_SURFACE_VARIATION_AND_SOURCE_ROUTE_PACKET_REQUIRES_REMEDIATION",
        "a_surface_route_packet_result": A_SURFACE_ROUTE_PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "surface_selection_result": SELECTION_RESULT,
        "selected_master_action_surface": SELECTED_MASTER_ACTION_SURFACE,
        "selected_surface_symbol": SELECTED_SURFACE_SYMBOL,
        "selected_route_id": SELECTED_ROUTE_ID,
        "master_action_doc": _ptr(master_action_doc_path),
        "master_action_A_surface_term": MASTER_ACTION_A_SURFACE_TERM,
        "master_A_action": MASTER_A_ACTION,
        "master_A_lagrangian": MASTER_A_LAGRANGIAN,
        "raw_gauge_route": RAW_GAUGE_ROUTE,
        "raw_variation_route": RAW_VARIATION_ROUTE,
        "source_form_route_shape": SOURCE_FORM_ROUTE_SHAPE,
        "source_form_route_status": SOURCE_FORM_ROUTE_STATUS,
        "gauge_route_status_decision": GAUGE_ROUTE_STATUS_DECISION,
        "toe_native_status_decision": TOE_NATIVE_STATUS_DECISION,
        "phi_ck_triad_template_context": PHI_CK_TRIAD_CONTEXT,
        "route_questions": questions,
        "route_question_count": len(questions),
        "calculation_steps": steps,
        "calculation_step_count": len(steps),
        "retained_blockers": blockers,
        "retained_blocker_count": len(blockers),
        "a_surface_variation_route_prepared": prepared,
        "a_surface_indexed": True,
        "raw_gauge_variation_formula_recorded": True,
        "raw_A_to_F_route_recorded": True,
        "raw_variation_shape_recorded": True,
        "source_route_shape_recorded": True,
        "source_route_shape_only_not_derived": True,
        "symbolic_calculation_recorded": True,
        "formal_theorem_backed_gauge_derivation": False,
        "a_surface_variation_executed": False,
        "a_surface_variation_route_executed": False,
        "gauge_group_selected": False,
        "bundle_domain_for_A_selected": False,
        "definition_of_F_selected": False,
        "covariant_derivative_D_mu_convention_selected": False,
        "matter_current_J_nu_derived": False,
        "external_current_policy_selected": False,
        "gauge_fixing_selected": False,
        "boundary_terms_controlled": False,
        "stress_energy_T_A_derived": False,
        "source_admissibility_proved": False,
        "current_conservation_proved": False,
        "gauge_current_constraint_proved": False,
        "C_k_analogues_constructed": False,
        "source_bridge_transport_ck_analogues_constructed": False,
        "maxwell_equations_derived": False,
        "yang_mills_equations_derived": False,
        "field_equations_derived": False,
        "gauge_field_derived": False,
        "gauge_surface_derived": False,
        "current_source_route_constructed": False,
        "stress_energy_route_constructed": False,
        "stress_energy_source_admissibility_proved": False,
        "toe_native_gauge_derivation_claimed": False,
        "toe_native_A_source_route_constructed": False,
        "toe_native_A_source_admissibility_claimed": False,
        "toe_native_A_current_conservation_claimed": False,
        "source_admissibility_claimed": False,
        "source_admissibility_completed": False,
        "source_map_closed": False,
        "qft_gr_solved": False,
        "qft_gr_closure_claimed": False,
        "qft_gr_seam_closed": False,
        "qft_gr_source_map_closure_authorized": False,
        "em_closure_claimed": False,
        "em_qft_closure_claimed": False,
        "semiclassical_coupling_authorized": False,
        "semiclassical_coupling_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "semiclassical_source_established": False,
        "toe_native_matter_derivation_claimed": False,
        "standard_model_derivation_claimed": False,
        "empirical_validation_claimed": False,
        "public_readiness_claimed": False,
        "public_submission_authorized": False,
        "canonical_master_action_promoted": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "phase2_readiness_claim": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "record_validated": True,
        "proof_depth_label": "ROUTE_SHAPE_RECORDED_STATUS_MARKER_VALIDATED",
        "accepted_outcomes_considered": [
            A_SURFACE_ROUTE_PACKET_RESULT,
            (
                "TOE_NATIVE_A_SURFACE_VARIATION_AND_SOURCE_ROUTE_PACKET_"
                "PREPARED_A_SURFACE_INDEXED_GAUGE_SOURCE_ROUTE_BLOCKED_BY_"
                "MISSING_GAUGE_GROUP_CURRENT_AND_DOMAIN_POLICY"
            ),
        ],
        "critical_gate_fail_conditions": [
            "gauge group selected",
            "bundle/domain for A selected",
            "definition of F selected",
            "covariant derivative D_mu convention selected",
            "matter-current J^nu derived",
            "external-current policy selected",
            "gauge fixing selected",
            "boundary terms controlled",
            "stress-energy T_A derived",
            "source admissibility proved",
            "current conservation proved",
            "C_k analogues constructed",
            "EM closure claimed",
            "QFT-GR closure claimed",
            "master-action promotion claimed",
        ],
        "downstream_progression": [
            {
                "stage": "A_surface_route_packet",
                "status": "RAW_GAUGE_VARIATION_RECORDED_SOURCE_ROUTE_BLOCKED",
                "decision": A_SURFACE_ROUTE_PACKET_RESULT,
                "reason": (
                    "The A surface has a recognizable gauge-action route, but "
                    "the repo has not selected enough structure to derive a "
                    "native current/source route."
                ),
            },
            {
                "stage": "A_surface_route_result_review",
                "status": "NEXT_TARGET_AUTHORIZED",
                "decision": selected_next_target,
                "reason": (
                    "The packet should be reviewed before any Maxwell/Yang-Mills, "
                    "current-conservation, stress-energy, C_k analogue, or EM "
                    "closure claim."
                ),
            },
        ],
        "mathematical_statement": (
            "For the working-form master-action A surface "
            + MASTER_A_LAGRANGIAN
            + ", this packet records the raw route "
            + RAW_GAUGE_ROUTE
            + " and the raw variation/source-route shape "
            + RAW_VARIATION_ROUTE
            + ". The expected coupled-current form "
            + SOURCE_FORM_ROUTE_SHAPE
            + " is recorded as route shape only, not as a derivation. The "
            "native source route remains blocked pending gauge group, A-domain, "
            "F-definition, D_mu convention, current policy, boundary control, "
            "stress-energy, source-admissibility, current-conservation, and C_k "
            "analogue content."
        ),
        "non_claim_boundary": (
            "This packet records a raw gauge variation/source-route shape for "
            "the candidate master-action A surface only. It does not select a "
            "gauge group, does not select the A bundle/domain, does not define "
            "F, does not select a D_mu convention, does not derive J^nu, does "
            "not admit an external current, does not select gauge fixing, does "
            "not control boundary terms, does not derive T_A, does not prove "
            "source admissibility or current conservation, does not construct "
            "C_k analogues, does not derive Maxwell or Yang-Mills equations, "
            "does not close EM, QFT-GR, or EM-QFT, does not authorize "
            "semiclassical coupling, does not promote the master action, and "
            "does not claim empirical validation, public readiness, or release "
            "authorization."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativeASurfaceVariationAndSourceRoutePacket",
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


def write_toe_native_a_surface_variation_and_source_route_packet(
    *,
    surface_selection_path: Path = SURFACE_SELECTION_PATH,
    master_action_doc_path: Path = MASTER_ACTION_DOC_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_toe_native_a_surface_variation_and_source_route_packet(
        surface_selection_path=surface_selection_path,
        master_action_doc_path=master_action_doc_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the ToE-native A surface variation/source route packet."
    )
    parser.add_argument("--surface-selection", type=Path, default=SURFACE_SELECTION_PATH)
    parser.add_argument("--master-action-doc", type=Path, default=MASTER_ACTION_DOC_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    surface_selection_path = (
        args.surface_selection
        if args.surface_selection.is_absolute()
        else REPO_ROOT / args.surface_selection
    )
    master_action_doc_path = (
        args.master_action_doc
        if args.master_action_doc.is_absolute()
        else REPO_ROOT / args.master_action_doc
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = write_toe_native_a_surface_variation_and_source_route_packet(
        surface_selection_path=surface_selection_path,
        master_action_doc_path=master_action_doc_path,
        out=out,
        captured_at_utc=args.captured_at_utc,
    )
    print(
        "toe_native_a_surface_variation_and_source_route_packet_report: "
        f"wrote {out} outcome={payload['outcome_id']} "
        f"next={payload['selected_next_target']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

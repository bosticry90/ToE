from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.phi_ck_source_bridge_transport_rule_family_closeout_report import (
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    CLOSEOUT_RESULT as PHI_CK_TRIAD_CLOSEOUT_RESULT,
    DEFAULT_OUT as PHI_CK_TRIAD_CLOSEOUT_PATH,
    FIRST_TRIAD_FAMILY_CLASSIFICATION,
    FULL_TOEFORMAL_AGGREGATE_STATUS,
    LEAN_VALIDATION_POLICY_ID,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as PHI_CK_TRIAD_CLOSEOUT_OUTCOME,
    PACKET_ID as PHI_CK_TRIAD_CLOSEOUT_PACKET_ID,
    RECOMMENDED_NEXT_MASTER_ACTION_SURFACE,
    RULE_FAMILY_CLASSIFICATION,
    SCHEMA_ID as PHI_CK_TRIAD_CLOSEOUT_SCHEMA_ID,
    SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
    SOURCE_RULE_DISPLAY_FORM,
    TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
    TRANSPORT_RULE_DISPLAY_FORM,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-19T00:00:00Z"

SCHEMA_ID = "MASTER_ACTION_SURFACE_SELECTION_AFTER_PHI_CK_TRIAD_20260619_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "MASTER_ACTION_SURFACE_SELECTION_AFTER_PHI_CK_TRIAD_v0"
SELECTION_RESULT = (
    "MASTER_ACTION_SURFACE_SELECTION_AFTER_PHI_CK_TRIAD_SELECTS_A_SURFACE_"
    "GAUGE_ROUTE_NO_VARIATION_OR_PROMOTION"
)
OUTCOME_ID = SELECTION_RESULT
PACKET_CLASSIFICATION = (
    "master_action_surface_selection_after_phi_ck_triad_selects_a_surface_"
    "gauge_route_no_variation_or_promotion"
)

NEXT_TARGET = "prepare_toe_native_A_surface_variation_and_source_route_packet"
NEXT_TARGET_KIND = "toe_native_A_surface_variation_and_source_route_packet_preparation"
ALTERNATE_A_TARGET_NAME = "prepare_A_surface_gauge_variation_and_source_route_packet"

SELECTED_MASTER_ACTION_SURFACE = "A_surface_gauge_route"
SELECTED_SURFACE_SYMBOL = "A"
SELECTED_ROUTE_ID = "toe_native_A_surface_gauge_variation_and_source_route"
SELECTED_ROUTE_LABEL = "candidate A gauge variation and source route"
SELECTED_ROUTE_STATUS = "selected_for_packet_preparation"
SELECTED_ROUTE_EXECUTION_STATUS = "not_executed"
SELECTED_ROUTE_SELECTION_REASON = (
    "A is the next tractable master-action surface after the phi/C_k triad "
    "because it tests the disciplined route pattern outside the scalar "
    "sandbox while avoiding the spinor-domain load of psi and the more "
    "speculative rho surface."
)

SURFACE_SELECTOR_CANDIDATES = [
    SELECTED_MASTER_ACTION_SURFACE,
    "psi_surface_fermion_matter_route",
    "rho_surface_statistical_entropy_route",
    "ck_further_constraint_family_elaboration",
]
SURFACE_SELECTOR_COMPARISON = {
    "A_surface_gauge_route": "recommended next tractable gauge/EM route",
    "psi_surface_fermion_matter_route": (
        "important but deferred because it requires spinor bundle, gamma "
        "matrix, adjoint, Dirac-operator, and curved-background domain "
        "conventions"
    ),
    "rho_surface_statistical_entropy_route": (
        "deferred as more speculative for the next math-first pressure test"
    ),
    "ck_further_constraint_family_elaboration": (
        "deferred to avoid over-elaborating phi before cross-surface testing"
    ),
}
PHI_CK_TRIAD_FORMS = [
    SOURCE_RULE_DISPLAY_FORM,
    BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
    TRANSPORT_RULE_DISPLAY_FORM,
]
GAUGE_ROUTE_CHAIN_STEPS = [
    "A_GAUGE_SURFACE",
    "VARIATION",
    "CURRENT_SOURCE_ROUTE",
    "STRESS_ENERGY_ROUTE",
    "GAUGE_CONSTRAINT_OR_CONSERVATION_CONDITION",
    "SOURCE_BRIDGE_TRANSPORT_CK_ANALOGUES",
]
GAUGE_ROUTE_CHAIN_FORM = " -> ".join(GAUGE_ROUTE_CHAIN_STEPS)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "MASTER_ACTION_SURFACE_SELECTION_AFTER_PHI_CK_TRIAD_20260619_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MasterActionSurfaceSelectionAfterPhiCKTriad.lean"
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


def _surface_options() -> list[dict[str, Any]]:
    return [
        {
            "surface_option_id": SELECTED_MASTER_ACTION_SURFACE,
            "surface_symbol": SELECTED_SURFACE_SYMBOL,
            "route_id": SELECTED_ROUTE_ID,
            "candidate_target": NEXT_TARGET,
            "alternate_target_name": ALTERNATE_A_TARGET_NAME,
            "status": SELECTED_ROUTE_STATUS,
            "execution_status": SELECTED_ROUTE_EXECUTION_STATUS,
            "technical_load": "moderate",
            "selection_reason": SELECTED_ROUTE_SELECTION_REASON,
            "variation_executed": False,
            "gauge_field_derived": False,
            "field_equations_derived": False,
            "current_conservation_proved": False,
        },
        {
            "surface_option_id": "psi_surface_fermion_matter_route",
            "surface_symbol": "psi",
            "route_id": "toe_native_psi_fermion_matter_route",
            "candidate_target": "prepare_toe_native_psi_surface_variation_and_source_route_packet",
            "status": "deferred_not_rejected",
            "execution_status": "not_executed",
            "technical_load": "high",
            "selection_reason": SURFACE_SELECTOR_COMPARISON[
                "psi_surface_fermion_matter_route"
            ],
            "variation_executed": False,
            "native_fermion_derivation_claimed": False,
        },
        {
            "surface_option_id": "rho_surface_statistical_entropy_route",
            "surface_symbol": "rho",
            "route_id": "toe_native_rho_statistical_entropy_route",
            "candidate_target": "prepare_toe_native_rho_surface_route_packet",
            "status": "deferred_not_rejected",
            "execution_status": "not_executed",
            "technical_load": "speculative",
            "selection_reason": SURFACE_SELECTOR_COMPARISON[
                "rho_surface_statistical_entropy_route"
            ],
            "variation_executed": False,
            "statistical_entropy_surface_promoted": False,
        },
        {
            "surface_option_id": "ck_further_constraint_family_elaboration",
            "surface_symbol": "C_k",
            "route_id": "further_phi_ck_constraint_family_elaboration",
            "candidate_target": "select_next_ck_constraint_family_after_phi_source_bridge_transport_triad",
            "status": "deferred_not_rejected",
            "execution_status": "not_executed",
            "technical_load": "governance_like_without_cross_surface_pressure",
            "selection_reason": SURFACE_SELECTOR_COMPARISON[
                "ck_further_constraint_family_elaboration"
            ],
            "new_ck_rules_constructed": False,
            "ck_variation_executed": False,
        },
    ]


def _selection_criteria(closeout: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "selector_consumes_phi_ck_triad_selector_target",
            "status": "accepted",
            "evidence": CONSUMED_TARGET,
            "assessment": "The selector consumes the active post-phi/C_k-triad surface target.",
        },
        {
            "row_id": "phi_ck_triad_closeout_accepted_as_template",
            "status": "accepted",
            "evidence": closeout.get("closeout_result"),
            "assessment": (
                "The phi/C_k source-bridge-transport triad is closed and "
                "available as a route template, not as a promoted theory."
            ),
        },
        {
            "row_id": "phi_ck_triad_forms_retained_as_context",
            "status": "accepted",
            "evidence": PHI_CK_TRIAD_FORMS,
            "assessment": "The source, bridge, and transport rules are retained as context.",
        },
        {
            "row_id": "a_surface_selected_as_next_pressure_test",
            "status": "accepted",
            "evidence": SELECTED_MASTER_ACTION_SURFACE,
            "assessment": (
                "The A gauge surface is selected as the next tractable "
                "cross-surface pressure test."
            ),
        },
        {
            "row_id": "psi_deferred_due_to_spinor_domain_load",
            "status": "accepted",
            "evidence": SURFACE_SELECTOR_COMPARISON[
                "psi_surface_fermion_matter_route"
            ],
            "assessment": "The psi route is important but technically heavier than A.",
        },
        {
            "row_id": "rho_deferred_as_more_speculative",
            "status": "accepted",
            "evidence": SURFACE_SELECTOR_COMPARISON[
                "rho_surface_statistical_entropy_route"
            ],
            "assessment": "The rho route is deferred as the less tractable next step.",
        },
        {
            "row_id": "more_ck_deferred_to_avoid_phi_over_elaboration",
            "status": "accepted",
            "evidence": SURFACE_SELECTOR_COMPARISON[
                "ck_further_constraint_family_elaboration"
            ],
            "assessment": "Further phi/C_k elaboration is deferred in favor of cross-surface testing.",
        },
        {
            "row_id": "next_a_surface_packet_authorized_only",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": "Only the next A-surface route packet is authorized.",
        },
        {
            "row_id": "gauge_route_chain_recorded_as_preview",
            "status": "accepted",
            "evidence": GAUGE_ROUTE_CHAIN_FORM,
            "assessment": (
                "The A route chain is recorded as a packet preview, not as an "
                "executed derivation."
            ),
        },
        {
            "row_id": "no_variation_derivation_closure_or_promotion",
            "status": "accepted",
            "evidence": [
                "A_variation_executed=false",
                "Maxwell_equations_derived=false",
                "current_conservation_proved=false",
                "master_action_promoted=false",
            ],
            "assessment": (
                "The selector does not execute variation, derive gauge field "
                "equations, prove current conservation, or promote the master action."
            ),
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "master_action_surface_selection_after_phi_ck_triad",
        "tiered_lean_validation_policy_formalized": True,
        "routine_packet_validation_tiers": [
            "touched Lean marker",
            "smallest affected Lake target",
            "lane aggregate",
            "current authority target",
        ],
        "release_preservation_validation": "full ToeFormal aggregate when feasible",
        "toeformal_import_update_requires_preservation_status": True,
        "aggregate_lean_validation_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "aggregate_lean_validation_status_allowed_values": ["NOT_RUN"],
        "full_toeformal_aggregate_status_for_packet": FULL_TOEFORMAL_AGGREGATE_STATUS,
        "full_toeformal_aggregate_passed": False,
        "full_toeformal_aggregate_failed": False,
        "full_toeformal_aggregate_timed_out": False,
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
    }


def build_master_action_surface_selection_after_phi_ck_triad(
    *,
    phi_ck_triad_closeout_path: Path = PHI_CK_TRIAD_CLOSEOUT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    closeout = _read_json(phi_ck_triad_closeout_path)
    surface_options = _surface_options()
    selection_criteria = _selection_criteria(closeout)
    acceptance_criteria = {
        "consumes_expected_selector_target": (
            closeout.get("schema_id") == PHI_CK_TRIAD_CLOSEOUT_SCHEMA_ID
            and closeout.get("packet_id") == PHI_CK_TRIAD_CLOSEOUT_PACKET_ID
            and closeout.get("outcome_id") == PHI_CK_TRIAD_CLOSEOUT_OUTCOME
            and closeout.get("closeout_result") == PHI_CK_TRIAD_CLOSEOUT_RESULT
            and closeout.get("selected_next_target") == CONSUMED_TARGET
            and closeout.get("accepted") is True
        ),
        "phi_ck_triad_closed_as_template": (
            closeout.get("family_classification") == FIRST_TRIAD_FAMILY_CLASSIFICATION
            and closeout.get("rule_family_classification") == RULE_FAMILY_CLASSIFICATION
            and closeout.get("source_admissibility_constraint_form")
            == SOURCE_ADMISSIBILITY_CONSTRAINT_FORM
            and closeout.get("bridge_admissibility_constraint_form")
            == BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM
            and closeout.get("transport_admissibility_constraint_form")
            == TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM
            and closeout.get("source_bridge_transport_admissibility_rule_family_closed")
            is True
        ),
        "prior_a_recommendation_preserved_not_preselected": (
            closeout.get("recommended_next_master_action_surface")
            == RECOMMENDED_NEXT_MASTER_ACTION_SURFACE
            and closeout.get("a_surface_gauge_route_recommended") is True
            and closeout.get("next_master_action_surface_selected") is False
            and closeout.get("selector_target_prepared") is False
        ),
        "a_surface_selected_for_packet_preparation": (
            SELECTED_MASTER_ACTION_SURFACE == "A_surface_gauge_route"
            and SELECTED_SURFACE_SYMBOL == "A"
            and NEXT_TARGET == "prepare_toe_native_A_surface_variation_and_source_route_packet"
        ),
        "surface_options_exactly_one_selected": (
            sum(1 for row in surface_options if row["status"] == SELECTED_ROUTE_STATUS)
            == 1
        ),
        "deferred_options_not_rejected": all(
            row["status"] == "deferred_not_rejected"
            for row in surface_options
            if row["surface_option_id"] != SELECTED_MASTER_ACTION_SURFACE
        ),
        "selection_criteria_all_accepted": all(
            row["status"] == "accepted" for row in selection_criteria
        ),
        "selector_only_no_route_execution": True,
        "no_gauge_derivation_or_current_proof": True,
        "no_new_ck_rules_or_closure": True,
        "no_master_action_promotion": True,
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_MASTER_ACTION_SURFACE_SELECTION_AFTER_PHI_CK_TRIAD"
    )
    validation_policy = _validation_policy()
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_MASTER_ACTION_SURFACE_SELECTION_AFTER_PHI_CK_TRIAD",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "MASTER_ACTION_SURFACE_SELECTION_AFTER_PHI_CK_TRIAD_REQUIRES_REMEDIATION",
        "selection_result": SELECTION_RESULT,
        "route_selection_result": SELECTION_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "alternate_a_target_name": ALTERNATE_A_TARGET_NAME,
        "phi_ck_triad_closeout_outcome": PHI_CK_TRIAD_CLOSEOUT_OUTCOME,
        "phi_ck_triad_closeout_result": PHI_CK_TRIAD_CLOSEOUT_RESULT,
        "phi_ck_triad_family_classification": FIRST_TRIAD_FAMILY_CLASSIFICATION,
        "phi_ck_triad_rule_family_classification": RULE_FAMILY_CLASSIFICATION,
        "phi_ck_triad_rule_forms": PHI_CK_TRIAD_FORMS,
        "source_admissibility_constraint_form": SOURCE_ADMISSIBILITY_CONSTRAINT_FORM,
        "bridge_admissibility_constraint_form": BRIDGE_ADMISSIBILITY_CONSTRAINT_FORM,
        "transport_admissibility_constraint_form": TRANSPORT_ADMISSIBILITY_CONSTRAINT_FORM,
        "phi_route_completed_admissibility_template": True,
        "phi_ck_triad_reopened": False,
        "surface_selector_candidates": SURFACE_SELECTOR_CANDIDATES,
        "surface_selector_comparison": SURFACE_SELECTOR_COMPARISON,
        "surface_option_count": len(surface_options),
        "surface_options": surface_options,
        "surface_options_selected_count": sum(
            1 for row in surface_options if row["status"] == SELECTED_ROUTE_STATUS
        ),
        "surface_options_deferred_count": sum(
            1 for row in surface_options if row["status"] == "deferred_not_rejected"
        ),
        "selected_master_action_surface": SELECTED_MASTER_ACTION_SURFACE,
        "selected_surface_symbol": SELECTED_SURFACE_SYMBOL,
        "selected_route_id": SELECTED_ROUTE_ID,
        "selected_route_label": SELECTED_ROUTE_LABEL,
        "selected_route_status": SELECTED_ROUTE_STATUS,
        "selected_route_execution_status": SELECTED_ROUTE_EXECUTION_STATUS,
        "selected_route_packet_authorized": accepted,
        "selected_route_execution_authorized": False,
        "selected_route_target": selected_next_target,
        "selected_route_reason": SELECTED_ROUTE_SELECTION_REASON,
        "gauge_route_chain_steps": GAUGE_ROUTE_CHAIN_STEPS,
        "gauge_route_chain_form": GAUGE_ROUTE_CHAIN_FORM,
        "gauge_route_chain_step_count": len(GAUGE_ROUTE_CHAIN_STEPS),
        "selection_criteria": selection_criteria,
        "selection_criteria_count": len(selection_criteria),
        "selection_criteria_accepted_count": sum(
            1 for row in selection_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "selector_target_prepared": accepted,
        "selector_target_accepted": accepted,
        "selection_executed": accepted,
        "master_action_surface_selection_executed": accepted,
        "a_surface_gauge_route_selected": accepted,
        "a_surface_gauge_route_packet_authorized": accepted,
        "a_surface_gauge_route_packet_prepared": False,
        "a_surface_gauge_route_execution_authorized": False,
        "psi_surface_deferred_as_harder": True,
        "rho_surface_deferred_as_more_speculative": True,
        "further_phi_ck_elaboration_deferred": True,
        "more_ck_elaboration_deferred": True,
        "a_surface_variation_executed": False,
        "a_surface_variation_route_prepared": False,
        "a_surface_variation_route_executed": False,
        "gauge_field_derived": False,
        "gauge_surface_derived": False,
        "maxwell_equations_derived": False,
        "yang_mills_equations_derived": False,
        "field_equations_derived": False,
        "current_source_route_constructed": False,
        "current_conservation_proved": False,
        "gauge_current_constraint_proved": False,
        "stress_energy_route_constructed": False,
        "stress_energy_source_admissibility_proved": False,
        "new_ck_rules_constructed": False,
        "source_bridge_transport_ck_analogues_constructed": False,
        "ck_action_embedding_claimed": False,
        "ck_variation_executed": False,
        "ck_variation_authorized": False,
        "native_phi_derivation_claimed": False,
        "v_phi_derivation_claimed": False,
        "qft_gr_closure_claimed": False,
        "qft_gr_solved": False,
        "qft_gr_seam_closed": False,
        "em_closure_claimed": False,
        "em_qft_closure_claimed": False,
        "semiclassical_coupling_authorized": False,
        "semiclassical_coupling_claimed": False,
        "semiclassical_einstein_equation_derived": False,
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
        "critical_gate_fail_conditions": [
            "execute A variation",
            "derive gauge field equations",
            "derive Maxwell equations",
            "prove current conservation",
            "prove stress-energy source admissibility",
            "construct new C_k rules",
            "claim QFT-GR closure",
            "claim EM closure",
            "promote the master action",
            "claim empirical validation",
            "record full ToeFormal aggregate as passed, failed, or timed out",
        ],
        "downstream_progression": [
            {
                "stage": "master_action_surface_selection_after_phi_ck_triad",
                "status": "SELECTED_A_SURFACE_GAUGE_ROUTE_FOR_PACKET_PREPARATION",
                "decision": SELECTION_RESULT,
                "reason": SELECTED_ROUTE_SELECTION_REASON,
            },
            {
                "stage": "toe_native_A_surface_variation_and_source_route_packet",
                "status": "NEXT_TARGET_AUTHORIZED_FOR_PREPARATION_ONLY",
                "decision": selected_next_target,
                "reason": (
                    "The next packet may specify the A variation/source route "
                    "and its blockers; it may not claim derivation by selection alone."
                ),
            },
        ],
        "mathematical_statement": (
            "The selector chooses A_surface_gauge_route as the next "
            "master-action surface after the closed phi/C_k source-bridge-"
            "transport triad. This is route selection only: it authorizes "
            "preparation of an A-surface variation/source packet and does not "
            "execute variation, derive gauge equations, prove current "
            "conservation, construct new C_k rules, close QFT-GR or EM, or "
            "promote the master action."
        ),
        "non_claim_boundary": (
            "This selector records A_surface_gauge_route as selected for the "
            "next preparation packet only. It treats the phi route as a closed "
            "admissibility-rule template and does not reopen the phi/C_k triad. "
            "It does not execute A variation, does not derive a gauge field, "
            "does not derive Maxwell equations, does not derive Yang-Mills "
            "equations, does not prove current conservation, does not prove "
            "stress-energy source admissibility, does not construct new C_k "
            "rules, does not close QFT-GR, does not close EM, does not authorize "
            "semiclassical coupling, does not claim empirical validation, and "
            "does not promote the master action. The full ToeFormal aggregate "
            "is recorded as NOT_RUN for this selector."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.MasterActionSurfaceSelectionAfterPhiCKTriad",
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
        "validation_policy": validation_policy,
        **validation_policy,
    }


def write_master_action_surface_selection_after_phi_ck_triad(
    *,
    phi_ck_triad_closeout_path: Path = PHI_CK_TRIAD_CLOSEOUT_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_master_action_surface_selection_after_phi_ck_triad(
        phi_ck_triad_closeout_path=phi_ck_triad_closeout_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the master-action surface selector after phi/C_k triad."
    )
    parser.add_argument(
        "--phi-ck-triad-closeout",
        type=Path,
        default=PHI_CK_TRIAD_CLOSEOUT_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    phi_ck_triad_closeout_path = (
        args.phi_ck_triad_closeout
        if args.phi_ck_triad_closeout.is_absolute()
        else REPO_ROOT / args.phi_ck_triad_closeout
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = write_master_action_surface_selection_after_phi_ck_triad(
        phi_ck_triad_closeout_path=phi_ck_triad_closeout_path,
        out=out,
        captured_at_utc=args.captured_at_utc,
    )
    print(
        "master_action_surface_selection_after_phi_ck_triad_report: "
        f"wrote {out} outcome={payload['outcome_id']} "
        f"next={payload['selected_next_target']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

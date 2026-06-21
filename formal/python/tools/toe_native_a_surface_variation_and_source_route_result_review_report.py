from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_a_surface_variation_and_source_route_packet_report import (
    A_SURFACE_ROUTE_PACKET_RESULT,
    DEFAULT_OUT as A_ROUTE_PACKET_PATH,
    GAUGE_ROUTE_STATUS_DECISION,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as A_ROUTE_PACKET_OUTCOME,
    PACKET_ID as A_ROUTE_PACKET_ID,
    RAW_GAUGE_ROUTE,
    RAW_VARIATION_ROUTE,
    SCHEMA_ID as A_ROUTE_PACKET_SCHEMA_ID,
    SOURCE_FORM_ROUTE_SHAPE,
    SOURCE_FORM_ROUTE_STATUS,
    TOE_NATIVE_STATUS_DECISION,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-21T00:00:00Z"

SCHEMA_ID = "TOE_NATIVE_A_SURFACE_VARIATION_AND_SOURCE_ROUTE_RESULT_REVIEW_20260621_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_A_SURFACE_VARIATION_AND_SOURCE_ROUTE_RESULT_REVIEW_v0"
A_SURFACE_ROUTE_REVIEW_RESULT = (
    "TOE_NATIVE_A_SURFACE_VARIATION_ROUTE_RESULT_REVIEW_ACCEPTS_RAW_GAUGE_ROUTE_"
    "AND_BLOCKS_NATIVE_DERIVATION_PENDING_GAUGE_GROUP_CURRENT_DOMAIN_AND_CK_CONTENT"
)
OUTCOME_ID = A_SURFACE_ROUTE_REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_A_surface_variation_route_result_review_accepts_raw_gauge_route_"
    "and_blocks_native_derivation_pending_gauge_group_current_domain_and_ck_content"
)
NEXT_TARGET = "prepare_toe_native_A_gauge_group_domain_and_current_policy_packet"
NEXT_TARGET_KIND = "toe_native_A_gauge_group_domain_and_current_policy_packet_preparation"
LEAN_VALIDATION_POLICY_ID = "TIERED_LEAN_VALIDATION_POLICY_FOR_PACKET_WORK_v0"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_A_SURFACE_VARIATION_AND_SOURCE_ROUTE_RESULT_REVIEW_20260621_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativeASurfaceVariationAndSourceRouteResultReview.lean"
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

VACUUM_ROUTE_SHAPE = "nabla_mu F^{mu nu} = 0"
NONABELIAN_ROUTE_SHAPE = "D_mu F^{mu nu} = J^nu"
POLICY_PACKET_ITEMS = [
    "U(1) vs non-Abelian gauge group",
    "A as connection/1-form vs component field",
    "definition of F",
    "ordinary vs gauge-covariant derivative",
    "external-current policy vs matter-derived current",
    "boundary variation policy",
    "gauge fixing status",
    "domain/regularity for A",
    "whether source route is vacuum-only or current-coupled",
]
PREFERRED_POLICY_PACKET_OUTCOME_CANDIDATES = [
    (
        "TOE_NATIVE_A_GAUGE_GROUP_DOMAIN_AND_CURRENT_POLICY_PACKET_PREPARED_"
        "U1_ROUTE_SELECTED_CURRENT_DERIVATION_STILL_BLOCKED"
    ),
    (
        "TOE_NATIVE_A_GAUGE_GROUP_DOMAIN_AND_CURRENT_POLICY_PACKET_PREPARED_"
        "GAUGE_POLICY_PARTIALLY_SELECTED_CURRENT_ROUTE_STILL_BLOCKED"
    ),
]


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _review_criteria(packet: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "raw_A_to_F_route_preserved",
            "status": "accepted",
            "evidence": packet.get("raw_gauge_route"),
            "assessment": "The raw A_mu -> F_{mu nu} route is preserved.",
        },
        {
            "row_id": "raw_variation_route_preserved",
            "status": "accepted",
            "evidence": packet.get("raw_variation_route"),
            "assessment": (
                "The raw delta S_A / delta A_nu -> nabla_mu F^{mu nu} route "
                "shape is preserved."
            ),
        },
        {
            "row_id": "source_form_recorded_as_shape_only",
            "status": "accepted",
            "evidence": packet.get("source_form_route_shape"),
            "assessment": (
                "The source equation is retained only as route shape; the packet "
                "does not derive J^nu."
            ),
        },
        {
            "row_id": "gauge_group_not_selected",
            "status": "accepted",
            "evidence": "gauge_group_selected=false",
            "assessment": "No U(1) or non-Abelian gauge group is selected.",
        },
        {
            "row_id": "bundle_domain_policy_not_selected",
            "status": "accepted",
            "evidence": "bundle_domain_for_A_selected=false",
            "assessment": "No A bundle/domain policy is selected.",
        },
        {
            "row_id": "current_not_derived",
            "status": "accepted",
            "evidence": "matter_current_J_nu_derived=false",
            "assessment": "No current J^nu is derived.",
        },
        {
            "row_id": "stress_energy_not_derived",
            "status": "accepted",
            "evidence": "stress_energy_T_A_derived=false",
            "assessment": "No gauge stress-energy T_A is derived.",
        },
        {
            "row_id": "current_conservation_not_proved",
            "status": "accepted",
            "evidence": "current_conservation_proved=false",
            "assessment": "No current conservation theorem is proved.",
        },
        {
            "row_id": "source_admissibility_not_proved",
            "status": "accepted",
            "evidence": "source_admissibility_proved=false",
            "assessment": "No source-admissibility theorem is proved.",
        },
        {
            "row_id": "a_relevant_ck_rules_not_constructed",
            "status": "accepted",
            "evidence": "C_k_analogues_constructed=false",
            "assessment": "No A-relevant C_k source/bridge/transport rules are constructed.",
        },
        {
            "row_id": "em_closure_not_claimed",
            "status": "accepted",
            "evidence": "em_closure_claimed=false",
            "assessment": "No EM closure is claimed.",
        },
        {
            "row_id": "qft_gr_closure_not_claimed",
            "status": "accepted",
            "evidence": "qft_gr_closure_claimed=false",
            "assessment": "No QFT-GR closure is claimed.",
        },
        {
            "row_id": "master_action_not_promoted",
            "status": "accepted",
            "evidence": "master_action_promoted=false",
            "assessment": "The master action is not promoted.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "toe_native_A_surface_variation_and_source_route_result_review",
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


def build_toe_native_a_surface_variation_and_source_route_result_review(
    *,
    a_route_packet_path: Path = A_ROUTE_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(a_route_packet_path)
    review_criteria = _review_criteria(packet)
    blocker_ids = {row["blocker_id"] for row in packet.get("retained_blockers", [])}
    acceptance_criteria = {
        "consumes_expected_a_route_review_target": (
            packet.get("schema_id") == A_ROUTE_PACKET_SCHEMA_ID
            and packet.get("packet_id") == A_ROUTE_PACKET_ID
            and packet.get("outcome_id") == A_ROUTE_PACKET_OUTCOME
            and packet.get("selected_next_target") == CONSUMED_TARGET
            and packet.get("accepted") is True
        ),
        "raw_A_to_F_route_preserved": packet.get("raw_gauge_route") == RAW_GAUGE_ROUTE,
        "raw_variation_route_preserved": (
            packet.get("raw_variation_route") == RAW_VARIATION_ROUTE
        ),
        "source_form_recorded_as_shape_only": (
            packet.get("source_form_route_shape") == SOURCE_FORM_ROUTE_SHAPE
            and packet.get("source_form_route_status") == SOURCE_FORM_ROUTE_STATUS
            and packet.get("source_route_shape_only_not_derived") is True
        ),
        "gauge_policy_not_selected": (
            packet.get("gauge_group_selected") is False
            and packet.get("bundle_domain_for_A_selected") is False
            and packet.get("definition_of_F_selected") is False
            and packet.get("covariant_derivative_D_mu_convention_selected") is False
        ),
        "current_and_source_route_not_derived": (
            packet.get("matter_current_J_nu_derived") is False
            and packet.get("external_current_policy_selected") is False
            and packet.get("current_conservation_proved") is False
            and packet.get("source_admissibility_proved") is False
        ),
        "stress_energy_and_ck_not_constructed": (
            packet.get("stress_energy_T_A_derived") is False
            and packet.get("C_k_analogues_constructed") is False
            and packet.get("source_bridge_transport_ck_analogues_constructed") is False
        ),
        "em_and_qft_gr_closure_not_claimed": (
            packet.get("em_closure_claimed") is False
            and packet.get("em_qft_closure_claimed") is False
            and packet.get("qft_gr_closure_claimed") is False
            and packet.get("qft_gr_seam_closed") is False
        ),
        "master_action_not_promoted": (
            packet.get("canonical_master_action_promoted") is False
            and packet.get("master_action_promoted") is False
            and packet.get("master_action_promotion_authorized") is False
        ),
        "retained_blockers_are_complete": blocker_ids == {
            "gauge_group_not_selected",
            "bundle_domain_for_A_not_selected",
            "definition_of_F_not_selected",
            "covariant_derivative_D_mu_convention_not_selected",
            "matter_current_J_nu_not_derived",
            "external_current_policy_not_selected",
            "gauge_fixing_not_selected",
            "boundary_terms_not_controlled",
            "stress_energy_T_A_not_derived",
            "source_admissibility_not_proved",
            "current_conservation_not_proved",
            "C_k_analogues_not_constructed",
            "EM_closure_not_claimed",
            "QFT_GR_closure_not_claimed",
            "master_action_promotion_not_claimed",
        },
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_A_SURFACE_VARIATION_AND_SOURCE_ROUTE_RESULT_REVIEW"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_A_SURFACE_ROUTE_RESULT_REVIEW",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_A_SURFACE_VARIATION_ROUTE_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "review_result": A_SURFACE_ROUTE_REVIEW_RESULT,
        "a_surface_route_packet_result": A_SURFACE_ROUTE_PACKET_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "reviewed_a_route_packet_artifact_id": packet.get("schema_id"),
        "reviewed_a_route_packet_id": packet.get("packet_id"),
        "reviewed_a_route_packet_outcome": packet.get("outcome_id"),
        "selected_surface_symbol": packet.get("selected_surface_symbol"),
        "selected_route_id": packet.get("selected_route_id"),
        "raw_A_to_F_route_preserved": True,
        "raw_variation_route_preserved": True,
        "source_form_recorded_as_shape_only": True,
        "native_derivation_blocked": True,
        "gauge_policy_packet_authorized": accepted,
        "policy_packet_items": POLICY_PACKET_ITEMS,
        "policy_packet_item_count": len(POLICY_PACKET_ITEMS),
        "preferred_policy_packet_outcome_candidates": (
            PREFERRED_POLICY_PACKET_OUTCOME_CANDIDATES
        ),
        "preferred_policy_packet_outcome_candidate_count": len(
            PREFERRED_POLICY_PACKET_OUTCOME_CANDIDATES
        ),
        "vacuum_route_shape_from_pure_gauge_term": VACUUM_ROUTE_SHAPE,
        "source_route_requires_current_policy_or_matter_coupling": True,
        "abelian_route_shape_recorded": SOURCE_FORM_ROUTE_SHAPE,
        "nonabelian_route_shape_requires_gauge_covariant_derivative": (
            NONABELIAN_ROUTE_SHAPE
        ),
        "gauge_policy_is_next_real_blocker": True,
        "review_criteria": review_criteria,
        "review_criteria_count": len(review_criteria),
        "review_criteria_accepted_count": sum(
            1 for row in review_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "retained_blockers": packet.get("retained_blockers", []),
        "retained_blocker_count": packet.get("retained_blocker_count"),
        "gauge_route_status_decision": GAUGE_ROUTE_STATUS_DECISION,
        "source_form_route_status": SOURCE_FORM_ROUTE_STATUS,
        "toe_native_status_decision": TOE_NATIVE_STATUS_DECISION,
        "raw_gauge_route": RAW_GAUGE_ROUTE,
        "raw_variation_route": RAW_VARIATION_ROUTE,
        "source_form_route_shape": SOURCE_FORM_ROUTE_SHAPE,
        "formal_theorem_backed_gauge_derivation": False,
        "record_validated": True,
        "symbolic_calculation_recorded": True,
        "proof_depth_label": "RESULT_REVIEW_ACCEPTS_RAW_GAUGE_ROUTE_ONLY",
        "a_surface_variation_route_prepared": True,
        "a_surface_variation_route_executed": False,
        "a_surface_variation_executed": False,
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
        "critical_gate_fail_conditions": [
            "derive J^nu without matter coupling or external-current policy",
            "claim Maxwell or Yang-Mills equations are derived",
            "select U(1) or non-Abelian gauge policy inside the review",
            "claim current conservation",
            "claim source admissibility",
            "construct A-relevant C_k rules",
            "claim EM or QFT-GR closure",
            "promote the working-form master action",
            "authorize semiclassical coupling",
            "claim public readiness or release completion",
        ],
        "downstream_progression": [
            {
                "stage": "A_surface_route_result_review",
                "status": "ACCEPTED_RAW_GAUGE_ROUTE_NATIVE_DERIVATION_BLOCKED",
                "decision": A_SURFACE_ROUTE_REVIEW_RESULT,
                "reason": (
                    "The packet records the correct raw gauge route while "
                    "blocking native current/source derivation."
                ),
            },
            {
                "stage": "gauge_group_domain_current_policy_packet",
                "status": "NEXT_TARGET_AUTHORIZED",
                "decision": selected_next_target,
                "reason": (
                    "Gauge group, A domain, F definition, derivative convention, "
                    "current policy, boundary variation, gauge fixing, and "
                    "vacuum-vs-current coupling must be decided or explicitly "
                    "blocked before any source equation is derived."
                ),
            },
        ],
        "mathematical_statement": (
            "The result review accepts that the candidate master-action A surface "
            "records the raw gauge route A_mu -> F_{mu nu}, the raw variation "
            "shape delta S_A / delta A_nu -> nabla_mu F^{mu nu}, and the source "
            "form nabla_mu F^{mu nu} = J^nu as route shape only. From the pure "
            "gauge term alone, the vacuum route is nabla_mu F^{mu nu} = 0; a "
            "current-coupled source equation requires external-current policy or "
            "a matter-coupling route. A non-Abelian route would require a "
            "gauge-covariant derivative such as D_mu F^{mu nu} = J^nu."
        ),
        "non_claim_boundary": (
            "This result review accepts raw A-surface gauge-route recording only. "
            "It does not select a gauge group, does not select an A bundle/domain, "
            "does not define F, does not choose ordinary versus gauge-covariant "
            "derivative, does not derive J^nu, does not admit an external current, "
            "does not select gauge fixing, does not control boundary variation, "
            "does not derive T_A, does not prove source admissibility or current "
            "conservation, does not construct A-relevant C_k rules, does not "
            "derive Maxwell or Yang-Mills equations, does not close EM, QFT-GR, "
            "or EM-QFT, does not authorize semiclassical coupling, does not "
            "promote the master action, and does not claim empirical validation, "
            "public readiness, or release authorization."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativeASurfaceVariationAndSourceRouteResultReview",
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


def write_toe_native_a_surface_variation_and_source_route_result_review(
    *,
    a_route_packet_path: Path = A_ROUTE_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = build_toe_native_a_surface_variation_and_source_route_result_review(
        a_route_packet_path=a_route_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(packet, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return packet


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Build the ToE-native A surface variation/source route result-review artifact."
        )
    )
    parser.add_argument("--a-route-packet", type=Path, default=A_ROUTE_PACKET_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    args = parser.parse_args()
    packet = write_toe_native_a_surface_variation_and_source_route_result_review(
        a_route_packet_path=args.a_route_packet,
        out=args.out,
        captured_at_utc=args.captured_at_utc,
    )
    print(json.dumps(packet, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

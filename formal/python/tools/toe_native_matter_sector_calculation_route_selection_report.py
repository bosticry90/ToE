from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_matter_sector_definition_packet_result_review_report import (
    DEFAULT_OUT as DEFINITION_RESULT_REVIEW_PATH,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as DEFINITION_RESULT_REVIEW_OUTCOME,
    RECOMMENDED_FIRST_ROUTE_HINT,
    RECOMMENDED_FIRST_ROUTE_STATUS,
    RECOMMENDED_FIRST_ROUTE_TARGET_HINT,
    REVIEW_RESULT as DEFINITION_RESULT_REVIEW_RESULT,
    SCHEMA_ID as DEFINITION_RESULT_REVIEW_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-18T00:00:00Z"

SCHEMA_ID = "TOE_NATIVE_MATTER_SECTOR_CALCULATION_ROUTE_SELECTION_20260618_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_MATTER_SECTOR_CALCULATION_ROUTE_SELECTION_v0"
ROUTE_SELECTION_RESULT = (
    "TOE_NATIVE_MATTER_SECTOR_CALCULATION_ROUTE_SELECTION_SELECTS_"
    "PHI_SURFACE_VARIATION_AND_SOURCE_ROUTE_NO_DERIVATION_CLAIM"
)
OUTCOME_ID = ROUTE_SELECTION_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_matter_sector_calculation_route_selection_selects_phi_surface_"
    "route_packet_preparation_only_no_derivation_claim"
)
SELECTED_SURFACE_SYMBOL = "phi"
SELECTED_ROUTE_ID = "toe_native_phi_surface_variation_and_source_route"
SELECTED_ROUTE_LABEL = "candidate phi surface variation and source route"
NEXT_TARGET = "prepare_toe_native_phi_surface_variation_and_source_route_packet"
NEXT_TARGET_KIND = "toe_native_phi_surface_variation_and_source_route_packet_preparation"
LEAN_VALIDATION_POLICY_ID = "TIERED_LEAN_VALIDATION_POLICY_FOR_PACKET_WORK_v0"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_MATTER_SECTOR_CALCULATION_ROUTE_SELECTION_20260618_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativeMatterSectorCalculationRouteSelection.lean"
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


def _candidate_by_symbol(packet: dict[str, Any], symbol: str) -> dict[str, Any]:
    for row in packet.get("matter_surface_inventory", []):
        if row.get("symbol") == symbol:
            return row
    return {}


def _route_options(review_packet: dict[str, Any]) -> list[dict[str, Any]]:
    phi_row = _candidate_by_symbol(review_packet, SELECTED_SURFACE_SYMBOL)
    return [
        {
            "route_id": SELECTED_ROUTE_ID,
            "surface_symbol": SELECTED_SURFACE_SYMBOL,
            "candidate_target": NEXT_TARGET,
            "status": "selected_for_packet_preparation",
            "execution_status": "not_executed",
            "selection_reason": (
                "The phi surface is the shortest bounded comparison route "
                "because the imported scalar sandbox supplies a reference "
                "witness while the ToE-native phi route remains unproved."
            ),
            "variation_route_status": phi_row.get("variation_route_status"),
            "stress_energy_route_status": phi_row.get("stress_energy_route_status"),
            "quantum_operator_route_status": phi_row.get(
                "quantum_operator_route_status"
            ),
            "nonclaim_boundary": (
                "Selection authorizes only preparation of a phi variation/source "
                "route packet; it does not derive the route."
            ),
        },
        {
            "route_id": "toe_native_gauge_current_route",
            "surface_symbol": "A",
            "candidate_target": "derive_current_from_candidate_gauge_term",
            "status": "deferred",
            "execution_status": "not_executed",
            "selection_reason": (
                "Gauge-current work remains useful but is deferred behind the "
                "shorter phi comparison route."
            ),
        },
        {
            "route_id": "toe_native_fermion_stress_energy_route",
            "surface_symbol": "psi",
            "candidate_target": "derive_dirac_or_fermion_stress_energy_route",
            "status": "deferred",
            "execution_status": "not_executed",
            "selection_reason": (
                "Fermion stress-energy depends on additional spinor/geometric "
                "conventions not selected in this packet."
            ),
        },
        {
            "route_id": "quantum_expectation_source_prerequisite_map",
            "surface_symbol": "rho",
            "candidate_target": "define_quantum_expectation_source_prerequisite_map",
            "status": "deferred",
            "execution_status": "not_executed",
            "selection_reason": (
                "Quantum expectation work requires state, operator, "
                "renormalization, and domain inputs not supplied by the "
                "current selector."
            ),
        },
    ]


def _selection_criteria(review_packet: dict[str, Any]) -> list[dict[str, Any]]:
    phi_row = _candidate_by_symbol(review_packet, SELECTED_SURFACE_SYMBOL)
    return [
        {
            "row_id": "selector_consumes_current_target",
            "status": "accepted",
            "evidence": CONSUMED_TARGET,
            "assessment": "The packet consumes the active route-selection target.",
        },
        {
            "row_id": "definition_review_accepts_surface_index_only",
            "status": "accepted",
            "evidence": review_packet.get("review_result"),
            "assessment": (
                "The selector starts from an accepted surface index, not from "
                "a matter derivation."
            ),
        },
        {
            "row_id": "phi_hint_is_nonbinding_selector_input",
            "status": "accepted",
            "evidence": RECOMMENDED_FIRST_ROUTE_STATUS,
            "assessment": (
                "The prior phi recommendation is treated as input to the "
                "selector, not as an already executed route."
            ),
        },
        {
            "row_id": "phi_surface_available_for_bounded_route_preparation",
            "status": "accepted",
            "evidence": phi_row,
            "assessment": (
                "The phi surface is indexed and has partially witnessed "
                "imported-scalar status, making it the shortest bounded "
                "comparison path."
            ),
        },
        {
            "row_id": "selected_route_prepares_packet_only",
            "status": "accepted",
            "evidence": NEXT_TARGET,
            "assessment": (
                "The selector authorizes only the next preparation packet."
            ),
        },
        {
            "row_id": "non_selected_routes_deferred_without_rejection",
            "status": "accepted",
            "evidence": [
                "toe_native_gauge_current_route",
                "toe_native_fermion_stress_energy_route",
                "quantum_expectation_source_prerequisite_map",
            ],
            "assessment": (
                "The gauge, fermion, and quantum routes are deferred, not "
                "disproved."
            ),
        },
        {
            "row_id": "no_toe_native_matter_derivation_claim",
            "status": "accepted",
            "evidence": "toe_native_matter_derivation_claimed=false",
            "assessment": "No ToE-native matter derivation is claimed.",
        },
        {
            "row_id": "no_standard_model_derivation_claim",
            "status": "accepted",
            "evidence": "standard_model_derivation_claimed=false",
            "assessment": "No Standard Model derivation is claimed.",
        },
        {
            "row_id": "no_qft_gr_or_semiclassical_closure",
            "status": "accepted",
            "evidence": "qft_gr_closure=false; semiclassical_coupling=false",
            "assessment": (
                "The selector does not close QFT-GR or authorize "
                "semiclassical coupling."
            ),
        },
        {
            "row_id": "no_master_action_promotion",
            "status": "accepted",
            "evidence": "master_action_promotion_authorized=false",
            "assessment": "The master action remains working-form/non-canonical.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "toe_native_matter_sector_calculation_route_selection",
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


def build_toe_native_matter_sector_calculation_route_selection(
    *,
    definition_result_review_path: Path = DEFINITION_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review_packet = _read_json(definition_result_review_path)
    phi_row = _candidate_by_symbol(review_packet, SELECTED_SURFACE_SYMBOL)
    route_options = _route_options(review_packet)
    selection_criteria = _selection_criteria(review_packet)
    acceptance_criteria = {
        "consumes_current_route_selection_target": (
            review_packet.get("selected_next_target") == CONSUMED_TARGET
        ),
        "definition_result_review_available_and_accepted": (
            review_packet.get("schema_id") == DEFINITION_RESULT_REVIEW_SCHEMA_ID
            and review_packet.get("outcome_id") == DEFINITION_RESULT_REVIEW_OUTCOME
            and review_packet.get("accepted") is True
        ),
        "prior_phi_hint_is_nonbinding": (
            review_packet.get("recommended_first_route_hint")
            == RECOMMENDED_FIRST_ROUTE_HINT
            and review_packet.get("recommended_first_route_status")
            == RECOMMENDED_FIRST_ROUTE_STATUS
            and review_packet.get("recommended_first_route_target_hint")
            == RECOMMENDED_FIRST_ROUTE_TARGET_HINT
        ),
        "phi_surface_indexed": phi_row.get("symbol") == SELECTED_SURFACE_SYMBOL,
        "phi_route_has_reference_witness_but_not_native_derivation": (
            phi_row.get("variation_route_status")
            == "partially_witnessed_for_imported_scalar_blocked_for_toe_native"
            and phi_row.get("stress_energy_route_status")
            == "partially_witnessed_for_imported_scalar_blocked_for_toe_native"
        ),
        "selected_route_is_packet_preparation_only": (
            NEXT_TARGET
            == "prepare_toe_native_phi_surface_variation_and_source_route_packet"
        ),
        "selected_route_options_exactly_one_selected": (
            sum(1 for row in route_options if row["status"] == "selected_for_packet_preparation")
            == 1
        ),
        "non_selected_routes_deferred": all(
            row["status"] == "deferred"
            for row in route_options
            if row["route_id"] != SELECTED_ROUTE_ID
        ),
        "selection_criteria_all_accepted": all(
            row["status"] == "accepted" for row in selection_criteria
        ),
        "no_toe_native_matter_derivation_claim": True,
        "no_standard_model_derivation_claim": True,
        "no_qft_gr_or_semiclassical_closure": True,
        "no_master_action_promotion": True,
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_MATTER_SECTOR_CALCULATION_ROUTE_SELECTION"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_ROUTE_SELECTION",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_MATTER_SECTOR_CALCULATION_ROUTE_SELECTION_REQUIRES_REMEDIATION",
        "route_selection_result": ROUTE_SELECTION_RESULT,
        "definition_result_review_result": DEFINITION_RESULT_REVIEW_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selected_surface_symbol": SELECTED_SURFACE_SYMBOL,
        "selected_route_id": SELECTED_ROUTE_ID,
        "selected_route_label": SELECTED_ROUTE_LABEL,
        "selected_route_status": "selected_for_packet_preparation",
        "selected_route_execution_status": "not_executed",
        "selected_route_packet_authorized": accepted,
        "selected_route_execution_authorized": False,
        "selected_route_target": NEXT_TARGET,
        "reviewed_definition_result_review_artifact_id": review_packet.get(
            "schema_id"
        ),
        "reviewed_definition_result_review_outcome": review_packet.get(
            "outcome_id"
        ),
        "candidate_symbols": review_packet.get("candidate_symbols", []),
        "candidate_surface_count": review_packet.get("candidate_surface_count"),
        "route_options": route_options,
        "route_option_count": len(route_options),
        "route_options_selected_count": sum(
            1 for row in route_options if row["status"] == "selected_for_packet_preparation"
        ),
        "route_options_deferred_count": sum(
            1 for row in route_options if row["status"] == "deferred"
        ),
        "selection_criteria": selection_criteria,
        "selection_criteria_count": len(selection_criteria),
        "selection_criteria_accepted_count": sum(
            1 for row in selection_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "selection_reason": (
            "Select phi first because it is the shortest bounded comparison "
            "route against the imported scalar witness while still requiring a "
            "separate ToE-native variation/source packet."
        ),
        "comparison_witness": review_packet.get("scalar_witness_closeout_result"),
        "comparison_witness_use": "reference_only_not_derivation",
        "scalar_witness_reopened": False,
        "scalar_witness_used_as_toe_native_derivation": False,
        "direct_phi_route_execution_authorized": False,
        "phi_variation_route_prepared": False,
        "phi_variation_route_executed": False,
        "phi_variation_derived": False,
        "phi_stress_energy_derived": False,
        "toe_native_phi_source_route_constructed": False,
        "toe_native_phi_source_admissibility_claimed": False,
        "toe_native_phi_source_conservation_claimed": False,
        "formal_theorem_backed_matter_derivation": False,
        "record_validated": True,
        "symbolic_calculation_recorded": False,
        "proof_depth_label": "RECORD_ONLY_SELECTOR_VALIDATED",
        "toe_native_matter_derivation_claimed": False,
        "toe_native_matter_sector_derived": False,
        "toe_native_matter_sector_defined": False,
        "toe_matter_sector_derived": False,
        "toe_matter_model_derived": False,
        "standard_model_derivation_claimed": False,
        "source_admissibility_claimed": False,
        "source_admissibility_completed": False,
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
            "ToE-native matter derivation",
            "Standard Model derivation",
            "canonical master-action promotion",
            "QFT-GR closure",
            "semiclassical coupling",
            "empirical validation",
            "public readiness",
            "phi variation/source route execution",
            "imported scalar witness promoted as ToE-native derivation",
        ],
        "downstream_progression": [
            {
                "stage": "route_selection",
                "status": "SELECTED_PHI_SURFACE_ROUTE_FOR_PACKET_PREPARATION",
                "decision": ROUTE_SELECTION_RESULT,
                "reason": (
                    "The selector chooses the phi surface as the first bounded "
                    "ToE-native matter route to prepare."
                ),
            },
            {
                "stage": "toe_native_phi_surface_variation_and_source_route_packet",
                "status": "NEXT_TARGET_AUTHORIZED_FOR_PREPARATION_ONLY",
                "decision": selected_next_target,
                "reason": (
                    "The next packet may specify the phi variation/source "
                    "route and its blockers; it may not claim derivation by "
                    "selection alone."
                ),
            },
        ],
        "mathematical_statement": (
            "The selector chooses the candidate phi surface as the first "
            "ToE-native matter-sector calculation route to prepare. This is a "
            "route-selection result only: no phi variation, stress-energy, "
            "source conservation, source admissibility, Standard Model "
            "derivation, QFT-GR closure, semiclassical coupling, or "
            "master-action promotion is established."
        ),
        "non_claim_boundary": (
            "This route selector chooses the phi surface variation/source route "
            "for the next preparation packet only. It does not execute the phi "
            "route, derive ToE-native matter, promote the imported scalar "
            "sandbox to a native derivation, derive the Standard Model, promote "
            "the master action, close QFT-GR, authorize semiclassical coupling, "
            "claim empirical validation, claim public readiness, or authorize "
            "release."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativeMatterSectorCalculationRouteSelection",
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


def write_toe_native_matter_sector_calculation_route_selection(
    *,
    definition_result_review_path: Path = DEFINITION_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_toe_native_matter_sector_calculation_route_selection(
        definition_result_review_path=definition_result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the ToE-native matter-sector calculation route selection."
    )
    parser.add_argument(
        "--definition-result-review",
        type=Path,
        default=DEFINITION_RESULT_REVIEW_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    definition_result_review_path = (
        args.definition_result_review
        if args.definition_result_review.is_absolute()
        else REPO_ROOT / args.definition_result_review
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = write_toe_native_matter_sector_calculation_route_selection(
        definition_result_review_path=definition_result_review_path,
        out=out,
        captured_at_utc=args.captured_at_utc,
    )
    print(
        "toe_native_matter_sector_calculation_route_selection_report: "
        f"wrote {out} outcome={payload['outcome_id']} "
        f"next={payload['selected_next_target']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

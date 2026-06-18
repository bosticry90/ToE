from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.toe_native_matter_sector_definition_packet_report import (
    DEFAULT_OUT as DEFINITION_PACKET_PATH,
    DEFINITION_RESULT,
    FIRST_CALCULATION_ROUTE_CANDIDATES,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as DEFINITION_PACKET_OUTCOME,
    PACKET_ID as DEFINITION_PACKET_ID,
    POST_REVIEW_ROUTE_SELECTION_TARGET,
    SCHEMA_ID as DEFINITION_PACKET_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-18T00:00:00Z"

SCHEMA_ID = "TOE_NATIVE_MATTER_SECTOR_DEFINITION_PACKET_RESULT_REVIEW_20260618_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "TOE_NATIVE_MATTER_SECTOR_DEFINITION_PACKET_RESULT_REVIEW_v0"
REVIEW_RESULT = (
    "TOE_NATIVE_MATTER_SECTOR_DEFINITION_RESULT_REVIEW_ACCEPTS_"
    "MASTER_ACTION_MATTER_SURFACE_INDEX_NO_DERIVATION_CLAIM"
)
OUTCOME_ID = REVIEW_RESULT
PACKET_CLASSIFICATION = (
    "toe_native_matter_sector_definition_packet_result_review_accepts_surface_"
    "index_and_authorizes_route_selection_only"
)
NEXT_TARGET = "select_toe_native_matter_sector_calculation_route"
NEXT_TARGET_KIND = "toe_native_matter_sector_calculation_route_selection"
RECOMMENDED_FIRST_ROUTE_HINT = "phi"
RECOMMENDED_FIRST_ROUTE_TARGET_HINT = (
    "prepare_toe_native_phi_surface_variation_and_source_route_packet"
)
RECOMMENDED_FIRST_ROUTE_STATUS = "recorded_as_nonbinding_selector_input"
LEAN_VALIDATION_POLICY_ID = "TIERED_LEAN_VALIDATION_POLICY_FOR_PACKET_WORK_v0"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_NATIVE_MATTER_SECTOR_DEFINITION_PACKET_RESULT_REVIEW_20260618_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "ToeNativeMatterSectorDefinitionPacketResultReview.lean"
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


def _review_criteria(packet: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "row_id": "required_surfaces_indexed",
            "status": "accepted",
            "evidence": packet.get("candidate_symbols", []),
            "assessment": "psi, A, phi, rho, and C_k are indexed.",
        },
        {
            "row_id": "surface_classifications_are_bounded",
            "status": "accepted",
            "evidence": packet.get("candidate_status_summary", {}),
            "assessment": (
                "The review accepts imported/provisional/placeholder status "
                "labels without treating them as derivations."
            ),
        },
        {
            "row_id": "variation_stress_energy_quantum_and_seam_routes_marked",
            "status": "accepted",
            "evidence": packet.get("route_status_summary", {}),
            "assessment": (
                "Every surface records variation, stress-energy, quantum/operator, "
                "and seam-dependency route status as specified or blocked."
            ),
        },
        {
            "row_id": "scalar_witness_preserved_only_as_reference",
            "status": "accepted",
            "evidence": packet.get("scalar_witness_closeout_result", ""),
            "assessment": (
                "The imported scalar sandbox remains a reference witness and is "
                "not promoted to a ToE-native derivation."
            ),
        },
        {
            "row_id": "master_action_working_form_status_preserved",
            "status": "accepted",
            "evidence": packet.get("master_action_promotion_status", ""),
            "assessment": (
                "The candidate master action remains working-form and "
                "non-canonical."
            ),
        },
        {
            "row_id": "no_toe_native_matter_derivation_claim",
            "status": "accepted",
            "evidence": "toe_native_matter_derivation_claimed=false",
            "assessment": "The packet makes no ToE-native matter derivation claim.",
        },
        {
            "row_id": "no_standard_model_derivation_claim",
            "status": "accepted",
            "evidence": "standard_model_derivation_claimed=false",
            "assessment": "The packet makes no Standard Model derivation claim.",
        },
        {
            "row_id": "no_canonical_master_action_promotion",
            "status": "accepted",
            "evidence": "canonical_master_action_promoted=false",
            "assessment": "The packet does not promote the master action.",
        },
        {
            "row_id": "no_qft_gr_or_semiclassical_closure",
            "status": "accepted",
            "evidence": (
                "qft_gr_closure_claimed=false; "
                "semiclassical_coupling_claimed=false"
            ),
            "assessment": (
                "The packet does not close QFT-GR or authorize semiclassical "
                "coupling."
            ),
        },
        {
            "row_id": "route_selection_authorized_only_after_review",
            "status": "accepted",
            "evidence": POST_REVIEW_ROUTE_SELECTION_TARGET,
            "assessment": (
                "The next live target is calculation-route selection, not an "
                "immediate matter derivation."
            ),
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": "toe_native_matter_sector_definition_packet_result_review",
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


def build_toe_native_matter_sector_definition_packet_result_review(
    *,
    definition_packet_path: Path = DEFINITION_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    definition_packet = _read_json(definition_packet_path)
    review_criteria = _review_criteria(definition_packet)
    surfaces = {
        row["symbol"]: row
        for row in definition_packet.get("matter_surface_inventory", [])
    }
    acceptance_criteria = {
        "consumes_expected_result_review_target": (
            definition_packet.get("selected_next_target") == CONSUMED_TARGET
        ),
        "definition_packet_available_and_accepted": (
            definition_packet.get("schema_id") == DEFINITION_PACKET_SCHEMA_ID
            and definition_packet.get("packet_id") == DEFINITION_PACKET_ID
            and definition_packet.get("outcome_id") == DEFINITION_PACKET_OUTCOME
            and definition_packet.get("accepted") is True
        ),
        "required_surfaces_indexed": (
            definition_packet.get("candidate_symbols")
            == ["psi", "A", "phi", "rho", "C_k"]
            and definition_packet.get("candidate_surface_count") == 5
        ),
        "surface_classifications_are_bounded": (
            surfaces.get("psi", {}).get("provisional_toe_native_candidate") is True
            and surfaces.get("A", {}).get("provisional_toe_native_candidate") is True
            and surfaces.get("phi", {}).get("provisional_toe_native_candidate") is True
            and surfaces.get("rho", {}).get("pure_organizing_placeholder") is True
            and surfaces.get("C_k", {}).get("pure_organizing_placeholder") is True
        ),
        "variation_stress_energy_quantum_and_seam_routes_marked": (
            definition_packet.get("route_status_summary", {}).get(
                "variation_route_specified_or_blocked"
            )
            is True
            and definition_packet.get("route_status_summary", {}).get(
                "stress_energy_route_specified_or_blocked"
            )
            is True
            and definition_packet.get("route_status_summary", {}).get(
                "quantum_operator_route_specified_or_blocked"
            )
            is True
            and definition_packet.get("route_status_summary", {}).get(
                "seam_constraint_dependency_recorded"
            )
            is True
        ),
        "scalar_witness_preserved_only_as_reference": (
            definition_packet.get("scalar_witness_closeout_preserved_as_reference")
            is True
            and definition_packet.get("scalar_sandbox_reopened") is False
        ),
        "master_action_working_form_status_preserved": (
            definition_packet.get("master_action_working_form_noncanonical") is True
            and definition_packet.get("master_action_promotion_status")
            == "BLOCKED_PENDING_CRITERIA"
        ),
        "no_toe_native_matter_derivation_claim": (
            definition_packet.get("toe_native_matter_derivation_claimed") is False
            and definition_packet.get("toe_native_matter_sector_derived") is False
        ),
        "no_standard_model_derivation_claim": (
            definition_packet.get("standard_model_derivation_claimed") is False
        ),
        "no_canonical_master_action_promotion": (
            definition_packet.get("canonical_master_action_promoted") is False
            and definition_packet.get("master_action_promotion_authorized") is False
        ),
        "no_qft_gr_or_semiclassical_closure": (
            definition_packet.get("qft_gr_closure_claimed") is False
            and definition_packet.get("qft_gr_seam_closed") is False
            and definition_packet.get("semiclassical_coupling_claimed") is False
            and definition_packet.get("semiclassical_coupling_authorized") is False
        ),
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
        ),
        "next_target_is_route_selection_only": (
            NEXT_TARGET == POST_REVIEW_ROUTE_SELECTION_TARGET
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_TOE_NATIVE_MATTER_SECTOR_DEFINITION_PACKET_RESULT_REVIEW"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_NONLIVE_RESULT_REVIEW",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "TOE_NATIVE_MATTER_SECTOR_DEFINITION_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "review_result": REVIEW_RESULT,
        "definition_result": DEFINITION_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "reviewed_definition_packet_artifact_id": definition_packet.get("schema_id"),
        "reviewed_definition_packet_outcome": definition_packet.get("outcome_id"),
        "candidate_symbols": definition_packet.get("candidate_symbols", []),
        "candidate_surface_count": definition_packet.get("candidate_surface_count"),
        "matter_surface_inventory": definition_packet.get(
            "matter_surface_inventory", []
        ),
        "candidate_status_summary": definition_packet.get(
            "candidate_status_summary", {}
        ),
        "route_status_summary": definition_packet.get("route_status_summary", {}),
        "review_criteria": review_criteria,
        "review_criteria_count": len(review_criteria),
        "review_criteria_accepted_count": sum(
            1 for row in review_criteria if row["status"] == "accepted"
        ),
        "acceptance_criteria": acceptance_criteria,
        "scalar_witness_closeout_preserved_as_reference": definition_packet.get(
            "scalar_witness_closeout_preserved_as_reference"
        ),
        "scalar_sandbox_reopened": False,
        "master_action_working_form_noncanonical": True,
        "master_action_surface_index_accepted": accepted,
        "route_selection_authorized": accepted,
        "recommended_first_route_hint": RECOMMENDED_FIRST_ROUTE_HINT,
        "recommended_first_route_target_hint": RECOMMENDED_FIRST_ROUTE_TARGET_HINT,
        "recommended_first_route_status": RECOMMENDED_FIRST_ROUTE_STATUS,
        "recommended_first_route_reason": (
            "phi is the shortest comparison path because the imported scalar "
            "sandbox already produced a positive classical source witness; the "
            "route selector must still make the formal selection."
        ),
        "route_selection_candidate_targets": FIRST_CALCULATION_ROUTE_CANDIDATES,
        "next_sequence": [
            "select_toe_native_matter_sector_calculation_route",
            "prepare_toe_native_phi_surface_variation_and_source_route_packet",
            "review_toe_native_phi_surface_variation_and_source_route_result",
            "compare_phi_native_candidate_route_against_provisional_scalar_witness",
        ],
        "definition_packet_only_review": True,
        "formal_theorem_backed_matter_derivation": False,
        "record_validated": True,
        "symbolic_calculation_recorded": False,
        "proof_depth_label": "RECORD_ONLY_REVIEW_VALIDATED",
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
            "direct phi route execution without selector",
        ],
        "downstream_progression": [
            {
                "stage": "definition_packet_result_review",
                "status": "ACCEPTED_SURFACE_INDEX_NO_DERIVATION_CLAIM",
                "decision": REVIEW_RESULT,
                "reason": (
                    "The review accepts only the master-action matter-surface "
                    "index and associated blocked/specified route statuses."
                ),
            },
            {
                "stage": "toe_native_matter_sector_calculation_route_selection",
                "status": "NEXT_TARGET_AUTHORIZED",
                "decision": selected_next_target,
                "reason": (
                    "The next packet should choose one indexed surface and "
                    "route, without jumping directly to all-matter derivation."
                ),
            },
            {
                "stage": "recommended_phi_route",
                "status": RECOMMENDED_FIRST_ROUTE_STATUS,
                "decision": RECOMMENDED_FIRST_ROUTE_TARGET_HINT,
                "reason": (
                    "The recommendation is a selector input only; it does not "
                    "supersede route selection."
                ),
            },
        ],
        "mathematical_statement": (
            "The result review accepts the ToE-native matter-sector definition "
            "packet as an index of master-action candidate surfaces only: psi, "
            "A, phi, rho, and C_k are recorded with status, variation, "
            "stress-energy, quantum/operator, and seam-dependency routes. No "
            "matter derivation, Standard Model derivation, canonical promotion, "
            "QFT-GR closure, or semiclassical coupling is claimed."
        ),
        "non_claim_boundary": (
            "This review accepts a candidate surface index only. It does not "
            "derive ToE-native matter, derive the Standard Model, promote the "
            "master action, close QFT-GR, authorize semiclassical coupling, "
            "claim empirical validation, claim public readiness, or execute the "
            "phi route before route selection."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.ToeNativeMatterSectorDefinitionPacketResultReview",
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


def write_toe_native_matter_sector_definition_packet_result_review(
    *,
    definition_packet_path: Path = DEFINITION_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_toe_native_matter_sector_definition_packet_result_review(
        definition_packet_path=definition_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the ToE-native matter-sector definition packet result review."
        )
    )
    parser.add_argument("--definition-packet", type=Path, default=DEFINITION_PACKET_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    definition_packet_path = (
        args.definition_packet
        if args.definition_packet.is_absolute()
        else REPO_ROOT / args.definition_packet
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = write_toe_native_matter_sector_definition_packet_result_review(
        definition_packet_path=definition_packet_path,
        out=out,
        captured_at_utc=args.captured_at_utc,
    )
    print(
        "toe_native_matter_sector_definition_packet_result_review_report: "
        f"wrote {out} outcome={payload['outcome_id']} "
        f"next={payload['selected_next_target']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

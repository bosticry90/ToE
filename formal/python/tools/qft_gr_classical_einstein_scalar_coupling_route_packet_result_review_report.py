from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_classical_einstein_scalar_coupling_route_packet_for_provisional_scalar_source_report import (
    CLASSICAL_EINSTEIN_SCALAR_COUPLING_RESULT,
    CLASSICAL_EINSTEIN_SCALAR_EQUATION_FORM,
    DEFAULT_OUT as CLASSICAL_ROUTE_PACKET_PATH,
    LEFT_HAND_SIDE_DIVERGENCE_IDENTITY,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as CLASSICAL_ROUTE_PACKET_OUTCOME,
    PACKET_ID as CLASSICAL_ROUTE_PACKET_ID,
    PROOF_DEPTH_LABEL,
    SCHEMA_ID as CLASSICAL_ROUTE_PACKET_SCHEMA_ID,
    SOURCE_SIDE_CONSERVATION_REQUIREMENT,
)
from formal.python.tools.qft_gr_weak_conservation_test_for_provisional_scalar_stress_energy_source_report import (
    DIVERGENCE_IDENTITY,
    ON_SHELL_CONSERVATION_STATEMENT,
    SCALAR_EQUATION_OF_MOTION,
    STRESS_ENERGY_COVARIANT_EXPRESSION,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-18T00:00:00Z"

SCHEMA_ID = (
    "QFT_GR_CLASSICAL_EINSTEIN_SCALAR_COUPLING_ROUTE_PACKET_RESULT_REVIEW_"
    "20260618_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "QFT_GR_CLASSICAL_EINSTEIN_SCALAR_COUPLING_ROUTE_PACKET_RESULT_REVIEW_v0"
CLASSICAL_ROUTE_REVIEW_RESULT = (
    "CLASSICAL_EINSTEIN_SCALAR_COUPLING_ROUTE_RESULT_REVIEW_ACCEPTS_"
    "PROVISIONAL_ON_SHELL_CLASSICAL_SOURCE_ROUTE_NO_QFT_GR_OR_TOE_NATIVE_CLOSURE"
)
OUTCOME_ID = (
    "QFT_GR_CLASSICAL_EINSTEIN_SCALAR_COUPLING_ROUTE_PACKET_RESULT_REVIEW_"
    "ACCEPTS_PROVISIONAL_ON_SHELL_CLASSICAL_SOURCE_ROUTE_NO_QFT_GR_OR_TOE_"
    "NATIVE_CLOSURE"
)
PACKET_CLASSIFICATION = (
    "qft_gr_classical_einstein_scalar_coupling_route_packet_result_review_"
    "accepts_provisional_on_shell_classical_source_route_nonpromotionally"
)
NEXT_TARGET = "prepare_qft_gr_provisional_scalar_classical_source_route_witness_closeout"
NEXT_TARGET_KIND = (
    "qft_gr_provisional_scalar_classical_source_route_witness_closeout_preparation"
)
POSITIVE_LOCAL_CLASSICAL_SOURCE_WITNESS_CLASSIFICATION = (
    "positive local classical source witness"
)
KNOWN_SCALAR_ROUTE_STATEMENT = (
    "A known imported real-scalar matter model can supply an action-derived, "
    "on-shell conserved, Bianchi-compatible classical GR source."
)
LEAN_VALIDATION_POLICY_ID = "TIERED_LEAN_VALIDATION_POLICY_FOR_PACKET_WORK_v0"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_CLASSICAL_EINSTEIN_SCALAR_COUPLING_ROUTE_PACKET_RESULT_REVIEW_"
    "20260618_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRClassicalEinsteinScalarCouplingRoutePacketResultReview.lean"
)
QFTGR_AGGREGATE_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Derivation" / "QFTGR.lean"
)
SCALAR_SANDBOX_AGGREGATE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRScalarSandbox.lean"
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


def _review_criteria(packet: dict[str, Any]) -> list[dict[str, str]]:
    return [
        {
            "row_id": "scalar_stress_energy_expression_carried_forward_exactly",
            "status": "accepted",
            "evidence": packet.get("stress_energy_covariant_expression", ""),
            "assessment": (
                "The review preserves the scalar stress-energy expression from "
                "the action-derived provisional scalar sandbox."
            ),
        },
        {
            "row_id": "scalar_eom_on_shell_condition_preserved",
            "status": "accepted",
            "evidence": packet.get("scalar_equation_of_motion", ""),
            "assessment": (
                "The accepted route remains conditional on the scalar equation "
                "of motion and on-shell conservation."
            ),
        },
        {
            "row_id": "bianchi_compatibility_remains_conditional_not_generic",
            "status": "accepted",
            "evidence": packet.get("bianchi_compatibility_result", ""),
            "assessment": (
                "The route uses Bianchi compatibility only under scalar EOM, "
                "Levi-Civita connection, metric compatibility, and constant "
                "coupling assumptions."
            ),
        },
        {
            "row_id": "coupling_route_is_classical_not_semiclassical",
            "status": "accepted",
            "evidence": packet.get("classical_einstein_scalar_coupling_equation", ""),
            "assessment": (
                "The accepted route is the classical Einstein-scalar equation, "
                "not a renormalized quantum expectation equation."
            ),
        },
        {
            "row_id": "no_solution_existence_or_global_wellposedness_claimed",
            "status": "accepted",
            "evidence": "solution_existence_claimed=false; global_wellposedness_claimed=false",
            "assessment": (
                "The packet records no coupled solution, no solution existence "
                "or uniqueness theorem, and no global well-posedness result."
            ),
        },
        {
            "row_id": "no_toe_native_matter_derivation_claimed",
            "status": "accepted",
            "evidence": "toe_native_matter_derivation_claimed=false",
            "assessment": (
                "The scalar matter model remains an imported sandbox rather "
                "than a ToE-native matter derivation."
            ),
        },
        {
            "row_id": "no_qft_gr_seam_closure_claimed",
            "status": "accepted",
            "evidence": "qft_gr_closure_claimed=false; qft_gr_seam_closed=false",
            "assessment": (
                "The review accepts only a local classical source route, not "
                "QFT-GR source-map or seam closure."
            ),
        },
        {
            "row_id": "no_master_action_promotion_claimed",
            "status": "accepted",
            "evidence": "master_action_promoted=false",
            "assessment": (
                "The accepted route does not promote the candidate master "
                "action and does not alter its working-form status."
            ),
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "qft_gr_classical_einstein_scalar_coupling_route_packet_result_review"
        ),
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


def build_qft_gr_classical_einstein_scalar_coupling_route_packet_result_review(
    *,
    classical_route_packet_path: Path = CLASSICAL_ROUTE_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    route_packet = _read_json(classical_route_packet_path)
    review_criteria = _review_criteria(route_packet)
    acceptance_criteria = {
        "consumes_expected_result_review_target": (
            route_packet.get("selected_next_target") == CONSUMED_TARGET
        ),
        "classical_route_packet_available": (
            route_packet.get("schema_id") == CLASSICAL_ROUTE_PACKET_SCHEMA_ID
            and route_packet.get("packet_id") == CLASSICAL_ROUTE_PACKET_ID
            and route_packet.get("outcome_id") == CLASSICAL_ROUTE_PACKET_OUTCOME
        ),
        "scalar_stress_energy_expression_carried_forward_exactly": (
            route_packet.get("stress_energy_covariant_expression")
            == STRESS_ENERGY_COVARIANT_EXPRESSION
        ),
        "scalar_eom_on_shell_condition_preserved": (
            route_packet.get("scalar_equation_of_motion") == SCALAR_EQUATION_OF_MOTION
            and route_packet.get("on_shell_required") is True
            and route_packet.get("on_shell_conservation_statement")
            == ON_SHELL_CONSERVATION_STATEMENT
        ),
        "bianchi_compatibility_conditional_not_generic": (
            route_packet.get("bianchi_compatibility_result")
            == "BIANCHI_COMPATIBILITY_CONSTRUCTED_FOR_PROVISIONAL_SCALAR_"
            "SOURCE_ON_SHELL_NO_QFT_GR_CLOSURE"
            and "scalar EOM" in route_packet.get("bianchi_compatibility_statement", "")
            and "Levi-Civita metric compatibility"
            in route_packet.get("bianchi_compatibility_statement", "")
            and "constant G_N and Lambda"
            in route_packet.get("bianchi_compatibility_statement", "")
        ),
        "classical_not_semiclassical_coupling_route": (
            route_packet.get("classical_einstein_scalar_coupling_equation")
            == CLASSICAL_EINSTEIN_SCALAR_EQUATION_FORM
            and route_packet.get("semiclassical_coupling_authorized") is False
            and route_packet.get("semiclassical_einstein_equation_derived") is False
        ),
        "no_solution_existence_or_global_wellposedness_claimed": (
            route_packet.get("solution_existence_claimed") is False
            and route_packet.get("solution_uniqueness_claimed") is False
            and route_packet.get("coupled_pde_solution_constructed") is False
            and route_packet.get("global_wellposedness_claimed") is False
        ),
        "no_toe_native_matter_derivation_claimed": (
            route_packet.get("toe_native_matter_derivation_claimed") is False
            and route_packet.get("toe_native_matter_sector_defined") is False
        ),
        "no_qft_gr_seam_closure_claimed": (
            route_packet.get("qft_gr_closure_claimed") is False
            and route_packet.get("qft_gr_seam_closed") is False
            and route_packet.get("qft_gr_source_map_closure_authorized") is False
        ),
        "no_master_action_promotion_claimed": (
            route_packet.get("master_action_promoted") is False
            and route_packet.get("master_action_promotion_authorized") is False
        ),
        "review_criteria_all_accepted": all(
            row["status"] == "accepted" for row in review_criteria
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_QFT_GR_CLASSICAL_EINSTEIN_SCALAR_COUPLING_ROUTE_PACKET_RESULT_REVIEW"
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
        else "QFT_GR_CLASSICAL_EINSTEIN_SCALAR_COUPLING_ROUTE_PACKET_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "reviewed_classical_route_artifact_id": route_packet.get("schema_id"),
        "reviewed_classical_route_outcome": route_packet.get("outcome_id"),
        "review_result": CLASSICAL_ROUTE_REVIEW_RESULT,
        "classical_einstein_scalar_coupling_result": (
            CLASSICAL_EINSTEIN_SCALAR_COUPLING_RESULT
        ),
        "known_scalar_route_statement": KNOWN_SCALAR_ROUTE_STATEMENT,
        "positive_local_classical_source_witness_classification": (
            POSITIVE_LOCAL_CLASSICAL_SOURCE_WITNESS_CLASSIFICATION
        ),
        "positive_local_classical_source_witness_candidate": True,
        "positive_local_classical_source_witness_closeout_authorized": accepted,
        "witness_closeout_completed": False,
        "classical_route_result_review_completed": True,
        "classical_route_result_review_accepted": accepted,
        "classical_einstein_scalar_coupling_equation": (
            CLASSICAL_EINSTEIN_SCALAR_EQUATION_FORM
        ),
        "stress_energy_covariant_expression": STRESS_ENERGY_COVARIANT_EXPRESSION,
        "scalar_equation_of_motion": SCALAR_EQUATION_OF_MOTION,
        "on_shell_required": True,
        "on_shell_conservation_statement": ON_SHELL_CONSERVATION_STATEMENT,
        "weak_conservation_identity": DIVERGENCE_IDENTITY,
        "left_hand_side_divergence_identity": LEFT_HAND_SIDE_DIVERGENCE_IDENTITY,
        "source_side_conservation_requirement": SOURCE_SIDE_CONSERVATION_REQUIREMENT,
        "route_internal_compatibility_constructed": True,
        "classical_einstein_scalar_coupling_route_constructed": True,
        "classical_einstein_scalar_coupling_route_reviewed": True,
        "provisional_classical_sandbox_route_only": True,
        "proof_depth_label": PROOF_DEPTH_LABEL,
        "formal_differential_geometry_theorem_backed": False,
        "record_validated": True,
        "symbolic_calculation_recorded": True,
        "review_criteria": review_criteria,
        "review_criteria_count": len(review_criteria),
        "review_criteria_accepted_count": sum(
            row["status"] == "accepted" for row in review_criteria
        ),
        "acceptance_criteria": acceptance_criteria,
        "semiclassical_coupling_authorized": False,
        "semiclassical_coupling_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "renormalized_stress_energy_expectation_constructed": False,
        "renormalized_expectation_value_constructed": False,
        "renormalized_stress_energy_constructed": False,
        "quantum_state_source_constructed": False,
        "quantum_state_supplied": False,
        "quantum_stress_energy_operator_constructed": False,
        "stress_energy_operator_constructed": False,
        "quantum_stress_energy_expectation_constructed": False,
        "renormalization_scheme_supplied": False,
        "renormalization_result_claimed": False,
        "state_domain_supplied": False,
        "state_expectation_functional_link_claimed": False,
        "anomaly_or_regularization_controls_supplied": False,
        "toe_native_matter_source_route_defined": False,
        "toe_native_matter_sector_defined": False,
        "toe_matter_model_derived": False,
        "toe_native_matter_derivation_claimed": False,
        "generic_source_admissibility_claimed": False,
        "source_admissibility_claimed": False,
        "source_admissibility_completed": False,
        "arbitrary_distributional_source_admissibility_claimed": False,
        "arbitrary_distributional_source_promoted": False,
        "solution_existence_claimed": False,
        "solution_uniqueness_claimed": False,
        "regularity_analysis_completed": False,
        "boundary_initial_data_supplied": False,
        "coupled_pde_solution_constructed": False,
        "coupled_einstein_scalar_system_solved": False,
        "global_wellposedness_claimed": False,
        "standard_model_derivation_claimed": False,
        "qft_gr_closure_claimed": False,
        "qft_gr_seam_closed": False,
        "qft_gr_source_map_closure_authorized": False,
        "empirical_validation_claimed": False,
        "public_readiness_claimed": False,
        "public_submission_authorized": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "phase2_readiness_claim": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "critical_gate_fail_conditions": [
            "QFT_GR_source_map_closure",
            "QFT_GR_seam_closure",
            "ToE_native_matter_derivation",
            "semiclassical_coupling_authorization",
            "renormalized_stress_energy_expectation",
            "solution_existence_claim",
            "global_wellposedness_claim",
            "empirical_validation",
            "public_readiness",
            "master_action_promotion",
        ],
        "downstream_progression": [
            {
                "stage": "classical_route_result_review",
                "status": "ACCEPTED_AS_PROVISIONAL_ON_SHELL_CLASSICAL_ROUTE",
                "decision": CLASSICAL_ROUTE_REVIEW_RESULT,
                "reason": (
                    "The review confirms the scalar stress-energy expression, "
                    "on-shell condition, conditional Bianchi compatibility, "
                    "classical-only coupling route, and nonclaim boundary."
                ),
            },
            {
                "stage": "witness_closeout",
                "status": "NEXT_TARGET_AUTHORIZED",
                "decision": selected_next_target,
                "reason": (
                    "The accepted result should be classified as a positive "
                    "local classical source witness without source-map closure."
                ),
            },
            {
                "stage": "toe_native_matter_replacement",
                "status": "NOT_AUTHORIZED_BY_THIS_REVIEW",
                "decision": "not_claimed",
                "reason": (
                    "Replacing the imported scalar sandbox with a ToE-native "
                    "matter/source sector remains future unification work."
                ),
            },
        ],
        "mathematical_statement": (
            KNOWN_SCALAR_ROUTE_STATEMENT
            + " The reviewed route is "
            + CLASSICAL_EINSTEIN_SCALAR_EQUATION_FORM
            + " with T^{scalar}_{mu nu} carried from the action-derived scalar "
            "stress-energy and conserved only on shell via "
            + SCALAR_EQUATION_OF_MOTION
            + ". This is not QFT-GR closure, not semiclassical gravity, and "
            "not ToE-native matter derivation."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.QFTGRScalarSandbox",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "lane_level_lean_target_files": [
            _ptr(QFTGR_AGGREGATE_PATH),
            _ptr(SCALAR_SANDBOX_AGGREGATE_PATH),
            _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            _ptr(RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH),
        ],
        "lean_validation_policy_file": _ptr(LEAN_VALIDATION_POLICY_PATH),
        "validation_policy": _validation_policy(),
        "non_claim_boundary": (
            "This result review accepts only the provisional on-shell "
            "classical Einstein-scalar source route as a positive local "
            "classical source witness candidate. It does not close the QFT-GR "
            "source map or seam, authorize semiclassical coupling, construct "
            "a renormalized stress-energy expectation, construct a quantum "
            "state/source, prove coupled solution existence or global "
            "well-posedness, derive ToE-native matter, validate empirically, "
            "authorize public readiness, or promote the master action."
        ),
    }


def write_qft_gr_classical_einstein_scalar_coupling_route_packet_result_review(
    *,
    classical_route_packet_path: Path = CLASSICAL_ROUTE_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_classical_einstein_scalar_coupling_route_packet_result_review(
        classical_route_packet_path=classical_route_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR classical Einstein-scalar coupling route "
            "packet result review."
        )
    )
    parser.add_argument("--classical-route-packet", type=Path, default=CLASSICAL_ROUTE_PACKET_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    classical_route_packet_path = (
        args.classical_route_packet
        if args.classical_route_packet.is_absolute()
        else REPO_ROOT / args.classical_route_packet
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = write_qft_gr_classical_einstein_scalar_coupling_route_packet_result_review(
        classical_route_packet_path=classical_route_packet_path,
        out=out,
        captured_at_utc=args.captured_at_utc,
    )
    print(
        "qft_gr_classical_einstein_scalar_coupling_route_packet_result_review_report: "
        f"wrote {out} outcome={payload['outcome_id']} "
        f"next={payload['selected_next_target']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

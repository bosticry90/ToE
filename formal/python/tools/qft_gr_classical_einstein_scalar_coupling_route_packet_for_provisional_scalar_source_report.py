from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_bianchi_compatibility_test_for_provisional_scalar_stress_energy_source_report import (
    BIANCHI_COMPATIBILITY_RESULT,
    BIANCHI_COMPATIBILITY_STATEMENT,
    CONTRACTED_BIANCHI_IDENTITY,
    METRIC_COMPATIBILITY_IDENTITY,
    SOURCE_SIDE_CONSERVATION_REQUIREMENT,
)
from formal.python.tools.qft_gr_semiclassical_coupling_gate_scope_review_for_provisional_scalar_source_report import (
    CLASSICAL_EINSTEIN_SCALAR_EQUATION_FORM,
    DEFAULT_OUT as SEMICLASSICAL_GATE_PACKET_PATH,
    NEXT_TARGET as AUTHORIZED_CLASSICAL_ROUTE_TARGET,
    OUTCOME_ID as SEMICLASSICAL_GATE_OUTCOME,
    PROOF_DEPTH_LABEL,
    SCHEMA_ID as SEMICLASSICAL_GATE_SCHEMA_ID,
    SEMICLASSICAL_COUPLING_GATE_RESULT,
    SEMICLASSICAL_COUPLING_NOT_AUTHORIZED_RESULT,
)
from formal.python.tools.qft_gr_source_admissibility_review_for_provisional_scalar_source_report import (
    PROVISIONAL_SCALAR_SOURCE_ADMISSIBILITY_RESULT,
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
    "QFT_GR_CLASSICAL_EINSTEIN_SCALAR_COUPLING_ROUTE_PACKET_FOR_PROVISIONAL_"
    "SCALAR_SOURCE_20260618_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "QFT_GR_CLASSICAL_EINSTEIN_SCALAR_COUPLING_ROUTE_PACKET_FOR_PROVISIONAL_"
    "SCALAR_SOURCE_v0"
)
CONSUMED_TARGET = AUTHORIZED_CLASSICAL_ROUTE_TARGET
NEXT_TARGET = "review_qft_gr_classical_einstein_scalar_coupling_route_packet_result"
NEXT_TARGET_KIND = "qft_gr_classical_einstein_scalar_coupling_route_packet_result_review"
CLASSICAL_EINSTEIN_SCALAR_COUPLING_RESULT = (
    "CLASSICAL_EINSTEIN_SCALAR_COUPLING_ROUTE_CONSTRUCTED_FOR_PROVISIONAL_"
    "ON_SHELL_SCALAR_SOURCE_NO_QFT_GR_OR_TOE_NATIVE_CLOSURE"
)
OUTCOME_ID = (
    "QFT_GR_CLASSICAL_EINSTEIN_SCALAR_COUPLING_ROUTE_PACKET_FOR_PROVISIONAL_"
    "SCALAR_SOURCE_PREPARED_WITH_CLASSICAL_EINSTEIN_SCALAR_COUPLING_ROUTE_"
    "CONSTRUCTED_FOR_PROVISIONAL_ON_SHELL_SCALAR_SOURCE_NO_QFT_GR_OR_TOE_"
    "NATIVE_CLOSURE"
)
PACKET_CLASSIFICATION = (
    "qft_gr_classical_einstein_scalar_coupling_route_packet_constructs_"
    "provisional_on_shell_classical_route_nonpromotionally"
)
LEFT_HAND_SIDE_DIVERGENCE_IDENTITY = (
    "nabla_mu(G^{mu nu} + Lambda g^{mu nu}) = 0"
)
CLASSICAL_ROUTE_SCOPE = (
    "provisional classical Einstein-scalar sandbox route only; no coupled "
    "solution existence, uniqueness, regularity, global well-posedness, "
    "semiclassical coupling, or ToE-native matter derivation"
)
NEXT_AFTER_RESULT_REVIEW_SUGGESTED = (
    "prepare_qft_gr_provisional_scalar_classical_source_route_witness_closeout"
)
LEAN_VALIDATION_POLICY_ID = "TIERED_LEAN_VALIDATION_POLICY_FOR_PACKET_WORK_v0"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_CLASSICAL_EINSTEIN_SCALAR_COUPLING_ROUTE_PACKET_FOR_PROVISIONAL_"
    "SCALAR_SOURCE_20260618_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRClassicalEinsteinScalarCouplingRoutePacketForProvisionalScalarSource.lean"
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
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "LEAN_VALIDATION_TIER_POLICY_v0.md"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _route_construction_steps() -> list[dict[str, str]]:
    return [
        {
            "step_id": "restate_provisional_scalar_stress_energy",
            "mathematical_content": STRESS_ENERGY_COVARIANT_EXPRESSION,
            "claim": "the classical scalar stress-energy source is reused from the action-derived scalar sandbox",
        },
        {
            "step_id": "state_on_shell_scalar_condition",
            "mathematical_content": SCALAR_EQUATION_OF_MOTION,
            "claim": "the route is conditional on the scalar field equation",
        },
        {
            "step_id": "state_classical_einstein_scalar_equation",
            "mathematical_content": CLASSICAL_EINSTEIN_SCALAR_EQUATION_FORM,
            "claim": "classical Einstein-scalar equation stated as provisional sandbox route",
        },
        {
            "step_id": "state_left_hand_side_identity",
            "mathematical_content": (
                CONTRACTED_BIANCHI_IDENTITY
                + " and "
                + METRIC_COMPATIBILITY_IDENTITY
            ),
            "claim": "Bianchi identity and metric compatibility make the left-hand side divergence-free for constant Lambda",
        },
        {
            "step_id": "insert_scalar_on_shell_conservation",
            "mathematical_content": DIVERGENCE_IDENTITY,
            "claim": "the prior scalar conservation identity supplies source-side conservation on shell",
        },
        {
            "step_id": "conclude_internal_classical_route_compatibility",
            "mathematical_content": (
                LEFT_HAND_SIDE_DIVERGENCE_IDENTITY
                + " and on shell "
                + SOURCE_SIDE_CONSERVATION_REQUIREMENT
            ),
            "claim": "the provisional scalar source can consistently appear on the right-hand side of the classical Einstein equation",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "qft_gr_classical_einstein_scalar_coupling_route_packet_for_"
            "provisional_scalar_source"
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
        "aggregate_lean_validation_status_allowed_values": [
            "PASSED",
            "INCOMPLETE_TIMEOUT_STEADY_PROGRESS",
            "FAILED",
            "NOT_RUN",
        ],
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
        "full_security_scan_required": False,
    }


def build_qft_gr_classical_einstein_scalar_coupling_route_packet_for_provisional_scalar_source(
    *,
    semiclassical_gate_packet_path: Path = SEMICLASSICAL_GATE_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    gate_packet = _read_json(semiclassical_gate_packet_path)
    route_steps = _route_construction_steps()
    acceptance_criteria = {
        "consumes_authorized_classical_route_target": (
            gate_packet.get("selected_next_target") == CONSUMED_TARGET
        ),
        "semiclassical_gate_packet_available": (
            gate_packet.get("schema_id") == SEMICLASSICAL_GATE_SCHEMA_ID
            and gate_packet.get("outcome_id") == SEMICLASSICAL_GATE_OUTCOME
        ),
        "classical_route_packet_authorized_by_gate": (
            gate_packet.get("classical_einstein_scalar_coupling_route_packet_authorized")
            is True
        ),
        "semiclassical_route_remains_not_authorized": (
            gate_packet.get("semiclassical_coupling_authorized") is False
            and gate_packet.get("semiclassical_einstein_equation_derived") is False
        ),
        "local_scalar_source_admissibility_carried": (
            gate_packet.get("source_admissibility_result")
            == PROVISIONAL_SCALAR_SOURCE_ADMISSIBILITY_RESULT
            and gate_packet.get("local_source_admissibility_review_passed") is True
        ),
        "classical_coupling_equation_stated": (
            CLASSICAL_EINSTEIN_SCALAR_EQUATION_FORM
            == "G_{mu nu} + Lambda g_{mu nu} = 8 pi G_N T^{scalar}_{mu nu}"
        ),
        "source_side_conservation_available_on_shell": (
            SCALAR_EQUATION_OF_MOTION == "box_g phi - V'(phi) = 0"
            and "nabla_mu T^{mu nu}" in DIVERGENCE_IDENTITY
        ),
        "left_hand_side_divergence_free_under_scope": (
            LEFT_HAND_SIDE_DIVERGENCE_IDENTITY
            == "nabla_mu(G^{mu nu} + Lambda g^{mu nu}) = 0"
        ),
        "solution_existence_and_wellposedness_not_claimed": True,
    }
    prepared = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if prepared
        else "REMEDIATE_QFT_GR_CLASSICAL_EINSTEIN_SCALAR_COUPLING_ROUTE_PACKET"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_NONLIVE_ROUTE_PACKET_RESULT",
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "accepted": prepared,
        "outcome_id": OUTCOME_ID
        if prepared
        else "QFT_GR_CLASSICAL_EINSTEIN_SCALAR_COUPLING_ROUTE_PACKET_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "authorized_by_semiclassical_gate_artifact_id": gate_packet.get("schema_id"),
        "authorized_by_semiclassical_gate_outcome": gate_packet.get("outcome_id"),
        "semiclassical_coupling_gate_result": SEMICLASSICAL_COUPLING_GATE_RESULT,
        "semiclassical_coupling_not_authorized_result": (
            SEMICLASSICAL_COUPLING_NOT_AUTHORIZED_RESULT
        ),
        "classical_einstein_scalar_coupling_result": (
            CLASSICAL_EINSTEIN_SCALAR_COUPLING_RESULT
        ),
        "classical_einstein_scalar_coupling_route_packet_prepared": True,
        "classical_einstein_scalar_coupling_route_constructed": True,
        "classical_einstein_scalar_coupling_route_recorded": True,
        "classical_einstein_scalar_coupling_route_claimed_scope": CLASSICAL_ROUTE_SCOPE,
        "classical_einstein_scalar_coupling_equation": (
            CLASSICAL_EINSTEIN_SCALAR_EQUATION_FORM
        ),
        "stress_energy_covariant_expression": STRESS_ENERGY_COVARIANT_EXPRESSION,
        "scalar_equation_of_motion": SCALAR_EQUATION_OF_MOTION,
        "on_shell_required": True,
        "on_shell_conservation_statement": ON_SHELL_CONSERVATION_STATEMENT,
        "weak_conservation_identity": DIVERGENCE_IDENTITY,
        "bianchi_compatibility_result": BIANCHI_COMPATIBILITY_RESULT,
        "bianchi_compatibility_statement": BIANCHI_COMPATIBILITY_STATEMENT,
        "contracted_bianchi_identity": CONTRACTED_BIANCHI_IDENTITY,
        "metric_compatibility_identity": METRIC_COMPATIBILITY_IDENTITY,
        "left_hand_side_divergence_identity": LEFT_HAND_SIDE_DIVERGENCE_IDENTITY,
        "source_side_conservation_requirement": SOURCE_SIDE_CONSERVATION_REQUIREMENT,
        "route_internal_compatibility_constructed": True,
        "provisional_scalar_source_passes_local_source_admissibility_review": True,
        "local_source_admissibility_review_passed": True,
        "provisional_classical_sandbox_route_only": True,
        "bounded_positive_classical_source_route_witness_candidate": True,
        "witness_closeout_completed": False,
        "next_after_result_review_suggested": NEXT_AFTER_RESULT_REVIEW_SUGGESTED,
        "proof_depth_label": PROOF_DEPTH_LABEL,
        "formal_differential_geometry_theorem_backed": False,
        "record_validated": True,
        "symbolic_calculation_recorded": True,
        "route_construction_steps": route_steps,
        "route_construction_step_count": len(route_steps),
        "accepted_outcomes_considered": [
            CLASSICAL_EINSTEIN_SCALAR_COUPLING_RESULT,
            "CLASSICAL_EINSTEIN_SCALAR_COUPLING_ROUTE_RECORDED_FOR_PROVISIONAL_SOURCE_NO_SOLUTION_OR_SEAM_CLOSURE",
            "CLASSICAL_EINSTEIN_SCALAR_COUPLING_ROUTE_BLOCKED_BY_MISSING_ON_SHELL_SOURCE_CONSERVATION",
        ],
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
            "semiclassical_coupling",
            "renormalized_stress_energy_expectation",
            "quantum_state_or_source_construction",
            "ToE_native_matter_derivation",
            "generic_source_admissibility",
            "solution_existence_claim",
            "global_wellposedness_claim",
            "QFT_GR_seam_closure",
            "master_action_promotion",
        ],
        "downstream_progression": [
            {
                "stage": "classical_einstein_scalar_route_result_review",
                "status": "RESULT_REVIEW_AUTHORIZED",
                "decision": selected_next_target,
                "reason": (
                    "The packet records a bounded classical source route and "
                    "requires result review before witness closeout."
                ),
            },
            {
                "stage": "provisional_scalar_classical_source_route_witness_closeout",
                "status": "SUGGESTED_AFTER_RESULT_REVIEW_ONLY",
                "decision": NEXT_AFTER_RESULT_REVIEW_SUGGESTED,
                "reason": (
                    "The scalar sandbox branch should close out as a bounded "
                    "positive classical source witness before any native-matter pivot."
                ),
            },
        ],
        "mathematical_statement": (
            "The provisional on-shell scalar source can be placed consistently "
            "on the right-hand side of the classical Einstein equation "
            + CLASSICAL_EINSTEIN_SCALAR_EQUATION_FORM
            + " because "
            + LEFT_HAND_SIDE_DIVERGENCE_IDENTITY
            + " and, on shell, "
            + SOURCE_SIDE_CONSERVATION_REQUIREMENT
            + ". This is a classical sandbox route only."
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
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet constructs only the provisional classical "
            "Einstein-scalar route under on-shell scalar-source conservation. "
            "It does not construct a coupled solution, prove solution "
            "existence or uniqueness, prove global well-posedness, authorize "
            "semiclassical coupling, construct a renormalized stress-energy "
            "expectation, construct a quantum state/source, derive ToE-native "
            "matter, claim generic source admissibility, close QFT-GR, "
            "validate empirically, authorize public readiness, or promote the "
            "master action."
        ),
    }


def write_qft_gr_classical_einstein_scalar_coupling_route_packet_for_provisional_scalar_source(
    *,
    semiclassical_gate_packet_path: Path = SEMICLASSICAL_GATE_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_classical_einstein_scalar_coupling_route_packet_for_provisional_scalar_source(
        semiclassical_gate_packet_path=semiclassical_gate_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR classical Einstein-scalar coupling route "
            "packet for the provisional scalar source."
        )
    )
    parser.add_argument("--semiclassical-gate-packet", type=Path, default=SEMICLASSICAL_GATE_PACKET_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    payload = write_qft_gr_classical_einstein_scalar_coupling_route_packet_for_provisional_scalar_source(
        semiclassical_gate_packet_path=args.semiclassical_gate_packet,
        out=args.out,
        captured_at_utc=args.captured_at_utc,
    )
    print(
        "qft_gr_classical_einstein_scalar_coupling_route_packet_for_provisional_scalar_source_report: "
        f"wrote {args.out} outcome={payload['outcome_id']} "
        f"next={payload['selected_next_target']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

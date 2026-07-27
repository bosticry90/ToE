from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
PACKET_RELATIVE_PATH = (
    "formal/docs/release/SHARED_LINEARIZED_QUADRATIC_GRAVITY_SOURCE_AND_"
    "SPECTRUM_COMPARISON_PACKET_20260718_v0.json"
)
HUMAN_REVIEW_RELATIVE_PATH = (
    "formal/docs/lanes/SHARED_LINEARIZED_QUADRATIC_GRAVITY_SOURCE_AND_"
    "SPECTRUM_COMPARISON_PACKET_REVIEW_20260718_v0.md"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/SHARED_LINEARIZED_QUADRATIC_GRAVITY_SOURCE_AND_"
    "SPECTRUM_COMPARISON_PACKET_REVIEW_20260718_v0.json"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_shared_linearized_quadratic_gravity_source_and_"
    "spectrum_comparison_packet_review_v0.py"
)
TARGET = (
    "review_shared_linearized_quadratic_gravity_source_and_spectrum_"
    "comparison_packet_v0_result"
)
VERDICT = (
    "ACCEPTED_FOR_ONE_BOUNDED_SHARED_LINEARIZED_QUADRATIC_GRAVITY_"
    "COMPARISON_EXECUTION"
)
SELECTED_NEXT_TARGET = (
    "execute_shared_linearized_quadratic_gravity_source_and_spectrum_"
    "comparison_v0"
)
SELECTED_NEXT_TARGET_KIND = (
    "ONE_BOUNDED_COMPARISON_EXECUTION_THEN_INDEPENDENT_RESULT_REVIEW"
)
RESULT_REVIEW_TARGET = (
    "review_shared_linearized_quadratic_gravity_source_and_spectrum_"
    "comparison_v0_result"
)

PACKET_HASHES = {
    "formal/docs/lanes/SHARED_LINEARIZED_QUADRATIC_GRAVITY_SOURCE_AND_SPECTRUM_COMPARISON_PACKET_20260718_v0.md":
        "cfbc31eb732588b9a7baf4496fdfac98abab19cf6851771d7e2a8908d6070057",
    PACKET_RELATIVE_PATH:
        "01ee3d662c3e0a346bd42e2f56c680fd0e790261161dc45577703933e4fab40b",
    "formal/python/tools/shared_linearized_quadratic_gravity_source_and_spectrum_comparison_packet_v0.py":
        "dd2c6a8b3b6008df99df07a64d5adb37127b7157a2bc0e3d9be0d61029507fc1",
    "formal/python/tests/test_shared_linearized_quadratic_gravity_source_and_spectrum_comparison_packet_v0.py":
        "14ea925f0d58509b8027f02d03962160b90456634de62284f315079795d2cb01",
    "formal/toe_formal/ToeFormal/Derivation/SharedLinearizedQuadraticGravitySourceAndSpectrumComparisonPacketV0.lean":
        "fa3a7b342b55039a3692f494a8fd740b73b322a8fe4cb591c2688235dd4cb275",
}

RESIDUE_RULE = (
    "At each simple physical pole, decompose the conserved-source saturated "
    "amplitude into the frozen spin-2 or scalar projector channel; factor out "
    "the common positive G/source normalization; and report the residue sign "
    "relative to the positive Einstein massless-spin-2 reference for a "
    "normalized physical polarization/source channel. Repeated, merged, or "
    "non-diagonalizable poles receive no sign until resolved by a limiting or "
    "diagonalized analysis."
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_packet() -> dict[str, Any]:
    value = json.loads((REPO_ROOT / PACKET_RELATIVE_PATH).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError("comparison packet must be a JSON object")
    return value


def _validate_packet() -> tuple[list[dict[str, str]], dict[str, Any]]:
    custody: list[dict[str, str]] = []
    for relative_path, expected in PACKET_HASHES.items():
        observed = _sha256(REPO_ROOT / relative_path)
        if observed != expected:
            raise ValueError(f"comparison packet custody drift: {relative_path}")
        custody.append({"relative_path": relative_path, "sha256": observed})
    packet = _load_packet()
    if packet.get("verdict") != "PREPARED_PENDING_INDEPENDENT_REVIEW":
        raise ValueError("packet is not pending independent review")
    if packet.get("selected_next_target") != TARGET:
        raise ValueError("packet does not rotate to this review")
    if packet["scope"].get("comparison_execution_authorized") is not False:
        raise ValueError("prepared packet improperly authorized execution")
    return custody, packet


def _add(a: tuple[int, int, int], b: tuple[int, int, int]) -> tuple[int, int, int]:
    return tuple(x + y for x, y in zip(a, b, strict=True))  # type: ignore[return-value]


def _scale(a: tuple[int, int, int], n: int) -> tuple[int, int, int]:
    return tuple(n * x for x in a)  # type: ignore[return-value]


def _normalization_audit() -> dict[str, Any]:
    # SI base-dimension exponents are ordered M, L, T.
    c = (0, 1, -1)
    G = (-1, 3, -2)
    A_EH = _add(_scale(c, 3), _scale(G, -1))
    d4x = (0, 4, 0)
    curvature = (0, -2, 0)
    stress = (1, -1, -2)
    gravity_action = _add(_add(A_EH, d4x), curvature)
    source_action = _add(_add(_scale(c, -1), d4x), stress)
    expected_action = (1, 2, -1)
    return {
        "dimension_order": ["M", "L", "T"],
        "c": list(c),
        "G": list(G),
        "A_EH": list(A_EH),
        "d4x": list(d4x),
        "curvature": list(curvature),
        "stress_energy": list(stress),
        "gravity_action": list(gravity_action),
        "source_action": list(source_action),
        "expected_action_J_s": list(expected_action),
        "alpha_dimension": [0, 2, 0],
        "beta_dimension": [0, 2, 0],
        "source_stationarity": (
            "A_EH H_mu_nu-(1/(2c))T_mu_nu=0 => "
            "H_mu_nu=(8 pi G/c^4)T_mu_nu"
        ),
        "derived_rhs_sign": "POSITIVE",
        "derived_rhs_coefficient": "8 pi G/c^4",
        "passed": (
            A_EH == (1, 0, -1)
            and gravity_action == expected_action
            and source_action == expected_action
        ),
    }


def _gate(gate_id: str, passed: bool, finding: str) -> dict[str, Any]:
    return {"gate_id": gate_id, "status": "PASS" if passed else "FAIL", "finding": finding}


def _review_gates(packet: dict[str, Any], audit: dict[str, Any]) -> list[dict[str, Any]]:
    classification = packet["classification"]
    action = packet["comparison_action_contract"]
    source = packet["external_source_contract"]
    basis = packet["quadratic_basis_contract"]
    geometry = packet["geometry_and_order_contract"]
    analytic = packet["fourier_gauge_and_green_contract"]
    projectors = packet["projector_contract"]
    derivation = packet["derivation_plan"]
    modes = packet["mode_pole_residue_register"]
    outputs = packet["prepared_output_register"]
    controls = packet["shared_path_control_contract"]
    scope = packet["scope"]
    derivation_ids = {row["step_id"] for row in derivation["rows"]}
    output_ids = {row["output_id"] for row in outputs["rows"]}
    rows = [
        _gate("G1_EXACT_AUTHORITY_AND_CUSTODY", True, "Five packet artifacts match frozen SHA-256 values."),
        _gate(
            "G2_IMMUTABLE_COMPARISON_ONLY_STATUS",
            classification["status"] == "SUPPLIED_COMPARISON_FAMILY"
            and classification["ToE_adoption"] == "NONE"
            and classification["successful_calculation_promotes_action"] is False,
            "The action cannot be promoted by a successful comparison calculation.",
        ),
        _gate(
            "G3_COMMON_NORMALIZATION_AND_SI_DIMENSIONS",
            audit["passed"] is True
            and action["A_EH"] == "c^3/(16 pi G)"
            and action["alpha_dimension_SI"] == action["beta_dimension_SI"] == "m^2",
            "Both gravitational and source variations have J s dimensions.",
        ),
        _gate(
            "G4_EXTERNAL_SOURCE_SIGN_AND_COEFFICIENT",
            audit["derived_rhs_sign"] == "POSITIVE"
            and audit["derived_rhs_coefficient"] == action["kappa"]
            and source["ToE_matter_action_selected"] is False
            and source["conservation"] == "partial_mu T^mu_nu = 0",
            "Independent stationarity algebra gives +8 pi G/c^4 and no native matter claim.",
        ),
        _gate(
            "G5_FOUR_DIMENSIONAL_GAUSS_BONNET_SCOPE",
            basis["dimension"] == 4
            and basis["coefficient_map"] == {
                "alpha_reduced": "alpha_unreduced-gamma",
                "beta_reduced": "beta_unreduced+4 gamma",
            }
            and basis["local_bulk_reduction_only"] is True
            and basis["boundary_global_transport_allowed"] is False,
            "The reduction is restricted to compact-support four-dimensional local-bulk variation.",
        ),
        _gate(
            "G6_MINKOWSKI_ADMISSIBLE_BUT_EXECUTION_GATED",
            action["cosmological_constant"] == 0
            and geometry["Minkowski_background_must_be_verified"] is True
            and "D4_MINKOWSKI_BACKGROUND" in derivation_ids
            and derivation["executed_step_count"] == 0,
            "Zero curvature is structurally admissible; D4 remains unexecuted until the Euler tensor exists.",
        ),
        _gate(
            "G7_LINEARIZATION_EXACT_IN_ALPHA_BETA",
            action["alpha_beta_domain"] == "symbolic real parameters"
            and action["alpha_beta_perturbative"] is False
            and geometry["alpha_beta_perturbative"] is False,
            "The h expansion does not assume small alpha or beta.",
        ),
        _gate(
            "G8_CONVENTIONS_AND_BOUNDARY_PRESCRIPTIONS_FROZEN",
            geometry["metric_signature"] == "(+,-,-,-)"
            and analytic["partial_symbol"] == "-i k_mu"
            and analytic["Box_symbol"] == "-k^2"
            and analytic["classical_dynamic_prescription"] == "RETARDED"
            and analytic["stationary_spatial_prescription"] == "DECAY_AT_INFINITY",
            "Curvature, Fourier, causal, and stationary conventions are explicit and disjoint.",
        ),
        _gate(
            "G9_GAUGE_FIXING_PRESERVES_MODE_QUESTIONS",
            analytic["gauge"] == "de Donder F_nu=0 with xi=1"
            and projectors["complete_longitudinal_projectors_required_for_inversion"] is True
            and projectors["conserved_source_saturation_required"] is True,
            "Gauge sectors remain through inversion and are removed only after conserved-source saturation.",
        ),
        _gate(
            "G10_NO_PRELOADED_MODES_OR_LITERATURE_RESULTS",
            derivation["executed_step_count"] == 0
            and derivation["literature_oracle_allowed_only_after_derivation"] is True
            and modes["scientific_judgment_count"] == 0
            and outputs["computed_output_count"] == 0,
            "All equations, modes, poles, residues, and Green functions remain blank.",
        ),
        _gate(
            "G11_POLE_AND_RESIDUE_SEMANTICS",
            set(modes["required_distinctions"]) == {
                "GHOST", "TACHYON", "CLASSICAL_INSTABILITY",
                "MATTER_INSTABILITY", "HEAVY_DECOUPLED_MODE",
            },
            "PASS with a binding operational residue rule for simple and degenerate poles.",
        ),
        _gate(
            "G12_ONE_OPERATOR_SUPPLIES_00_AND_0I",
            {"D8_PROJECTOR_INVERSION", "D9_CONSERVED_SOURCE_SATURATION", "D10_STATIC_CHANNEL_INVERSION"}.issubset(derivation_ids)
            and {"STATIONARY_00_GREEN_FUNCTION", "STATIONARY_0I_GREEN_FUNCTION", "CONSERVED_SOURCE_SATURATED_PROPAGATOR"}.issubset(output_ids),
            "Both source channels are components of one inverted, saturated operator.",
        ),
        _gate(
            "G13_STATIC_AND_DYNAMIC_PRESCRIPTIONS_NOT_MIXED",
            analytic["prescriptions_may_be_conflated"] is False
            and analytic["residue_reporting_label"] == "FEYNMAN +i0 FOR POLE ORIENTATION ONLY"
            and analytic["growing_Yukawa_branch_allowed"] is False,
            "Retarded dynamics, pole reporting, and decaying static inversion have separate roles.",
        ),
        _gate(
            "G14_TEN_CONTROLS_USE_THE_SHARED_PATH",
            controls["control_count"] == 10
            and controls["executed_control_count"] == 0
            and controls["coefficient_fitting_prohibited"] is True
            and all(row["uses_shared_derivation_path"] is True and row["status"] == "NOT_EXECUTED" for row in controls["rows"]),
            "All ten controls are unrun and route through the primary calculation.",
        ),
        _gate(
            "G15_ONE_EXECUTION_AND_HARD_STOP",
            scope["packet_preparation_executed"] is True
            and scope["comparison_execution_authorized"] is False
            and scope["comparison_action_selected"] is False,
            "Review authorizes one execution only, followed by independent result review.",
        ),
    ]
    return rows


def build_review() -> dict[str, Any]:
    custody, packet = _validate_packet()
    human = REPO_ROOT / HUMAN_REVIEW_RELATIVE_PATH
    test = REPO_ROOT / TEST_RELATIVE_PATH
    if not human.is_file() or not test.is_file():
        raise ValueError("review human record or focused test missing")
    audit = _normalization_audit()
    gates = _review_gates(packet, audit)
    if any(row["status"] != "PASS" for row in gates):
        raise ValueError("comparison packet review gate failed")
    return {
        "schema_id": "SHARED_LINEARIZED_QUADRATIC_GRAVITY_SOURCE_AND_SPECTRUM_COMPARISON_PACKET_REVIEW_20260718_v0",
        "captured_at_utc": "2026-07-18T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_packet_verdict": packet["verdict"],
            "frozen_packet_artifacts": custody,
            "human_review": {"relative_path": HUMAN_REVIEW_RELATIVE_PATH, "sha256": _sha256(human)},
            "generator": {"relative_path": Path(__file__).resolve().relative_to(REPO_ROOT).as_posix(), "sha256": _sha256(Path(__file__).resolve())},
            "test": {"relative_path": TEST_RELATIVE_PATH, "sha256": _sha256(test)},
        },
        "independent_normalization_audit": audit,
        "binding_residue_rule": RESIDUE_RULE,
        "scientific_oracle_spot_checks": [
            {"source": "https://arxiv.org/abs/hep-th/9509142", "role": "POST_DERIVATION_MODE_AND_GHOST_ORACLE_ONLY"},
            {"source": "https://arxiv.org/abs/1007.1917", "role": "POST_DERIVATION_FOURTH_ORDER_WEAK_FIELD_AND_GAUSS_BONNET_ORACLE_ONLY"},
            {"source": "https://arxiv.org/abs/1104.0819", "role": "POST_DERIVATION_ANALYTIC_F_R_SCALAR_MODE_ORACLE_ONLY"},
            {"source": "https://arxiv.org/abs/gr-qc/9403028", "role": "GENERAL_COVARIANT_VARIATIONAL_CONTEXT_ONLY"},
        ],
        "review_gates": {
            "gate_count": len(gates),
            "pass_count": sum(row["status"] == "PASS" for row in gates),
            "failure_count": sum(row["status"] != "PASS" for row in gates),
            "rows": gates,
        },
        "authorized_execution": {
            "execution_count": 1,
            "derivation_step_count": 10,
            "shared_path_control_count": 10,
            "required_output_count": 11,
            "result_review_target": RESULT_REVIEW_TARGET,
            "clauses": [
                "Hash and revalidate the accepted packet before symbolic variation.",
                "Treat alpha and beta as exact real parameters with units m^2.",
                "Keep the source first-order, supplied, symmetric, and conserved.",
                "Pass D1 through D7 before projector inversion.",
                "Pass the Minkowski background check before defining poles.",
                "Derive the complete gauge-fixed operator before source saturation.",
                "Apply the binding operational residue rule.",
                "Derive 00 and 0i from the same saturated operator and Fourier convention.",
                "Execute all ten controls through the same path and fail closed on failure.",
                "Compare with literature only after derivation and record convention translations.",
                "Emit all eleven outputs or a localized blocked result.",
                f"Stop at {RESULT_REVIEW_TARGET}.",
            ],
        },
        "scope": {
            "independent_packet_review_executed": True,
            "packet_accepted": True,
            "one_comparison_execution_authorized": True,
            "comparison_execution_executed": False,
            "metric_or_tetrad_variation_executed": False,
            "linearized_field_equation_derived": False,
            "propagator_or_mode_calculation_executed": False,
            "pole_or_residue_judgment_made": False,
            "Green_function_computed": False,
            "comparison_action_selected": False,
            "coefficient_selection_authorized": False,
            "empirical_fitting_authorized": False,
            "orbital_precession_authorized": False,
            "frame_dragging_reopened": False,
            "matter_sector_selected": False,
            "native_gravitational_principle_identified": False,
            "new_postulate_authorized": False,
            "master_action_mutation_authorized": False,
            "authoritative_V2_population_authorized": False,
        },
        "current_posture": {
            "derivation_stages_completed": "0/10",
            "mode_judgments": "0/3",
            "physical_outputs": "0/11",
            "shared_path_controls_executed": "0/10",
            "comparison_action": "SUPPLIED_COMPARISON_ONLY",
            "native_gravitational_principle": "NOT_IDENTIFIED",
            "gravitational_action": "NOT_SELECTED",
        },
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_review(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Review the shared quadratic-gravity comparison packet.")
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--write", action="store_true")
    group.add_argument("--check", action="store_true")
    args = parser.parse_args()
    expected = artifact_bytes()
    path = REPO_ROOT / REPORT_RELATIVE_PATH
    if args.write:
        path.write_bytes(expected)
        print("shared_linearized_quadratic_gravity_packet_review_v0: wrote review")
        return 0
    if not path.is_file() or path.read_bytes() != expected:
        print("shared_linearized_quadratic_gravity_packet_review_v0: FAILED artifact drift")
        return 1
    print("shared_linearized_quadratic_gravity_packet_review_v0: OK gates=15/15 execution=1")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

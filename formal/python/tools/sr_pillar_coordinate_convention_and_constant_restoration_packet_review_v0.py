from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
PACKET_RELATIVE_PATH = (
    "formal/docs/release/"
    "SR_PILLAR_COORDINATE_CONVENTION_AND_CONSTANT_RESTORATION_PACKET_20260717_v0.json"
)
PACKET_TOOL_RELATIVE_PATH = (
    "formal/python/tools/"
    "sr_pillar_coordinate_convention_and_constant_restoration_packet_v0.py"
)
PACKET_TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_sr_pillar_coordinate_convention_and_constant_restoration_packet_v0.py"
)
REVIEW_TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_sr_pillar_coordinate_convention_and_constant_restoration_packet_review_v0.py"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "SR_PILLAR_COORDINATE_CONVENTION_AND_CONSTANT_RESTORATION_PACKET_REVIEW_20260717_v0.json"
)

CONSUMED_TARGET = (
    "review_sr_pillar_coordinate_convention_and_constant_restoration_packet_v0_result"
)
VERDICT = "BLOCKED_INCOMPLETE_ELECTROMAGNETIC_QUANTUM_CONVENTION_CLOSURE"
FIRST_DIAGNOSTIC = "F_TENSOR_COMPONENT_AND_LEVI_CIVITA_CONVENTION_UNSPECIFIED"
SELECTED_NEXT_TARGET = (
    "prepare_sr_pillar_coordinate_convention_and_constant_restoration_packet_v1"
)

FROZEN_INPUT_HASHES = {
    PACKET_RELATIVE_PATH:
        "a109ffb9742e80c7cafcfde0ca4627ef87644f8906a87418bb89f7fac5b027a8",
    PACKET_TOOL_RELATIVE_PATH:
        "2f6aa787eca902ae9401799e2d4bb70380703913104fa2674d1c2614ebf2c5fb",
    PACKET_TEST_RELATIVE_PATH:
        "abe6738904e6f006abfedd70358a176c363d7391b808ffab18d0d9f663197515",
}

Dimension = tuple[int, int, int, int]


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _add(left: Dimension, right: Dimension) -> Dimension:
    return tuple(a + b for a, b in zip(left, right, strict=True))  # type: ignore[return-value]


def _scale(factor: int, value: Dimension) -> Dimension:
    return tuple(factor * item for item in value)  # type: ignore[return-value]


def _as_dimension(value: object, label: str) -> Dimension:
    if not isinstance(value, list) or len(value) != 4 or not all(
        isinstance(item, int) for item in value
    ):
        raise ValueError(f"invalid dimension vector: {label}")
    return value[0], value[1], value[2], value[3]


def _read_frozen_inputs() -> tuple[dict[str, Any], list[dict[str, str]]]:
    bindings: list[dict[str, str]] = []
    for relative_path, expected_hash in FROZEN_INPUT_HASHES.items():
        raw = (REPO_ROOT / relative_path).read_bytes()
        observed_hash = _sha256(raw)
        if observed_hash != expected_hash:
            raise ValueError(f"frozen input hash mismatch: {relative_path}")
        bindings.append({"relative_path": relative_path, "sha256": observed_hash})
    packet = json.loads((REPO_ROOT / PACKET_RELATIVE_PATH).read_text(encoding="utf-8"))
    if not isinstance(packet, dict):
        raise ValueError("packet root must be an object")
    return packet, bindings


def _validate_packet_identity(packet: dict[str, Any]) -> None:
    if packet.get("schema_id") != (
        "SR_PILLAR_COORDINATE_CONVENTION_AND_CONSTANT_RESTORATION_PACKET_20260717_v0"
    ):
        raise ValueError("packet schema mismatch")
    if packet.get("verdict") != "PREPARED_PENDING_INDEPENDENT_REVIEW":
        raise ValueError("packet verdict mismatch")
    if packet.get("selected_next_target") != CONSUMED_TARGET:
        raise ValueError("packet selected target mismatch")
    generator = packet.get("authority", {}).get("generator", {})
    if (
        generator.get("relative_path") != PACKET_TOOL_RELATIVE_PATH
        or generator.get("sha256") != FROZEN_INPUT_HASHES[PACKET_TOOL_RELATIVE_PATH]
    ):
        raise ValueError("packet generator binding mismatch")


def _independent_dimension_audit(packet: dict[str, Any]) -> dict[str, Any]:
    raw_dimensions = packet.get("dimension_table")
    if not isinstance(raw_dimensions, dict):
        raise ValueError("dimension table missing")
    d = {
        key: _as_dimension(value, key) for key, value in raw_dimensions.items()
    }
    expected_base = {
        "dimensionless": (0, 0, 0, 0),
        "c": (0, 1, -1, 0),
        "coordinate_x_mu": (0, 1, 0, 0),
        "coordinate_derivative_partial_mu": (0, -1, 0, 0),
        "proper_time_tau": (0, 0, 1, 0),
        "four_momentum_p_mu": (1, 1, -1, 0),
        "mass_m": (1, 0, 0, 0),
        "charge_density_rho": (0, -3, 0, 1),
        "four_current_J_mu": (0, -2, -1, 1),
        "field_tensor_F_mu_nu_SI": (1, 0, -1, -1),
        "stress_energy_T_mu_nu": (1, -1, -2, 0),
        "mu_0": (1, 1, 0, -2),
        "epsilon_0": (-1, -3, 2, 2),
    }
    base_vectors_match = all(d.get(key) == value for key, value in expected_base.items())
    rows: list[dict[str, Any]] = []

    def record(
        check_id: str,
        left: Dimension,
        right: Dimension,
        expected: Dimension,
    ) -> None:
        rows.append(
            {
                "check_id": check_id,
                "left": list(left),
                "right": list(right),
                "expected": list(expected),
                "passed": left == right == expected,
            }
        )

    record(
        "INTERVAL_TERMS_HAVE_LENGTH_SQUARED",
        _add(_scale(2, d["c"]), _scale(2, d["proper_time_tau"])),
        _scale(2, d["coordinate_x_mu"]),
        (0, 2, 0, 0),
    )
    record(
        "MASS_SHELL_TERMS_MATCH",
        _scale(2, d["four_momentum_p_mu"]),
        _add(_scale(2, d["mass_m"]), _scale(2, d["c"])),
        (2, 2, -2, 0),
    )
    record(
        "CONTINUITY_TERMS_MATCH",
        _add(d["coordinate_derivative_partial_mu"], d["four_current_J_mu"]),
        _add((0, 0, -1, 0), d["charge_density_rho"]),
        (0, -3, -1, 1),
    )
    record(
        "SOURCED_MAXWELL_SI_TERMS_MATCH",
        _add(d["coordinate_derivative_partial_mu"], d["field_tensor_F_mu_nu_SI"]),
        _add(d["mu_0"], d["four_current_J_mu"]),
        (1, -1, -1, -1),
    )
    record(
        "STRESS_EXCHANGE_SI_TERMS_MATCH",
        _add(d["coordinate_derivative_partial_mu"], d["stress_energy_T_mu_nu"]),
        _add(d["field_tensor_F_mu_nu_SI"], d["four_current_J_mu"]),
        (1, -2, -2, 0),
    )
    record(
        "VACUUM_CONSTANT_IDENTITY_IS_DIMENSIONLESS",
        _add(_add(d["epsilon_0"], d["mu_0"]), _scale(2, d["c"])),
        d["dimensionless"],
        (0, 0, 0, 0),
    )
    passed = sum(1 for row in rows if row["passed"])
    return {
        "method": "independent M,L,T,Q vector reconstruction without importing the packet generator",
        "base_vectors_match_independent_expectations": base_vectors_match,
        "check_count": len(rows),
        "passed_check_count": passed,
        "checks": rows,
        "bounded_finding": "DIMENSIONAL_CLOSURE_REPRODUCED_6_OF_6",
    }


def _electromagnetic_scaling_audit(packet: dict[str, Any]) -> dict[str, Any]:
    normalization = packet.get("unit_policy", {}).get("electromagnetic_normalization", {})
    expected = {
        "A_N": "A_SI / sqrt(mu_0)",
        "F_N": "F_SI / sqrt(mu_0)",
        "J_N": "sqrt(mu_0) J_SI",
        "inverse_map": (
            "A_SI=sqrt(mu_0)A_N; F_SI=sqrt(mu_0)F_N; "
            "J_SI=J_N/sqrt(mu_0)"
        ),
    }
    exact_map_recorded = normalization == expected
    return {
        "exact_declared_object_map_reproduced": exact_map_recorded,
        "sourced_maxwell_mu0_exponent": {
            "natural_left_F_exponent": "-1/2",
            "natural_right_J_exponent": "+1/2",
            "restored_equation": "partial_mu F_SI^{mu nu} = mu_0 J_SI^nu",
            "passed": exact_map_recorded,
        },
        "exchange_product_mu0_exponent": {
            "F_N_times_J_N": "-1/2 + 1/2 = 0",
            "passed": exact_map_recorded,
        },
        "gauge_stress_mu0_exponent": {
            "F_N_squared": "-1",
            "restored_prefactor": "mu_0^-1",
            "passed": exact_map_recorded,
        },
        "bounded_finding": "DECLARED_C_MU0_RESCALING_ALGEBRA_REPRODUCED",
    }


def _gap_findings(packet: dict[str, Any]) -> list[dict[str, Any]]:
    components = packet.get("component_definitions", {})
    equations = packet.get("representative_equations", [])
    controls = packet.get("negative_controls", [])
    recorded_not_applied = packet.get("unit_policy", {}).get(
        "recorded_but_not_applied_in_v0", []
    )
    equation_rows = equations if isinstance(equations, list) else []
    control_rows = controls if isinstance(controls, list) else []

    tensor_fields_absent = all(
        key not in components
        for key in (
            "field_tensor_definition",
            "field_tensor_components",
            "levi_civita_convention",
            "covariant_four_potential",
        )
    )
    quantum_equations_absent = not any(
        row.get("equation_id") in {"DIRAC_EQUATION", "GAUGE_COVARIANT_DERIVATIVE"}
        for row in equation_rows
        if isinstance(row, dict)
    )
    executable_round_trips_absent = not any(
        isinstance(row, dict) and "round_trip_result" in row for row in equation_rows
    )
    negative_controls_not_executed = all(isinstance(row, str) for row in control_rows)
    required_missing_controls = [
        "REJECT_p0_EQUALS_E_INSTEAD_OF_E_OVER_c",
        "REJECT_DIMENSIONFUL_GAUGE_DERIVATIVE_WITHOUT_hbar",
        "REJECT_T0i_WITH_INCORRECT_COMPONENT_DIMENSION_OR_MEANING",
    ]
    controls_text = "\n".join(str(row) for row in control_rows)
    missing_controls_confirmed = all(
        marker not in controls_text for marker in required_missing_controls
    )
    stress_text = str(components.get("stress_energy_components", ""))
    stress_semantics_incomplete = "T^i0" not in stress_text and "T^ij" not in stress_text
    exact_source_bindings_absent = all(
        isinstance(row, dict)
        and "source_relative_path" not in row
        and "source_json_pointer" not in row
        for row in equation_rows
    )
    flat_curved_adapter_absent = not any(
        isinstance(row, dict) and "flat_curved_adapter" in row for row in equation_rows
    )

    findings = [
        {
            "finding_id": FIRST_DIAGNOSTIC,
            "confirmed": tensor_fields_absent,
            "materiality": "BLOCKING",
            "evidence": (
                "A^mu_SI=(phi/c,A) is recorded, but A_mu, the defining sign/order of "
                "F^{mu nu}, F^{0i}/F^{ij}, and the three- and four-dimensional "
                "Levi-Civita orientation are not fixed."
            ),
        },
        {
            "finding_id": "QUANTUM_GAUGE_HBAR_AND_CURRENT_NORMALIZATION_UNSPECIFIED",
            "confirmed": quantum_equations_absent and "hbar" in recorded_not_applied,
            "materiality": "BLOCKING",
            "evidence": (
                "hbar is explicitly not applied; no dimensionful Dirac equation or "
                "D_mu convention fixes q, hbar, c, A_mu, and J=q psibar gamma psi "
                "under the selected SI/natural field rescaling."
            ),
        },
        {
            "finding_id": "BIDIRECTIONAL_EQUATION_ROUND_TRIPS_NOT_EXECUTED",
            "confirmed": executable_round_trips_absent,
            "materiality": "BLOCKING",
            "evidence": (
                "The packet declares invertibility and verifies dimensions, but no one "
                "of the six equations has an executable SI-to-natural-to-SI identity check."
            ),
        },
        {
            "finding_id": "NEGATIVE_CONTROLS_DECLARED_NOT_EXECUTED_AND_INCOMPLETE",
            "confirmed": negative_controls_not_executed and missing_controls_confirmed,
            "materiality": "BLOCKING",
            "evidence": (
                "All eight controls are labels without executed outcomes or registered "
                "diagnostics; p^0=E, lost-hbar, and incorrect-T^0i defects are absent."
            ),
            "required_missing_controls": required_missing_controls,
        },
        {
            "finding_id": "STRESS_ENERGY_COMPONENT_SEMANTICS_INCOMPLETE",
            "confirmed": stress_semantics_incomplete,
            "materiality": "BLOCKING",
            "evidence": (
                "T^00 and T^0i are described, but T^i0=c times momentum density and "
                "T^ij as stress/momentum flux are not fixed."
            ),
        },
        {
            "finding_id": "REPRESENTATIVE_EQUATION_SOURCE_BINDINGS_INCOMPLETE",
            "confirmed": exact_source_bindings_absent,
            "materiality": "BLOCKING",
            "evidence": (
                "The six rows do not bind exact authoritative paths and JSON fields; "
                "the mass-shell row has no identified authoritative source surface."
            ),
        },
        {
            "finding_id": "FLAT_CURVED_DERIVATIVE_ADAPTER_UNSPECIFIED",
            "confirmed": flat_curved_adapter_absent,
            "materiality": "BLOCKING",
            "evidence": (
                "The bound psi-A sources use nabla_mu on curved backgrounds, while the "
                "representative packet uses partial_mu in flat SR without a declared adapter."
            ),
        },
    ]
    if not all(item["confirmed"] for item in findings):
        missing = [item["finding_id"] for item in findings if not item["confirmed"]]
        raise ValueError(f"expected bounded review finding not reproduced: {missing}")
    return findings


def build_review() -> dict[str, Any]:
    packet, bindings = _read_frozen_inputs()
    _validate_packet_identity(packet)
    dimension_audit = _independent_dimension_audit(packet)
    if (
        not dimension_audit["base_vectors_match_independent_expectations"]
        or dimension_audit["passed_check_count"] != 6
    ):
        raise ValueError("independent dimension audit did not reproduce 6/6")
    em_audit = _electromagnetic_scaling_audit(packet)
    if not em_audit["exact_declared_object_map_reproduced"]:
        raise ValueError("declared electromagnetic scaling map was not reproduced")
    findings = _gap_findings(packet)

    tool_path = Path(__file__).resolve()
    test_path = REPO_ROOT / REVIEW_TEST_RELATIVE_PATH
    if not test_path.exists():
        raise ValueError("review test is missing")
    return {
        "schema_id": "SR_PILLAR_COORDINATE_CONVENTION_AND_CONSTANT_RESTORATION_PACKET_REVIEW_20260717_v0",
        "captured_at_utc": "2026-07-17T00:00:00Z",
        "target": CONSUMED_TARGET,
        "verdict": VERDICT,
        "first_diagnostic": FIRST_DIAGNOSTIC,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "review_authority": {
            "frozen_inputs": bindings,
            "reviewer": {
                "relative_path": tool_path.relative_to(REPO_ROOT).as_posix(),
                "sha256": _sha256(tool_path.read_bytes()),
            },
            "review_test": {
                "relative_path": REVIEW_TEST_RELATIVE_PATH,
                "sha256": _sha256(test_path.read_bytes()),
            },
        },
        "retained_findings": {
            "temporal_coordinate": "x^0 = c t",
            "metric_signature": "(+,-,-,-)",
            "restoration_target": "SI",
            "all_coordinate_components_have_dimension_L": True,
            "partial_0_equals_c_inverse_partial_t": True,
            "p_0_component_policy": "p^0 = E/c",
            "J_0_component_policy": "J^0 = c rho",
            "dimension_audit": dimension_audit,
            "electromagnetic_scaling_audit": em_audit,
            "bounded_assessment": (
                "The coordinate/signature baseline and declared c/mu_0 rescaling are "
                "worth retaining in v1; the block does not reverse those findings."
            ),
        },
        "blocking_findings": {
            "count": len(findings),
            "all_confirmed": all(item["confirmed"] for item in findings),
            "findings": findings,
        },
        "v1_contract": [
            "fix A^mu, A_mu, F^{mu nu}=partial^mu A^nu-partial^nu A^mu (or one explicit alternative), F^{0i}, F^{ij}, and the three- and four-dimensional Levi-Civita orientation under (+,-,-,-)",
            "fix one complete dimensionful Dirac/gauge convention for i hbar c gamma^mu D_mu-m c^2 and D_mu, including q, hbar, c, A_mu, and the induced mapping of J^mu=q psibar gamma^mu psi; otherwise explicitly exclude psi-made currents from the six-surface application",
            "bind each representative equation to an exact authoritative path and field, including an authoritative mass-shell surface",
            "declare the flat partial_mu versus curved nabla_mu adapter wherever a bound source is curved",
            "execute and record SI-to-natural-to-SI and natural-to-SI-to-natural identity checks for all six equations",
            "replace negative-control labels with executed mutations, expected diagnostics, observed diagnostics, and pass/fail results",
            "add executed p^0=E, lost-hbar, and incorrect-T^0i negative controls",
            "complete T^{00}, T^{0i}, T^{i0}, and T^{ij} component meanings and units",
            "preserve packet-only scope, immutable historical artifacts, R13 closure, dormant comparators, and all nonclaims",
        ],
        "scope_and_authorization": {
            "packet_v0_accepted": False,
            "six_surface_application_authorized": False,
            "scientific_equation_migration_executed": False,
            "historical_artifacts_modified": False,
            "repository_wide_migration_authorized": False,
            "r13_reopened": False,
            "external_comparator_activated": False,
            "automation_created": False,
            "only_bounded_v1_packet_preparation_authorized": True,
        },
        "claim_ceiling": (
            "Independent packet review only. The review reproduces six dimensional "
            "checks and the declared c/mu_0 scaling algebra, but blocks packet acceptance "
            "and all equation application or migration. It establishes no SR recovery, "
            "Lorentz invariance of the master action, pillar completion, seam closure, "
            "physical validation, prediction, new physics, R13 result, or comparator adoption."
        ),
        "hard_stop": {
            "review_complete": True,
            "packet_accepted": False,
            "application_authorized": False,
            "migration_authorized": False,
            "next_action": SELECTED_NEXT_TARGET,
            "successor_scope": "ONE_BOUNDED_v1_PACKET_ONLY",
        },
    }


def artifact_bytes() -> bytes:
    return (
        json.dumps(build_review(), indent=2, sort_keys=True, ensure_ascii=True) + "\n"
    ).encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    report_path = REPO_ROOT / REPORT_RELATIVE_PATH
    raw = artifact_bytes()
    if args.check:
        if not report_path.exists() or report_path.read_bytes() != raw:
            raise SystemExit("SR convention/restoration packet review is stale or missing")
        review = json.loads(raw)
        print(
            json.dumps(
                {
                    "blocking_findings": review["blocking_findings"]["count"],
                    "dimension_checks": (
                        f"{review['retained_findings']['dimension_audit']['passed_check_count']}/"
                        f"{review['retained_findings']['dimension_audit']['check_count']}"
                    ),
                    "status": "CHECKED",
                    "verdict": review["verdict"],
                },
                sort_keys=True,
            )
        )
        return 0
    report_path.write_bytes(raw)
    print(report_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

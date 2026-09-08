from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "SR_PILLAR_COORDINATE_CONVENTION_AND_CONSTANT_RESTORATION_PACKET_20260717_v0.json"
)
TARGET = "prepare_sr_pillar_coordinate_convention_and_constant_restoration_packet"
SELECTED_NEXT_TARGET = (
    "review_sr_pillar_coordinate_convention_and_constant_restoration_packet_v0_result"
)

SOURCE_HASHES = {
    "formal/docs/release/POST_R13_FULL_TOE_PRIORITY_RETURN_SELECTION_20260717_v0.json":
        "bfabe6d69a5bf046683948e21e78e1952e518fdfb94fde5c56369c784a2f1a4f",
    "formal/docs/release/PILLAR_SEAM_UNIT_MAPPING_LEDGER_BLOCKER_RESPONSE_ROUTE_SELECTION_PACKET_RESULT_REVIEW_20260713_v2.json":
        "6dac3d95a29e7ab0d29a99d5903b682bf235b92e025b044890a2e927d8b6f875",
    "formal/docs/release/PILLAR_SEAM_UNIT_MAPPING_LEDGER_FIRST_UNIT_SELECTOR_PACKET_RESULT_REVIEW_20260713_v0.json":
        "e84d7a00a29a21dae59a8d3fb26f56a6a97cf3b6021766a6b176fde81a3d610d",
    "formal/docs/release/SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0.json":
        "6a4273b3f95bca657bbc9dcdbab82d118a8223ab6de55a213374421b560838a1",
    "formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md":
        "c57729dfbf52040538bab1e1b73ce55ce5dee2c554fc8bffb050259c43fc3206",
    "formal/output/sr_covariance_science_increment_20260325_v0.json":
        "48758450fdd246698adcbe16a390151553d07eccbaec97040ca2f8056e04093c",
    "formal/docs/release/TOE_NATIVE_PHI_SIGNATURE_DOMAIN_AND_POTENTIAL_POLICY_PACKET_20260618_v0.json":
        "c20a3f407ca9f7ab80889692a7a3a075b421f0f48b4f7b5405e650146e7b342c",
    "formal/docs/release/TOE_NATIVE_A_STRESS_ENERGY_ROUTE_UNDER_SELECTED_U1_POLICY_RESULT_REVIEW_20260621_v0.json":
        "0c8dcd2ab7becdb7f1a33a4b079472acd936ecd0fad82133009cbe9fc3ee6f91",
    "formal/docs/release/TOE_NATIVE_PSI_A_U1_SOURCED_MAXWELL_ROUTE_PACKET_20260624_v0.json":
        "ce76ca985cfbbc7624b3cbb8cfe19a5396719203933b79a42c076b195949c93a",
    "formal/docs/release/TOE_NATIVE_PSI_A_U1_MATTER_SECTOR_EXCHANGE_ROUTE_RESULT_REVIEW_20260625_v0.json":
        "4828f1b901f62d2d253e2c1a1b5543c197a979f851aaa394ff0481ca7716aec6",
}


Dimension = tuple[int, int, int, int]


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _dimension(*values: int) -> Dimension:
    if len(values) != 4:
        raise ValueError("dimension vector must have M,L,T,Q components")
    return values[0], values[1], values[2], values[3]


def _add(left: Dimension, right: Dimension) -> Dimension:
    return tuple(a + b for a, b in zip(left, right, strict=True))  # type: ignore[return-value]


def _scale(factor: int, value: Dimension) -> Dimension:
    return tuple(factor * item for item in value)  # type: ignore[return-value]


DIMENSIONS: dict[str, Dimension] = {
    "dimensionless": _dimension(0, 0, 0, 0),
    "c": _dimension(0, 1, -1, 0),
    "coordinate_x_mu": _dimension(0, 1, 0, 0),
    "coordinate_derivative_partial_mu": _dimension(0, -1, 0, 0),
    "proper_time_tau": _dimension(0, 0, 1, 0),
    "four_velocity_u_mu": _dimension(0, 1, -1, 0),
    "mass_m": _dimension(1, 0, 0, 0),
    "four_momentum_p_mu": _dimension(1, 1, -1, 0),
    "energy_E": _dimension(1, 2, -2, 0),
    "charge_density_rho": _dimension(0, -3, 0, 1),
    "current_density_j": _dimension(0, -2, -1, 1),
    "four_current_J_mu": _dimension(0, -2, -1, 1),
    "four_potential_A_mu_SI": _dimension(1, 1, -1, -1),
    "field_tensor_F_mu_nu_SI": _dimension(1, 0, -1, -1),
    "stress_energy_T_mu_nu": _dimension(1, -1, -2, 0),
    "mu_0": _dimension(1, 1, 0, -2),
    "epsilon_0": _dimension(-1, -3, 2, 2),
    "hbar": _dimension(1, 2, -1, 0),
}


def _cross_checks() -> list[dict[str, Any]]:
    d = DIMENSIONS
    checks = [
        {
            "check_id": "INTERVAL_TERMS_HAVE_LENGTH_SQUARED",
            "left": _add(_scale(2, d["c"]), _scale(2, d["proper_time_tau"])),
            "right": _scale(2, d["coordinate_x_mu"]),
            "expected": _dimension(0, 2, 0, 0),
        },
        {
            "check_id": "MASS_SHELL_TERMS_MATCH",
            "left": _scale(2, d["four_momentum_p_mu"]),
            "right": _add(_scale(2, d["mass_m"]), _scale(2, d["c"])),
            "expected": _dimension(2, 2, -2, 0),
        },
        {
            "check_id": "CONTINUITY_TERMS_MATCH",
            "left": _add(d["coordinate_derivative_partial_mu"], d["four_current_J_mu"]),
            "right": _add(_dimension(0, 0, -1, 0), d["charge_density_rho"]),
            "expected": _dimension(0, -3, -1, 1),
        },
        {
            "check_id": "SOURCED_MAXWELL_SI_TERMS_MATCH",
            "left": _add(d["coordinate_derivative_partial_mu"], d["field_tensor_F_mu_nu_SI"]),
            "right": _add(d["mu_0"], d["four_current_J_mu"]),
            "expected": _dimension(1, -1, -1, -1),
        },
        {
            "check_id": "STRESS_EXCHANGE_SI_TERMS_MATCH",
            "left": _add(d["coordinate_derivative_partial_mu"], d["stress_energy_T_mu_nu"]),
            "right": _add(d["field_tensor_F_mu_nu_SI"], d["four_current_J_mu"]),
            "expected": _dimension(1, -2, -2, 0),
        },
        {
            "check_id": "VACUUM_CONSTANT_IDENTITY_IS_DIMENSIONLESS",
            "left": _add(_add(d["epsilon_0"], d["mu_0"]), _scale(2, d["c"])),
            "right": d["dimensionless"],
            "expected": d["dimensionless"],
        },
    ]
    for check in checks:
        check["passed"] = check["left"] == check["right"] == check["expected"]
        check["left"] = list(check["left"])
        check["right"] = list(check["right"])
        check["expected"] = list(check["expected"])
    return checks


def _read_bound_sources() -> list[dict[str, str]]:
    result: list[dict[str, str]] = []
    for relative_path, expected_hash in SOURCE_HASHES.items():
        raw = (REPO_ROOT / relative_path).read_bytes()
        observed_hash = _sha256(raw)
        if observed_hash != expected_hash:
            raise ValueError(f"source hash mismatch: {relative_path}")
        result.append({"relative_path": relative_path, "sha256": observed_hash})
    return result


def _validate_authority() -> None:
    selection = json.loads(
        (REPO_ROOT / next(iter(SOURCE_HASHES))).read_text(encoding="utf-8")
    )
    if selection.get("selected_next_target") != TARGET:
        raise ValueError("post-R13 selection target mismatch")

    route_review = json.loads(
        (
            REPO_ROOT
            / "formal/docs/release/PILLAR_SEAM_UNIT_MAPPING_LEDGER_BLOCKER_RESPONSE_ROUTE_SELECTION_PACKET_RESULT_REVIEW_20260713_v2.json"
        ).read_text(encoding="utf-8")
    )
    route_map = route_review["independent_packet_audit"][
        "independently_selected_route_map"
    ]
    if (
        route_review.get("verdict") != "ACCEPT"
        or route_map.get("PILLAR-SR-units_and_dimensions-v0")
        != "CONVENTION_AND_CONSTANT_RESTORATION"
    ):
        raise ValueError("accepted SR route authority mismatch")

    selector = json.loads(
        (
            REPO_ROOT
            / "formal/docs/release/PILLAR_SEAM_UNIT_MAPPING_LEDGER_FIRST_UNIT_SELECTOR_PACKET_RESULT_REVIEW_20260713_v0.json"
        ).read_text(encoding="utf-8")
    )
    if (
        selector.get("verdict") != "ACCEPT"
        or selector.get("selected_row_id") != "PILLAR-SR-units_and_dimensions-v0"
        or selector.get("selected_weighted_score") != 51
    ):
        raise ValueError("accepted SR selector authority mismatch")

    sr_increment = json.loads(
        (
            REPO_ROOT / "formal/output/sr_covariance_science_increment_20260325_v0.json"
        ).read_text(encoding="utf-8")
    )
    if sr_increment.get("units") != "c_equals_1":
        raise ValueError("SR covariance source-unit posture mismatch")


def build_packet() -> dict[str, Any]:
    sources = _read_bound_sources()
    _validate_authority()
    cross_checks = _cross_checks()
    if not all(check["passed"] for check in cross_checks):
        raise ValueError("dimension cross-check failed")

    tool_path = Path(__file__).resolve()
    tool_relative_path = tool_path.relative_to(REPO_ROOT).as_posix()
    return {
        "schema_id": "SR_PILLAR_COORDINATE_CONVENTION_AND_CONSTANT_RESTORATION_PACKET_20260717_v0",
        "captured_at_utc": "2026-07-17T00:00:00Z",
        "target": TARGET,
        "verdict": "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "claim_ceiling": (
            "Convention-lock and restoration-map preparation only. No equation surface "
            "is migrated or rewritten; no SR recovery, Lorentz invariance of the master "
            "action, pillar completion, seam closure, empirical adequacy, prediction, "
            "new physics, R13 reopening, or external-comparator activation follows."
        ),
        "authority": {
            "consumed_target": TARGET,
            "selected_pillar_code": "SR",
            "selected_weighted_score": 51,
            "selected_route": "CONVENTION_AND_CONSTANT_RESTORATION",
            "bound_sources": sources,
            "generator": {
                "relative_path": tool_relative_path,
                "sha256": _sha256(tool_path.read_bytes()),
            },
        },
        "scope": {
            "packet_preparation_only": True,
            "representative_equation_application_executed": False,
            "historical_artifacts_modified": False,
            "repository_wide_rewrite_authorized": False,
            "multiple_metric_conventions_supported": False,
            "multiple_restoration_unit_systems_supported": False,
            "symbolic_units_engine_authorized": False,
            "r13_reopened": False,
            "external_comparator_activated": False,
        },
        "selected_conventions": {
            "spacetime_dimension": "3+1",
            "coordinate_order": ["x^0", "x^1", "x^2", "x^3"],
            "coordinate_definition": "x^mu = (c t, x, y, z)",
            "temporal_coordinate": "x^0 = c t",
            "coordinate_dimension": "L for every component",
            "metric_signature": "(+,-,-,-)",
            "flat_metric": "eta_mu_nu = diag(+1,-1,-1,-1)",
            "interval": "ds^2 = c^2 dt^2 - dx^2 - dy^2 - dz^2",
            "proper_time": "ds^2 = c^2 d tau^2 for timelike paths",
            "covariant_derivative_components": "partial_mu = (c^-1 partial_t, nabla)",
            "contravariant_derivative_components": "partial^mu = (c^-1 partial_t, -nabla)",
            "index_range": "mu,nu,alpha in {0,1,2,3}",
            "index_rule": "raise and lower only with eta_mu_nu or its explicitly selected curved extension",
            "speed_of_light": "c = 299792458 m s^-1 exactly",
            "representative_domain": "flat inertial SR-facing equation surfaces",
        },
        "unit_policy": {
            "dimension_vector_basis": ["M", "L", "T", "Q"],
            "restored_target_system": "SI",
            "source_working_form": "rationalized natural-unit notation with c=1 and electromagnetic normalization suppressed",
            "source_working_form_status": "BOUNDED_PACKET_CLASSIFICATION_PENDING_INDEPENDENT_REVIEW",
            "suppressed_constants_in_scope": ["c", "mu_0", "epsilon_0"],
            "recorded_but_not_applied_in_v0": ["hbar", "G", "k_B"],
            "vacuum_identity": "epsilon_0 mu_0 c^2 = 1",
            "electromagnetic_normalization": {
                "A_N": "A_SI / sqrt(mu_0)",
                "F_N": "F_SI / sqrt(mu_0)",
                "J_N": "sqrt(mu_0) J_SI",
                "inverse_map": "A_SI=sqrt(mu_0)A_N; F_SI=sqrt(mu_0)F_N; J_SI=J_N/sqrt(mu_0)",
            },
        },
        "dimension_table": {
            key: list(value) for key, value in sorted(DIMENSIONS.items())
        },
        "component_definitions": {
            "four_velocity": "u^mu = dx^mu/d tau = gamma(c, v)",
            "four_momentum": "p^mu = m u^mu = (E/c, p)",
            "four_current": "J^mu_SI = (c rho, j)",
            "four_potential": "A^mu_SI = (phi/c, A)",
            "stress_energy_components": "T^00 is energy density; T^0i is energy flux divided by c under x^0=ct",
        },
        "representative_equations": [
            {
                "equation_id": "SR_INTERVAL",
                "natural_form": "ds^2 = dt_N^2 - dx^2 - dy^2 - dz^2",
                "restored_SI_form": "ds^2 = c^2 dt^2 - dx^2 - dy^2 - dz^2",
                "map": "t_N = c t",
                "application_status": "FROZEN_FOR_LATER_BOUNDED_APPLICATION",
            },
            {
                "equation_id": "SR_MASS_SHELL",
                "natural_form": "p_mu p^mu = m_N^2",
                "restored_SI_form": "p_mu p^mu = m^2 c^2, with p^mu=(E/c,p)",
                "map": "m_N = m c",
                "application_status": "FROZEN_FOR_LATER_BOUNDED_APPLICATION",
            },
            {
                "equation_id": "CURRENT_CONSERVATION",
                "natural_form": "partial_mu J_N^mu = 0",
                "restored_SI_form": "partial_mu J_SI^mu = partial_t rho + div(j) = 0",
                "map": "partial_0=c^-1 partial_t and J_SI^0=c rho",
                "application_status": "FROZEN_FOR_LATER_BOUNDED_APPLICATION",
            },
            {
                "equation_id": "SOURCED_MAXWELL",
                "natural_form": "partial_mu F_N^{mu nu} = J_N^nu",
                "restored_SI_form": "partial_mu F_SI^{mu nu} = mu_0 J_SI^nu",
                "map": "F_N=F_SI/sqrt(mu_0); J_N=sqrt(mu_0)J_SI",
                "application_status": "FROZEN_FOR_LATER_BOUNDED_APPLICATION",
            },
            {
                "equation_id": "MATTER_STRESS_ENERGY_EXCHANGE",
                "natural_form": "partial_mu T_matter^{mu nu} = F_N^nu{}_alpha J_N^alpha",
                "restored_SI_form": "partial_mu T_matter^{mu nu} = F_SI^nu{}_alpha J_SI^alpha",
                "map": "F_N J_N = F_SI J_SI under the selected electromagnetic normalization",
                "application_status": "FROZEN_FOR_LATER_BOUNDED_APPLICATION",
            },
            {
                "equation_id": "GAUGE_STRESS_ENERGY_NORMALIZATION",
                "natural_form": "T_A,N^{mu nu} = -F_N^{mu}{}_alpha F_N^{nu alpha} + (1/4) eta^{mu nu} F_N^2",
                "restored_SI_form": "T_A,SI^{mu nu} = mu_0^-1[-F_SI^{mu}{}_alpha F_SI^{nu alpha} + (1/4) eta^{mu nu} F_SI^2]",
                "map": "F_N=F_SI/sqrt(mu_0)",
                "application_status": "FROZEN_FOR_LATER_BOUNDED_APPLICATION",
            },
        ],
        "reversibility_cross_checks": {
            "dimension_check_count": len(cross_checks),
            "passed_dimension_check_count": sum(
                1 for check in cross_checks if check["passed"]
            ),
            "checks": cross_checks,
            "forward_suppression_backward_restoration_rule": (
                "Apply the declared object map before setting constants to one; invert "
                "the same object map before interpreting SI components."
            ),
            "algebraic_maps_declared_invertible": True,
        },
        "negative_controls": [
            "REJECT_x0_EQUALS_t_WHILE_ALL_COORDINATES_ARE_DECLARED_LENGTH",
            "REJECT_SIGNATURE_FLIP_WITHOUT_CONTRACTION_AND_STRESS_SIGN_REAUDIT",
            "REJECT_partial0_EQUALS_partial_t_UNDER_x0_EQUALS_ct",
            "REJECT_J0_EQUALS_rho_UNDER_x0_EQUALS_ct",
            "REJECT_SOURCED_MAXWELL_EQUALITY_WITHOUT_mu0_AS_SI",
            "REJECT_GAUGE_STRESS_ENERGY_WITHOUT_mu0_INVERSE_AS_SI",
            "REJECT_CONSTANT_INSERTION_WITHOUT_AN_OBJECT_NORMALIZATION_MAP",
            "REJECT_HISTORICAL_ARTIFACT_REWRITE_DURING_PACKET_PREPARATION",
        ],
        "migration_inventory": [
            {
                "surface": "SR covariance science increment",
                "finding": "uses c=1 and writes t and x with equal dimensions",
                "later_action": "bind t_N=ct and re-express interval/boost components",
            },
            {
                "surface": "ToE-native phi policy",
                "finding": "already selects (+,-,-,-); field and coupling dimensions remain incomplete",
                "later_action": "preserve signature and audit hbar/c restoration separately",
            },
            {
                "surface": "ToE-native A stress-energy route",
                "finding": "already selects (+,-,-,-) and natural gauge normalization",
                "later_action": "apply F_N=F_SI/sqrt(mu_0) and restore mu_0^-1",
            },
            {
                "surface": "psi-A sourced Maxwell and exchange routes",
                "finding": "records partial/nabla F=J and FJ exchange in suppressed normalization",
                "later_action": "apply the selected current/field normalization and component map",
            },
            {
                "surface": "cosmology background surfaces",
                "finding": "cosmic/conformal-time and lapse conventions require a separate adapter",
                "later_action": "do not migrate until the SR convention packet is accepted",
            },
            {
                "surface": "fixed-background scalar numerical sandboxes",
                "finding": "use local (-,+) or (-,+,+) test conventions",
                "later_action": "retain immutable artifacts; define explicit signature adapters only if compared",
            },
        ],
        "independent_review_requirements": [
            "verify every authority source hash and upstream verdict",
            "verify x^0=ct makes all coordinate components length-valued",
            "verify (+,-,-,-) matches the selected ToE-native phi and A policies",
            "verify all dimension vectors in the M,L,T,Q basis",
            "verify partial_0 and J^0 reproduce the ordinary continuity equation",
            "verify the mass-shell restoration and p^0=E/c convention",
            "verify the electromagnetic field/current normalization is invertible",
            "verify sourced Maxwell restores exactly one mu_0 factor in SI",
            "verify the matter exchange product is normalization-invariant",
            "verify the gauge stress tensor restores mu_0^-1",
            "verify every negative control is explicit and diagnostic",
            "verify no historical artifact, R13 evidence, or external comparator was modified or activated",
        ],
        "hard_stop": {
            "packet_version": 0,
            "independent_packet_review_required": True,
            "representative_equation_application_authorized_now": False,
            "migration_authorized_now": False,
            "repository_wide_rewrite_authorized": False,
            "successor_if_accepted": "prepare_bounded_sr_convention_restoration_application_to_selected_authoritative_equations",
            "successor_if_blocked": "prepare_sr_pillar_coordinate_convention_and_constant_restoration_packet_v1_only_if_independent_review_identifies_a_bounded_contract_defect",
        },
    }


def artifact_bytes() -> bytes:
    return (
        json.dumps(build_packet(), indent=2, sort_keys=True, ensure_ascii=True) + "\n"
    ).encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    report_path = REPO_ROOT / REPORT_RELATIVE_PATH
    raw = artifact_bytes()
    if args.check:
        if not report_path.exists() or report_path.read_bytes() != raw:
            raise SystemExit("SR convention/restoration packet is stale or missing")
        packet = json.loads(raw)
        print(
            json.dumps(
                {
                    "dimension_checks": (
                        f"{packet['reversibility_cross_checks']['passed_dimension_check_count']}/"
                        f"{packet['reversibility_cross_checks']['dimension_check_count']}"
                    ),
                    "representative_equations": len(packet["representative_equations"]),
                    "status": "CHECKED",
                    "verdict": packet["verdict"],
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

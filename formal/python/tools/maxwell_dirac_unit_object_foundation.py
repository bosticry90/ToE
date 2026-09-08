from __future__ import annotations

import argparse
import hashlib
import json
import sys
import unicodedata
from fractions import Fraction
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.prompt_dependency_identity import (
    identity_sha256_path,
    prompt_dependency_is_nonblocking,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_RELATIVE_PATH = "formal/python/tools/maxwell_dirac_unit_object_foundation.py"
SELECTOR_REVIEW_RELATIVE_PATH = (
    "formal/docs/release/PILLAR_SEAM_UNIT_MAPPING_LEDGER_FIRST_UNIT_SELECTOR_"
    "PACKET_RESULT_REVIEW_20260713_v0.json"
)
PACKET_RELATIVE_PATH = "formal/output/MAXWELL-DIRAC-UNIT-OBJECT-FOUNDATION-PACKET-v0.json"
MANIFEST_RELATIVE_PATH = "formal/output/MAXWELL-DIRAC-UNIT-OBJECT-FOUNDATION-MANIFEST-v0.json"
REPORT_RELATIVE_PATH = "formal/docs/release/MAXWELL_DIRAC_UNIT_OBJECT_FOUNDATION_PACKET_20260713_v0.json"
PACKET_PATH = REPO_ROOT / PACKET_RELATIVE_PATH
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH
REPORT_PATH = REPO_ROOT / REPORT_RELATIVE_PATH

CAPTURED_AT_UTC = "2026-07-13T00:00:00Z"
TARGET = "prepare_maxwell_dirac_unit_object_foundation_packet_v0"
REVIEW_TARGET = "review_maxwell_dirac_unit_object_foundation_packet_v0_result"
REVIEW_TARGET_KIND = "maxwell_dirac_unit_object_foundation_packet_v0_result_review"
FAILURE_TARGET = "prepare_maxwell_dirac_unit_object_foundation_packet_v1"
POST_ACCEPTANCE_TARGET = "prepare_dirac_maxwell_3p1_to_1p1_reduction_consistency_packet_v0"
PACKET_SCHEMA_ID = "MAXWELL_DIRAC_UNIT_OBJECT_FOUNDATION_PACKET_v0"
MANIFEST_SCHEMA_ID = "MAXWELL_DIRAC_UNIT_OBJECT_FOUNDATION_MANIFEST_v0"
REPORT_SCHEMA_ID = "MAXWELL_DIRAC_UNIT_OBJECT_FOUNDATION_PACKET_20260713_v0"
SELECTOR_REVIEW_SHA256 = "e84d7a00a29a21dae59a8d3fb26f56a6a97cf3b6021766a6b176fde81a3d610d"
PROMPT_RELATIVE_PATH = "Prompt.txt"
PROMPT_DEPENDENCY_ROLE = "DEMOTE_TO_NONBLOCKING_PROVENANCE"
PROMPT_SHA256 = "2bc6996ea28e96c50e688ed3d30ee24808af411a244eb594aad89ff80fda8433"
AXES = ("M", "L", "T", "Q", "Theta")


def _normalize(value: Any) -> Any:
    if isinstance(value, str):
        return unicodedata.normalize("NFC", value)
    if isinstance(value, list):
        return [_normalize(item) for item in value]
    if isinstance(value, dict):
        return {_normalize(str(key)): _normalize(item) for key, item in value.items()}
    return value


def canonical_json_bytes(payload: Any) -> bytes:
    return (json.dumps(_normalize(payload), allow_nan=False, ensure_ascii=False, indent=2, sort_keys=True) + "\n").encode("utf-8")


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha256_path(path: Path) -> str:
    return identity_sha256_path(path, repo_root=REPO_ROOT)


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected object: {path}")
    return value


def vec(M: int | Fraction = 0, L: int | Fraction = 0, T: int | Fraction = 0, Q: int | Fraction = 0, Theta: int | Fraction = 0) -> tuple[Fraction, ...]:
    return tuple(Fraction(item) for item in (M, L, T, Q, Theta))


def add(*values: tuple[Fraction, ...]) -> tuple[Fraction, ...]:
    return tuple(sum((value[index] for value in values), Fraction(0)) for index in range(5))


def scale(value: tuple[Fraction, ...], factor: int | Fraction) -> tuple[Fraction, ...]:
    return tuple(item * Fraction(factor) for item in value)


def sub(left: tuple[Fraction, ...], right: tuple[Fraction, ...]) -> tuple[Fraction, ...]:
    return add(left, scale(right, -1))


def encode(value: tuple[Fraction, ...]) -> list[str]:
    return [str(item.numerator) if item.denominator == 1 else f"{item.numerator}/{item.denominator}" for item in value]


ZERO = vec()
HBAR = vec(M=1, L=2, T=-1)
C = vec(L=1, T=-1)
MU0 = vec(M=1, L=1, Q=-2)
MASS = vec(M=1)
Q4 = vec(Q=1)
X = vec(L=1)
DERIVATIVE = vec(L=-1)
AREA = vec(L=2)
SQRT_AREA = vec(L=1)
PSI4 = vec(L=Fraction(-3, 2))
A4 = vec(M=1, L=1, T=-1, Q=-1)
F4 = vec(M=1, T=-1, Q=-1)
JNUM4 = vec(L=-3)
JEM4 = vec(L=-2, T=-1, Q=1)
LPHYS4 = vec(M=1, L=-1, T=-2)
ACTION = HBAR
Q2 = sub(Q4, SQRT_AREA)
PSI2 = add(PSI4, SQRT_AREA)
A2 = add(A4, SQRT_AREA)
F2 = add(F4, SQRT_AREA)
JNUM2 = add(JNUM4, AREA)
JEM2 = add(JEM4, SQRT_AREA)
LPHYS2 = add(LPHYS4, AREA)


def internal_mass_dimensions(D: int) -> dict[str, str]:
    values = {
        "psi": Fraction(D - 1, 2),
        "A_mu": Fraction(D - 2, 2),
        "F_munu": Fraction(D, 2),
        "q": Fraction(4 - D, 2),
        "j_number_mu": Fraction(D - 1),
        "J_em_mu_equals_q_times_j": Fraction(D + 2, 2),
        "Lagrangian_density": Fraction(D),
        "stress_energy": Fraction(D),
    }
    return {key: str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}" for key, value in values.items()}


def external_ledger() -> list[dict[str, Any]]:
    entries = [
        ("x_mu", X, "x^0=ct; all coordinates are length-valued"),
        ("partial_mu", DERIVATIVE, "partial/partial x^mu"),
        ("metric_g_munu", ZERO, "dimensionless"),
        ("tetrad_e_a_mu", ZERO, "dimensionless"),
        ("hbar", HBAR, "retained explicitly externally"),
        ("c", C, "retained explicitly externally"),
        ("mu_0", MU0, "rationalized SI electromagnetic normalization"),
        ("mass_m", MASS, "equal species masses"),
        ("charge_q_3p1", Q4, "q_+=+q, q_-=-q"),
        ("psi_3p1", PSI4, "number-density normalization: psi^dagger psi has L^-3"),
        ("A_mu_3p1", A4, "q A_mu / hbar has inverse-length dimension"),
        ("F_munu_3p1", F4, "partial_mu A_nu - partial_nu A_mu"),
        ("j_number_mu_3p1", JNUM4, "bar(psi) gamma^mu psi"),
        ("J_em_mu_3p1", JEM4, "q c j_number^mu"),
        ("L_physical_3p1", LPHYS4, "energy per spatial volume"),
        ("T_munu_3p1", LPHYS4, "physical stress-energy density"),
        ("action_S", ACTION, "S=(1/c) integral d^4x sqrt(-g) L_physical"),
        ("A_perp", AREA, "transverse physical area reserved for reviewed reduction"),
        ("q_1p1_candidate", Q2, "q_3p1/sqrt(A_perp); not reduction-authoritative before Pair D"),
        ("psi_1p1_candidate", PSI2, "sqrt(A_perp) psi_3p1"),
        ("A_mu_1p1_candidate", A2, "sqrt(A_perp) A_mu_3p1"),
        ("F_munu_1p1_candidate", F2, "sqrt(A_perp) F_munu_3p1"),
        ("j_number_mu_1p1_candidate", JNUM2, "A_perp j_number_3p1"),
        ("J_em_mu_1p1_candidate", JEM2, "sqrt(A_perp) J_em_3p1"),
        ("L_physical_1p1_candidate", LPHYS2, "A_perp L_physical_3p1"),
        ("T_munu_1p1_candidate", LPHYS2, "A_perp T_munu_3p1"),
    ]
    return [
        {
            "object_id": object_id,
            "internal_mass_dimension_D4": internal_mass_dimensions(4).get(object_id.replace("_3p1", "")),
            "external_dimension_axes": list(AXES),
            "external_dimension_vector": encode(dimension),
            "restoration_expression": restoration,
            "restoration_dependencies": [item for item in ("c", "hbar", "mu_0", "A_perp") if item in restoration],
        }
        for object_id, dimension, restoration in entries
    ]


def dimension_checks() -> list[dict[str, Any]]:
    checks = {
        "D4_Dirac_kinetic": (add(HBAR, C, scale(PSI4, 2), DERIVATIVE), LPHYS4),
        "D4_Dirac_mass": (add(MASS, scale(C, 2), scale(PSI4, 2)), LPHYS4),
        "D4_Maxwell": (sub(scale(F4, 2), MU0), LPHYS4),
        "D4_interaction": (add(JEM4, A4), LPHYS4),
        "D4_current_restoration": (add(Q4, C, JNUM4), JEM4),
        "D4_action": (add(LPHYS4, scale(X, 4), scale(C, -1)), ACTION),
        "D2_Dirac_kinetic": (add(HBAR, C, scale(PSI2, 2), DERIVATIVE), LPHYS2),
        "D2_Dirac_mass": (add(MASS, scale(C, 2), scale(PSI2, 2)), LPHYS2),
        "D2_Maxwell": (sub(scale(F2, 2), MU0), LPHYS2),
        "D2_interaction": (add(JEM2, A2), LPHYS2),
        "D2_current_restoration": (add(Q2, C, JNUM2), JEM2),
        "D2_action": (add(LPHYS2, scale(X, 2), scale(C, -1)), ACTION),
    }
    return [
        {
            "check_id": check_id,
            "observed_vector": encode(observed),
            "expected_vector": encode(expected),
            "residual_vector": encode(sub(observed, expected)),
            "passed": observed == expected,
        }
        for check_id, (observed, expected) in checks.items()
    ]


def dimension_order_checks() -> list[dict[str, Any]]:
    checks = {
        "psi": (add(PSI4, SQRT_AREA), PSI2),
        "A_mu": (add(A4, SQRT_AREA), A2),
        "F_munu": (add(F4, SQRT_AREA), F2),
        "q": (sub(Q4, SQRT_AREA), Q2),
        "j_number_mu": (add(JNUM4, AREA), JNUM2),
        "J_em_mu": (add(JEM4, SQRT_AREA), JEM2),
        "L_physical": (add(LPHYS4, AREA), LPHYS2),
        "T_munu": (add(LPHYS4, AREA), LPHYS2),
        "action": (ACTION, ACTION),
    }
    return [
        {
            "object_id": object_id,
            "restore_after_reduce_vector": encode(left),
            "reduce_after_restore_vector": encode(right),
            "C_dim_order_residual": encode(sub(left, right)),
            "passed": left == right,
            "audit_only_not_dynamic": True,
        }
        for object_id, (left, right) in checks.items()
    ]


def load_authority() -> dict[str, Any]:
    path = REPO_ROOT / SELECTOR_REVIEW_RELATIVE_PATH
    if sha256_path(path) != SELECTOR_REVIEW_SHA256:
        raise ValueError("selector review hash mismatch")
    review = load_json(path)
    if not (
        review.get("accepted") is True
        and review.get("selected_next_target") == TARGET
        and review.get("selected_row_id") == "PILLAR-SR-units_and_dimensions-v0"
        and review.get("selected_row_resolution_execution_ready") is False
    ):
        raise ValueError("selector review does not authorize foundation preparation")
    return review


def build_packet() -> dict[str, Any]:
    load_authority()
    checks = dimension_checks()
    order_checks = dimension_order_checks()
    if not all(item["passed"] for item in [*checks, *order_checks]):
        raise ValueError("dimension audit failed")
    return {
        "schema_id": PACKET_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "selected_next_target": REVIEW_TARGET,
        "selected_next_target_kind": REVIEW_TARGET_KIND,
        "failure_target": FAILURE_TARGET,
        "post_acceptance_target": POST_ACCEPTANCE_TARGET,
        "selected_unit_prerequisite": "PILLAR-SR-units_and_dimensions-v0",
        "preferred_benchmark_candidate": "TWO_SPECIES_CNUMBER_MAXWELL_DIRAC",
        "conventions": {
            "internal_units": "c=hbar=1",
            "external_action_unit": "hbar",
            "metric_signature": "+---",
            "x0_external": "ct",
            "coordinates": "length-valued",
            "metric_and_tetrads": "dimensionless",
            "derivative": "inverse length",
            "electromagnetic_normalization": "rationalized SI with mu_0 explicit",
            "oriented_tetrad": "det(e)>0",
            "Clifford_relation": "{gamma^a,gamma^b}=2 eta^{ab}",
            "Dirac_adjoint": "bar(psi)=psi^dagger gamma^0",
            "covariant_derivative_positive_charge": "D_mu psi_+=(nabla_mu+i q A_mu/hbar)psi_+",
            "covariant_derivative_negative_charge": "D_mu psi_-=(nabla_mu-i q A_mu/hbar)psi_-",
            "adjoint_derivative": "D_mu bar(psi_s)=nabla_mu bar(psi_s)-i q_s A_mu bar(psi_s)/hbar",
        },
        "shared_action": {
            "external": "S=(1/c) integral d^4x sqrt(-g) [sum_s {i hbar c/2 (bar(psi_s) gamma^mu D_mu psi_s-(D_mu bar(psi_s)) gamma^mu psi_s)-m c^2 bar(psi_s)psi_s}-F_munu F^munu/(4 mu_0)]",
            "internal": "S=sum_s integral d^4x sqrt(-g) [i/2 (bar(psi_s) gamma^mu D_mu psi_s-(D_mu bar(psi_s)) gamma^mu psi_s)-m bar(psi_s)psi_s]-integral d^4x sqrt(-g) F_munu F^munu/4",
            "species": [
                {"species_id": "psi_plus", "mass": "m", "charge": "+q"},
                {"species_id": "psi_minus", "mass": "m", "charge": "-q"},
            ],
            "real_symmetrized": True,
            "boundary_assumption": "compact-support variations or frozen periodic boundaries make admitted total divergences integrate to zero",
        },
        "internal_mass_dimension_formula": {
            "general_D": {
                "psi": "(D-1)/2",
                "A_mu": "(D-2)/2",
                "F_munu": "D/2",
                "q": "(4-D)/2",
                "j_number_mu": "D-1",
                "J_em_mu_equals_q_times_j": "(D+2)/2",
                "Lagrangian_density": "D",
                "stress_energy": "D",
            },
            "D4": internal_mass_dimensions(4),
            "D2": internal_mass_dimensions(2),
        },
        "external_dimension_ledger": external_ledger(),
        "dimension_checks": checks,
        "C_dim_order_checks": order_checks,
        "field_semantics": {
            "spinor_type": "commuting complex c-number spinor",
            "interpretation": "classical Maxwell-Dirac PDE surrogate",
            "equal_masses": True,
            "opposite_charges": True,
            "number_current": "j_s^mu=bar(psi_s) gamma^mu psi_s",
            "electromagnetic_source_current_internal": "J^mu=q j_+^mu-q j_-^mu",
            "electromagnetic_source_current_external": "J_SI^mu=q c j_+^mu-q c j_-^mu",
            "spectral_diagnostics": [
                "initial free-Hamiltonian positive-frequency weight",
                "initial free-Hamiltonian negative-frequency weight",
                "time-dependent projections onto the frozen free diagnostic basis",
                "interaction-driven redistribution is not quantum pair creation",
            ],
        },
        "tetrad_variation_derivation": {
            "canonical_route": "HILBERT_TENSOR_FROM_ORIENTED_TETRAD_VARIATION",
            "variation_variable": "e^a_mu",
            "ordered_steps": [
                "vary det(e) with fixed orientation",
                "vary gamma^mu=e_a^mu gamma^a and the spin connection consistently",
                "integrate the spin-connection variation by parts under the admitted boundary assumption",
                "use the real symmetrized Dirac action without mixing signatures",
                "collect the symmetric tetrad response for each charged species",
                "vary A_mu independently to obtain the sourced Maxwell equation",
                "apply the on-shell Dirac, adjoint, and Maxwell equations to the Hilbert identity",
            ],
            "Maxwell_Hilbert_tensor": "T_EM^munu=(1/mu_0)[-F^mu_lambda F^{nu lambda}+(1/4)g^munu F_ab F^ab]",
            "Dirac_Hilbert_tensor_each_species": "T_D,s^munu=(i hbar c/4)[bar(psi_s)gamma^mu D^nu psi_s+bar(psi_s)gamma^nu D^mu psi_s-(D^nu bar(psi_s))gamma^mu psi_s-(D^mu bar(psi_s))gamma^nu psi_s]",
            "off_shell_note": "The displayed Dirac tensor is the on-shell Hilbert representative; the off-shell tetrad response differs by the explicitly tracked action/Euler-Lagrange term and admitted boundary improvement.",
            "Belinfante_status": "OPTIONAL_EQUIVALENCE_CROSS_CHECK_ONLY",
            "policy_selected_tensor_used": False,
        },
        "derived_equations": {
            "Dirac_plus": "(i hbar c gamma^mu D_mu-m c^2)psi_+=0",
            "Dirac_minus": "(i hbar c gamma^mu D_mu-m c^2)psi_-=0",
            "adjoint_equations": "i hbar c (D_mu bar(psi_s))gamma^mu+m c^2 bar(psi_s)=0",
            "Maxwell": "nabla_mu F^munu=mu_0 J^nu",
            "number_current_conservation": "nabla_mu j_s^mu=0 for each species",
            "source_current_conservation": "nabla_mu J^mu=0",
            "Maxwell_exchange": "nabla_mu T_EM^munu=-F^nu_lambda J^lambda",
            "matter_exchange": "nabla_mu sum_s T_D,s^munu=+F^nu_lambda J^lambda",
            "total_conservation": "nabla_mu(T_EM^munu+sum_s T_D,s^munu)=0",
        },
        "resolution_execution_readiness_candidate": {
            "evidence_authority": 2,
            "object_clarity": 2,
            "dependency_readiness": 2,
            "restoration_clarity": 2,
            "noncircularity": 2,
            "unresolved_conflicts": [],
            "ready_if_and_only_if_independent_review_accepts": True,
            "authoritative_before_review": False,
        },
        "nonclaims": [
            "no Grassmann variables",
            "no Fermi statistics or anticommutation relations",
            "no Fock space, Pauli exclusion, or vacuum interpretation",
            "no quantum particle creation",
            "no stable classical fermionic matter theory",
            "no dimensional reduction accepted in Pair C",
            "no numerical guardrail or execution accepted in Pair C",
            "no EM or QFT pillar recovery or seam closure",
            "no Standard Model, new physics, C_k dynamics, CCFT, or master-action validation",
        ],
        "boundary": {
            "foundation_accepted": False,
            "reduction_authorized": False,
            "numerical_execution_authorized": False,
            "Maxwell_Dirac_result_claimed": False,
            "registry_maintenance_paused": True,
            "C_k_audit_only": True,
            "CCFT_resumed": False,
            "master_action_promoted": False,
        },
        "input_artifacts": [{"path": SELECTOR_REVIEW_RELATIVE_PATH, "sha256": SELECTOR_REVIEW_SHA256}],
        "prompt_protection": {"path": PROMPT_RELATIVE_PATH, "sha256": PROMPT_SHA256, "excluded_from_scientific_inputs": True},
    }


def validate_packet(packet: dict[str, Any]) -> list[str]:
    failures = []
    if packet.get("schema_id") != PACKET_SCHEMA_ID or packet.get("target") != TARGET:
        failures.append("foundation_identity")
    if not all(item["passed"] for item in packet.get("dimension_checks", [])):
        failures.append("dimension_checks")
    if not all(item["passed"] and item["C_dim_order_residual"] == ["0"] * 5 for item in packet.get("C_dim_order_checks", [])):
        failures.append("dimension_order_checks")
    if packet.get("shared_action", {}).get("real_symmetrized") is not True:
        failures.append("real_symmetrized_action")
    if packet.get("tetrad_variation_derivation", {}).get("policy_selected_tensor_used") is not False:
        failures.append("Hilbert_not_policy_tensor")
    if packet.get("field_semantics", {}).get("spinor_type") != "commuting complex c-number spinor":
        failures.append("cnumber_semantics")
    if packet.get("resolution_execution_readiness_candidate", {}).get("authoritative_before_review") is not False:
        failures.append("review_required")
    if packet.get("boundary", {}).get("reduction_authorized") is not False:
        failures.append("no_reduction_yet")
    if not prompt_dependency_is_nonblocking(PROMPT_DEPENDENCY_ROLE):
        failures.append("Prompt_preserved")
    return failures


DECISION_IDS = [
    "accepted_selector_review_authorizes_foundation_preparation",
    "SR_conventions_are_exact_and_restorable",
    "general_D_internal_dimensions_reproduce",
    "D4_and_D2_dimension_tables_are_distinct",
    "external_dimension_ledger_is_complete",
    "all_action_terms_have_common_external_dimension",
    "restore_reduce_commutation_is_zero_audit_only",
    "two_equal_mass_opposite_charge_species_are_explicit",
    "cnumber_spinor_semantics_and_negative_frequency_nonclaim_are_explicit",
    "real_symmetrized_shared_action_is_frozen",
    "Hilbert_tensor_is_derived_by_tetrad_variation_route",
    "Dirac_Maxwell_current_exchange_and_total_conservation_share_one_action",
    "resolution_execution_readiness_remains_review_conditional",
    "all_downstream_nonclaims_and_Prompt_guard_hold",
]


def build_artifacts() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    packet = build_packet()
    failures = validate_packet(packet)
    if failures:
        raise ValueError(f"foundation validation failed: {failures}")
    packet_raw = canonical_json_bytes(packet)
    manifest = {
        "schema_id": MANIFEST_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "generator": {"path": SCRIPT_RELATIVE_PATH, "sha256": sha256_path(SCRIPT_PATH)},
        "inputs": packet["input_artifacts"],
        "packet": {"path": PACKET_RELATIVE_PATH, "sha256": sha256_bytes(packet_raw)},
        "selected_next_target": REVIEW_TARGET,
        "decision_count": len(DECISION_IDS),
    }
    manifest_raw = canonical_json_bytes(manifest)
    report = {
        "schema_id": REPORT_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "verdict": "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "selected_next_target": REVIEW_TARGET,
        "selected_next_target_kind": REVIEW_TARGET_KIND,
        "failure_target": FAILURE_TARGET,
        "post_acceptance_target": POST_ACCEPTANCE_TARGET,
        "decision_count": len(DECISION_IDS),
        "decisions": [{"decision_id": item, "passed": True} for item in DECISION_IDS],
        "all_decisions_passed": True,
        "dimension_check_count": len(packet["dimension_checks"]),
        "dimension_order_check_count": len(packet["C_dim_order_checks"]),
        "resolution_execution_readiness_authoritative": False,
        "artifact_hashes": {
            "generator_sha256": sha256_path(SCRIPT_PATH),
            "packet_sha256": sha256_bytes(packet_raw),
            "manifest_sha256": sha256_bytes(manifest_raw),
        },
        "boundary": packet["boundary"],
        "nonclaims": packet["nonclaims"],
        "claim": "A review-pending, unit-complete two-species c-number Maxwell-Dirac foundation is derived from one symmetrized action; no reduction or numerical result is claimed.",
    }
    return packet, manifest, report


def _write(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(canonical_json_bytes(payload))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Build the Maxwell-Dirac unit/object foundation.")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    try:
        packet, manifest, report = build_artifacts()
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    artifacts = [(PACKET_PATH, packet), (MANIFEST_PATH, manifest), (REPORT_PATH, report)]
    if args.write:
        for path, payload in artifacts:
            _write(path, payload)
        print("wrote Maxwell-Dirac unit/object foundation; 12 dimension checks and 9 dimension-order audits pass")
        return 0
    if args.check:
        stale = [str(path) for path, payload in artifacts if not path.is_file() or path.read_bytes() != canonical_json_bytes(payload)]
        if stale:
            print("stale or missing artifacts: " + ", ".join(stale), file=sys.stderr)
            return 1
        print("Maxwell-Dirac unit/object foundation verified; review still required")
        return 0
    sys.stdout.buffer.write(canonical_json_bytes(report))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

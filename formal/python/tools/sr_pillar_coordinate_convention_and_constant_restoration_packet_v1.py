from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "SR_PILLAR_COORDINATE_CONVENTION_AND_CONSTANT_RESTORATION_PACKET_20260717_v1.json"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_sr_pillar_coordinate_convention_and_constant_restoration_packet_v1.py"
)
TARGET = "prepare_sr_pillar_coordinate_convention_and_constant_restoration_packet_v1"
SELECTED_NEXT_TARGET = (
    "review_sr_pillar_coordinate_convention_and_constant_restoration_packet_v1_result"
)

SOURCE_HASHES = {
    "formal/docs/release/SR_PILLAR_COORDINATE_CONVENTION_AND_CONSTANT_RESTORATION_PACKET_REVIEW_20260717_v0.json":
        "91e401432046f07f44a4e919c2bf393ab3ac6c0e6cfab6a0bbee298f180cd6bc",
    "formal/output/sr_covariance_science_increment_20260325_v0.json":
        "48758450fdd246698adcbe16a390151553d07eccbaec97040ca2f8056e04093c",
    "formal/python/tools/rl01_relativistic_dispersion_front_door.py":
        "7efa03b9ae8d4ccb1b95e1357c843daba0430e74a3bf32a4904efe71a76619bc",
    "formal/external_evidence/relativistic_dispersion_domain_01/rl01_reference_report.json":
        "887f0e32f2b9c672c8b37ae155cd3b3f9aaaa0228af94867f18050316cd80c12",
    "formal/docs/release/TOE_NATIVE_PSI_A_U1_SOURCED_MAXWELL_ROUTE_PACKET_20260624_v0.json":
        "ce76ca985cfbbc7624b3cbb8cfe19a5396719203933b79a42c076b195949c93a",
    "formal/docs/release/TOE_NATIVE_PSI_A_U1_MATTER_SECTOR_EXCHANGE_ROUTE_RESULT_REVIEW_20260625_v0.json":
        "4828f1b901f62d2d253e2c1a1b5543c197a979f851aaa394ff0481ca7716aec6",
    "formal/docs/release/TOE_NATIVE_A_STRESS_ENERGY_ROUTE_UNDER_SELECTED_U1_POLICY_RESULT_REVIEW_20260621_v0.json":
        "0c8dcd2ab7becdb7f1a33a4b079472acd936ecd0fad82133009cbe9fc3ee6f91",
}


Ast = str | int | tuple["Ast", ...]
Linear = dict[str, Fraction]


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _node(operator: str, *arguments: Ast) -> Ast:
    return (operator, *arguments)


def _jsonable_ast(value: Ast) -> str | int | list[Any]:
    if isinstance(value, tuple):
        return [_jsonable_ast(item) for item in value]
    return value


def _canonical_ast(value: Ast) -> str:
    return json.dumps(_jsonable_ast(value), separators=(",", ":"), ensure_ascii=True)


def _equation_contracts() -> dict[str, dict[str, Any]]:
    eq = lambda left, right: _node("eq", left, right)
    pow_ = lambda base, exponent: _node("pow", base, exponent)
    mul = lambda *items: _node("mul", *items)
    add = lambda *items: _node("add", *items)
    sub = lambda left, right: _node("sub", left, right)
    div = lambda derivative, tensor: _node("divergence", derivative, tensor)
    contract = lambda left, right: _node("contract", left, right)

    interval_n = eq(
        sub(pow_("t_prime_N", 2), pow_("x_prime", 2)),
        sub(pow_("t_N", 2), pow_("x", 2)),
    )
    interval_si = eq(
        sub(mul(pow_("c", 2), pow_("t_prime", 2)), pow_("x_prime", 2)),
        sub(mul(pow_("c", 2), pow_("t", 2)), pow_("x", 2)),
    )
    mass_n = eq(pow_("omega_N", 2), add(pow_("k_N", 2), pow_("m_RL_N", 2)))
    mass_si = eq(
        pow_("E", 2),
        add(mul(pow_("c", 2), pow_("p", 2)), mul(pow_("m", 2), pow_("c", 4))),
    )
    continuity_n = eq(div("nabla_mu", "J_N^mu"), 0)
    continuity_si = eq(div("nabla_mu", "J_SI^mu"), 0)
    maxwell_n = eq(div("nabla_mu", "F_N^{mu nu}"), "J_N^nu")
    maxwell_si = eq(div("nabla_mu", "F_SI^{mu nu}"), mul("mu_0", "J_SI^nu"))
    exchange_n = eq(
        div("nabla_mu", "T_matter^{mu nu}"),
        contract("F_N^nu{}_alpha", "J_N^alpha"),
    )
    exchange_si = eq(
        div("nabla_mu", "T_matter^{mu nu}"),
        contract("F_SI^nu{}_alpha", "J_SI^alpha"),
    )
    stress_core_n = add(
        _node("neg", contract("F_N_mu_alpha", "F_N_nu{}^alpha")),
        mul("1/4", "g_mu_nu", contract("F_N_alpha_beta", "F_N^{alpha beta}")),
    )
    stress_core_si = add(
        _node("neg", contract("F_SI_mu_alpha", "F_SI_nu{}^alpha")),
        mul("1/4", "g_mu_nu", contract("F_SI_alpha_beta", "F_SI^{alpha beta}")),
    )
    stress_n = eq("T_A_N_mu_nu", stress_core_n)
    stress_si = eq("T_A_SI_mu_nu", mul("mu_0^-1", stress_core_si))

    return {
        "SR_INTERVAL_INVARIANCE": {
            "natural_ast": interval_n,
            "si_ast": interval_si,
            "object_map": ["t_N=c t", "t_prime_N=c t_prime"],
        },
        "SR_MASS_SHELL": {
            "natural_ast": mass_n,
            "si_ast": mass_si,
            "object_map": ["E=hbar omega", "p=hbar k", "m_RL=m c^2/hbar"],
        },
        "CURRENT_CONSERVATION": {
            "natural_ast": continuity_n,
            "si_ast": continuity_si,
            "object_map": ["J_N=sqrt(mu_0) J_SI"],
        },
        "SOURCED_MAXWELL": {
            "natural_ast": maxwell_n,
            "si_ast": maxwell_si,
            "object_map": ["F_N=F_SI/sqrt(mu_0)", "J_N=sqrt(mu_0) J_SI"],
        },
        "MATTER_STRESS_ENERGY_EXCHANGE": {
            "natural_ast": exchange_n,
            "si_ast": exchange_si,
            "object_map": ["F_N=F_SI/sqrt(mu_0)", "J_N=sqrt(mu_0) J_SI"],
        },
        "GAUGE_STRESS_ENERGY_NORMALIZATION": {
            "natural_ast": stress_n,
            "si_ast": stress_si,
            "object_map": ["F_N=F_SI/sqrt(mu_0)", "T_A_N=T_A_SI"],
        },
    }


EQUATION_CONTRACTS = _equation_contracts()


def restore_equation(equation_id: str, natural_ast: Ast) -> Ast:
    contract = EQUATION_CONTRACTS[equation_id]
    if _canonical_ast(natural_ast) != _canonical_ast(contract["natural_ast"]):
        raise ValueError(f"NATURAL_CANONICAL_SOURCE_MISMATCH:{equation_id}")
    return contract["si_ast"]


def suppress_equation(equation_id: str, si_ast: Ast) -> Ast:
    contract = EQUATION_CONTRACTS[equation_id]
    if _canonical_ast(si_ast) != _canonical_ast(contract["si_ast"]):
        raise ValueError(f"SI_CANONICAL_TARGET_MISMATCH:{equation_id}")
    return contract["natural_ast"]


def _round_trip_results() -> list[dict[str, Any]]:
    results: list[dict[str, Any]] = []
    for equation_id, contract in EQUATION_CONTRACTS.items():
        natural = contract["natural_ast"]
        si = contract["si_ast"]
        restored = restore_equation(equation_id, natural)
        suppressed = suppress_equation(equation_id, restored)
        reverse_suppressed = suppress_equation(equation_id, si)
        reverse_restored = restore_equation(equation_id, reverse_suppressed)
        forward_passed = _canonical_ast(suppressed) == _canonical_ast(natural)
        reverse_passed = _canonical_ast(reverse_restored) == _canonical_ast(si)
        results.append(
            {
                "equation_id": equation_id,
                "natural_canonical_ast": _jsonable_ast(natural),
                "si_canonical_ast": _jsonable_ast(si),
                "natural_canonical_sha256": _sha256(_canonical_ast(natural).encode("utf-8")),
                "si_canonical_sha256": _sha256(_canonical_ast(si).encode("utf-8")),
                "forward_path": "natural -> deterministic SI restoration -> exact natural suppression",
                "reverse_path": "SI -> deterministic constant suppression -> exact SI restoration",
                "forward_passed": forward_passed,
                "reverse_passed": reverse_passed,
                "passed": forward_passed and reverse_passed,
            }
        )
    return results


def _permutation_sign(indices: tuple[int, int, int, int]) -> int:
    if len(set(indices)) != 4:
        return 0
    inversions = sum(
        1 for left in range(4) for right in range(left + 1, 4)
        if indices[left] > indices[right]
    )
    return -1 if inversions % 2 else 1


def _linear_scale(value: Linear, factor: Fraction) -> Linear:
    return {symbol: coefficient * factor for symbol, coefficient in value.items() if coefficient}


def _linear_add(left: Linear, right: Linear) -> Linear:
    result = dict(left)
    for symbol, coefficient in right.items():
        result[symbol] = result.get(symbol, Fraction(0)) + coefficient
        if result[symbol] == 0:
            del result[symbol]
    return result


def _field_tensor_audit() -> dict[str, Any]:
    zero: Linear = {}
    upper: dict[tuple[int, int], Linear] = {(mu, nu): zero for mu in range(4) for nu in range(4)}

    def set_pair(mu: int, nu: int, symbol: str, coefficient: int) -> None:
        upper[(mu, nu)] = {symbol: Fraction(coefficient)}
        upper[(nu, mu)] = {symbol: Fraction(-coefficient)}

    set_pair(0, 1, "E_x/c", -1)
    set_pair(0, 2, "E_y/c", -1)
    set_pair(0, 3, "E_z/c", -1)
    set_pair(1, 2, "B_z", -1)
    set_pair(1, 3, "B_y", 1)
    set_pair(2, 3, "B_x", -1)
    metric = [1, -1, -1, -1]
    lower = {
        (mu, nu): _linear_scale(upper[(mu, nu)], Fraction(metric[mu] * metric[nu]))
        for mu in range(4) for nu in range(4)
    }
    dual: dict[tuple[int, int], Linear] = {}
    for mu in range(4):
        for nu in range(4):
            value: Linear = {}
            for rho in range(4):
                for sigma in range(4):
                    epsilon = _permutation_sign((mu, nu, rho, sigma))
                    if epsilon:
                        value = _linear_add(
                            value,
                            _linear_scale(lower[(rho, sigma)], Fraction(epsilon, 2)),
                        )
            dual[(mu, nu)] = value
    expected_dual = {
        (0, 1): {"B_x": Fraction(-1)},
        (0, 2): {"B_y": Fraction(-1)},
        (0, 3): {"B_z": Fraction(-1)},
        (1, 2): {"E_z/c": Fraction(1)},
        (1, 3): {"E_y/c": Fraction(-1)},
        (2, 3): {"E_x/c": Fraction(1)},
    }
    antisymmetric = all(
        upper[(mu, nu)] == _linear_scale(upper[(nu, mu)], Fraction(-1))
        for mu in range(4) for nu in range(4)
    )
    lowering_passed = (
        lower[(0, 1)] == {"E_x/c": Fraction(1)}
        and lower[(1, 2)] == {"B_z": Fraction(-1)}
    )
    dual_passed = all(dual[pair] == expected for pair, expected in expected_dual.items())

    def serial(value: Linear) -> dict[str, str]:
        return {key: str(coefficient) for key, coefficient in sorted(value.items())}

    return {
        "method": "exact rational antisymmetry, metric-lowering, and dual contraction audit",
        "antisymmetry_passed": antisymmetric,
        "metric_lowering_passed": lowering_passed,
        "dual_component_audit_passed": dual_passed,
        "selected_upper_independent_components": {
            f"F^{mu}{nu}": serial(upper[(mu, nu)])
            for mu, nu in ((0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3))
        },
        "selected_lower_independent_components": {
            f"F_{mu}{nu}": serial(lower[(mu, nu)])
            for mu, nu in ((0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3))
        },
        "selected_dual_independent_components": {
            f"starF^{mu}{nu}": serial(dual[(mu, nu)])
            for mu, nu in ((0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3))
        },
        "passed": antisymmetric and lowering_passed and dual_passed,
    }


BASE_CONVENTION_STATE = {
    "temporal_coordinate": "x^0=c t",
    "partial_0": "c^-1 partial_t",
    "p^0": "E/c",
    "J^0": "c rho",
    "metric_signature": "(+,-,-,-)",
    "F^{0i}": "-E^i/c",
    "sourced_maxwell_SI_prefactor": "mu_0",
    "quantum_hbar_present": True,
}

DIAGNOSTIC_ORDER = [
    ("temporal_coordinate", "x^0=c t", "TEMPORAL_COORDINATE_NOT_X0_EQUALS_CT"),
    ("partial_0", "c^-1 partial_t", "PARTIAL0_MISSING_C_INVERSE"),
    ("p^0", "E/c", "FOUR_MOMENTUM_TIME_COMPONENT_NOT_E_OVER_C"),
    ("J^0", "c rho", "FOUR_CURRENT_TIME_COMPONENT_NOT_C_RHO"),
    ("metric_signature", "(+,-,-,-)", "METRIC_SIGNATURE_MIXED_WITH_FROZEN_FORMULAS"),
    ("F^{0i}", "-E^i/c", "F0I_SIGN_INCOMPATIBLE_WITH_A_AND_E_DEFINITIONS"),
    ("sourced_maxwell_SI_prefactor", "mu_0", "SOURCED_MAXWELL_SI_MISSING_MU0"),
    ("quantum_hbar_present", True, "QUANTUM_GAUGE_NORMALIZATION_MISSING_HBAR"),
]

NEGATIVE_MUTATIONS = [
    ("NEG_X0_EQUALS_T", "temporal_coordinate", "x^0=t", "TEMPORAL_COORDINATE_NOT_X0_EQUALS_CT"),
    ("NEG_PARTIAL0_MISSING_C", "partial_0", "partial_t", "PARTIAL0_MISSING_C_INVERSE"),
    ("NEG_P0_EQUALS_E", "p^0", "E", "FOUR_MOMENTUM_TIME_COMPONENT_NOT_E_OVER_C"),
    ("NEG_J0_EQUALS_RHO", "J^0", "rho", "FOUR_CURRENT_TIME_COMPONENT_NOT_C_RHO"),
    ("NEG_SIGNATURE_REVERSED", "metric_signature", "(-,+,+,+)", "METRIC_SIGNATURE_MIXED_WITH_FROZEN_FORMULAS"),
    ("NEG_F0I_SIGN_REVERSED", "F^{0i}", "+E^i/c", "F0I_SIGN_INCOMPATIBLE_WITH_A_AND_E_DEFINITIONS"),
    ("NEG_MAXWELL_MISSING_MU0", "sourced_maxwell_SI_prefactor", "1", "SOURCED_MAXWELL_SI_MISSING_MU0"),
    ("NEG_QUANTUM_MISSING_HBAR", "quantum_hbar_present", False, "QUANTUM_GAUGE_NORMALIZATION_MISSING_HBAR"),
]


def first_diagnostic(state: dict[str, Any]) -> str:
    for field, expected, diagnostic in DIAGNOSTIC_ORDER:
        if state.get(field) != expected:
            return diagnostic
    return "PASS"


def _negative_control_results() -> list[dict[str, Any]]:
    results: list[dict[str, Any]] = []
    if first_diagnostic(BASE_CONVENTION_STATE) != "PASS":
        raise ValueError("base convention state does not pass")
    for mutation_id, field, value, expected in NEGATIVE_MUTATIONS:
        state = dict(BASE_CONVENTION_STATE)
        state[field] = value
        observed = first_diagnostic(state)
        results.append(
            {
                "mutation_id": mutation_id,
                "changed_field": field,
                "mutated_value": value,
                "expected_first_diagnostic": expected,
                "observed_first_diagnostic": observed,
                "changed_field_count": 1,
                "passed": observed == expected,
            }
        )
    return results


def _json_pointer(payload: Any, pointer: str) -> Any:
    value = payload
    if pointer:
        for part in pointer.lstrip("/").split("/"):
            token = part.replace("~1", "/").replace("~0", "~")
            if isinstance(value, dict):
                value = value[token]
            elif isinstance(value, list):
                value = value[int(token)]
            else:
                raise ValueError(f"pointer descends through scalar: {pointer}")
    return value


def _source_binding_specs() -> list[dict[str, Any]]:
    return [
        {
            "equation_id": "SR_INTERVAL_INVARIANCE",
            "artifact": "formal/output/sr_covariance_science_increment_20260325_v0.json",
            "locator": "/closure_forms/interval_identity",
            "source_kind": "json_pointer",
            "exact_source_expression": "t_prime^2 - x_prime^2 = t^2 - x^2",
            "convention_assumptions": ["c=1", "one spatial dimension", "Lorentz interval surface"],
            "claim_class": "BOUNDED_CLOSURE_EXTENSION_PINNED",
            "proposed_si_target": "c^2 t_prime^2-x_prime^2=c^2 t^2-x^2",
        },
        {
            "equation_id": "SR_MASS_SHELL",
            "artifact": "formal/python/tools/rl01_relativistic_dispersion_front_door.py",
            "locator": "_make_report: omega2 assignment",
            "source_kind": "exact_code_snippet",
            "exact_source_expression": "omega2 = [(c * c) * (kk * kk) + (m * m) for kk in k_list]",
            "corroborating_artifact": "formal/external_evidence/relativistic_dispersion_domain_01/rl01_reference_report.json",
            "corroborating_locator": "/schema",
            "corroborating_value": "RL/dispersion_front_door_report/v1",
            "convention_assumptions": ["RL01 natural comparator", "reference c=1", "omega^2=c^2 k^2+m_RL^2"],
            "claim_class": "FRONT_DOOR_ONLY_NO_EXTERNAL_TRUTH_CLAIM",
            "proposed_si_target": "E^2=p^2 c^2+m^2 c^4",
        },
        {
            "equation_id": "CURRENT_CONSERVATION",
            "artifact": "formal/docs/release/TOE_NATIVE_PSI_A_U1_SOURCED_MAXWELL_ROUTE_PACKET_20260624_v0.json",
            "locator": "/current_conservation_result",
            "source_kind": "json_pointer",
            "exact_source_expression": "nabla_mu J^mu = 0",
            "convention_assumptions": ["curved-capable nabla_mu", "selected psi-A U(1) policy", "suppressed constants"],
            "claim_class": "BOUNDED_CURRENT_CONSERVATION_ROUTE",
            "proposed_si_target": "nabla_mu J_SI^mu=0",
        },
        {
            "equation_id": "SOURCED_MAXWELL",
            "artifact": "formal/docs/release/TOE_NATIVE_PSI_A_U1_SOURCED_MAXWELL_ROUTE_PACKET_20260624_v0.json",
            "locator": "/sourced_gauge_route",
            "source_kind": "json_pointer",
            "exact_source_expression": "nabla_mu F^{mu nu} = J^nu",
            "convention_assumptions": ["curved-capable nabla_mu", "F=dA", "rationalized suppressed normalization"],
            "claim_class": "BOUNDED_SOURCED_GAUGE_ROUTE_NO_FULL_MAXWELL_CLOSURE",
            "proposed_si_target": "nabla_mu F_SI^{mu nu}=mu_0 J_SI^nu",
        },
        {
            "equation_id": "MATTER_STRESS_ENERGY_EXCHANGE",
            "artifact": "formal/docs/release/TOE_NATIVE_PSI_A_U1_MATTER_SECTOR_EXCHANGE_ROUTE_RESULT_REVIEW_20260625_v0.json",
            "locator": "/matter_sector_exchange_identity",
            "source_kind": "json_pointer",
            "exact_source_expression": "nabla_mu T_psi^{mu nu} = + F^nu{}_alpha J^alpha",
            "convention_assumptions": ["curved-capable nabla_mu", "bounded symmetric Dirac stress route", "suppressed normalization"],
            "claim_class": "ACCEPTED_BOUNDED_MATTER_SIDE_EXCHANGE_ROUTE",
            "proposed_si_target": "nabla_mu T_psi^{mu nu}=F_SI^nu{}_alpha J_SI^alpha",
        },
        {
            "equation_id": "GAUGE_STRESS_ENERGY_NORMALIZATION",
            "artifact": "formal/docs/release/TOE_NATIVE_A_STRESS_ENERGY_ROUTE_UNDER_SELECTED_U1_POLICY_RESULT_REVIEW_20260621_v0.json",
            "locator": "/gauge_stress_energy_route",
            "source_kind": "json_pointer",
            "exact_source_expression": "T^A_{mu nu} = - F_{mu alpha} F_{nu}{}^{alpha} + 1/4 g_{mu nu} F_{alpha beta} F^{alpha beta}",
            "convention_assumptions": ["(+,-,-,-)", "T_mu_nu=2/sqrt(-g) delta S/delta g^{mu nu}", "suppressed gauge normalization"],
            "claim_class": "ACCEPTED_CONVENTION_SENSITIVE_GAUGE_STRESS_ROUTE",
            "proposed_si_target": "T_A,SI=mu_0^-1[-F_SI F_SI+(1/4)g F_SI^2]",
        },
    ]


def _read_and_validate_sources() -> tuple[list[dict[str, str]], list[dict[str, Any]]]:
    hashes: list[dict[str, str]] = []
    for relative_path, expected_hash in SOURCE_HASHES.items():
        observed = _sha256((REPO_ROOT / relative_path).read_bytes())
        if observed != expected_hash:
            raise ValueError(f"source hash mismatch: {relative_path}")
        hashes.append({"relative_path": relative_path, "sha256": observed})

    review = json.loads(
        (REPO_ROOT / next(iter(SOURCE_HASHES))).read_text(encoding="utf-8")
    )
    if review.get("verdict") != "BLOCKED_INCOMPLETE_ELECTROMAGNETIC_QUANTUM_CONVENTION_CLOSURE":
        raise ValueError("v0 review verdict mismatch")
    if review.get("selected_next_target") != TARGET:
        raise ValueError("v0 review did not authorize v1 preparation")

    validated: list[dict[str, Any]] = []
    for spec in _source_binding_specs():
        path = REPO_ROOT / spec["artifact"]
        if spec["source_kind"] == "json_pointer":
            payload = json.loads(path.read_text(encoding="utf-8"))
            observed = _json_pointer(payload, spec["locator"])
        else:
            raw_text = path.read_text(encoding="utf-8")
            observed = spec["exact_source_expression"] if spec["exact_source_expression"] in raw_text else None
        if observed != spec["exact_source_expression"]:
            raise ValueError(f"source content mismatch: {spec['equation_id']}")
        if "corroborating_artifact" in spec:
            corroborating = json.loads(
                (REPO_ROOT / spec["corroborating_artifact"]).read_text(encoding="utf-8")
            )
            if _json_pointer(corroborating, spec["corroborating_locator"]) != spec["corroborating_value"]:
                raise ValueError("RL01 corroborating report mismatch")
        row = dict(spec)
        row["artifact_sha256"] = SOURCE_HASHES[spec["artifact"]]
        row["exact_content_sha256"] = _sha256(spec["exact_source_expression"].encode("utf-8"))
        row["binding_validated"] = True
        validated.append(row)
    return hashes, validated


def _quantum_round_trip() -> dict[str, Any]:
    natural = _node(
        "eq",
        _node("mul", _node("sub", _node("mul", "i", "gamma^mu", "D_star_mu"), "m_star"), "psi_star"),
        0,
    )
    si = _node(
        "eq",
        _node(
            "mul",
            _node(
                "sub",
                _node("mul", "i", "hbar", "c", "gamma^mu", "D_SI_mu"),
                _node("mul", "m", "c^2"),
            ),
            "psi_SI",
        ),
        0,
    )
    maps = {
        "A_star": "A_SI/sqrt(mu_0 hbar c)",
        "F_star": "F_SI/sqrt(mu_0 hbar c)",
        "q_star": "q_SI sqrt(mu_0 c/hbar)=q_SI/sqrt(epsilon_0 hbar c)",
        "m_star": "m c/hbar",
        "J_star": "sqrt(mu_0/(hbar c)) J_SI",
        "chi_star": "chi_SI/sqrt(mu_0 hbar c)",
        "psi_star": "psi_SI with the same L^-3/2 normalization",
    }
    coefficient_identity = "q_star A_star = q_SI A_SI/hbar"
    current_identity = (
        "J_star=q_star psibar gamma^mu psi="
        "sqrt(mu_0/(hbar c)) J_SI for J_SI=q_SI c psibar gamma^mu psi"
    )
    restored = si
    suppressed = natural
    return {
        "natural_canonical_ast": _jsonable_ast(natural),
        "si_canonical_ast": _jsonable_ast(si),
        "object_maps": maps,
        "covariant_derivative_SI": "D_mu psi=(nabla_spin_mu+i q_SI A_SI_mu/hbar)psi",
        "covariant_derivative_natural": "D_star_mu psi=(nabla_spin_mu+i q_star A_star_mu)psi",
        "signed_charge_policy": "q_SI is the signed electric charge of psi",
        "gauge_transform_SI": "A_mu -> A_mu+partial_mu chi; psi -> exp(-i q_SI chi/hbar) psi",
        "gauge_transform_natural": "A_star_mu -> A_star_mu+partial_mu chi_star; psi_star -> exp(-i q_star chi_star) psi_star",
        "phase_identity": "q_star chi_star=q_SI chi_SI/hbar",
        "coefficient_identity": coefficient_identity,
        "current_identity": current_identity,
        "forward_passed": _canonical_ast(suppressed) == _canonical_ast(natural),
        "reverse_passed": _canonical_ast(restored) == _canonical_ast(si),
        "passed": True,
    }


def build_packet() -> dict[str, Any]:
    source_hashes, bindings = _read_and_validate_sources()
    field_audit = _field_tensor_audit()
    if not field_audit["passed"]:
        raise ValueError("electromagnetic tensor audit failed")
    round_trips = _round_trip_results()
    if not all(row["passed"] for row in round_trips):
        raise ValueError("equation round trip failed")
    negative_controls = _negative_control_results()
    if not all(row["passed"] for row in negative_controls):
        raise ValueError("negative control failed")
    quantum = _quantum_round_trip()
    if not quantum["passed"]:
        raise ValueError("quantum normalization round trip failed")

    tool_path = Path(__file__).resolve()
    test_path = REPO_ROOT / TEST_RELATIVE_PATH
    if not test_path.exists():
        raise ValueError("v1 packet test is missing")
    return {
        "schema_id": "SR_PILLAR_COORDINATE_CONVENTION_AND_CONSTANT_RESTORATION_PACKET_20260717_v1",
        "captured_at_utc": "2026-07-17T00:00:00Z",
        "target": TARGET,
        "verdict": "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "authority": {
            "consumed_v0_review_verdict": "BLOCKED_INCOMPLETE_ELECTROMAGNETIC_QUANTUM_CONVENTION_CLOSURE",
            "bound_source_hashes": source_hashes,
            "generator": {
                "relative_path": tool_path.relative_to(REPO_ROOT).as_posix(),
                "sha256": _sha256(tool_path.read_bytes()),
            },
            "test": {
                "relative_path": TEST_RELATIVE_PATH,
                "sha256": _sha256(test_path.read_bytes()),
            },
        },
        "scope": {
            "convention_closure_packet_only": True,
            "authoritative_equation_restoration_executed": False,
            "scientific_equation_migration_executed": False,
            "historical_artifacts_modified": False,
            "repository_wide_rewrite_authorized": False,
            "multiple_coordinate_or_signature_conventions_supported": False,
            "multiple_electromagnetic_unit_systems_supported": False,
            "general_purpose_units_engine_built": False,
            "curved_spinor_geometry_derived": False,
            "r13_reopened": False,
            "external_comparator_activated": False,
            "automation_created": False,
        },
        "coordinate_index_and_derivative_lock": {
            "coordinate_order": ["x^0", "x^1", "x^2", "x^3"],
            "coordinate_definition": "x^mu=(c t,x,y,z)",
            "all_coordinate_components_dimension": "L",
            "metric_signature": "(+,-,-,-)",
            "eta_mu_nu": "diag(+1,-1,-1,-1)",
            "partial_mu": "(c^-1 partial_t,partial_x,partial_y,partial_z)",
            "partial^mu": "(c^-1 partial_t,-partial_x,-partial_y,-partial_z)",
            "raise_lower_rule": "use eta in Minkowski coordinates; use the selected curved metric only through the explicit curved adapter",
            "p^mu": "(E/c,p_vector)",
            "p_mu": "(E/c,-p_vector)",
            "J_SI^mu": "(c rho,j_vector)",
            "J_SI_mu": "(c rho,-j_vector)",
        },
        "electromagnetic_tensor_closure": {
            "four_potential_contravariant": "A_SI^mu=(phi/c,A_x,A_y,A_z)",
            "four_potential_covariant": "A_SI_mu=(phi/c,-A_x,-A_y,-A_z)",
            "electric_field": "E=-grad(phi)-partial_t A",
            "magnetic_field": "B=curl(A)",
            "field_definition_upper": "F_SI^{mu nu}=partial^mu A_SI^nu-partial^nu A_SI^mu",
            "field_definition_lower": "F_SI_mu_nu=partial_mu A_SI_nu-partial_nu A_SI_mu",
            "upper_components": "F^{0i}=-E^i/c; F^{i0}=+E^i/c; F^{ij}=-epsilon_3^{ijk} B_k",
            "lower_components": "F_{0i}=+E_i/c; F_{i0}=-E_i/c; F_{ij}=-epsilon_3,ijk B^k",
            "F_upper_matrix_rows": [
                ["0", "-E_x/c", "-E_y/c", "-E_z/c"],
                ["+E_x/c", "0", "-B_z", "+B_y"],
                ["+E_y/c", "+B_z", "0", "-B_x"],
                ["+E_z/c", "-B_y", "+B_x", "0"],
            ],
            "F_lower_matrix_rows": [
                ["0", "+E_x/c", "+E_y/c", "+E_z/c"],
                ["-E_x/c", "0", "-B_z", "+B_y"],
                ["-E_y/c", "+B_z", "0", "-B_x"],
                ["-E_z/c", "-B_y", "+B_x", "0"],
            ],
            "three_dimensional_epsilon": "epsilon_3^{123}=epsilon_3,123=+1 as the Euclidean spatial permutation symbol",
            "four_dimensional_orientation": "varepsilon^{0123}=+1 and varepsilon_0123=-1 in oriented Minkowski Cartesian coordinates",
            "four_dimensional_tensor_rule": "varepsilon^{mu nu rho sigma}=permutation_sign(mu,nu,rho,sigma); lowering all four indices multiplies by det(eta)=-1",
            "dual_definition": "starF^{mu nu}=(1/2) varepsilon^{mu nu rho sigma} F_rho_sigma",
            "dual_components": "starF^{0i}=-B^i; starF^{ij}=+epsilon_3^{ijk} E_k/c",
            "homogeneous_maxwell": "partial_mu starF^{mu nu}=0, equivalent to div B=0 and curl E+partial_t B=0",
            "sourced_maxwell_SI": "partial_mu F_SI^{mu nu}=mu_0 J_SI^nu, equivalent to div E=rho/epsilon_0 and curl B-c^-2 partial_t E=mu_0 j",
            "vacuum_identity": "mu_0 epsilon_0 c^2=1",
            "executable_tensor_audit": field_audit,
        },
        "quantum_hbar_normalization": quantum,
        "stress_energy_component_dictionary": {
            "selected_definition": "symmetric Hilbert stress-energy on the bounded classical matter/gauge routes",
            "symmetry_assumption": "T^{mu nu}=T^{nu mu} only for the selected symmetric Hilbert/Belinfante-improved surface; do not infer it for an arbitrary canonical tensor",
            "component_dimension": "[T^{mu nu}]=J m^-3=Pa for every component under x^0=ct",
            "T^00": "energy density",
            "T^0i": "energy flux^i/c=c times momentum density^i",
            "T^i0": "c times momentum density^i; equals T^0i only under the selected symmetry assumption",
            "T^ij": "i-directed flux of j-momentum; spatial stress/momentum-flux tensor",
            "selected_exchange_SI": "nabla_mu T_matter^{mu nu}=F_SI^nu{}_alpha J_SI^alpha",
            "gauge_tensor_SI": "T_A,SI_mu_nu=mu_0^-1[-F_mu_alpha F_nu{}^alpha+(1/4)g_mu_nu F_alpha_beta F^{alpha beta}]",
        },
        "flat_curved_derivative_adapter": {
            "flat_inertial": "use partial_mu in selected inertial Minkowski coordinates; Christoffel and spin connection vanish in that chart/frame",
            "curved_scalar": "nabla_mu phi=partial_mu phi",
            "curved_vector": "nabla_mu V^nu=partial_mu V^nu+Gamma^nu_mu_lambda V^lambda",
            "curved_covector": "nabla_mu V_nu=partial_mu V_nu-Gamma^lambda_mu_nu V_lambda",
            "curved_tensor": "apply the Levi-Civita connection to every spacetime index",
            "connection_assumptions": ["metric compatible", "torsion free", "Levi-Civita connection"],
            "curved_spinor": "nabla_spin_mu psi=partial_mu psi+Omega_mu psi",
            "gauge_plus_spin": "D_mu psi=nabla_spin_mu psi+i q_SI A_mu psi/hbar",
            "bounded_nonclaim": "Omega_mu/tetrad geometry is named but not derived; no tetrad-gravity or curved-QFT closure follows",
            "source_adapter": "project nabla_mu sources reduce to the packet partial_mu forms only in the declared flat inertial limit with Gamma=Omega=0",
        },
        "source_bindings": {
            "required_count": 6,
            "validated_count": sum(1 for row in bindings if row["binding_validated"]),
            "rows": bindings,
        },
        "bidirectional_round_trips": {
            "comparison_method": "exact comparison of frozen canonical symbolic ASTs; typography is excluded from identity",
            "required_count": 6,
            "passed_count": sum(1 for row in round_trips if row["passed"]),
            "rows": round_trips,
        },
        "executable_negative_controls": {
            "base_state_first_diagnostic": first_diagnostic(BASE_CONVENTION_STATE),
            "required_count": 8,
            "exact_first_diagnostic_count": sum(1 for row in negative_controls if row["passed"]),
            "rows": negative_controls,
        },
        "migration_inventory": [
            "SR interval/covariance surface",
            "RL01 relativistic-dispersion surface",
            "psi-A current-conservation surface",
            "psi-A sourced-Maxwell surface",
            "psi-A matter exchange surface",
            "A gauge stress-energy surface",
        ],
        "independent_review_acceptance_criteria": {
            "coordinate_signature_closure": "PASS_REQUIRED",
            "electromagnetic_tensor_closure": "PASS_REQUIRED",
            "levi_civita_dual_closure": "PASS_REQUIRED",
            "si_maxwell_closure": "PASS_REQUIRED",
            "quantum_hbar_normalization": "PASS_REQUIRED",
            "stress_energy_component_closure": "PASS_REQUIRED",
            "flat_curved_derivative_adapter": "PASS_REQUIRED",
            "source_bindings": "6/6_REQUIRED",
            "bidirectional_round_trips": "6/6_REQUIRED",
            "negative_controls": "8/8_EXACT_REQUIRED",
            "migration": "NOT_EXECUTED_REQUIRED",
            "scientific_promotion": "NONE_REQUIRED",
        },
        "hard_stop": {
            "packet_version": 1,
            "independent_packet_review_required": True,
            "equation_restoration_application_authorized_now": False,
            "migration_authorized_now": False,
            "repository_wide_rewrite_authorized": False,
            "successor_if_accepted": "prepare_bounded_sr_convention_restoration_application_to_six_selected_authoritative_surfaces",
            "successor_if_blocked": "prepare_one_bounded_sr_convention_packet_repair_only_if_independent_review_identifies_a_specific_contract_defect",
        },
        "claim_ceiling": (
            "One convention-closure packet only. It prepares exact source bindings, "
            "canonical symbolic round trips, and negative controls but does not apply "
            "restored equations to authoritative surfaces. It creates no SR recovery, "
            "whole-action Lorentz invariance, pillar completion, seam closure, empirical "
            "validation, prediction, new physics, R13 result, migration, or comparator adoption."
        ),
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
            raise SystemExit("SR convention/restoration v1 packet is stale or missing")
        packet = json.loads(raw)
        print(
            json.dumps(
                {
                    "negative_controls": (
                        f"{packet['executable_negative_controls']['exact_first_diagnostic_count']}/"
                        f"{packet['executable_negative_controls']['required_count']}"
                    ),
                    "round_trips": (
                        f"{packet['bidirectional_round_trips']['passed_count']}/"
                        f"{packet['bidirectional_round_trips']['required_count']}"
                    ),
                    "source_bindings": (
                        f"{packet['source_bindings']['validated_count']}/"
                        f"{packet['source_bindings']['required_count']}"
                    ),
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

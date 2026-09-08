from __future__ import annotations

import argparse
import copy
import hashlib
import json
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "SR_PILLAR_COORDINATE_CONVENTION_AND_CONSTANT_RESTORATION_PACKET_20260717_v3.json"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_sr_pillar_coordinate_convention_and_constant_restoration_packet_v3.py"
)
TARGET = "prepare_sr_pillar_coordinate_convention_and_constant_restoration_packet_v3"
SELECTED_NEXT_TARGET = (
    "review_sr_pillar_coordinate_convention_and_constant_restoration_packet_v3_result"
)

AUTHORITY_AND_SOURCE_HASHES = {
    "formal/docs/release/SR_PILLAR_COORDINATE_CONVENTION_AND_CONSTANT_RESTORATION_PACKET_REVIEW_20260717_v2.json":
        "f1ab919d888baf3b492cff22a2f516780ac0c4dc9ef72f6618c50be3207e3b5e",
    "formal/docs/release/SR_PILLAR_COORDINATE_CONVENTION_AND_CONSTANT_RESTORATION_PACKET_20260717_v2.json":
        "1d94f4c8cab0337322eb537feebe32aeb344369e5b402164a03987b7b56c1b05",
    "formal/docs/release/SR_PILLAR_COORDINATE_CONVENTION_AND_CONSTANT_RESTORATION_PACKET_REVIEW_20260717_v1.json":
        "2c6ea6800243635b05da4e89847f177987de6b9ccaeb6bbbe8c8e769a2a1a183",
    "formal/docs/release/SR_PILLAR_COORDINATE_CONVENTION_AND_CONSTANT_RESTORATION_PACKET_20260717_v1.json":
        "2185ef29df93a403595bc2540b5a6543ba34a8842fb7e92ab3218bd5efdc2e0a",
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


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


@dataclass(frozen=True)
class Literal:
    value: int


@dataclass(frozen=True)
class Symbol:
    name: str
    domain: str


@dataclass(frozen=True)
class Constant:
    name: str


@dataclass(frozen=True)
class Index:
    name: str
    variance: str


@dataclass(frozen=True)
class Indexed:
    object_id: str
    normalization: str
    indices: tuple[Index, ...]


@dataclass(frozen=True)
class ScalarProduct:
    factors: tuple[Any, ...]


@dataclass(frozen=True)
class OperatorProduct:
    operators: tuple[Any, ...]


@dataclass(frozen=True)
class Apply:
    operator: Any
    operand: Any


@dataclass(frozen=True)
class Sum:
    terms: tuple[Any, ...]


@dataclass(frozen=True)
class Power:
    base: Any
    exponent: int


@dataclass(frozen=True)
class Derivative:
    kind: str
    index: Index
    operand: Any


@dataclass(frozen=True)
class Equality:
    left: Any
    right: Any


Expr = (
    Literal | Symbol | Constant | Indexed | ScalarProduct | OperatorProduct |
    Apply | Sum | Power | Derivative | Equality
)


def _ast_json(value: Expr) -> dict[str, Any]:
    if isinstance(value, Literal):
        return {"node": "literal", "value": value.value}
    if isinstance(value, Symbol):
        return {"node": "symbol", "name": value.name, "domain": value.domain}
    if isinstance(value, Constant):
        return {"node": "constant", "name": value.name}
    if isinstance(value, Index):
        return {"node": "index", "name": value.name, "variance": value.variance}
    if isinstance(value, Indexed):
        return {
            "node": "indexed",
            "object_id": value.object_id,
            "normalization": value.normalization,
            "indices": [_ast_json(index) for index in value.indices],
        }
    if isinstance(value, ScalarProduct):
        return {"node": "scalar_product", "factors": [_ast_json(item) for item in value.factors]}
    if isinstance(value, OperatorProduct):
        return {"node": "operator_product", "operators": [_ast_json(item) for item in value.operators]}
    if isinstance(value, Apply):
        return {
            "node": "apply",
            "operator": _ast_json(value.operator),
            "operand": _ast_json(value.operand),
        }
    if isinstance(value, Sum):
        return {"node": "sum", "terms": [_ast_json(item) for item in value.terms]}
    if isinstance(value, Power):
        return {"node": "power", "base": _ast_json(value.base), "exponent": value.exponent}
    if isinstance(value, Derivative):
        return {
            "node": "derivative",
            "kind": value.kind,
            "index": _ast_json(value.index),
            "operand": _ast_json(value.operand),
        }
    if isinstance(value, Equality):
        return {"node": "equality", "left": _ast_json(value.left), "right": _ast_json(value.right)}
    raise TypeError(f"unsupported AST node: {type(value)!r}")


def canonical(value: Expr) -> str:
    return json.dumps(_ast_json(normalize(value)), sort_keys=True, separators=(",", ":"))


ZERO = Literal(0)
ONE = Literal(1)
NEG_ONE = Constant("-1")
C = Constant("c")
HBAR = Constant("hbar")
MU0 = Constant("mu_0")
SQRT_MU0 = Constant("sqrt_mu_0")
I = Constant("i")
QUARTER = Constant("1/4")


def P(*factors: Expr) -> Expr:
    return normalize(ScalarProduct(tuple(factors)))


def OP(*operators: Expr) -> OperatorProduct:
    value = normalize(OperatorProduct(tuple(operators)))
    assert isinstance(value, OperatorProduct)
    return value


def APP(operator: Expr, operand: Expr) -> Apply:
    value = normalize(Apply(operator, operand))
    assert isinstance(value, Apply)
    return value


def A(*terms: Expr) -> Expr:
    return normalize(Sum(tuple(terms)))


def N(value: Expr) -> Expr:
    return P(NEG_ONE, value)


def Pow(base: Expr, exponent: int) -> Expr:
    return normalize(Power(base, exponent))


def Eq(left: Expr, right: Expr) -> Equality:
    value = normalize(Equality(left, right))
    assert isinstance(value, Equality)
    return value


def _is_atomic(value: Expr) -> bool:
    return isinstance(value, (Symbol, Constant))


def _is_constant_factor(value: Expr) -> bool:
    return isinstance(value, Constant) or (
        isinstance(value, Power) and isinstance(value.base, Constant)
    )


def _power_factor(base: Expr, exponent: int) -> Expr:
    if exponent == 0:
        return ONE
    if exponent == 1:
        return base
    return Power(base, exponent)


def normalize(value: Expr) -> Expr:
    if isinstance(value, (Literal, Symbol, Constant, Index, Indexed)):
        return value
    if isinstance(value, Equality):
        return Equality(normalize(value.left), normalize(value.right))
    if isinstance(value, OperatorProduct):
        operators: list[Expr] = []
        for raw in value.operators:
            operator = normalize(raw)
            if isinstance(operator, OperatorProduct):
                operators.extend(operator.operators)
            else:
                operators.append(operator)
        return OperatorProduct(tuple(operators))
    if isinstance(value, Apply):
        return Apply(normalize(value.operator), normalize(value.operand))
    if isinstance(value, Sum):
        terms: list[Expr] = []
        for raw in value.terms:
            term = normalize(raw)
            if isinstance(term, Sum):
                terms.extend(term.terms)
            elif term != ZERO:
                terms.append(term)
        if not terms:
            return ZERO
        terms.sort(key=lambda item: json.dumps(_ast_json(item), sort_keys=True))
        return terms[0] if len(terms) == 1 else Sum(tuple(terms))
    if isinstance(value, Power):
        base = normalize(value.base)
        exponent = value.exponent
        if exponent == 0:
            return ONE
        if exponent == 1:
            return base
        if isinstance(base, Power):
            return normalize(Power(base.base, base.exponent * exponent))
        if isinstance(base, ScalarProduct):
            return normalize(ScalarProduct(tuple(Power(item, exponent) for item in base.factors)))
        return Power(base, exponent)
    if isinstance(value, Derivative):
        operand = normalize(value.operand)
        if isinstance(operand, ScalarProduct):
            constants = tuple(item for item in operand.factors if _is_constant_factor(item))
            remainder = tuple(item for item in operand.factors if not _is_constant_factor(item))
            if constants and remainder:
                return normalize(
                    ScalarProduct(constants + (Derivative(value.kind, value.index, normalize(ScalarProduct(remainder))),))
                )
        return Derivative(value.kind, value.index, operand)
    if isinstance(value, ScalarProduct):
        factors: list[Expr] = []
        for raw in value.factors:
            factor = normalize(raw)
            if isinstance(factor, Indexed) and factor.object_id in {"gamma", "D"}:
                raise ValueError("OPERATOR_IN_SCALAR_PRODUCT")
            if factor == ZERO:
                return ZERO
            if factor == ONE:
                continue
            if isinstance(factor, ScalarProduct):
                factors.extend(factor.factors)
            else:
                factors.append(factor)
        sum_index = next((i for i, item in enumerate(factors) if isinstance(item, Sum)), None)
        if sum_index is not None:
            selected = factors[sum_index]
            assert isinstance(selected, Sum)
            remainder = factors[:sum_index] + factors[sum_index + 1 :]
            return normalize(Sum(tuple(ScalarProduct(tuple(remainder + [term])) for term in selected.terms)))
        exponents: dict[Expr, int] = {}
        others: list[Expr] = []
        for factor in factors:
            if _is_atomic(factor):
                exponents[factor] = exponents.get(factor, 0) + 1
            elif isinstance(factor, Power) and _is_atomic(factor.base):
                exponents[factor.base] = exponents.get(factor.base, 0) + factor.exponent
            else:
                others.append(factor)
        sqrt_exponent = exponents.get(SQRT_MU0, 0)
        if abs(sqrt_exponent) >= 2:
            pairs = int(sqrt_exponent / 2)
            exponents[SQRT_MU0] = sqrt_exponent - 2 * pairs
            exponents[MU0] = exponents.get(MU0, 0) + pairs
        combined = [
            _power_factor(atom, exponent)
            for atom, exponent in exponents.items()
            if exponent != 0
        ] + others
        combined.sort(key=lambda item: json.dumps(_ast_json(item), sort_keys=True))
        if not combined:
            return ONE
        return combined[0] if len(combined) == 1 else ScalarProduct(tuple(combined))
    raise TypeError(f"unsupported normalization node: {type(value)!r}")


def scale_equality(value: Equality, factor: Expr) -> Equality:
    return Eq(P(factor, value.left), P(factor, value.right))


@dataclass(frozen=True)
class RewriteRule:
    rule_id: str
    source: Expr
    target: Expr
    meaning: str


@dataclass
class EquationContract:
    equation_id: str
    binding_id: str
    source_ast: Equality
    expected_si_ast: Equality
    forward_rules: list[RewriteRule]
    inverse_rules: list[RewriteRule]
    required_forward_rule_ids: set[str]
    required_inverse_rule_ids: set[str]
    forward_scale: Expr = ONE
    inverse_scale: Expr = ONE
    forward_scale_rule_id: str = "NO_FORWARD_SCALE"
    inverse_scale_rule_id: str = "NO_INVERSE_SCALE"
    adapter_id: str = "EXACT_OBJECT_IDENTITY"
    auxiliary: bool = False


@dataclass(frozen=True)
class TransformResult:
    equation_id: str
    direction: str
    computed_ast: Equality
    expected_ast: Equality
    applied_rule_ids: tuple[str, ...]
    provenance_trace: tuple[str, ...]
    binding_id: str
    adapter_id: str
    source_canonical_sha256: str
    computed_canonical_sha256: str
    lineage_id: str
    passed: bool
    first_diagnostic: str
    untrusted_summary_ignored: bool
    _issuance_capability: object | None = field(default=None, repr=False, compare=False)


class ProductionContractError(RuntimeError):
    def __init__(self, diagnostic: str):
        super().__init__(diagnostic)
        self.diagnostic = diagnostic


_ISSUED_FORWARD_RESULTS: dict[int, dict[str, Any]] = {}
_ISSUANCE_COUNTER = 0


def _reset_issuance_registry_for_packet_build() -> None:
    global _ISSUANCE_COUNTER
    _ISSUED_FORWARD_RESULTS.clear()
    _ISSUANCE_COUNTER = 0


def _convention_fingerprint(state: dict[str, Any]) -> str:
    return _sha256(json.dumps(state, sort_keys=True, separators=(",", ":")).encode("utf-8"))


def _register_forward_result(
    result: TransformResult,
    *,
    convention_state: dict[str, Any],
) -> None:
    _ISSUED_FORWARD_RESULTS[id(result)] = {
        "result": result,
        "capability": result._issuance_capability,
        "equation_id": result.equation_id,
        "direction": result.direction,
        "computed_canonical": canonical(result.computed_ast),
        "expected_canonical": canonical(result.expected_ast),
        "applied_rule_ids": result.applied_rule_ids,
        "binding_id": result.binding_id,
        "adapter_id": result.adapter_id,
        "source_canonical_sha256": result.source_canonical_sha256,
        "computed_canonical_sha256": result.computed_canonical_sha256,
        "lineage_id": result.lineage_id,
        "passed": result.passed,
        "first_diagnostic": result.first_diagnostic,
        "convention_fingerprint": _convention_fingerprint(convention_state),
    }


def _validate_issued_forward_result(
    result: TransformResult,
    *,
    convention_state: dict[str, Any],
    binding_id: str,
    adapter_id: str,
) -> None:
    record = _ISSUED_FORWARD_RESULTS.get(id(result))
    if record is None or record["result"] is not result:
        raise ProductionContractError("LINEAGE_PROVENANCE_FAILURE")
    checks = (
        record["capability"] is result._issuance_capability,
        result._issuance_capability is not None,
        record["equation_id"] == result.equation_id,
        record["direction"] == result.direction == "restore",
        record["computed_canonical"] == canonical(result.computed_ast),
        record["expected_canonical"] == canonical(result.expected_ast),
        record["applied_rule_ids"] == result.applied_rule_ids,
        record["binding_id"] == result.binding_id == binding_id,
        record["adapter_id"] == result.adapter_id == adapter_id,
        record["source_canonical_sha256"] == result.source_canonical_sha256,
        record["computed_canonical_sha256"] == result.computed_canonical_sha256,
        record["lineage_id"] == result.lineage_id,
        record["passed"] is result.passed is True,
        record["first_diagnostic"] == result.first_diagnostic == "PASS",
        record["convention_fingerprint"] == _convention_fingerprint(convention_state),
    )
    if not all(checks):
        raise ProductionContractError("LINEAGE_PROVENANCE_FAILURE")


def _rewrite(value: Expr, rules: list[RewriteRule], trace: list[str]) -> Expr:
    normalized = normalize(value)
    for rule in rules:
        if canonical(normalized) == canonical(rule.source):
            trace.append(f"APPLIED:{rule.rule_id}")
            return normalize(rule.target)
    if isinstance(normalized, Equality):
        return Eq(_rewrite(normalized.left, rules, trace), _rewrite(normalized.right, rules, trace))
    if isinstance(normalized, ScalarProduct):
        return P(*(_rewrite(item, rules, trace) for item in normalized.factors))
    if isinstance(normalized, OperatorProduct):
        return OP(*(_rewrite(item, rules, trace) for item in normalized.operators))
    if isinstance(normalized, Apply):
        return APP(
            _rewrite(normalized.operator, rules, trace),
            _rewrite(normalized.operand, rules, trace),
        )
    if isinstance(normalized, Sum):
        return A(*(_rewrite(item, rules, trace) for item in normalized.terms))
    if isinstance(normalized, Power):
        return Pow(_rewrite(normalized.base, rules, trace), normalized.exponent)
    if isinstance(normalized, Derivative):
        return normalize(
            Derivative(normalized.kind, normalized.index, _rewrite(normalized.operand, rules, trace))
        )
    return normalized


UP = "up"
DOWN = "down"


def ix(name: str, variance: str) -> Index:
    return Index(name, variance)


MU_D = ix("mu", DOWN)
MU_U = ix("mu", UP)
NU_D = ix("nu", DOWN)
NU_U = ix("nu", UP)
ALPHA_D = ix("alpha", DOWN)
ALPHA_U = ix("alpha", UP)
BETA_D = ix("beta", DOWN)
BETA_U = ix("beta", UP)


def V(object_id: str, normalization: str, *indices: Index) -> Indexed:
    return Indexed(object_id, normalization, tuple(indices))


def D(kind: str, index: Index, operand: Expr) -> Derivative:
    return Derivative(kind, index, operand)


def _rule(rule_id: str, source: Expr, target: Expr, meaning: str) -> RewriteRule:
    return RewriteRule(rule_id, normalize(source), normalize(target), meaning)


def _build_contracts() -> dict[str, EquationContract]:
    contracts: dict[str, EquationContract] = {}

    tpn = Symbol("t_prime", "natural")
    tn = Symbol("t", "natural")
    xpn = Symbol("x_prime", "natural")
    xn = Symbol("x", "natural")
    tpsi = Symbol("t_prime", "SI")
    tsi = Symbol("t", "SI")
    xpsi = Symbol("x_prime", "SI")
    xsi = Symbol("x", "SI")
    interval_source = Eq(A(Pow(tpn, 2), N(Pow(xpn, 2))), A(Pow(tn, 2), N(Pow(xn, 2))))
    interval_expected = Eq(
        A(P(Pow(C, 2), Pow(tpsi, 2)), N(Pow(xpsi, 2))),
        A(P(Pow(C, 2), Pow(tsi, 2)), N(Pow(xsi, 2))),
    )
    interval_forward = [
        _rule("MAP_T_PRIME_N_TO_C_T_PRIME", tpn, P(C, tpsi), "x'^0=c t'"),
        _rule("MAP_T_N_TO_C_T", tn, P(C, tsi), "x^0=c t"),
        _rule("MAP_X_PRIME_IDENTITY_TO_SI", xpn, xpsi, "spatial coordinate identity"),
        _rule("MAP_X_IDENTITY_TO_SI", xn, xsi, "spatial coordinate identity"),
    ]
    interval_inverse = [
        _rule("SUPPRESS_T_PRIME_SI_TO_T_PRIME_N_OVER_C", tpsi, P(tpn, Pow(C, -1)), "t'=t'_N/c"),
        _rule("SUPPRESS_T_SI_TO_T_N_OVER_C", tsi, P(tn, Pow(C, -1)), "t=t_N/c"),
        _rule("SUPPRESS_X_PRIME_SI_TO_N", xpsi, xpn, "spatial identity"),
        _rule("SUPPRESS_X_SI_TO_N", xsi, xn, "spatial identity"),
    ]
    contracts["SR_INTERVAL_INVARIANCE"] = EquationContract(
        "SR_INTERVAL_INVARIANCE", "SR_INTERVAL_INVARIANCE", interval_source,
        interval_expected, interval_forward, interval_inverse,
        {rule.rule_id for rule in interval_forward}, {rule.rule_id for rule in interval_inverse},
    )

    omega = Symbol("omega", "RL01")
    k = Symbol("k", "RL01")
    mrl = Symbol("m", "RL01")
    crl = Symbol("c", "RL01")
    energy = Symbol("E", "SI")
    momentum = Symbol("p", "SI")
    mass = Symbol("m", "SI")
    mass_source = Eq(Pow(omega, 2), A(P(Pow(crl, 2), Pow(k, 2)), Pow(mrl, 2)))
    mass_expected = Eq(Pow(energy, 2), A(P(Pow(C, 2), Pow(momentum, 2)), P(Pow(mass, 2), Pow(C, 4))))
    mass_forward = [
        _rule("MAP_OMEGA_TO_E_OVER_HBAR", omega, P(energy, Pow(HBAR, -1)), "E=hbar omega"),
        _rule("MAP_K_TO_P_OVER_HBAR", k, P(momentum, Pow(HBAR, -1)), "p=hbar k"),
        _rule("MAP_RL_M_TO_MC2_OVER_HBAR", mrl, P(mass, Pow(C, 2), Pow(HBAR, -1)), "m_RL=m c^2/hbar"),
        _rule("MAP_RL_C_TO_SI_C", crl, C, "restore c"),
    ]
    mass_inverse = [
        _rule("SUPPRESS_E_TO_HBAR_OMEGA", energy, P(HBAR, omega), "E=hbar omega"),
        _rule("SUPPRESS_P_TO_HBAR_K", momentum, P(HBAR, k), "p=hbar k"),
        _rule("SUPPRESS_M_TO_HBAR_MRL_OVER_C2", mass, P(HBAR, mrl, Pow(crl, -2)), "m=hbar m_RL/c^2"),
        _rule("SUPPRESS_SI_C_TO_RL_C", C, crl, "retain RL01 c parameter"),
    ]
    contracts["SR_MASS_SHELL"] = EquationContract(
        "SR_MASS_SHELL", "SR_MASS_SHELL", mass_source, mass_expected,
        mass_forward, mass_inverse, {rule.rule_id for rule in mass_forward},
        {rule.rule_id for rule in mass_inverse}, Pow(HBAR, 2), Pow(HBAR, -2),
        "CLEAR_HBAR_SQUARED_FORWARD", "CLEAR_HBAR_SQUARED_INVERSE",
    )

    jn = V("J", "N", MU_U)
    jsi = V("J", "SI", MU_U)
    current_source = Eq(D("nabla", MU_D, jn), ZERO)
    current_expected = Eq(D("nabla", MU_D, jsi), ZERO)
    current_forward = [_rule("MAP_J_N_TO_SQRT_MU0_J_SI", jn, P(SQRT_MU0, jsi), "J_N=sqrt(mu0)J_SI")]
    current_inverse = [_rule("SUPPRESS_J_SI_TO_J_N_OVER_SQRT_MU0", jsi, P(Pow(SQRT_MU0, -1), jn), "J_SI=J_N/sqrt(mu0)")]
    contracts["CURRENT_CONSERVATION"] = EquationContract(
        "CURRENT_CONSERVATION", "CURRENT_CONSERVATION", current_source,
        current_expected, current_forward, current_inverse,
        {current_forward[0].rule_id}, {current_inverse[0].rule_id},
        Pow(SQRT_MU0, -1), SQRT_MU0,
        "CANCEL_COMMON_SQRT_MU0_FORWARD", "CANCEL_COMMON_SQRT_MU0_INVERSE",
    )

    fn = V("F", "N", MU_U, NU_U)
    fsi = V("F", "SI", MU_U, NU_U)
    jn_nu = V("J", "N", NU_U)
    jsi_nu = V("J", "SI", NU_U)
    maxwell_source = Eq(D("nabla", MU_D, fn), jn_nu)
    maxwell_expected = Eq(D("nabla", MU_D, fsi), P(MU0, jsi_nu))
    maxwell_forward = [
        _rule("MAP_F_N_TO_F_SI_OVER_SQRT_MU0", fn, P(Pow(SQRT_MU0, -1), fsi), "F_N=F_SI/sqrt(mu0)"),
        _rule("MAP_J_N_TO_SQRT_MU0_J_SI", jn_nu, P(SQRT_MU0, jsi_nu), "J_N=sqrt(mu0)J_SI"),
    ]
    maxwell_inverse = [
        _rule("SUPPRESS_F_SI_TO_SQRT_MU0_F_N", fsi, P(SQRT_MU0, fn), "F_SI=sqrt(mu0)F_N"),
        _rule("SUPPRESS_J_SI_TO_J_N_OVER_SQRT_MU0", jsi_nu, P(Pow(SQRT_MU0, -1), jn_nu), "J_SI=J_N/sqrt(mu0)"),
    ]
    contracts["SOURCED_MAXWELL"] = EquationContract(
        "SOURCED_MAXWELL", "SOURCED_MAXWELL", maxwell_source, maxwell_expected,
        maxwell_forward, maxwell_inverse, {rule.rule_id for rule in maxwell_forward},
        {rule.rule_id for rule in maxwell_inverse}, SQRT_MU0, Pow(SQRT_MU0, -1),
        "MULTIPLY_BY_SQRT_MU0_FORWARD", "MULTIPLY_BY_INV_SQRT_MU0_INVERSE",
    )

    tpsi_n = V("T_psi", "N", MU_U, NU_U)
    tpsi_si = V("T_psi", "SI", MU_U, NU_U)
    fn_mixed = V("F", "N", NU_U, ALPHA_D)
    fsi_mixed = V("F", "SI", NU_U, ALPHA_D)
    jn_alpha = V("J", "N", ALPHA_U)
    jsi_alpha = V("J", "SI", ALPHA_U)
    exchange_source = Eq(D("nabla", MU_D, tpsi_n), P(fn_mixed, jn_alpha))
    exchange_expected = Eq(D("nabla", MU_D, tpsi_si), P(fsi_mixed, jsi_alpha))
    exchange_forward = [
        _rule("MAP_T_PSI_N_IDENTITY_TO_SI", tpsi_n, tpsi_si, "preserve exact T_psi identity"),
        _rule("MAP_F_N_TO_F_SI_OVER_SQRT_MU0", fn_mixed, P(Pow(SQRT_MU0, -1), fsi_mixed), "F normalization"),
        _rule("MAP_J_N_TO_SQRT_MU0_J_SI", jn_alpha, P(SQRT_MU0, jsi_alpha), "J normalization"),
    ]
    exchange_inverse = [
        _rule("SUPPRESS_T_PSI_SI_IDENTITY_TO_N", tpsi_si, tpsi_n, "preserve exact T_psi identity"),
        _rule("SUPPRESS_F_SI_TO_SQRT_MU0_F_N", fsi_mixed, P(SQRT_MU0, fn_mixed), "F normalization"),
        _rule("SUPPRESS_J_SI_TO_J_N_OVER_SQRT_MU0", jsi_alpha, P(Pow(SQRT_MU0, -1), jn_alpha), "J normalization"),
    ]
    contracts["MATTER_STRESS_ENERGY_EXCHANGE"] = EquationContract(
        "MATTER_STRESS_ENERGY_EXCHANGE", "MATTER_STRESS_ENERGY_EXCHANGE",
        exchange_source, exchange_expected, exchange_forward, exchange_inverse,
        {rule.rule_id for rule in exchange_forward}, {rule.rule_id for rule in exchange_inverse},
    )

    tan = V("T_A", "N", MU_D, NU_D)
    tasi = V("T_A", "SI", MU_D, NU_D)
    metric = V("g", "shared", MU_D, NU_D)
    fn1 = V("F", "N", MU_D, ALPHA_D)
    fn2 = V("F", "N", NU_D, ALPHA_U)
    fn3 = V("F", "N", ALPHA_D, BETA_D)
    fn4 = V("F", "N", ALPHA_U, BETA_U)
    fs1 = V("F", "SI", MU_D, ALPHA_D)
    fs2 = V("F", "SI", NU_D, ALPHA_U)
    fs3 = V("F", "SI", ALPHA_D, BETA_D)
    fs4 = V("F", "SI", ALPHA_U, BETA_U)
    stress_source = Eq(tan, A(N(P(fn1, fn2)), P(QUARTER, metric, fn3, fn4)))
    stress_expected = Eq(tasi, P(Pow(MU0, -1), A(N(P(fs1, fs2)), P(QUARTER, metric, fs3, fs4))))
    stress_forward = [_rule("MAP_T_A_N_IDENTITY_TO_SI", tan, tasi, "stress object identity")]
    stress_inverse = [_rule("SUPPRESS_T_A_SI_IDENTITY_TO_N", tasi, tan, "stress object identity")]
    for number, (source_f, target_f) in enumerate(((fn1, fs1), (fn2, fs2), (fn3, fs3), (fn4, fs4)), start=1):
        stress_forward.append(_rule(f"MAP_F_N_VARIANT_{number}_TO_SI_OVER_SQRT_MU0", source_f, P(Pow(SQRT_MU0, -1), target_f), "F normalization"))
        stress_inverse.append(_rule(f"SUPPRESS_F_SI_VARIANT_{number}_TO_SQRT_MU0_N", target_f, P(SQRT_MU0, source_f), "F normalization"))
    contracts["GAUGE_STRESS_ENERGY_NORMALIZATION"] = EquationContract(
        "GAUGE_STRESS_ENERGY_NORMALIZATION", "GAUGE_STRESS_ENERGY_NORMALIZATION",
        stress_source, stress_expected, stress_forward, stress_inverse,
        {rule.rule_id for rule in stress_forward}, {rule.rule_id for rule in stress_inverse},
    )

    gamma_n = V("gamma", "natural", MU_U)
    gamma_si = V("gamma", "SI", MU_U)
    dstar = V("D", "natural", MU_D)
    dsi = V("D", "SI", MU_D)
    mstar = Symbol("m", "natural_inverse_length")
    psi_n = Symbol("psi", "natural")
    psi_si = Symbol("psi", "SI")
    q_source = Eq(
        A(P(I, APP(OP(gamma_n, dstar), psi_n)), N(P(mstar, psi_n))),
        ZERO,
    )
    q_expected = Eq(
        A(
            P(I, HBAR, C, APP(OP(gamma_si, dsi), psi_si)),
            N(P(Symbol("m", "SI"), Pow(C, 2), psi_si)),
        ),
        ZERO,
    )
    q_forward = [
        _rule("MAP_GAMMA_N_IDENTITY_TO_SI", gamma_n, gamma_si, "gamma identity"),
        _rule("MAP_D_STAR_TO_D_SI", dstar, dsi, "D_star contains q_star A_star=q_SI A_SI/hbar"),
        _rule("MAP_M_STAR_TO_MC_OVER_HBAR", mstar, P(Symbol("m", "SI"), C, Pow(HBAR, -1)), "m_star=m c/hbar"),
        _rule("MAP_PSI_N_IDENTITY_TO_SI", psi_n, psi_si, "spinor normalization retained"),
    ]
    q_inverse = [
        _rule("SUPPRESS_GAMMA_SI_IDENTITY_TO_N", gamma_si, gamma_n, "gamma identity"),
        _rule("SUPPRESS_D_SI_TO_D_STAR", dsi, dstar, "suppress q A/hbar"),
        _rule("SUPPRESS_M_SI_TO_HBAR_MSTAR_OVER_C", Symbol("m", "SI"), P(HBAR, mstar, Pow(C, -1)), "m=hbar m_star/c"),
        _rule("SUPPRESS_PSI_SI_IDENTITY_TO_N", psi_si, psi_n, "spinor normalization retained"),
    ]
    contracts["QUANTUM_DIRAC_NORMALIZATION_AUX"] = EquationContract(
        "QUANTUM_DIRAC_NORMALIZATION_AUX", "QUANTUM_DIRAC_NORMALIZATION_AUX",
        q_source, q_expected, q_forward, q_inverse,
        {rule.rule_id for rule in q_forward}, {rule.rule_id for rule in q_inverse},
        P(HBAR, C), P(Pow(HBAR, -1), Pow(C, -1)),
        "RESTORE_HBAR_C_DIRAC_SCALE", "SUPPRESS_HBAR_C_DIRAC_SCALE",
        auxiliary=True,
    )
    return contracts


CONTRACTS = _build_contracts()
SIX_EQUATION_IDS = tuple(key for key, value in CONTRACTS.items() if not value.auxiliary)


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

CONVENTION_MUTATIONS = [
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
    for field_name, expected, diagnostic in DIAGNOSTIC_ORDER:
        if state.get(field_name) != expected:
            return diagnostic
    return "PASS"


def _read_v1_binding_rows() -> dict[str, dict[str, Any]]:
    packet = json.loads(
        (
            REPO_ROOT
            / "formal/docs/release/SR_PILLAR_COORDINATE_CONVENTION_AND_CONSTANT_RESTORATION_PACKET_20260717_v1.json"
        ).read_text(encoding="utf-8")
    )
    return {row["equation_id"]: row for row in packet["source_bindings"]["rows"]}


def _json_pointer(payload: Any, pointer: str) -> Any:
    value = payload
    for part in pointer.lstrip("/").split("/"):
        token = part.replace("~1", "/").replace("~0", "~")
        value = value[int(token)] if isinstance(value, list) else value[token]
    return value


def _validate_binding(equation_id: str, supplied_binding_id: str, trace: list[str]) -> None:
    if supplied_binding_id != equation_id:
        raise ProductionContractError("SOURCE_BINDING_ID_MISMATCH")
    if equation_id == "QUANTUM_DIRAC_NORMALIZATION_AUX":
        trace.append("PREFLIGHT:BINDING:QUANTUM_AUXILIARY_CONVENTION")
        return
    rows = _read_v1_binding_rows()
    row = rows[equation_id]
    raw = (REPO_ROOT / row["artifact"]).read_bytes()
    if _sha256(raw) != row["artifact_sha256"]:
        raise ProductionContractError("SOURCE_BINDING_HASH_MISMATCH")
    if row["source_kind"] == "json_pointer":
        observed = _json_pointer(json.loads(raw.decode("utf-8")), row["locator"])
    else:
        text = raw.decode("utf-8")
        observed = row["exact_source_expression"] if row["exact_source_expression"] in text else None
    if observed != row["exact_source_expression"]:
        raise ProductionContractError("SOURCE_BINDING_CONTENT_MISMATCH")
    trace.append(f"PREFLIGHT:BINDING_VALID:{equation_id}")


def _contains_object(value: Expr, object_id: str) -> bool:
    if isinstance(value, Indexed):
        return value.object_id == object_id
    if isinstance(value, Equality):
        return _contains_object(value.left, object_id) or _contains_object(value.right, object_id)
    if isinstance(value, ScalarProduct):
        return any(_contains_object(item, object_id) for item in value.factors)
    if isinstance(value, OperatorProduct):
        return any(_contains_object(item, object_id) for item in value.operators)
    if isinstance(value, Apply):
        return _contains_object(value.operator, object_id) or _contains_object(value.operand, object_id)
    if isinstance(value, Sum):
        return any(_contains_object(item, object_id) for item in value.terms)
    if isinstance(value, Power):
        return _contains_object(value.base, object_id)
    if isinstance(value, Derivative):
        return _contains_object(value.operand, object_id)
    return False


def _contains_constant(value: Expr, name: str) -> bool:
    if isinstance(value, Constant):
        return value.name == name
    if isinstance(value, Equality):
        return _contains_constant(value.left, name) or _contains_constant(value.right, name)
    if isinstance(value, ScalarProduct):
        return any(_contains_constant(item, name) for item in value.factors)
    if isinstance(value, OperatorProduct):
        return any(_contains_constant(item, name) for item in value.operators)
    if isinstance(value, Apply):
        return _contains_constant(value.operator, name) or _contains_constant(value.operand, name)
    if isinstance(value, Sum):
        return any(_contains_constant(item, name) for item in value.terms)
    if isinstance(value, Power):
        return _contains_constant(value.base, name)
    if isinstance(value, Derivative):
        return _contains_constant(value.operand, name)
    return False


OPERATOR_OBJECT_IDS = {"gamma", "D"}


def _validate_semantic_ast(value: Expr) -> None:
    if isinstance(value, ScalarProduct):
        for factor in value.factors:
            if isinstance(factor, Indexed) and factor.object_id in OPERATOR_OBJECT_IDS:
                raise ProductionContractError("OPERATOR_IN_SCALAR_PRODUCT")
            _validate_semantic_ast(factor)
        return
    if isinstance(value, OperatorProduct):
        if not value.operators:
            raise ProductionContractError("EMPTY_OPERATOR_PRODUCT")
        for operator in value.operators:
            if not isinstance(operator, Indexed) or operator.object_id not in OPERATOR_OBJECT_IDS:
                raise ProductionContractError("NONOPERATOR_IN_OPERATOR_PRODUCT")
            _validate_semantic_ast(operator)
        return
    if isinstance(value, Apply):
        if not isinstance(value.operator, (Indexed, OperatorProduct, Derivative)):
            raise ProductionContractError("INVALID_APPLICATION_OPERATOR")
        _validate_semantic_ast(value.operator)
        _validate_semantic_ast(value.operand)
        return
    if isinstance(value, Equality):
        _validate_semantic_ast(value.left)
        _validate_semantic_ast(value.right)
        return
    if isinstance(value, Sum):
        for term in value.terms:
            _validate_semantic_ast(term)
        return
    if isinstance(value, Power):
        _validate_semantic_ast(value.base)
        return
    if isinstance(value, Derivative):
        _validate_semantic_ast(value.operand)


def _operator_id(value: Expr) -> str:
    if isinstance(value, Indexed):
        return value.object_id
    if isinstance(value, Derivative):
        return f"Derivative:{value.kind}:{value.index.name}:{value.index.variance}"
    return type(value).__name__


def _application_chain(value: Expr) -> tuple[tuple[str, ...], int] | None:
    if isinstance(value, Apply):
        if isinstance(value.operator, OperatorProduct):
            head = tuple(_operator_id(item) for item in value.operator.operators)
        else:
            head = (_operator_id(value.operator),)
        nested = _application_chain(value.operand)
        if nested is None:
            return head, 1
        return head + nested[0], nested[1] + 1
    children: tuple[Expr, ...] = ()
    if isinstance(value, Equality):
        children = (value.left, value.right)
    elif isinstance(value, ScalarProduct):
        children = value.factors
    elif isinstance(value, OperatorProduct):
        children = value.operators
    elif isinstance(value, Sum):
        children = value.terms
    elif isinstance(value, Power):
        children = (value.base,)
    elif isinstance(value, Derivative):
        children = (value.operand,)
    for child in children:
        found = _application_chain(child)
        if found is not None:
            return found
    return None


def _quantum_source_mismatch_diagnostic(observed: Expr, expected: Expr) -> str:
    observed_chain = _application_chain(observed)
    expected_chain = _application_chain(expected)
    if observed_chain is not None and expected_chain is not None:
        if (
            observed_chain[0] != expected_chain[0]
            and sorted(observed_chain[0]) == sorted(expected_chain[0])
        ):
            return "OPERATOR_ORDER_MISMATCH"
        if observed_chain[0] == expected_chain[0] and observed_chain[1] != expected_chain[1]:
            return "DERIVATIVE_SCOPE_MISMATCH"
    return "SOURCE_CANONICAL_AST_MISMATCH"


def _validate_rule_set(contract: EquationContract, direction: str, trace: list[str]) -> None:
    rules = contract.forward_rules if direction == "restore" else contract.inverse_rules
    required = (
        contract.required_forward_rule_ids
        if direction == "restore"
        else contract.required_inverse_rule_ids
    )
    present = {rule.rule_id for rule in rules}
    if present != required:
        raise ProductionContractError("REQUIRED_OBJECT_MAP_MISSING")
    trace.append(f"PREFLIGHT:OBJECT_MAP_SET_VALID:{direction}:{len(required)}")


def _preflight(
    contract: EquationContract,
    source_ast: Equality,
    *,
    convention_state: dict[str, Any],
    binding_id: str,
    adapter_id: str,
    direction: str,
) -> list[str]:
    trace = ["PREFLIGHT:START"]
    _validate_binding(contract.equation_id, binding_id, trace)
    diagnostic = first_diagnostic(convention_state)
    if diagnostic != "PASS":
        raise ProductionContractError(diagnostic)
    trace.append("PREFLIGHT:CONVENTION_PASS")
    if adapter_id != contract.adapter_id:
        raise ProductionContractError("ADAPTER_VALIDATION_FAILURE")
    trace.append(f"PREFLIGHT:ADAPTER_VALID:{adapter_id}")
    _validate_semantic_ast(source_ast)
    trace.append("PREFLIGHT:SEMANTIC_AST_TYPES_VALID")
    if (
        contract.equation_id == "MATTER_STRESS_ENERGY_EXCHANGE"
        and _contains_object(source_ast, "T_matter")
        and not _contains_object(source_ast, "T_psi")
    ):
        raise ProductionContractError("SOURCE_OBJECT_IDENTITY_MISMATCH")
    expected_source = contract.source_ast if direction == "restore" else contract.expected_si_ast
    if canonical(source_ast) != canonical(expected_source):
        if contract.equation_id == "QUANTUM_DIRAC_NORMALIZATION_AUX":
            raise ProductionContractError(
                _quantum_source_mismatch_diagnostic(source_ast, expected_source)
            )
        raise ProductionContractError("SOURCE_CANONICAL_AST_MISMATCH")
    trace.append("PREFLIGHT:SOURCE_AST_EXACT")
    _validate_rule_set(contract, direction, trace)
    trace.append("PREFLIGHT:PASS")
    return trace


def restore(
    equation_id: str,
    source_ast: Equality,
    *,
    convention_state: dict[str, Any],
    binding_id: str,
    adapter_id: str = "EXACT_OBJECT_IDENTITY",
    untrusted_summary_pass: bool | None = None,
) -> TransformResult:
    if equation_id not in CONTRACTS:
        raise ProductionContractError("TARGET_NOT_IN_FROZEN_INVENTORY")
    contract = CONTRACTS[equation_id]
    trace = _preflight(
        contract,
        source_ast,
        convention_state=convention_state,
        binding_id=binding_id,
        adapter_id=adapter_id,
        direction="restore",
    )
    applied: list[str] = []
    computed = _rewrite(source_ast, contract.forward_rules, applied)
    assert isinstance(computed, Equality)
    if contract.forward_scale != ONE:
        computed = scale_equality(computed, contract.forward_scale)
        applied.append(f"APPLIED:{contract.forward_scale_rule_id}")
    computed = normalize(computed)
    assert isinstance(computed, Equality)
    applied_ids = tuple(item.split(":", 1)[1] for item in applied)
    unused = contract.required_forward_rule_ids - set(applied_ids)
    if unused:
        raise ProductionContractError("DECLARED_OBJECT_MAP_NOT_APPLIED")
    trace.extend(applied)
    trace.append("TRANSFORM:CANONICALIZED")
    expected = normalize(contract.expected_si_ast)
    assert isinstance(expected, Equality)
    passed = canonical(computed) == canonical(expected)
    diagnostic = "PASS" if passed else "EXPECTED_TARGET_MISMATCH"
    if equation_id == "QUANTUM_DIRAC_NORMALIZATION_AUX" and not passed:
        if not _contains_constant(contract.forward_scale, "hbar"):
            diagnostic = "QUANTUM_HBAR_RESTORATION_MISSING"
    trace.append(f"ORACLE_COMPARE:{diagnostic}")
    if untrusted_summary_pass is not None:
        trace.append("UNTRUSTED_SUMMARY_IGNORED")
    source_hash = _sha256(canonical(source_ast).encode("utf-8"))
    computed_hash = _sha256(canonical(computed).encode("utf-8"))
    capability: object | None = object() if passed else None
    global _ISSUANCE_COUNTER
    if passed:
        _ISSUANCE_COUNTER += 1
        lineage = f"RESTORE_ISSUED_{_ISSUANCE_COUNTER:04d}"
        trace.append(f"LINEAGE:ISSUED:{lineage}")
    else:
        lineage = "NOT_ISSUED_ORACLE_MISMATCH"
    result = TransformResult(
        equation_id, "restore", computed, expected, applied_ids, tuple(trace), binding_id,
        adapter_id, source_hash, computed_hash, lineage, passed, diagnostic,
        untrusted_summary_pass is not None, capability,
    )
    if passed:
        _register_forward_result(result, convention_state=convention_state)
    return result


def suppress(
    forward_result: TransformResult,
    *,
    convention_state: dict[str, Any],
    binding_id: str,
    adapter_id: str = "EXACT_OBJECT_IDENTITY",
) -> TransformResult:
    if not isinstance(forward_result, TransformResult):
        raise ProductionContractError("LINEAGE_PROVENANCE_FAILURE")
    _validate_issued_forward_result(
        forward_result,
        convention_state=convention_state,
        binding_id=binding_id,
        adapter_id=adapter_id,
    )
    contract = CONTRACTS[forward_result.equation_id]
    trace = _preflight(
        contract,
        forward_result.computed_ast,
        convention_state=convention_state,
        binding_id=binding_id,
        adapter_id=adapter_id,
        direction="suppress",
    )
    trace.insert(1, f"LINEAGE:CONSUMED_FORWARD_RESULT:{forward_result.lineage_id}")
    applied: list[str] = []
    computed = _rewrite(forward_result.computed_ast, contract.inverse_rules, applied)
    assert isinstance(computed, Equality)
    if contract.inverse_scale != ONE:
        computed = scale_equality(computed, contract.inverse_scale)
        applied.append(f"APPLIED:{contract.inverse_scale_rule_id}")
    computed = normalize(computed)
    assert isinstance(computed, Equality)
    applied_ids = tuple(item.split(":", 1)[1] for item in applied)
    unused = contract.required_inverse_rule_ids - set(applied_ids)
    if unused:
        raise ProductionContractError("DECLARED_OBJECT_MAP_NOT_APPLIED")
    trace.extend(applied)
    trace.append("TRANSFORM:CANONICALIZED")
    expected = normalize(contract.source_ast)
    assert isinstance(expected, Equality)
    passed = canonical(computed) == canonical(expected)
    diagnostic = "PASS" if passed else "SOURCE_ROUND_TRIP_MISMATCH"
    trace.append(f"SOURCE_COMPARE:{diagnostic}")
    source_hash = _sha256(canonical(forward_result.computed_ast).encode("utf-8"))
    computed_hash = _sha256(canonical(computed).encode("utf-8"))
    lineage = f"SUPPRESSED_FROM:{forward_result.lineage_id}"
    return TransformResult(
        forward_result.equation_id, "suppress", computed, expected, applied_ids,
        tuple(trace), binding_id, adapter_id, source_hash, computed_hash, lineage,
        passed, diagnostic, False, None,
    )


def _valid_round_trips() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for equation_id in SIX_EQUATION_IDS:
        contract = CONTRACTS[equation_id]
        forward = restore(
            equation_id,
            contract.source_ast,
            convention_state=dict(BASE_CONVENTION_STATE),
            binding_id=contract.binding_id,
        )
        inverse = suppress(
            forward,
            convention_state=dict(BASE_CONVENTION_STATE),
            binding_id=contract.binding_id,
        )
        rows.append(
            {
                "equation_id": equation_id,
                "source_ast": _ast_json(contract.source_ast),
                "expected_si_oracle_ast": _ast_json(contract.expected_si_ast),
                "computed_si_ast": _ast_json(forward.computed_ast),
                "computed_suppressed_ast": _ast_json(inverse.computed_ast),
                "forward_rule_trace": list(forward.provenance_trace),
                "inverse_rule_trace": list(inverse.provenance_trace),
                "forward_lineage_id": forward.lineage_id,
                "forward_passed": forward.passed,
                "expected_target_comparison_passed": forward.passed,
                "inverse_computed_from_forward_output": (
                    f"LINEAGE:CONSUMED_FORWARD_RESULT:{forward.lineage_id}"
                    in inverse.provenance_trace
                ),
                "inverse_passed": inverse.passed,
                "semantic_round_trip_passed": forward.passed and inverse.passed,
            }
        )
    return rows


def _production_convention_controls() -> list[dict[str, Any]]:
    contract = CONTRACTS["SR_INTERVAL_INVARIANCE"]
    rows: list[dict[str, Any]] = []
    for mutation_id, field_name, value, expected in CONVENTION_MUTATIONS:
        state = dict(BASE_CONVENTION_STATE)
        state[field_name] = value
        observed = "NO_DIAGNOSTIC"
        emitted_output = False
        try:
            restore(
                contract.equation_id,
                contract.source_ast,
                convention_state=state,
                binding_id=contract.binding_id,
            )
            emitted_output = True
        except ProductionContractError as error:
            observed = error.diagnostic
        rows.append(
            {
                "mutation_id": mutation_id,
                "changed_field": field_name,
                "changed_field_count": 1,
                "expected_first_diagnostic": expected,
                "observed_first_diagnostic": observed,
                "output_emitted_before_failure": emitted_output,
                "passed": observed == expected and not emitted_output,
            }
        )
    return rows


def _mutate_first_operator_application(value: Expr, mode: str) -> Expr:
    changed = False

    def visit(node: Expr) -> Expr:
        nonlocal changed
        if not changed and isinstance(node, Apply) and isinstance(node.operator, OperatorProduct):
            operators = node.operator.operators
            if len(operators) >= 2:
                changed = True
                if mode == "reverse":
                    return Apply(OperatorProduct(tuple(reversed(operators))), node.operand)
                if mode == "nest":
                    nested: Expr = node.operand
                    for operator in reversed(operators[1:]):
                        nested = Apply(operator, nested)
                    return Apply(operators[0], nested)
        if isinstance(node, Equality):
            return Equality(visit(node.left), visit(node.right))
        if isinstance(node, ScalarProduct):
            return ScalarProduct(tuple(visit(item) for item in node.factors))
        if isinstance(node, Sum):
            return Sum(tuple(visit(item) for item in node.terms))
        if isinstance(node, Power):
            return Power(visit(node.base), node.exponent)
        if isinstance(node, Derivative):
            return Derivative(node.kind, node.index, visit(node.operand))
        if isinstance(node, Apply):
            return Apply(visit(node.operator), visit(node.operand))
        if isinstance(node, OperatorProduct):
            return OperatorProduct(tuple(visit(item) for item in node.operators))
        return node

    result = normalize(visit(value))
    if not changed:
        raise ValueError("operator application mutation target not found")
    assert isinstance(result, Equality)
    return result


def _observed_restore_error(
    contract: EquationContract,
    source_ast: Equality,
    *,
    convention_state: dict[str, Any],
    binding_id: str | None = None,
    adapter_id: str = "EXACT_OBJECT_IDENTITY",
) -> str:
    try:
        restore(
            contract.equation_id,
            source_ast,
            convention_state=convention_state,
            binding_id=binding_id or contract.binding_id,
            adapter_id=adapter_id,
        )
    except ProductionContractError as error:
        return error.diagnostic
    return "NO_DIAGNOSTIC"


def _positive_controls() -> list[dict[str, Any]]:
    valid_rows = _valid_round_trips()
    gamma = V("gamma", "SI", MU_U)
    dop = V("D", "SI", MU_D)
    psi = Symbol("psi", "SI")
    return [
        {
            "control_id": "POS_UNCHANGED_SIX_PRODUCTION_PATHS",
            "mutation_count": 0,
            "passed": len(valid_rows) == 6 and all(row["semantic_round_trip_passed"] for row in valid_rows),
        },
        {
            "control_id": "POS_SAFE_SCALAR_CONSTANT_REORDERING",
            "mutation_count": 0,
            "passed": canonical(P(HBAR, C)) == canonical(P(C, HBAR)),
        },
        {
            "control_id": "POS_OPERATOR_ORDER_AND_SCOPE_REMAIN_DISTINCT",
            "mutation_count": 0,
            "passed": (
                canonical(APP(OP(gamma, dop), psi)) != canonical(APP(OP(dop, gamma), psi))
                and canonical(APP(OP(gamma, dop), psi)) != canonical(APP(gamma, APP(dop, psi)))
            ),
        },
    ]


def _production_adversarial_controls() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    maxwell = CONTRACTS["SOURCED_MAXWELL"]
    base_state = dict(BASE_CONVENTION_STATE)

    original_oracle = maxwell.expected_si_ast
    wrong_oracle = Eq(original_oracle.left, N(original_oracle.right))
    maxwell.expected_si_ast = wrong_oracle
    try:
        result = restore(maxwell.equation_id, maxwell.source_ast, convention_state=base_state, binding_id=maxwell.binding_id)
        rows.append({"mutation_id": "ADV_WRONG_SI_ORACLE", "changed_premise_count": 1, "expected_first_diagnostic": "EXPECTED_TARGET_MISMATCH", "observed_first_diagnostic": result.first_diagnostic, "computed_output_unchanged_by_oracle": canonical(result.computed_ast) != canonical(wrong_oracle), "passed": not result.passed and result.first_diagnostic == "EXPECTED_TARGET_MISMATCH"})
    finally:
        maxwell.expected_si_ast = original_oracle

    original_rules = list(maxwell.forward_rules)
    maxwell.forward_rules = original_rules[:-1]
    try:
        observed = _observed_restore_error(maxwell, maxwell.source_ast, convention_state=base_state)
        rows.append({"mutation_id": "ADV_REQUIRED_MAP_REMOVED", "changed_premise_count": 1, "expected_first_diagnostic": "REQUIRED_OBJECT_MAP_MISSING", "observed_first_diagnostic": observed, "passed": observed == "REQUIRED_OBJECT_MAP_MISSING"})
    finally:
        maxwell.forward_rules = original_rules

    original_rule = maxwell.forward_rules[1]
    maxwell.forward_rules[1] = RewriteRule(original_rule.rule_id, original_rule.source, V("J", "SI", NU_U), "intentionally wrong J map")
    try:
        result = restore(maxwell.equation_id, maxwell.source_ast, convention_state=base_state, binding_id=maxwell.binding_id)
        rows.append({"mutation_id": "ADV_OBJECT_MAP_MUTATED", "changed_premise_count": 1, "expected_first_diagnostic": "EXPECTED_TARGET_MISMATCH", "observed_first_diagnostic": result.first_diagnostic, "passed": not result.passed and result.first_diagnostic == "EXPECTED_TARGET_MISMATCH"})
    finally:
        maxwell.forward_rules[1] = original_rule

    extra_rule = RewriteRule("EXTRA_INAPPLICABLE_MAP", Symbol("unused", "probe"), Symbol("unused_target", "probe"), "extra map")
    maxwell.forward_rules = original_rules + [extra_rule]
    try:
        observed = _observed_restore_error(maxwell, maxwell.source_ast, convention_state=base_state)
        rows.append({"mutation_id": "ADV_EXTRA_MAP_ADDED", "changed_premise_count": 1, "expected_first_diagnostic": "REQUIRED_OBJECT_MAP_MISSING", "observed_first_diagnostic": observed, "passed": observed == "REQUIRED_OBJECT_MAP_MISSING"})
    finally:
        maxwell.forward_rules = original_rules

    invalid_state = dict(base_state)
    invalid_state["partial_0"] = "partial_t"
    observed = _observed_restore_error(maxwell, maxwell.source_ast, convention_state=invalid_state)
    rows.append({"mutation_id": "ADV_PUBLIC_ENTRY_WITHOUT_MANUAL_PREFLIGHT", "changed_premise_count": 1, "expected_first_diagnostic": "PARTIAL0_MISSING_C_INVERSE", "observed_first_diagnostic": observed, "passed": observed == "PARTIAL0_MISSING_C_INVERSE"})

    exchange = CONTRACTS["MATTER_STRESS_ENERGY_EXCHANGE"]
    wrong_source = copy.deepcopy(exchange.source_ast)
    assert isinstance(wrong_source.left, Derivative)
    wrong_source = Eq(D("nabla", MU_D, V("T_matter", "N", MU_U, NU_U)), wrong_source.right)
    observed = _observed_restore_error(exchange, wrong_source, convention_state=base_state)
    rows.append({"mutation_id": "ADV_T_PSI_REPLACED_BY_T_MATTER", "changed_premise_count": 1, "expected_first_diagnostic": "SOURCE_OBJECT_IDENTITY_MISMATCH", "observed_first_diagnostic": observed, "passed": observed == "SOURCE_OBJECT_IDENTITY_MISMATCH"})

    observed = _observed_restore_error(exchange, exchange.source_ast, convention_state=base_state, adapter_id="UNDECLARED_T_PSI_TO_MATTER")
    rows.append({"mutation_id": "ADV_INVALID_ADAPTER", "changed_premise_count": 1, "expected_first_diagnostic": "ADAPTER_VALIDATION_FAILURE", "observed_first_diagnostic": observed, "passed": observed == "ADAPTER_VALIDATION_FAILURE"})

    result = restore(maxwell.equation_id, maxwell.source_ast, convention_state=base_state, binding_id=maxwell.binding_id, untrusted_summary_pass=False)
    observed = "PASS_UNTRUSTED_SUMMARY_IGNORED" if result.passed and result.untrusted_summary_ignored else result.first_diagnostic
    rows.append({"mutation_id": "ADV_UNTRUSTED_SUMMARY_ONLY", "changed_premise_count": 1, "expected_first_diagnostic": "PASS_UNTRUSTED_SUMMARY_IGNORED", "observed_first_diagnostic": observed, "untrusted_summary_ignored": result.untrusted_summary_ignored, "passed": observed == "PASS_UNTRUSTED_SUMMARY_IGNORED"})

    observed = "NO_DIAGNOSTIC"
    try:
        suppress(maxwell.expected_si_ast, convention_state=base_state, binding_id=maxwell.binding_id)  # type: ignore[arg-type]
    except ProductionContractError as error:
        observed = error.diagnostic
    rows.append({"mutation_id": "ADV_SUPPRESS_STORED_TARGET_WITHOUT_LINEAGE", "changed_premise_count": 1, "expected_first_diagnostic": "LINEAGE_PROVENANCE_FAILURE", "observed_first_diagnostic": observed, "passed": observed == "LINEAGE_PROVENANCE_FAILURE"})

    quantum = CONTRACTS["QUANTUM_DIRAC_NORMALIZATION_AUX"]
    original_scale = quantum.forward_scale
    quantum.forward_scale = C
    try:
        result = restore(quantum.equation_id, quantum.source_ast, convention_state=base_state, binding_id=quantum.binding_id)
        rows.append({"mutation_id": "ADV_QUANTUM_HBAR_OMITTED", "changed_premise_count": 1, "expected_first_diagnostic": "QUANTUM_HBAR_RESTORATION_MISSING", "observed_first_diagnostic": result.first_diagnostic, "passed": not result.passed and result.first_diagnostic == "QUANTUM_HBAR_RESTORATION_MISSING"})
    finally:
        quantum.forward_scale = original_scale

    wrong_order = _mutate_first_operator_application(quantum.source_ast, "reverse")
    observed = _observed_restore_error(quantum, wrong_order, convention_state=base_state)
    rows.append({"mutation_id": "ADV_QUANTUM_OPERATOR_ORDER_REVERSED", "changed_premise_count": 1, "expected_first_diagnostic": "OPERATOR_ORDER_MISMATCH", "observed_first_diagnostic": observed, "passed": observed == "OPERATOR_ORDER_MISMATCH"})

    wrong_scope = _mutate_first_operator_application(quantum.source_ast, "nest")
    observed = _observed_restore_error(quantum, wrong_scope, convention_state=base_state)
    rows.append({"mutation_id": "ADV_QUANTUM_DERIVATIVE_SCOPE_CHANGED", "changed_premise_count": 1, "expected_first_diagnostic": "DERIVATIVE_SCOPE_MISMATCH", "observed_first_diagnostic": observed, "passed": observed == "DERIVATIVE_SCOPE_MISMATCH"})

    valid_forward = restore(maxwell.equation_id, maxwell.source_ast, convention_state=base_state, binding_id=maxwell.binding_id)
    forged = TransformResult(
        valid_forward.equation_id, valid_forward.direction, valid_forward.computed_ast,
        valid_forward.expected_ast, valid_forward.applied_rule_ids,
        valid_forward.provenance_trace, valid_forward.binding_id, valid_forward.adapter_id,
        valid_forward.source_canonical_sha256, valid_forward.computed_canonical_sha256,
        valid_forward.lineage_id, valid_forward.passed, valid_forward.first_diagnostic,
        valid_forward.untrusted_summary_ignored, valid_forward._issuance_capability,
    )
    observed = "NO_DIAGNOSTIC"
    try:
        suppress(forged, convention_state=base_state, binding_id=maxwell.binding_id)
    except ProductionContractError as error:
        observed = error.diagnostic
    rows.append({"mutation_id": "ADV_MANUAL_TRANSFORM_RESULT_COPY", "changed_premise_count": 1, "expected_first_diagnostic": "LINEAGE_PROVENANCE_FAILURE", "observed_first_diagnostic": observed, "passed": observed == "LINEAGE_PROVENANCE_FAILURE"})

    observed = "NO_DIAGNOSTIC"
    try:
        suppress(valid_forward, convention_state=base_state, binding_id="CURRENT_CONSERVATION")
    except ProductionContractError as error:
        observed = error.diagnostic
    rows.append({"mutation_id": "ADV_VALID_RESULT_WRONG_BINDING", "changed_premise_count": 1, "expected_first_diagnostic": "LINEAGE_PROVENANCE_FAILURE", "observed_first_diagnostic": observed, "passed": observed == "LINEAGE_PROVENANCE_FAILURE"})
    return rows


def _validate_authority_hashes() -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for relative_path, expected_hash in AUTHORITY_AND_SOURCE_HASHES.items():
        observed = _sha256((REPO_ROOT / relative_path).read_bytes())
        if observed != expected_hash:
            raise ValueError(f"authority/source hash mismatch: {relative_path}")
        rows.append({"relative_path": relative_path, "sha256": observed})
    review = json.loads(
        (
            REPO_ROOT
            / "formal/docs/release/SR_PILLAR_COORDINATE_CONVENTION_AND_CONSTANT_RESTORATION_PACKET_REVIEW_20260717_v2.json"
        ).read_text(encoding="utf-8")
    )
    if review.get("verdict") != "BLOCKED_CANONICALIZATION_AND_LINEAGE_CONTRACT_UNSOUND":
        raise ValueError("v2 review verdict mismatch")
    if review.get("selected_next_target") != TARGET:
        raise ValueError("v2 review did not authorize v3")
    return rows


def build_packet() -> dict[str, Any]:
    _reset_issuance_registry_for_packet_build()
    authority_rows = _validate_authority_hashes()
    valid_rows = _valid_round_trips()
    convention_controls = _production_convention_controls()
    adversarial = _production_adversarial_controls()
    positive_controls = _positive_controls()
    if not all(row["semantic_round_trip_passed"] for row in valid_rows):
        raise ValueError("valid production round trip failed")
    if not all(row["passed"] for row in convention_controls):
        raise ValueError("production convention control failed")
    if not all(row["passed"] for row in adversarial):
        raise ValueError("production adversarial control failed")
    if not all(row["passed"] for row in positive_controls):
        raise ValueError("production positive control failed")
    quantum_contract = CONTRACTS["QUANTUM_DIRAC_NORMALIZATION_AUX"]
    quantum_forward = restore(
        quantum_contract.equation_id,
        quantum_contract.source_ast,
        convention_state=dict(BASE_CONVENTION_STATE),
        binding_id=quantum_contract.binding_id,
    )
    quantum_inverse = suppress(
        quantum_forward,
        convention_state=dict(BASE_CONVENTION_STATE),
        binding_id=quantum_contract.binding_id,
    )
    if not (quantum_forward.passed and quantum_inverse.passed):
        raise ValueError("quantum production round trip failed")

    tool_path = Path(__file__).resolve()
    test_path = REPO_ROOT / TEST_RELATIVE_PATH
    if not test_path.exists():
        raise ValueError("v3 test missing")
    gamma_si = V("gamma", "SI", MU_U)
    d_si = V("D", "SI", MU_D)
    psi_si = Symbol("psi", "SI")
    canonicalization_checks = {
        "safe_scalar_constants_commute": canonical(P(HBAR, C)) == canonical(P(C, HBAR)),
        "operator_order_preserved": canonical(APP(OP(gamma_si, d_si), psi_si)) != canonical(APP(OP(d_si, gamma_si), psi_si)),
        "derivative_application_scope_preserved": canonical(APP(OP(gamma_si, d_si), psi_si)) != canonical(APP(gamma_si, APP(d_si, psi_si))),
        "gamma_D_and_D_gamma_ast_nodes_are_ordered": _ast_json(OP(gamma_si, d_si)) != _ast_json(OP(d_si, gamma_si)),
    }
    return {
        "schema_id": "SR_PILLAR_COORDINATE_CONVENTION_AND_CONSTANT_RESTORATION_PACKET_20260717_v3",
        "captured_at_utc": "2026-07-17T00:00:00Z",
        "target": TARGET,
        "verdict": "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "authority": {
            "consumed_v2_review_verdict": "BLOCKED_CANONICALIZATION_AND_LINEAGE_CONTRACT_UNSOUND",
            "frozen_authority_and_sources": authority_rows,
            "generator": {"relative_path": tool_path.relative_to(REPO_ROOT).as_posix(), "sha256": _sha256(tool_path.read_bytes())},
            "test": {"relative_path": TEST_RELATIVE_PATH, "sha256": _sha256(test_path.read_bytes())},
        },
        "retained_physical_convention": {
            "temporal_coordinate": "x^0=c t",
            "metric_signature": "(+,-,-,-)",
            "restoration_target": "SI",
            "v1_independent_em_dual_checks": "7/7 PASSED",
            "v1_independent_quantum_checks": "7/7 PASSED",
            "v1_independent_stress_adapter_checks": "10/10 PASSED",
            "v1_independent_source_content_bindings": "6/6 PASSED",
            "reconsidered_in_v3": False,
        },
        "typed_bounded_ast": {
            "node_types": ["Literal", "Symbol", "Constant", "Index", "Indexed", "ScalarProduct", "OperatorProduct", "Apply", "Sum", "Power", "Derivative", "Equality"],
            "scope": "six frozen source equations plus one auxiliary quantum normalization equation",
            "ScalarProduct": "commutative normalization is whitelisted for declared scalar/classical component multiplication",
            "OperatorProduct": "operator sequence is immutable and never sorted",
            "Apply": "operator and operand are distinct and application nesting preserves scope",
            "Derivative": "kind, index variance, and operand scope are preserved",
            "arbitrary_text_replacement_used": False,
            "general_tensor_algebra_claimed": False,
            "general_equation_parser_built": False,
        },
        "operator_aware_canonicalization": {
            "required_count": len(canonicalization_checks),
            "passed_count": sum(canonicalization_checks.values()),
            "checks": canonicalization_checks,
            "global_product_commutativity_assumed": False,
            "registered_commutation_theorems": [],
        },
        "production_entry_contract": {
            "public_forward": "restore(equation_id, source_ast, convention_state, binding_id, adapter_id)",
            "public_inverse": "suppress(forward_result, convention_state, binding_id, adapter_id)",
            "mandatory_order": ["source binding validation", "convention preflight", "adapter validation", "semantic AST type validation", "exact source AST validation", "required object-map validation", "structural transformation", "operator-aware canonical normalization", "independent expected-target comparison", "opaque forward-result issuance"],
            "inverse_requires_computed_forward_result": True,
            "inverse_requires_same_issued_object_identity": True,
            "issuance_registry_revalidates": ["object identity", "opaque capability identity", "source binding", "convention fingerprint", "adapter", "computed AST", "expected AST", "applied maps", "hashes", "oracle pass"],
            "manual_TransformResult_construction_rejected": True,
            "stored_target_suppression_rejected": True,
            "untrusted_pass_summaries_ignored": True,
            "no_public_raw_transform_entry_point": True,
        },
        "six_source_bindings": {
            "required_count": 6,
            "validated_count": 6,
            "equation_ids": list(SIX_EQUATION_IDS),
            "exact_T_psi_route": True,
            "T_matter_adapter_used": False,
        },
        "computed_production_round_trips": {
            "required_count": 6,
            "forward_computed_count": sum(row["forward_passed"] for row in valid_rows),
            "expected_target_comparison_count": sum(row["expected_target_comparison_passed"] for row in valid_rows),
            "inverse_from_forward_output_count": sum(row["inverse_computed_from_forward_output"] for row in valid_rows),
            "semantic_round_trip_count": sum(row["semantic_round_trip_passed"] for row in valid_rows),
            "rows": valid_rows,
        },
        "quantum_production_round_trip": {
            "source_ast": _ast_json(quantum_contract.source_ast),
            "computed_si_ast": _ast_json(quantum_forward.computed_ast),
            "expected_si_ast": _ast_json(quantum_contract.expected_si_ast),
            "computed_suppressed_ast": _ast_json(quantum_inverse.computed_ast),
            "forward_trace": list(quantum_forward.provenance_trace),
            "inverse_trace": list(quantum_inverse.provenance_trace),
            "hbar_c_scale_applied": "APPLIED:RESTORE_HBAR_C_DIRAC_SCALE" in quantum_forward.provenance_trace,
            "forward_passed": quantum_forward.passed,
            "inverse_passed": quantum_inverse.passed,
            "passed": quantum_forward.passed and quantum_inverse.passed,
        },
        "production_convention_negative_controls": {
            "required_count": 8,
            "exact_first_diagnostic_count": sum(row["passed"] for row in convention_controls),
            "all_failed_before_output": all(not row["output_emitted_before_failure"] for row in convention_controls),
            "rows": convention_controls,
        },
        "production_positive_controls": {
            "required_count": len(positive_controls),
            "passed_count": sum(row["passed"] for row in positive_controls),
            "rows": positive_controls,
        },
        "production_contract_adversarial_controls": {
            "classification": "ATOMIC_SINGLE_PREMISE_NEGATIVE_CONTROLS_ONLY",
            "required_count": len(adversarial),
            "passed_count": sum(row["passed"] for row in adversarial),
            "all_single_mutation": all(row["changed_premise_count"] == 1 for row in adversarial),
            "rows": adversarial,
        },
        "scope": {
            "v3_packet_preparation_only": True,
            "authoritative_equation_restoration_executed": False,
            "scientific_equation_migration_executed": False,
            "authoritative_sources_modified": False,
            "historical_artifacts_modified": False,
            "repository_wide_rewrite_authorized": False,
            "multiple_signatures_or_coordinate_conventions_supported": False,
            "additional_electromagnetic_unit_systems_supported": False,
            "r13_reopened": False,
            "external_comparator_activated": False,
            "automation_created": False,
        },
        "independent_review_requirements": [
            "repeat the exact gamma^mu D_mu versus D_mu gamma^mu mutation that blocked v2 and require inequality and OPERATOR_ORDER_MISMATCH",
            "mutate gamma^mu D_mu psi into nested gamma^mu(D_mu psi) and require derivative/application-scope distinction",
            "verify scalar hbar c and c hbar canonicalize equally only through ScalarProduct",
            "repeat the wrong-but-dimensionally-valid SI Maxwell oracle mutation and require EXPECTED_TARGET_MISMATCH",
            "remove and mutate object maps and verify production failure or oracle mismatch",
            "verify every applied rule appears in forward and inverse provenance",
            "manually construct a TransformResult with every visible field and copied capability and require LINEAGE_PROVENANCE_FAILURE",
            "verify suppression accepts only the exact restore-issued object under the original binding, adapter, and convention fingerprint",
            "verify all eight convention mutations fail through the public restore entry point before output",
            "verify exact T_psi identity is preserved and undeclared T_matter substitution fails",
            "verify the auxiliary quantum transform derives and suppresses the hbar c factors",
            "verify positive controls are separate and every adversarial row changes exactly one premise",
            "verify all six sources and authority artifacts remain byte-identical",
        ],
        "hard_stop": {
            "packet_version": 3,
            "independent_packet_review_required": True,
            "bounded_restoration_application_authorized_now": False,
            "migration_authorized_now": False,
            "successor_if_accepted": "prepare_bounded_sr_convention_restoration_application_to_six_selected_authoritative_surfaces",
            "successor_if_blocked": "CLOSE_LANE_AS_BLOCKED_SR_RESTORATION_TOOLING_CONTRACT",
            "automatic_v4_authorized": False,
            "v4_requires_fresh_full_project_priority_decision": True,
            "final_automatically_authorized_implementation_attempt": True,
        },
        "claim_ceiling": (
            "Bounded v3 final automatically authorized production-contract packet preparation only. The typed transforms "
            "operate on packet-local copies of six exact source ASTs and do not edit or "
            "restore authoritative project equations. No migration, SR recovery, pillar "
            "completion, seam closure, empirical validation, prediction, new physics, "
            "master-action promotion, R13 change, or comparator adoption follows."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_packet(), indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    report_path = REPO_ROOT / REPORT_RELATIVE_PATH
    raw = artifact_bytes()
    if args.check:
        if not report_path.exists() or report_path.read_bytes() != raw:
            raise SystemExit("SR convention/restoration v3 packet is stale or missing")
        packet = json.loads(raw)
        print(json.dumps({
            "atomic_negative_controls": f"{packet['production_contract_adversarial_controls']['passed_count']}/{packet['production_contract_adversarial_controls']['required_count']}",
            "convention_controls": f"{packet['production_convention_negative_controls']['exact_first_diagnostic_count']}/{packet['production_convention_negative_controls']['required_count']}",
            "operator_semantics": f"{packet['operator_aware_canonicalization']['passed_count']}/{packet['operator_aware_canonicalization']['required_count']}",
            "positive_controls": f"{packet['production_positive_controls']['passed_count']}/{packet['production_positive_controls']['required_count']}",
            "round_trips": f"{packet['computed_production_round_trips']['semantic_round_trip_count']}/{packet['computed_production_round_trips']['required_count']}",
            "status": "CHECKED",
            "verdict": packet["verdict"],
        }, sort_keys=True))
        return 0
    report_path.write_bytes(raw)
    print(report_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

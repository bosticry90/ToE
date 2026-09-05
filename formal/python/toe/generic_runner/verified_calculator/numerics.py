"""Certificate-oriented interval, ODE/RGE, covariance, and QMC controls."""
from __future__ import annotations

from dataclasses import dataclass
from decimal import Decimal, Context, ROUND_CEILING, ROUND_FLOOR, localcontext
from fractions import Fraction
import hashlib
import math
from statistics import fmean
from typing import Any, Iterable, Mapping, Sequence

import numpy as np
from scipy.integrate import solve_ivp
import sympy as sp

from .canonical import digest
from .contracts import ResourceLimitsV1, UncertaintySemantics
from .errors import CalculatorError, require


def _decimal_text(value: Decimal) -> str:
    require(value.is_finite(), "NONFINITE_NUMERICAL_RESULT")
    normalized = value.normalize()
    text = format(normalized, "f") if normalized.adjusted() > -20 and normalized.adjusted() < 20 else format(normalized, "E")
    return "0" if normalized == 0 else text


@dataclass(frozen=True)
class RationalIntervalV1:
    lower: Fraction
    upper: Fraction

    def __post_init__(self) -> None:
        require(self.lower <= self.upper, "INTERVAL_ORDER")

    @classmethod
    def decode(cls, value: Mapping[str, Any]) -> "RationalIntervalV1":
        require(set(value) == {"kind", "lower", "upper"} and value["kind"] == "RATIONAL_INTERVAL", "INTERVAL_SCHEMA")
        return cls(Fraction(value["lower"]), Fraction(value["upper"]))

    def to_dict(self) -> dict[str, str]:
        return {"kind": "RATIONAL_INTERVAL", "lower": str(self.lower), "upper": str(self.upper)}

    def add(self, other: "RationalIntervalV1") -> "RationalIntervalV1":
        return RationalIntervalV1(self.lower + other.lower, self.upper + other.upper)

    def subtract(self, other: "RationalIntervalV1") -> "RationalIntervalV1":
        return RationalIntervalV1(self.lower - other.upper, self.upper - other.lower)

    def multiply(self, other: "RationalIntervalV1") -> "RationalIntervalV1":
        values = [a * b for a in (self.lower, self.upper) for b in (other.lower, other.upper)]
        return RationalIntervalV1(min(values), max(values))

    def divide(self, other: "RationalIntervalV1") -> "RationalIntervalV1":
        require(not (other.lower <= 0 <= other.upper), "INTERVAL_ZERO_DIVISOR")
        return self.multiply(RationalIntervalV1(1 / other.upper, 1 / other.lower))

    def power(self, exponent: int) -> "RationalIntervalV1":
        require(type(exponent) is int and abs(exponent) <= 32, "INTERVAL_POWER")
        if exponent < 0:
            require(not (self.lower <= 0 <= self.upper), "INTERVAL_ZERO_DIVISOR")
            return RationalIntervalV1(1 / self.upper, 1 / self.lower).power(-exponent)
        if exponent == 0:
            return RationalIntervalV1(Fraction(1), Fraction(1))
        values = [self.lower ** exponent, self.upper ** exponent]
        if exponent % 2 == 0 and self.lower <= 0 <= self.upper:
            values.append(Fraction(0))
        return RationalIntervalV1(min(values), max(values))

    def contains(self, other: "RationalIntervalV1") -> bool:
        return self.lower <= other.lower and other.upper <= self.upper


@dataclass(frozen=True)
class DecimalIntervalV1:
    lower: Decimal
    upper: Decimal
    precision_digits: int

    def __post_init__(self) -> None:
        require(self.lower.is_finite() and self.upper.is_finite() and self.lower <= self.upper, "DECIMAL_INTERVAL")
        require(type(self.precision_digits) is int and 2 <= self.precision_digits <= 771, "DECIMAL_PRECISION")

    @classmethod
    def decode(cls, value: Mapping[str, Any]) -> "DecimalIntervalV1":
        require(set(value) == {"kind", "lower", "upper", "precision_digits"} and value["kind"] == "DECIMAL_INTERVAL", "DECIMAL_INTERVAL_SCHEMA")
        return cls(Decimal(value["lower"]), Decimal(value["upper"]), value["precision_digits"])

    def to_dict(self) -> dict[str, Any]:
        return {"kind": "DECIMAL_INTERVAL", "lower": _decimal_text(self.lower), "upper": _decimal_text(self.upper), "precision_digits": self.precision_digits}

    @staticmethod
    def _round_at(expression, rounding: str, precision: int) -> Decimal:
        with localcontext(Context(prec=precision, rounding=rounding)):
            return +expression()

    def add(self, other: "DecimalIntervalV1") -> "DecimalIntervalV1":
        precision = min(self.precision_digits, other.precision_digits)
        lower = self._round_at(lambda: self.lower + other.lower, ROUND_FLOOR, precision)
        upper = self._round_at(lambda: self.upper + other.upper, ROUND_CEILING, precision)
        return DecimalIntervalV1(lower, upper, precision)

    def subtract(self, other: "DecimalIntervalV1") -> "DecimalIntervalV1":
        precision = min(self.precision_digits, other.precision_digits)
        lower = self._round_at(lambda: self.lower - other.upper, ROUND_FLOOR, precision)
        upper = self._round_at(lambda: self.upper - other.lower, ROUND_CEILING, precision)
        return DecimalIntervalV1(lower, upper, precision)

    def multiply(self, other: "DecimalIntervalV1") -> "DecimalIntervalV1":
        precision = min(self.precision_digits, other.precision_digits)
        lows = [self._round_at(lambda a=a, b=b: a * b, ROUND_FLOOR, precision) for a in (self.lower, self.upper) for b in (other.lower, other.upper)]
        highs = [self._round_at(lambda a=a, b=b: a * b, ROUND_CEILING, precision) for a in (self.lower, self.upper) for b in (other.lower, other.upper)]
        return DecimalIntervalV1(min(lows), max(highs), precision)

    def divide(self, other: "DecimalIntervalV1") -> "DecimalIntervalV1":
        require(not (other.lower <= 0 <= other.upper), "INTERVAL_ZERO_DIVISOR")
        precision = min(self.precision_digits, other.precision_digits)
        lows = [self._round_at(lambda a=a, b=b: a / b, ROUND_FLOOR, precision) for a in (self.lower, self.upper) for b in (other.lower, other.upper)]
        highs = [self._round_at(lambda a=a, b=b: a / b, ROUND_CEILING, precision) for a in (self.lower, self.upper) for b in (other.lower, other.upper)]
        return DecimalIntervalV1(min(lows), max(highs), precision)

    def power(self, exponent: int) -> "DecimalIntervalV1":
        require(type(exponent) is int and abs(exponent) <= 32, "INTERVAL_POWER")
        if exponent < 0:
            require(not (self.lower <= 0 <= self.upper), "INTERVAL_ZERO_DIVISOR")
            positive = self.power(-exponent)
            lower = self._round_at(lambda: Decimal(1) / positive.upper, ROUND_FLOOR, self.precision_digits)
            upper = self._round_at(lambda: Decimal(1) / positive.lower, ROUND_CEILING, self.precision_digits)
            return DecimalIntervalV1(lower, upper, self.precision_digits)
        if exponent == 0:
            return DecimalIntervalV1(Decimal(1), Decimal(1), self.precision_digits)
        lows = [self._round_at(lambda endpoint=endpoint: endpoint ** exponent, ROUND_FLOOR, self.precision_digits) for endpoint in (self.lower, self.upper)]
        highs = [self._round_at(lambda endpoint=endpoint: endpoint ** exponent, ROUND_CEILING, self.precision_digits) for endpoint in (self.lower, self.upper)]
        if exponent % 2 == 0 and self.lower <= 0 <= self.upper:
            lows.append(Decimal(0)); highs.append(Decimal(0))
        return DecimalIntervalV1(min(lows), max(highs), self.precision_digits)

    def contains(self, other: "DecimalIntervalV1") -> bool:
        return self.lower <= other.lower and other.upper <= self.upper


def evaluate_interval_certificate(certificate: Mapping[str, Any], limits: ResourceLimitsV1 | None = None) -> dict[str, Any]:
    """Small independent checker for a finite interval-operation certificate."""
    limits = limits or ResourceLimitsV1()
    require(set(certificate) == {"schema_id", "arithmetic", "inputs", "steps", "output"} and certificate["schema_id"] == "IntervalCertificateV1", "INTERVAL_CERTIFICATE_SCHEMA")
    arithmetic = certificate["arithmetic"]
    require(arithmetic in {"EXACT_RATIONAL", "DECIMAL_DIRECTED"}, "INTERVAL_ARITHMETIC")
    decoder = RationalIntervalV1.decode if arithmetic == "EXACT_RATIONAL" else DecimalIntervalV1.decode
    require(isinstance(certificate["inputs"], Mapping) and len(certificate["inputs"]) <= limits.container_members, "INTERVAL_INPUTS")
    require(isinstance(certificate["steps"], list) and len(certificate["steps"]) <= limits.dag_nodes, "INTERVAL_STEP_LIMIT")
    values = {key: decoder(value) for key, value in certificate["inputs"].items()}
    require(len(values) == len(certificate["inputs"]), "INTERVAL_INPUTS")
    for row in certificate["steps"]:
        require(set(row) in ({"id", "operation", "parents"}, {"id", "operation", "parents", "parameters"}), "INTERVAL_STEP_SCHEMA")
        require(row["id"] not in values, "INTERVAL_DUPLICATE_ID", row["id"])
        parents = [values[key] for key in row["parents"]]
        operation = row["operation"]
        if operation == "POW_INT":
            require(len(parents) == 1 and set(row) == {"id", "operation", "parents", "parameters"} and set(row["parameters"]) == {"exponent"}, "INTERVAL_OPERATION", row["id"])
            values[row["id"]] = parents[0].power(row["parameters"]["exponent"])
        else:
            require(operation in {"ADD", "SUB", "MUL", "DIV"} and len(parents) == 2 and set(row) == {"id", "operation", "parents"}, "INTERVAL_OPERATION", row["id"])
            values[row["id"]] = {"ADD": parents[0].add, "SUB": parents[0].subtract, "MUL": parents[0].multiply, "DIV": parents[0].divide}[operation](parents[1])
    output = certificate["output"]
    require(set(output) == {"value_id", "claimed_enclosure"} and output["value_id"] in values, "INTERVAL_OUTPUT")
    claimed = decoder(output["claimed_enclosure"])
    actual = values[output["value_id"]]
    require(claimed.contains(actual), "INTERVAL_CERTIFICATE_MISMATCH")
    return {"status": "VERIFIED_ENCLOSURE", "certificate_hash": digest(certificate, "IntervalCertificateV1"), "enclosure": claimed.to_dict(), "computed_inner_enclosure": actual.to_dict(), "guarantee": "Contains the exact result of the certified finite interval expression under the stated arithmetic."}


ALLOWED_NUMERICAL_OPS = {"CONST", "VAR", "TIME", "STATE", "ADD", "SUB", "MUL", "DIV", "NEG", "POW_INT", "EXP", "LOG", "SIN", "COS", "SQRT"}


class DeclarativeExpressionV1:
    def __init__(self, tree: Mapping[str, Any], *, variables: Sequence[str] = (), state_size: int = 0, limits: ResourceLimitsV1 | None = None) -> None:
        self.tree = dict(tree)
        self.variables = tuple(variables)
        self.state_size = state_size
        self.limits = limits or ResourceLimitsV1()
        count = 0

        def validate(node: Any) -> None:
            nonlocal count
            count += 1
            require(count <= self.limits.expression_nodes, "EXPRESSION_NODE_LIMIT")
            require(isinstance(node, Mapping) and isinstance(node.get("op"), str) and node["op"] in ALLOWED_NUMERICAL_OPS, "NUMERICAL_EXPRESSION")
            op = node["op"]
            if op == "CONST":
                require(set(node) == {"op", "value"} and isinstance(node["value"], str), "NUMERICAL_CONST")
                value = Decimal(node["value"]); require(value.is_finite(), "NUMERICAL_CONST")
            elif op == "VAR":
                require(set(node) == {"op", "name"} and node["name"] in self.variables, "NUMERICAL_VARIABLE")
            elif op == "TIME":
                require(set(node) == {"op"}, "NUMERICAL_TIME")
            elif op == "STATE":
                require(set(node) == {"op", "index"} and type(node["index"]) is int and 0 <= node["index"] < self.state_size, "NUMERICAL_STATE")
            elif op in {"NEG", "EXP", "LOG", "SIN", "COS", "SQRT"}:
                require(set(node) == {"op", "argument"}, "NUMERICAL_UNARY")
                validate(node["argument"])
            elif op == "POW_INT":
                require(set(node) == {"op", "base", "exponent"} and type(node["exponent"]) is int and abs(node["exponent"]) <= 32, "NUMERICAL_POWER")
                validate(node["base"])
            else:
                require(set(node) == {"op", "left", "right"}, "NUMERICAL_BINARY")
                validate(node["left"]); validate(node["right"])

        validate(self.tree)

    def evaluate(self, *, variables: Mapping[str, float] | None = None, time: float = 0.0, state: Sequence[float] = ()) -> float:
        variables = variables or {}

        def visit(node: Mapping[str, Any]) -> float:
            op = node["op"]
            if op == "CONST": return float(Decimal(node["value"]))
            if op == "VAR": return float(variables[node["name"]])
            if op == "TIME": return float(time)
            if op == "STATE": return float(state[node["index"]])
            if op == "NEG": return -visit(node["argument"])
            if op == "POW_INT": return visit(node["base"]) ** node["exponent"]
            if op in {"EXP", "LOG", "SIN", "COS", "SQRT"}:
                return {"EXP": math.exp, "LOG": math.log, "SIN": math.sin, "COS": math.cos, "SQRT": math.sqrt}[op](visit(node["argument"]))
            left, right = visit(node["left"]), visit(node["right"])
            if op == "ADD": return left + right
            if op == "SUB": return left - right
            if op == "MUL": return left * right
            if op == "DIV":
                require(right != 0.0, "NUMERICAL_ZERO_DIVISOR")
                return left / right
            raise CalculatorError("NUMERICAL_EXPRESSION")

        result = visit(self.tree)
        require(math.isfinite(result), "NONFINITE_NUMERICAL_RESULT")
        return result

    def to_sympy(self) -> sp.Expr:
        symbols = {name: sp.Symbol(name) for name in self.variables}
        time_symbol = sp.Symbol("_time")
        states = [sp.Symbol(f"_state_{index}") for index in range(self.state_size)]

        def visit(node: Mapping[str, Any]) -> sp.Expr:
            op = node["op"]
            if op == "CONST": return sp.Rational(node["value"])
            if op == "VAR": return symbols[node["name"]]
            if op == "TIME": return time_symbol
            if op == "STATE": return states[node["index"]]
            if op == "NEG": return -visit(node["argument"])
            if op == "POW_INT": return visit(node["base"]) ** node["exponent"]
            if op in {"EXP", "LOG", "SIN", "COS", "SQRT"}:
                return {"EXP": sp.exp, "LOG": sp.log, "SIN": sp.sin, "COS": sp.cos, "SQRT": sp.sqrt}[op](visit(node["argument"]))
            left, right = visit(node["left"]), visit(node["right"])
            return {"ADD": left + right, "SUB": left - right, "MUL": left * right, "DIV": left / right}[op]

        return visit(self.tree)


def solve_declarative_ode(specification: Mapping[str, Any], limits: ResourceLimitsV1 | None = None) -> dict[str, Any]:
    limits = limits or ResourceLimitsV1()
    required = {"schema_id", "system_kind", "rhs", "initial_time", "final_time", "initial_state", "parameters", "rtol", "atol", "method"}
    require(set(specification) == required and specification["schema_id"] == "DeclarativeOdeSpecV1", "ODE_SPEC_SCHEMA")
    require(specification["system_kind"] in {"ODE", "RGE"}, "ODE_SYSTEM_KIND")
    initial = [float(Decimal(item)) for item in specification["initial_state"]]
    require(initial and len(initial) <= 256 and all(math.isfinite(item) for item in initial), "ODE_INITIAL_STATE")
    parameters = {key: float(Decimal(value)) for key, value in specification["parameters"].items()}
    expressions = [DeclarativeExpressionV1(tree, variables=tuple(parameters), state_size=len(initial), limits=limits) for tree in specification["rhs"]]
    require(len(expressions) == len(initial), "ODE_RHS_ARITY")
    t0, t1 = float(Decimal(specification["initial_time"])), float(Decimal(specification["final_time"]))
    rtol, atol = float(Decimal(specification["rtol"])), float(Decimal(specification["atol"]))
    require(math.isfinite(t0) and math.isfinite(t1) and t1 > t0 and 0 < rtol <= 1e-3 and 0 < atol <= 1e-3, "ODE_NUMERICAL_POLICY")
    require(specification["method"] in {"DOP853", "RK45", "Radau"}, "ODE_METHOD")

    def rhs(time: float, state: np.ndarray) -> np.ndarray:
        return np.asarray([expression.evaluate(variables=parameters, time=time, state=state) for expression in expressions], dtype=float)

    solution = solve_ivp(rhs, (t0, t1), initial, method=specification["method"], rtol=rtol, atol=atol, dense_output=False)
    require(solution.success and solution.t[-1] == t1 and np.all(np.isfinite(solution.y[:, -1])), "ODE_SOLVER_FAILURE", detail=solution.message)
    return {
        "schema_id": "NumericalRunReceiptV1", "system_kind": specification["system_kind"], "solver": f"scipy.solve_ivp:{specification['method']}",
        "specification_hash": digest(specification, "DeclarativeOdeSpecV1"), "final_time_hex": float(solution.t[-1]).hex(),
        "final_state_hex": [float(value).hex() for value in solution.y[:, -1]], "function_evaluations": int(solution.nfev),
        "assurance": "SINGLE_ROUTE_NUMERICAL_RESULT", "arbitrary_callback_executed": False,
    }


def covariance_propagation(specification: Mapping[str, Any], limits: ResourceLimitsV1 | None = None) -> dict[str, Any]:
    limits = limits or ResourceLimitsV1()
    require(set(specification) == {"schema_id", "variables", "mean", "covariance", "outputs"} and specification["schema_id"] == "CovariancePropagationSpecV1", "COVARIANCE_SPEC_SCHEMA")
    variables = tuple(specification["variables"])
    require(variables and len(set(variables)) == len(variables) <= limits.symbols, "COVARIANCE_VARIABLES")
    mean = np.asarray([float(Decimal(specification["mean"][name])) for name in variables], dtype=float)
    covariance = np.asarray([[float(Decimal(value)) for value in row] for row in specification["covariance"]], dtype=float)
    require(covariance.shape == (len(variables), len(variables)) and np.allclose(covariance, covariance.T, rtol=0, atol=1e-15), "COVARIANCE_MATRIX")
    require(np.linalg.eigvalsh(covariance).min() >= -1e-14, "COVARIANCE_NOT_POSITIVE_SEMIDEFINITE")
    expressions = [DeclarativeExpressionV1(tree, variables=variables, limits=limits) for tree in specification["outputs"]]
    symbols = sp.symbols(variables)
    if not isinstance(symbols, tuple): symbols = (symbols,)
    substitutions = dict(zip(symbols, mean))
    sympy_outputs = [expression.to_sympy() for expression in expressions]
    jacobian = np.asarray([[float(sp.N(sp.diff(expr, symbol).subs(substitutions), 17)) for symbol in symbols] for expr in sympy_outputs], dtype=float)
    output_covariance = jacobian @ covariance @ jacobian.T
    outputs = [expression.evaluate(variables=dict(zip(variables, mean))) for expression in expressions]
    require(np.all(np.isfinite(jacobian)) and np.all(np.isfinite(output_covariance)), "NONFINITE_NUMERICAL_RESULT")
    return {
        "schema_id": "UncertaintyReceiptV1", "semantics": UncertaintySemantics.LOCAL_LINEAR_COVARIANCE.value,
        "specification_hash": digest(specification, "CovariancePropagationSpecV1"), "output_mean_hex": [float(value).hex() for value in outputs],
        "jacobian_hex": [[float(value).hex() for value in row] for row in jacobian],
        "output_covariance_hex": [[float(value).hex() for value in row] for row in output_covariance],
        "limitations": ["Local first-order linearization", "Depends on the stated covariance model", "Not a guaranteed range"],
    }


SOBOL_BITS = 32
SOBOL_DIRECTION_TABLE_ID = "VPC_SOBOL_2D_BRATLEY_FOX_BASE_V1"


def _sobol_directions(dimension: int) -> tuple[int, ...]:
    require(dimension in (0, 1), "SOBOL_DIMENSION_LIMIT")
    directions = [1 << (SOBOL_BITS - index) for index in range(1, SOBOL_BITS + 1)]
    if dimension == 1:
        for index in range(1, SOBOL_BITS):
            directions[index] = directions[index - 1] ^ (directions[index - 1] >> 1)
    return tuple(directions)


def sobol_uint32(sample_count: int, dimension: int, seed: int, scrambling: str = "DIGITAL_XOR_SHA256_V1") -> tuple[tuple[int, ...], ...]:
    require(type(sample_count) is int and 1 <= sample_count <= 1_048_576, "SOBOL_SAMPLE_COUNT")
    require(type(dimension) is int and 1 <= dimension <= 2, "SOBOL_DIMENSION_LIMIT")
    require(type(seed) is int and 0 <= seed < 2 ** 64, "SOBOL_SEED")
    require(scrambling in {"NONE", "DIGITAL_XOR_SHA256_V1"}, "SOBOL_SCRAMBLING")
    directions = [_sobol_directions(axis) for axis in range(dimension)]
    shifts = []
    for axis in range(dimension):
        if scrambling == "NONE":
            shifts.append(0)
        else:
            material = f"VPC_SOBOL_SHIFT_V1\0{seed}\0{axis}".encode("ascii")
            shifts.append(int.from_bytes(hashlib.sha256(material).digest()[:4], "big"))
    points = []
    for index in range(sample_count):
        gray = index ^ (index >> 1)
        row = []
        for axis in range(dimension):
            value, bits = 0, gray
            bit = 0
            while bits:
                if bits & 1: value ^= directions[axis][bit]
                bits >>= 1; bit += 1
            row.append(value ^ shifts[axis])
        points.append(tuple(row))
    return tuple(points)


def _uint32_points_hash(points: Sequence[Sequence[int]]) -> str:
    hasher = hashlib.sha256(b"VPC_SOBOL_UINT32_INPUT_SET_v1\0")
    for row in points:
        for value in row:
            hasher.update(int(value).to_bytes(4, "big"))
    return hasher.hexdigest()


def qmc_ensemble(specification: Mapping[str, Any], limits: ResourceLimitsV1 | None = None) -> dict[str, Any]:
    limits = limits or ResourceLimitsV1()
    required = {"schema_id", "variables", "bounds", "integrand", "generator_family", "specification_version", "direction_table", "scrambling", "ordering", "sample_count_convention", "sample_count", "seed"}
    require(set(specification) == required and specification["schema_id"] == "QMCEnsembleSpecV1", "QMC_SPEC_SCHEMA")
    require(specification["generator_family"] == "SOBOL" and specification["specification_version"] == "VPC_SOBOL_UINT32_V1", "QMC_GENERATOR_IDENTITY")
    require(specification["direction_table"] == SOBOL_DIRECTION_TABLE_ID and specification["ordering"] == "GRAY_CODE_INDEX_ORDER" and specification["sample_count_convention"] == "FIRST_N_FROM_INDEX_ZERO", "QMC_GENERATOR_IDENTITY")
    variables = tuple(specification["variables"])
    require(1 <= len(variables) <= 2 and len(set(variables)) == len(variables), "QMC_VARIABLES")
    bounds = [(float(Decimal(row[0])), float(Decimal(row[1]))) for row in specification["bounds"]]
    require(len(bounds) == len(variables) and all(math.isfinite(a) and math.isfinite(b) and a < b for a, b in bounds), "QMC_BOUNDS")
    points = sobol_uint32(specification["sample_count"], len(variables), specification["seed"], specification["scrambling"])
    expression = DeclarativeExpressionV1(specification["integrand"], variables=variables, limits=limits)
    samples = []
    for point in points:
        values = {name: lower + (upper - lower) * integer / 2 ** 32 for name, integer, (lower, upper) in zip(variables, point, bounds)}
        samples.append(expression.evaluate(variables=values))
    mean = fmean(samples)
    variance = fmean([(value - mean) ** 2 for value in samples])
    ordered = sorted(samples)
    quantile = lambda fraction: ordered[min(len(ordered) - 1, int(fraction * (len(ordered) - 1)))]
    return {
        "schema_id": "UncertaintyReceiptV1", "semantics": UncertaintySemantics.SAMPLED_DISTRIBUTION_ESTIMATE.value,
        "specification_hash": digest(specification, "QMCEnsembleSpecV1"), "generated_input_set_sha256": _uint32_points_hash(points),
        "generator_identity": {"family": "SOBOL", "version": "VPC_SOBOL_UINT32_V1", "direction_table": SOBOL_DIRECTION_TABLE_ID, "scrambling": specification["scrambling"], "ordering": "GRAY_CODE_INDEX_ORDER", "sample_count_convention": "FIRST_N_FROM_INDEX_ZERO", "dimension": len(variables), "sample_count": len(points), "seed": specification["seed"]},
        "mean_hex": float(mean).hex(), "variance_hex": float(variance).hex(), "minimum_hex": float(ordered[0]).hex(), "maximum_hex": float(ordered[-1]).hex(),
        "quantiles_hex": {"0.05": float(quantile(0.05)).hex(), "0.5": float(quantile(0.5)).hex(), "0.95": float(quantile(0.95)).hex()},
        "limitations": ["Distribution estimate under the stated sampling model", "Not a guaranteed range", "Single digitally shifted Sobol ensemble"],
    }

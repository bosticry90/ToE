from __future__ import annotations

import argparse
import ast
import hashlib
import hmac
import inspect
import json
import math
import os
import platform
import secrets
import struct
import subprocess
import sys
import tempfile
import time
import traceback
import tracemalloc
import uuid
from decimal import Decimal, InvalidOperation, ROUND_HALF_EVEN, localcontext
from pathlib import Path
from typing import Any, Callable


os.environ.setdefault("OMP_NUM_THREADS", "1")
os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
os.environ.setdefault("MKL_NUM_THREADS", "1")
os.environ.setdefault("NUMEXPR_NUM_THREADS", "1")

import numpy as np


REPO_ROOT = Path(__file__).resolve().parents[3]
SOURCE_RELATIVE_PATH = (
    "formal/python/tools/scalar_only_yukawa_analytic_sphere_kernel_"
    "exploratory_sandbox_v0.py"
)
RESULT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "EXPLORATORY_SANDBOX_20260719_v0.json"
)
RESULT_SHA_RELATIVE_PATH = RESULT_RELATIVE_PATH + ".sha256"
RAW_LOG_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "EXPLORATORY_SANDBOX_20260719_v0.log"
)
STAGE_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "EXPLORATORY_SANDBOX_20260719_v0.stages.json"
)
CONSUMPTION_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "EXPLORATORY_SANDBOX_20260719_v0.authority_consumed.json"
)
INFRA_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_KERNEL_REPLACEMENT_VALIDATION_"
    "INFRASTRUCTURE_PREREQUISITE_PACKET_20260719_v0.json"
)
KERNEL_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "REPLACEMENT_PACKET_20260719_v1.json"
)
SELECTOR_RELATIVE_PATH = (
    "formal/docs/release/POST_SCALAR_ONLY_YUKAWA_KERNEL_REPLACEMENT_VALIDATION_"
    "INFRASTRUCTURE_PREREQUISITE_PACKET_V0_REVIEW_SCIENTIFIC_RESPONSE_"
    "SELECTION_20260719_v0.json"
)
ORACLE_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_ORACLE_"
    "QUALIFICATION_EXECUTION_20260719_v0.json"
)

EXPECTED_HASHES = {
    INFRA_RELATIVE_PATH: "66ce9cd50115963c531c31524e20e7c567692f5455f8b8bde5411bf685da4d12",
    KERNEL_RELATIVE_PATH: "cbd393070a567368a83327bd99e53dbb18013bba8ac9447cc7952b74a2d6c122",
    SELECTOR_RELATIVE_PATH: "dce00265fabc1e7b7c9847fc369096bed32c9d0b792861aa21b8c6ad5dff8d44",
    ORACLE_RELATIVE_PATH: "d2527fd3c03a107734b3b55920c35f73185cbbf0f6c13132ff94c40ec447676d",
}

REVIEW_SHA256 = "729f86d0b1f2ab1ed475b073017fff8f47f4768720c4fab0d65b00c7652c668a"
G_SI = 6.67430e-11
DEFAULT_A_Y = 1.0 / 3.0
MIN_SUBNORMAL = float.fromhex("0x0.0000000000001p-1022")
LOG_MIN_SUBNORMAL = math.log(MIN_SUBNORMAL)
MAX_X = 1000.0
EXPLORATORY_LABELS = (
    "EXPLORATORY_IMPLEMENTATION_RESULT",
    "NON_PRODUCTION",
    "NON_ADJUDICATIVE",
    "NO_SCIENTIFIC_CLAIM",
)
FORBIDDEN_MODULES = (
    "scalar_only_yukawa_torsion_balance_production_v1",
    "scalar_only_yukawa_analytic_sphere_oracle_qualification_v0",
    "reduced_four_dimensional_density_integral_yukawa_energy",
    "forbidden_oracle",
    "forbidden_cubature",
)


class DuplicateKeyError(ValueError):
    pass


class SchemaValidationError(ValueError):
    pass


class ForbiddenDependencyDetected(RuntimeError):
    pass


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _canonical_bytes(value: Any) -> bytes:
    return (
        json.dumps(
            value,
            sort_keys=True,
            ensure_ascii=True,
            allow_nan=False,
            separators=(",", ":"),
        )
        + "\n"
    ).encode("utf-8")


def _atomic_write(path: Path, payload: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix=path.name + ".", suffix=".tmp", dir=path.parent)
    try:
        with os.fdopen(fd, "wb") as handle:
            handle.write(payload)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    finally:
        if os.path.exists(temporary):
            os.unlink(temporary)


def _strict_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise DuplicateKeyError(f"duplicate key: {key}")
        result[key] = value
    return result


def _reject_nonfinite(token: str) -> None:
    raise SchemaValidationError(f"nonfinite constant: {token}")


def loads_strict(text: str) -> Any:
    return json.loads(
        text,
        object_pairs_hook=_strict_pairs,
        parse_constant=_reject_nonfinite,
    )


def _load_contract(relative_path: str) -> dict[str, Any]:
    value = loads_strict((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise SchemaValidationError(f"contract is not an object: {relative_path}")
    return value


def _float_hex(value: float) -> str:
    value = float(value)
    if not math.isfinite(value):
        raise FloatingPointError("NONFINITE_BINARY64_OUTPUT")
    return value.hex().lower()


def _qualified_exception(exc: BaseException) -> dict[str, str]:
    qualified_type = f"{type(exc).__module__}.{type(exc).__qualname__}"
    if isinstance(exc, DuplicateKeyError):
        qualified_type = "validation_infrastructure.DuplicateKeyError"
    elif isinstance(exc, SchemaValidationError):
        qualified_type = "validation_infrastructure.SchemaValidationError"
    return {
        "type": qualified_type,
        "message": str(exc),
    }


def _decimal(value: str) -> Decimal:
    with localcontext() as context:
        context.prec = 100
        context.rounding = ROUND_HALF_EVEN
        return Decimal(value)


def _decimal_from_float(value: float) -> Decimal:
    with localcontext() as context:
        context.prec = 100
        context.rounding = ROUND_HALF_EVEN
        return Decimal.from_float(float(value))


def _abs_rel(candidate: float, reference: str, absolute: str, relative: str) -> dict[str, Any]:
    with localcontext() as context:
        context.prec = 100
        context.rounding = ROUND_HALF_EVEN
        observed = Decimal.from_float(float(candidate))
        expected = Decimal(reference)
        difference = abs(observed - expected)
        envelope = Decimal(absolute) + Decimal(relative) * abs(expected)
        return {
            "passed": difference <= envelope,
            "difference_decimal": str(difference).upper(),
            "envelope_decimal": str(envelope).upper(),
        }


def _h_factor(x: float, *, forced_regime: str | None = None) -> tuple[float, str]:
    if not math.isfinite(x) or x < 0.0:
        raise ValueError("INVALID_DIMENSIONLESS_RADIUS")
    if x > MAX_X:
        raise ValueError("X_OUTSIDE_QUALIFIED_DOMAIN")
    regime = forced_regime
    if regime is None:
        regime = "small" if x <= 0.1 else "direct" if x <= 40.0 else "scaled"
    if x == 0.0:
        return 1.0, "SMALL_X_SERIES"
    if regime == "small":
        x2 = x * x
        series = 1.0 + x2 / 10.0 + x2 * x2 / 280.0
        series += x2**3 / 15120.0 + x2**4 / 1330560.0
        return math.exp(-x) * series, "SMALL_X_SERIES"
    if regime == "direct":
        value = math.exp(-x) * 3.0 * (x * math.cosh(x) - math.sinh(x)) / (x**3)
        return value, "MODERATE_X_DIRECT"
    if regime == "scaled":
        value = 3.0 * ((x - 1.0) + (x + 1.0) * math.exp(-2.0 * x)) / (2.0 * x**3)
        return value, "LARGE_X_SCALED"
    raise ValueError(f"UNKNOWN_EVALUATOR_REGIME:{regime}")


def _validate_scalar(name: str, value: float, *, positive: bool = False, nonnegative: bool = False) -> float:
    value = float(value)
    if not math.isfinite(value):
        raise ValueError(f"NONFINITE_{name.upper()}")
    if positive and value <= 0.0:
        raise ValueError(f"NONPOSITIVE_{name.upper()}")
    if nonnegative and value < 0.0:
        raise ValueError(f"NEGATIVE_{name.upper()}")
    return value


def _candidate_core(
    distance_m: Any,
    lambda_m: float,
    *,
    mass_d_kg: float,
    mass_a_kg: float,
    radius_d_m: float,
    radius_a_m: float,
    yukawa_amplitude: float,
    component: str,
    mutation_id: str | None = None,
) -> tuple[np.ndarray, np.ndarray, dict[str, Any]]:
    if component not in ("newtonian", "yukawa", "total"):
        raise ValueError("UNKNOWN_COMPONENT")
    mass_d_kg = _validate_scalar("mass_d_kg", mass_d_kg, positive=True)
    mass_a_kg = _validate_scalar("mass_a_kg", mass_a_kg, positive=True)
    radius_d_m = _validate_scalar("radius_d_m", radius_d_m, nonnegative=True)
    radius_a_m = _validate_scalar("radius_a_m", radius_a_m, nonnegative=True)
    yukawa_amplitude = _validate_scalar(
        "yukawa_amplitude", yukawa_amplitude, nonnegative=True
    )
    lambda_m = float(lambda_m)
    if component == "newtonian" and lambda_m == 0.0:
        pass
    elif mutation_id == "M09_NONPOSITIVE_YUKAWA_RANGE_ACCEPTED" and lambda_m <= 0.0:
        lambda_m = 1.0
    else:
        lambda_m = _validate_scalar("lambda_m", lambda_m, positive=True)

    distances = np.asarray(distance_m, dtype=np.float64)
    if distances.size == 0:
        raise ValueError("EMPTY_DISTANCE_ARRAY")
    flat = distances.reshape(-1)
    invalid: list[int] = []
    gaps: list[float] = []
    radius_sum = math.fsum((radius_d_m, radius_a_m))
    for index, raw_distance in enumerate(flat):
        distance = float(raw_distance)
        if not math.isfinite(distance) or distance <= 0.0:
            invalid.append(index)
            gaps.append(float("nan"))
            continue
        gap = math.fsum((distance, -radius_d_m, -radius_a_m))
        gaps.append(gap)
        if mutation_id != "M08_TOUCHING_OR_OVERLAPPING_INPUT_ACCEPTED":
            if gap <= 0.0:
                invalid.append(index)
                continue
            if gap < 16.0 * math.ulp(max(distance, radius_sum)):
                invalid.append(index)
    if invalid:
        if distances.ndim == 0 and len(invalid) == 1 and gaps[0] <= 0.0:
            raise ValueError("TOUCHING_OR_OVERLAPPING")
        raise ValueError("INVALID_DISTANCE_ELEMENTS:" + ",".join(str(value) for value in invalid))

    x_d = 0.0 if component == "newtonian" else radius_d_m / lambda_m
    x_a = 0.0 if component == "newtonian" else radius_a_m / lambda_m
    if component != "newtonian" and mutation_id != "M10_X_ABOVE_QUALIFIED_MAXIMUM_ACCEPTED":
        if x_d > MAX_X or x_a > MAX_X:
            raise ValueError("X_OUTSIDE_QUALIFIED_DOMAIN")

    h_d, regime_d = (1.0, "NOT_USED_NEWTONIAN")
    h_a, regime_a = (1.0, "NOT_USED_NEWTONIAN")
    if component != "newtonian":
        if mutation_id == "M06_DIRECT_LARGE_X_HYPERBOLIC_OVERFLOW":
            with np.errstate(over="raise", invalid="raise"):
                xd = np.float64(x_d)
                xa = np.float64(x_a)
                h_d = float(np.exp(-xd) * 3.0 * (xd * np.cosh(xd) - np.sinh(xd)) / xd**3)
                h_a = float(np.exp(-xa) * 3.0 * (xa * np.cosh(xa) - np.sinh(xa)) / xa**3)
            regime_d = regime_a = "FORCED_DIRECT"
        elif mutation_id == "M07_DIRECT_SMALL_X_CANCELLATION":
            h_d, regime_d = _h_factor(x_d, forced_regime="direct")
            h_a, regime_a = _h_factor(x_a, forced_regime="direct")
        else:
            maximum = MAX_X if mutation_id != "M10_X_ABOVE_QUALIFIED_MAXIMUM_ACCEPTED" else math.inf
            if x_d > maximum or x_a > maximum:
                raise ValueError("X_OUTSIDE_QUALIFIED_DOMAIN")
            if mutation_id == "M10_X_ABOVE_QUALIFIED_MAXIMUM_ACCEPTED":
                h_d = 3.0 * ((x_d - 1.0) + (x_d + 1.0) * math.exp(-2.0 * x_d)) / (2.0 * x_d**3)
                h_a = 3.0 * ((x_a - 1.0) + (x_a + 1.0) * math.exp(-2.0 * x_a)) / (2.0 * x_a**3)
                regime_d = regime_a = "UNQUALIFIED_SCALED_MUTATION"
            else:
                h_d, regime_d = _h_factor(x_d)
                h_a, regime_a = _h_factor(x_a)
        if mutation_id == "M02_MISSING_SECOND_SPHERE_FACTOR":
            h_a = 1.0

    energy = np.empty(distances.shape, dtype=np.float64)
    derivative = np.empty(distances.shape, dtype=np.float64)
    energy_flat = energy.reshape(-1)
    derivative_flat = derivative.reshape(-1)
    for index, raw_distance in enumerate(flat):
        distance = float(raw_distance)
        gap = gaps[index]
        if mutation_id == "M01_GAP_SUBSTITUTED_FOR_CENTER_DISTANCE":
            distance = gap
            gap = math.fsum((distance, -radius_d_m, -radius_a_m))
        newtonian_energy = -G_SI * mass_d_kg * mass_a_kg / distance
        newtonian_derivative = -newtonian_energy / distance
        yukawa_energy = 0.0
        yukawa_derivative = 0.0
        if component != "newtonian":
            amplitude = 1.0 if mutation_id == "M03_MISSING_A_Y_ONE_THIRD" else yukawa_amplitude
            if amplitude == 0.0:
                yukawa_energy = 0.0
                yukawa_derivative = 0.0
            else:
                log_abs = (
                    math.log(amplitude)
                    + math.log(G_SI)
                    + math.log(mass_d_kg)
                    + math.log(mass_a_kg)
                    - math.log(distance)
                    - gap / lambda_m
                    + math.log(h_d)
                    + math.log(h_a)
                )
                if log_abs < LOG_MIN_SUBNORMAL:
                    raise FloatingPointError(
                        "UNREPRESENTABLE_NONZERO_OUTPUT_WITH_LOG_ABS:" + format(log_abs, ".17e")
                    )
                yukawa_energy = -math.exp(log_abs)
                yukawa_derivative = -yukawa_energy * (1.0 / distance + 1.0 / lambda_m)
            if mutation_id == "M04_REVERSED_ATTRACTIVE_SIGN":
                yukawa_energy = -yukawa_energy
            if mutation_id == "M05_WRONG_RADIAL_DERIVATIVE_SIGN":
                yukawa_derivative = -yukawa_derivative
                newtonian_derivative = -newtonian_derivative
        if component == "newtonian":
            energy_flat[index] = newtonian_energy
            derivative_flat[index] = (
                -newtonian_derivative
                if mutation_id == "M05_WRONG_RADIAL_DERIVATIVE_SIGN"
                else newtonian_derivative
            )
        elif component == "yukawa":
            energy_flat[index] = yukawa_energy
            derivative_flat[index] = yukawa_derivative
        else:
            energy_flat[index] = newtonian_energy + yukawa_energy
            derivative_flat[index] = newtonian_derivative + yukawa_derivative
    if mutation_id == "M11_OUTPUT_SHAPE_OR_DTYPE_CHANGED":
        energy = energy.astype(np.float32)
        derivative = derivative.astype(np.float32)
    return energy, derivative, {
        "x_d_float_hex": _float_hex(x_d),
        "x_a_float_hex": _float_hex(x_a),
        "regime_d": regime_d,
        "regime_a": regime_a,
    }


def pair_energy_and_radial_derivative(
    distance_m: Any,
    lambda_m: float,
    *,
    mass_d_kg: float,
    mass_a_kg: float,
    radius_d_m: float,
    radius_a_m: float,
    yukawa_amplitude: float = DEFAULT_A_Y,
    component: str = "total",
    yukawa_sign: float = 1.0,
    remove_attractor_form_factor: bool = False,
) -> tuple[np.ndarray, np.ndarray]:
    if (
        float(yukawa_amplitude) != DEFAULT_A_Y
        or float(yukawa_sign) != 1.0
        or bool(remove_attractor_form_factor)
    ):
        raise PermissionError("VALIDATION_HOOK_FORBIDDEN_ON_PUBLIC_ENTRYPOINT")
    energy, derivative, _ = _candidate_core(
        distance_m,
        lambda_m,
        mass_d_kg=mass_d_kg,
        mass_a_kg=mass_a_kg,
        radius_d_m=radius_d_m,
        radius_a_m=radius_a_m,
        yukawa_amplitude=DEFAULT_A_Y,
        component=component,
    )
    return energy, derivative


def _token_mac(secret: bytes, token: dict[str, Any]) -> str:
    fields = {key: value for key, value in token.items() if key != "mac_hex"}
    return hmac.new(secret, _canonical_bytes(fields), hashlib.sha256).hexdigest()


class ValidationHarnessSession:
    def __init__(self, manifest: dict[str, Any], secret: bytes):
        self.manifest = manifest
        self._secret = secret
        self._used_nonces: set[str] = set()
        self._allowed = {
            (row["fixture_id"], row["mutation_id"])
            for row in manifest["allowed_bindings"]
        }

    def issue_capability(self, fixture_id: str, mutation_id: str) -> dict[str, Any]:
        if (fixture_id, mutation_id) not in self._allowed:
            raise PermissionError("CAPABILITY_WRONG_FIXTURE")
        issued = time.monotonic_ns()
        token: dict[str, Any] = {
            "schema_id": "CapabilityTokenV0",
            "run_id": self.manifest["run_id"],
            "pid": os.getpid(),
            "fixture_id": fixture_id,
            "mutation_id": mutation_id,
            "review_sha256": self.manifest["review_sha256"],
            "nonce_hex": secrets.token_hex(32),
            "issued_ns": issued,
            "expires_ns": issued + 30_000_000_000,
            "mac_hex": "",
        }
        token["mac_hex"] = _token_mac(self._secret, token)
        return token

    def authenticate(
        self,
        capability: Any,
        fixture_id: str,
        mutation_id: str,
        *,
        now_ns: int | None = None,
    ) -> None:
        if capability is None:
            raise PermissionError("CAPABILITY_REQUIRED")
        required = {
            "schema_id", "run_id", "pid", "fixture_id", "mutation_id",
            "review_sha256", "nonce_hex", "issued_ns", "expires_ns", "mac_hex",
        }
        if not isinstance(capability, dict) or set(capability) != required:
            raise PermissionError("CAPABILITY_SCHEMA_INVALID")
        if not hmac.compare_digest(capability["mac_hex"], _token_mac(self._secret, capability)):
            raise PermissionError("CAPABILITY_MAC_INVALID")
        if capability["pid"] != os.getpid():
            raise PermissionError("CAPABILITY_WRONG_PROCESS")
        if capability["run_id"] != self.manifest["run_id"]:
            raise PermissionError("CAPABILITY_WRONG_RUN")
        if capability["review_sha256"] != self.manifest["review_sha256"]:
            raise PermissionError("CAPABILITY_WRONG_REVIEW")
        if capability["fixture_id"] != fixture_id:
            raise PermissionError("CAPABILITY_WRONG_FIXTURE")
        if capability["mutation_id"] != mutation_id:
            raise PermissionError("CAPABILITY_WRONG_MUTATION")
        now = time.monotonic_ns() if now_ns is None else now_ns
        if capability["issued_ns"] > now:
            raise PermissionError("CAPABILITY_FUTURE_ISSUE")
        if now > capability["expires_ns"]:
            raise PermissionError("CAPABILITY_EXPIRED")
        nonce = capability["nonce_hex"]
        if nonce in self._used_nonces:
            raise PermissionError("CAPABILITY_REPLAYED")
        self._used_nonces.add(nonce)


def _frame_read(fd: int) -> tuple[dict[str, Any], bytes, bytes]:
    def read_exact(length: int) -> bytes:
        chunks = bytearray()
        while len(chunks) < length:
            chunk = os.read(fd, length - len(chunks))
            if not chunk:
                raise EOFError("TRUNCATED_CAPABILITY_PIPE_FRAME")
            chunks.extend(chunk)
        return bytes(chunks)

    manifest_length = struct.unpack(">I", read_exact(4))[0]
    manifest_bytes = read_exact(manifest_length)
    secret = read_exact(32)
    trailing = os.read(fd, 1)
    os.close(fd)
    if trailing:
        raise ValueError("TRAILING_CAPABILITY_PIPE_BYTES")
    manifest = loads_strict(manifest_bytes.decode("utf-8"))
    if _canonical_bytes(manifest) != manifest_bytes:
        raise ValueError("NONCANONICAL_CAPABILITY_MANIFEST")
    if manifest["child_pid"] != os.getpid():
        raise PermissionError("CAPABILITY_WRONG_PROCESS")
    return manifest, secret, manifest_bytes


def _json_pointer(document: Any, pointer: str) -> Any:
    if not pointer.startswith("/"):
        raise SchemaValidationError("MISSING_POINTER")
    value = document
    for raw in pointer.split("/")[1:]:
        token = raw.replace("~1", "/").replace("~0", "~")
        if isinstance(value, dict) and token in value:
            value = value[token]
        elif isinstance(value, list) and token.isdigit() and int(token) < len(value):
            value = value[int(token)]
        else:
            raise SchemaValidationError("MISSING_POINTER")
    return value


def adjudicate_v0(predicate: dict[str, Any], document: dict[str, Any]) -> dict[str, Any]:
    kind = predicate["kind"]
    observed: Any = None
    reference: Any = None
    difference: str | None = None
    envelope: str | None = None
    passed = False
    if kind == "NUMERIC":
        observed_hex = _json_pointer(document, predicate["observed_pointer"])
        observed = _decimal_from_float(float.fromhex(observed_hex))
        if predicate["reference_pointer"] is not None:
            reference_hex = _json_pointer(document, predicate["reference_pointer"])
            reference = _decimal_from_float(float.fromhex(reference_hex))
        else:
            reference = _decimal(predicate["reference_decimal"])
        absolute = _decimal(predicate["absolute_tolerance_decimal"])
        relative = _decimal(predicate["relative_tolerance_decimal"])
        delta = abs(observed - reference)
        if predicate["comparator"] == "ABS_REL_LE":
            bound = absolute + relative * abs(reference)
            passed = delta <= bound
            envelope = str(bound).upper()
        elif predicate["comparator"] == "RELATIVE_DIFFERENCE_GE":
            bound = relative
            ratio = delta / max(abs(reference), absolute)
            passed = ratio >= bound
            difference = str(ratio).upper()
            envelope = str(bound).upper()
        elif predicate["comparator"] == "EXACT_FLOAT_HEX":
            passed = observed_hex == predicate["reference_decimal"]
        else:
            raise SchemaValidationError("UNKNOWN_ENUM")
        if difference is None:
            difference = str(delta).upper()
    elif kind == "RELATIONAL":
        left = _json_pointer(document, predicate["left_pointer"])
        right = (
            _json_pointer(document, predicate["right_pointer"])
            if predicate["right_pointer"] is not None
            else predicate["right_literal"]
        )
        if isinstance(left, str) and left.startswith(("0x", "-0x")):
            left = float.fromhex(left)
        if isinstance(right, str) and right.startswith(("0x", "-0x")):
            right = float.fromhex(right)
        operators: dict[str, Callable[[Any, Any], bool]] = {
            "EQ": lambda a, b: a == b,
            "NE": lambda a, b: a != b,
            "LT": lambda a, b: a < b,
            "LE": lambda a, b: a <= b,
            "GT": lambda a, b: a > b,
            "GE": lambda a, b: a >= b,
        }
        if predicate["operator"] not in operators:
            raise SchemaValidationError("UNKNOWN_ENUM")
        observed, reference = left, right
        passed = operators[predicate["operator"]](left, right)
    elif kind == "EXCEPTION":
        record = document["calls"][predicate["call_id"]]
        observed = record
        reference = {
            "type": predicate["exception_type"],
            "message": predicate["message"],
        }
        passed = record == reference
    elif kind == "DEPENDENCY":
        observed = _json_pointer(document, predicate["scan_result_pointer"])
        reference = predicate["expected_violation_ids"]
        passed = observed == reference
    else:
        raise SchemaValidationError("UNKNOWN_ENUM")
    return {
        "predicate_id": predicate["predicate_id"],
        "kind": kind,
        "passed": bool(passed),
        "observed_canonical": observed,
        "reference_canonical": reference,
        "difference_decimal": difference,
        "envelope_decimal": envelope,
        "failure_code": None if passed else "PREDICATE_FALSE",
    }


def scan_python_dependency_contract(source_id: str, source: str) -> dict[str, Any]:
    violations: set[str] = set()
    try:
        tree = ast.parse(source, filename=source_id)
    except SyntaxError:
        return {
            "source_id": source_id,
            "parsed": False,
            "violation_ids": ["PARSE_ERROR"],
            "passed": False,
        }
    aliases: dict[str, str] = {}
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for alias in node.names:
                name = alias.name
                aliases[alias.asname or name.split(".")[0]] = name
                if any(name == item or name.startswith(item + ".") for item in FORBIDDEN_MODULES):
                    violations.add(f"FORBIDDEN_IMPORT:{name}")
        elif isinstance(node, ast.ImportFrom):
            name = node.module or ""
            if any(name == item or name.startswith(item + ".") for item in FORBIDDEN_MODULES):
                violations.add(f"FORBIDDEN_IMPORT:{name}")
        elif isinstance(node, ast.Call):
            if isinstance(node.func, ast.Name) and node.func.id == "__import__":
                violations.add("DYNAMIC_IMPORT:__import__")
            if (
                isinstance(node.func, ast.Attribute)
                and isinstance(node.func.value, ast.Name)
                and aliases.get(node.func.value.id) == "importlib"
                and node.func.attr == "import_module"
            ):
                violations.add("DYNAMIC_IMPORT:importlib.import_module")
            if isinstance(node.func, ast.Attribute) and isinstance(node.func.value, ast.Name):
                root = aliases.get(node.func.value.id, node.func.value.id)
                target = f"{root}.{node.func.attr}"
                if target in ("forbidden_oracle.evaluate", "forbidden_cubature.integrate"):
                    violations.add(f"FORBIDDEN_CALL:{target}")
    ordered = sorted(violations)
    return {
        "source_id": source_id,
        "parsed": True,
        "violation_ids": ordered,
        "passed": len(ordered) == 0,
    }


def _fixture_baseline(fixture_id: str) -> dict[str, Any]:
    if fixture_id == "F01_LINEAR_PAIR":
        return {"value_float_hex": _float_hex(1.25 + 2.0 * -0.5)}
    if fixture_id == "F02_NEGATIVE_SQUARE":
        return {"value_float_hex": _float_hex(-(2.0 * 2.0))}
    if fixture_id == "F03_REQUIRED_EXCEPTION":
        raise ZeroDivisionError("synthetic zero denominator")
    if fixture_id == "F04_ARRAY_IDENTITY":
        values = np.asarray([1.0, 2.0], dtype=np.float64).copy(order="C")
        return {
            "dtype": str(values.dtype),
            "shape": list(values.shape),
            "values_float_hex": [_float_hex(value) for value in values],
        }
    if fixture_id == "F05_PRIVATE_CAPABILITY":
        return {"value_ascii": "echo"}
    if fixture_id == "F06_DEPENDENCY_SCAN":
        return scan_python_dependency_contract(
            "SYNTHETIC_BAD_IMPORT_V0",
            "import forbidden_oracle\nforbidden_oracle.evaluate()\n",
        )
    if fixture_id == "F07_DUPLICATE_JSON":
        return {"object": loads_strict('{"a":1}')}
    if fixture_id == "F08_UNKNOWN_ENUM":
        return {"status": _validate_run_status("COMPLETE")}
    raise ValueError("UNKNOWN_FIXTURE")


def evaluate_fixture(fixture_id: str, input_record_id: str) -> dict[str, Any]:
    try:
        output = _fixture_baseline(fixture_id)
        return {
            "fixture_id": fixture_id,
            "input_record_id": input_record_id,
            "status": "RETURNED",
            "output": output,
            "exception": None,
        }
    except Exception as exc:
        return {
            "fixture_id": fixture_id,
            "input_record_id": input_record_id,
            "status": "RAISED",
            "output": None,
            "exception": _qualified_exception(exc),
        }


def _validate_run_status(value: str) -> str:
    if value not in ("COMPLETE", "FAILED"):
        raise SchemaValidationError("/status:UNKNOWN_ENUM_VALUE")
    return value


def _evaluate_mutated_fixture(
    fixture_id: str,
    input_record_id: str,
    mutation_id: str,
    *,
    capability: dict[str, Any] | None,
    session: ValidationHarnessSession,
) -> dict[str, Any]:
    session.authenticate(capability, fixture_id, mutation_id)
    try:
        if mutation_id == "M01_SCALE_BY_TWO":
            output = {"value_float_hex": _float_hex((1.25 + 2.0 * -0.5) * 2.0)}
        elif mutation_id == "M02_FLIP_SIGN":
            output = {"value_float_hex": _float_hex(4.0)}
        elif mutation_id == "M03_SUPPRESS_EXCEPTION":
            output = {"returned": True, "value_float_hex": _float_hex(0.0)}
        elif mutation_id == "M04_CAST_FLOAT32":
            output = {"dtype": "float32", "shape": [2]}
        elif mutation_id == "M06_INSERT_FORBIDDEN_IMPORT":
            output = {
                "scanner": scan_python_dependency_contract(
                    "SYNTHETIC_BAD_IMPORT_V0",
                    "import forbidden_oracle\nforbidden_oracle.evaluate()\n",
                )
            }
        elif mutation_id == "M07_DUPLICATE_KEY_INPUT":
            output = {"object": loads_strict('{"a":1,"a":2}')}
        elif mutation_id == "M08_UNKNOWN_ENUM_INPUT":
            output = {"status": _validate_run_status("UNKNOWN")}
        else:
            output = _fixture_baseline(fixture_id)
        return {
            "fixture_id": fixture_id,
            "input_record_id": input_record_id,
            "status": "RETURNED",
            "output": output,
            "exception": None,
        }
    except Exception as exc:
        return {
            "fixture_id": fixture_id,
            "input_record_id": input_record_id,
            "status": "RAISED",
            "output": None,
            "exception": _qualified_exception(exc),
        }


def _make_manifest(run_id: str, child_pid: int, binding: tuple[str, str]) -> dict[str, Any]:
    issued = time.monotonic_ns()
    return {
        "schema_id": "QualificationLaunchManifestV0",
        "run_id": run_id,
        "child_pid": child_pid,
        "review_sha256": REVIEW_SHA256,
        "allowed_bindings": [
            {"fixture_id": binding[0], "mutation_id": binding[1]}
        ],
        "issued_ns": issued,
        "expires_ns": issued + 30_000_000_000,
    }


def _launch_child(run_id: str, child_kind: str, child_id: str, binding: tuple[str, str]) -> dict[str, Any]:
    read_fd, write_fd = os.pipe()
    os.set_inheritable(read_fd, True)
    command = [
        sys.executable,
        str(REPO_ROOT / SOURCE_RELATIVE_PATH),
        "--child-kind",
        child_kind,
        "--child-id",
        child_id,
        "--read-fd",
        str(read_fd),
    ]
    process = subprocess.Popen(
        command,
        cwd=REPO_ROOT,
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        close_fds=False,
    )
    os.close(read_fd)
    secret = secrets.token_bytes(32)
    manifest = _make_manifest(run_id, process.pid, binding)
    manifest_bytes = _canonical_bytes(manifest)
    frame = struct.pack(">I", len(manifest_bytes)) + manifest_bytes + secret
    try:
        os.write(write_fd, frame)
    finally:
        os.close(write_fd)
    try:
        stdout, stderr = process.communicate(timeout=15)
    except subprocess.TimeoutExpired:
        process.kill()
        stdout, stderr = process.communicate()
        return {
            "child_kind": child_kind,
            "child_id": child_id,
            "child_pid": process.pid,
            "returncode": process.returncode,
            "stdout_ascii": stdout.decode("utf-8", errors="replace"),
            "stderr_ascii": stderr.decode("utf-8", errors="replace"),
            "timeout": True,
            "passed": False,
        }
    if process.returncode != 0:
        return {
            "child_kind": child_kind,
            "child_id": child_id,
            "child_pid": process.pid,
            "returncode": process.returncode,
            "stdout_ascii": stdout.decode("utf-8", errors="replace"),
            "stderr_ascii": stderr.decode("utf-8", errors="replace"),
            "passed": False,
        }
    value = loads_strict(stdout.decode("utf-8"))
    value["child_pid"] = process.pid
    value["returncode"] = process.returncode
    value["stderr_ascii"] = stderr.decode("utf-8", errors="replace")
    return value


def _synthetic_route_child(route_id: str, session: ValidationHarnessSession, infra: dict[str, Any]) -> dict[str, Any]:
    routes = {row["route_id"]: row for row in infra["mutation_routing_contract_v0"]["route_rows"]}
    predicates = {row["predicate_id"]: row for row in infra["typed_adjudicator_contract_v0"]["predicate_rows"]}
    route = routes[route_id]
    baseline = evaluate_fixture(route["fixture_id"], route["input_record_id"])
    baseline_passed = baseline["status"] in ("RETURNED", "RAISED")
    capability = session.issue_capability(route["fixture_id"], route["mutation_id"])
    calls: dict[str, Any] = {}
    if route["mutation_id"] == "M05_BYPASS_CAPABILITY":
        try:
            _evaluate_mutated_fixture(
                route["fixture_id"], route["input_record_id"], route["mutation_id"],
                capability=None, session=session,
            )
        except Exception as exc:
            calls["C06_PRIVATE_WITHOUT_CAPABILITY"] = _qualified_exception(exc)
        mutation_document = {"calls": calls}
    else:
        mutation = _evaluate_mutated_fixture(
            route["fixture_id"], route["input_record_id"], route["mutation_id"],
            capability=capability, session=session,
        )
        if route["mutation_id"] in ("M07_DUPLICATE_KEY_INPUT", "M08_UNKNOWN_ENUM_INPUT"):
            call_id = "C08_LOAD_DUPLICATE" if route["mutation_id"] == "M07_DUPLICATE_KEY_INPUT" else "C09_VALIDATE_UNKNOWN_ENUM"
            calls[call_id] = mutation["exception"]
            mutation_document = {"calls": calls}
        elif route["mutation_id"] == "M06_INSERT_FORBIDDEN_IMPORT":
            mutation_document = mutation["output"]
        else:
            mutation_document = {
                "baseline": baseline["output"],
                "mutation": mutation["output"],
            }
    adjudication = adjudicate_v0(predicates[route["predicate_id"]], mutation_document)
    return {
        "child_kind": "synthetic-route",
        "child_id": route_id,
        "baseline_passed": baseline_passed,
        "route_id": route_id,
        "mutation_id": route["mutation_id"],
        "fixture_id": route["fixture_id"],
        "predicate_id": route["predicate_id"],
        "detected": adjudication["passed"],
        "adjudication": adjudication,
        "passed": baseline_passed and adjudication["passed"],
    }


def _row_inputs(row: dict[str, Any]) -> dict[str, float]:
    return {
        "distance": float.fromhex(row["center_distance_m_hex"]),
        "lambda_m": float.fromhex(row["lambda_m_hex"]),
        "mass_1": float.fromhex(row["mass_1_kg_hex"]),
        "mass_2": float.fromhex(row["mass_2_kg_hex"]),
        "radius_1": float.fromhex(row["radius_1_m_hex"]),
        "radius_2": float.fromhex(row["radius_2_m_hex"]),
        "amplitude": float.fromhex(row["yukawa_amplitude_hex"]),
    }


def _private_candidate_call(row: dict[str, Any], component: str, mutation_id: str | None = None, distance_override: Any = None) -> tuple[np.ndarray, np.ndarray, dict[str, Any]]:
    values = _row_inputs(row)
    return _candidate_core(
        values["distance"] if distance_override is None else distance_override,
        values["lambda_m"],
        mass_d_kg=values["mass_1"],
        mass_a_kg=values["mass_2"],
        radius_d_m=values["radius_1"],
        radius_a_m=values["radius_2"],
        yukawa_amplitude=values["amplitude"],
        component=component,
        mutation_id=mutation_id,
    )


def _kernel_mutation_child(mutation_id: str, session: ValidationHarnessSession, kernel: dict[str, Any]) -> dict[str, Any]:
    mutations = {row["mutation_id"]: row for row in kernel["mutation_routing_v1"]["rows"]}
    regressions = {row["case_id"]: row for row in kernel["regression_and_derivative_reference_v1"]["rows"]}
    probes = {row["probe_id"]: row for row in kernel["limit_and_boundary_probe_contract_v1"]["rows"]}
    mutation = mutations[mutation_id]
    fixture_id = mutation["case_ids"][0]
    detected = False
    details: dict[str, Any] = {}
    try:
        if fixture_id in regressions:
            row = regressions[fixture_id]
        elif fixture_id in probes:
            probe = probes[fixture_id]
            row = {
                "case_id": fixture_id,
                **probe["inputs"],
                "center_distance_m_hex": probe["inputs"].get("center_distance_m_hex", "0x0.0p+0"),
                "mass_1_kg_hex": probe["inputs"].get("mass_1_kg_hex", "0x1.0p+0"),
                "mass_2_kg_hex": probe["inputs"].get("mass_2_kg_hex", "0x1.0p+0"),
                "radius_1_m_hex": probe["inputs"].get("radius_1_m_hex", "0x0.0p+0"),
                "radius_2_m_hex": probe["inputs"].get("radius_2_m_hex", "0x0.0p+0"),
                "lambda_m_hex": probe["inputs"].get("lambda_m_hex", "0x0.0p+0"),
                "yukawa_amplitude_hex": probe["inputs"].get("yukawa_amplitude_hex", float(DEFAULT_A_Y).hex()),
            }
        else:
            row = {}
        baseline_passed = False
        if mutation_id == "M08_TOUCHING_OR_OVERLAPPING_INPUT_ACCEPTED":
            try:
                _private_candidate_call(row, "total")
            except ValueError as exc:
                baseline_passed = str(exc) == "TOUCHING_OR_OVERLAPPING"
        elif mutation_id == "M09_NONPOSITIVE_YUKAWA_RANGE_ACCEPTED":
            baseline_results = []
            for component in ("yukawa", "total"):
                try:
                    _private_candidate_call(row, component)
                    baseline_results.append(False)
                except ValueError:
                    baseline_results.append(True)
            baseline_passed = all(baseline_results)
        elif mutation_id == "M10_X_ABOVE_QUALIFIED_MAXIMUM_ACCEPTED":
            try:
                _private_candidate_call(row, "yukawa")
            except ValueError as exc:
                baseline_passed = str(exc) == "X_OUTSIDE_QUALIFIED_DOMAIN"
        elif mutation_id == "M11_OUTPUT_SHAPE_OR_DTYPE_CHANGED":
            baseline_passed = all(
                bool(np.isfinite(_public_row_call(regressions[case_id], "total")[0]).all())
                for case_id in mutation["case_ids"]
            )
        elif mutation_id == "M12_REFERENCE_HELPER_SHARED_WITH_CANDIDATE":
            baseline_scan = scan_python_dependency_contract(
                SOURCE_RELATIVE_PATH,
                (REPO_ROOT / SOURCE_RELATIVE_PATH).read_text(encoding="utf-8"),
            )
            baseline_passed = not baseline_scan["violation_ids"]
            details["baseline_scanner"] = baseline_scan
        else:
            baseline_component = "newtonian" if mutation_id == "M05_WRONG_RADIAL_DERIVATIVE_SIGN" else "yukawa"
            baseline_energy, baseline_derivative, _ = _private_candidate_call(
                row, baseline_component
            )
            baseline_passed = bool(
                np.isfinite(baseline_energy).all()
                and np.isfinite(baseline_derivative).all()
            )
        details["baseline_passed_before_capability"] = baseline_passed
        if not baseline_passed:
            return {
                "child_kind": "kernel-mutation",
                "child_id": mutation_id,
                "mutation_id": mutation_id,
                "fixture_id": fixture_id,
                "baseline_passed": False,
                "detected": False,
                "details": details,
                "passed": False,
            }
        token = session.issue_capability(fixture_id, mutation_id)
        session.authenticate(token, fixture_id, mutation_id)
        if mutation_id == "M05_WRONG_RADIAL_DERIVATIVE_SIGN":
            values = []
            for component in ("newtonian", "yukawa"):
                _, derivative, _ = _private_candidate_call(row, component, mutation_id)
                values.append(float(derivative))
            detected = any(value < 0.0 for value in values)
            details["mutated_derivatives_float_hex"] = [_float_hex(value) for value in values]
        elif mutation_id == "M06_DIRECT_LARGE_X_HYPERBOLIC_OVERFLOW":
            try:
                _private_candidate_call(row, "yukawa", mutation_id)
            except FloatingPointError as exc:
                detected = True
                details["exception"] = _qualified_exception(exc)
        elif mutation_id == "M07_DIRECT_SMALL_X_CANCELLATION":
            x = float.fromhex(row["radius_1_m_hex"]) / float.fromhex(row["lambda_m_hex"])
            stable, _ = _h_factor(x)
            direct, _ = _h_factor(x, forced_regime="direct")
            difference = abs(direct - stable)
            threshold = 5e-15 + 5e-12 * abs(stable)
            detected = difference > threshold
            details.update({
                "stable_h_float_hex": _float_hex(stable),
                "direct_h_float_hex": _float_hex(direct),
                "difference_float_hex": _float_hex(difference),
                "threshold_float_hex": _float_hex(threshold),
            })
        elif mutation_id == "M08_TOUCHING_OR_OVERLAPPING_INPUT_ACCEPTED":
            energy, _, _ = _private_candidate_call(row, "total", mutation_id)
            detected = bool(np.isfinite(energy).all())
        elif mutation_id == "M09_NONPOSITIVE_YUKAWA_RANGE_ACCEPTED":
            returns = []
            for component in ("yukawa", "total"):
                energy, _, _ = _private_candidate_call(row, component, mutation_id)
                returns.append(bool(np.isfinite(energy).all()))
            detected = all(returns)
            details["mutated_calls_returned"] = returns
        elif mutation_id == "M10_X_ABOVE_QUALIFIED_MAXIMUM_ACCEPTED":
            energy, _, _ = _private_candidate_call(row, "yukawa", mutation_id)
            detected = bool(np.isfinite(energy).all())
        elif mutation_id == "M11_OUTPUT_SHAPE_OR_DTYPE_CHANGED":
            first = regressions[mutation["case_ids"][0]]
            second = regressions[mutation["case_ids"][1]]
            distance = np.asarray(
                [float.fromhex(first["center_distance_m_hex"]), float.fromhex(second["center_distance_m_hex"])],
                dtype=np.float64,
            )
            energy, _, _ = _private_candidate_call(first, "total", mutation_id, distance_override=distance)
            detected = energy.dtype != np.float64 or energy.shape != distance.shape
            details.update({"dtype": str(energy.dtype), "shape": list(energy.shape)})
        elif mutation_id == "M12_REFERENCE_HELPER_SHARED_WITH_CANDIDATE":
            source = "import forbidden_oracle\nforbidden_oracle.evaluate()\n"
            scan = scan_python_dependency_contract("M12_INJECTED_SOURCE", source)
            detected = "FORBIDDEN_IMPORT:forbidden_oracle" in scan["violation_ids"]
            details["scanner"] = scan
        else:
            energy, derivative, _ = _private_candidate_call(row, "yukawa", mutation_id)
            mutated_energy = float(energy)
            mutated_derivative = float(derivative)
            reference = _decimal(row["yukawa_energy_reference_J_decimal"])
            if mutation_id in (
                "M01_GAP_SUBSTITUTED_FOR_CENTER_DISTANCE",
                "M02_MISSING_SECOND_SPHERE_FACTOR",
                "M03_MISSING_A_Y_ONE_THIRD",
            ):
                relative = abs(_decimal_from_float(mutated_energy) - reference) / abs(reference)
                threshold = _decimal(mutation["relative_tolerance"])
                detected = relative >= threshold
                details["relative_error_decimal"] = str(relative).upper()
            elif mutation_id == "M04_REVERSED_ATTRACTIVE_SIGN":
                detected = mutated_energy > 0.0 and reference < 0
            details.update({
                "mutated_energy_float_hex": _float_hex(mutated_energy),
                "mutated_derivative_float_hex": _float_hex(mutated_derivative),
            })
    except Exception as exc:
        details["unexpected_exception"] = _qualified_exception(exc)
    return {
        "child_kind": "kernel-mutation",
        "child_id": mutation_id,
        "mutation_id": mutation_id,
        "fixture_id": fixture_id,
        "baseline_passed": details.get("baseline_passed_before_capability", False),
        "detected": detected,
        "details": details,
        "passed": detected,
    }


def _child_main(kind: str, child_id: str, read_fd: int) -> int:
    try:
        manifest, secret, _ = _frame_read(read_fd)
        session = ValidationHarnessSession(manifest, secret)
        if kind == "synthetic-route":
            result = _synthetic_route_child(child_id, session, _load_contract(INFRA_RELATIVE_PATH))
        elif kind == "kernel-mutation":
            result = _kernel_mutation_child(child_id, session, _load_contract(KERNEL_RELATIVE_PATH))
        else:
            raise ValueError("UNKNOWN_CHILD_KIND")
        sys.stdout.buffer.write(_canonical_bytes(result))
        sys.stdout.buffer.flush()
        return 0 if result["passed"] else 1
    except Exception as exc:
        failure = {
            "child_kind": kind,
            "child_id": child_id,
            "passed": False,
            "child_error": _qualified_exception(exc),
            "traceback_ascii": traceback.format_exc(),
        }
        sys.stdout.buffer.write(_canonical_bytes(failure))
        sys.stdout.buffer.flush()
        return 1


def _capability_control_rows(run_id: str) -> list[dict[str, Any]]:
    manifest = _make_manifest(run_id, os.getpid(), ("F01_LINEAR_PAIR", "M01_SCALE_BY_TWO"))
    secret = secrets.token_bytes(32)
    rows: list[dict[str, Any]] = []

    def run(control_id: str, expected: str, operation: Callable[[], None]) -> None:
        observed = None
        try:
            operation()
        except PermissionError as exc:
            observed = str(exc)
        rows.append({
            "control_id": control_id,
            "expected_error": expected,
            "observed_error": observed,
            "passed": observed == expected,
        })

    session = ValidationHarnessSession(manifest, secret)
    token = session.issue_capability("F01_LINEAR_PAIR", "M01_SCALE_BY_TWO")
    forged = dict(token)
    forged["mac_hex"] = "00" * 32
    run("C02_FORGED_MAC_REJECTED", "CAPABILITY_MAC_INVALID", lambda: session.authenticate(forged, "F01_LINEAR_PAIR", "M01_SCALE_BY_TWO"))

    wrong_pid = dict(token)
    wrong_pid["pid"] = os.getpid() + 1
    wrong_pid["mac_hex"] = _token_mac(secret, wrong_pid)
    run("C03_WRONG_PID_REJECTED", "CAPABILITY_WRONG_PROCESS", lambda: session.authenticate(wrong_pid, "F01_LINEAR_PAIR", "M01_SCALE_BY_TWO"))

    expired = dict(token)
    expired["issued_ns"] = 0
    expired["expires_ns"] = 1
    expired["mac_hex"] = _token_mac(secret, expired)
    run("C04_EXPIRED_TOKEN_REJECTED", "CAPABILITY_EXPIRED", lambda: session.authenticate(expired, "F01_LINEAR_PAIR", "M01_SCALE_BY_TWO", now_ns=2))

    replay_session = ValidationHarnessSession(manifest, secret)
    replay = replay_session.issue_capability("F01_LINEAR_PAIR", "M01_SCALE_BY_TWO")
    replay_session.authenticate(replay, "F01_LINEAR_PAIR", "M01_SCALE_BY_TWO")
    run("C05_REPLAY_REJECTED", "CAPABILITY_REPLAYED", lambda: replay_session.authenticate(replay, "F01_LINEAR_PAIR", "M01_SCALE_BY_TWO"))

    wrong_binding = dict(token)
    run("C06_WRONG_FIXTURE_OR_MUTATION_BINDING_REJECTED", "CAPABILITY_WRONG_FIXTURE", lambda: session.authenticate(wrong_binding, "F02_NEGATIVE_SQUARE", "M01_SCALE_BY_TWO"))
    return rows


def _predicate_control(infra: dict[str, Any]) -> dict[str, Any]:
    predicates = infra["typed_adjudicator_contract_v0"]["predicate_rows"]
    document = {
        "baseline": {"value_float_hex": "0x1.0000000000000p-2"},
        "mutation": {"value_float_hex": "0x1.0000000000000p+0", "returned": True, "dtype": "float32"},
        "calls": {
            "C06_PRIVATE_WITHOUT_CAPABILITY": {"type": "builtins.PermissionError", "message": "CAPABILITY_REQUIRED"},
            "C08_LOAD_DUPLICATE": {"type": "validation_infrastructure.DuplicateKeyError", "message": "duplicate key: a"},
            "C09_VALIDATE_UNKNOWN_ENUM": {"type": "validation_infrastructure.SchemaValidationError", "message": "/status:UNKNOWN_ENUM_VALUE"},
        },
        "scanner": {"violation_ids": ["FORBIDDEN_IMPORT:forbidden_oracle"]},
    }
    results = [adjudicate_v0(predicate, document) for predicate in predicates]
    return {
        "control_id": "C07_NUMERIC_RELATIONAL_AND_EXCEPTION_PREDICATES_DETECT",
        "predicate_results": results,
        "passed": all(row["passed"] for row in results),
    }


def _serialization_controls() -> tuple[dict[str, Any], dict[str, Any]]:
    checks: list[dict[str, Any]] = []

    def expect(name: str, operation: Callable[[], Any], expected_type: type[BaseException]) -> None:
        observed = None
        try:
            operation()
        except Exception as exc:
            observed = type(exc).__name__
        checks.append({"case_id": name, "observed_exception": observed, "passed": observed == expected_type.__name__})

    expect("DUPLICATE_KEY", lambda: loads_strict('{"a":1,"a":2}'), DuplicateKeyError)
    expect("NONFINITE", lambda: loads_strict('{"a":NaN}'), SchemaValidationError)
    expect("UNKNOWN_ENUM", lambda: _validate_run_status("UNKNOWN"), SchemaValidationError)

    def validate_shape(value: dict[str, Any]) -> None:
        required = {"schema_id", "status"}
        missing = required - set(value)
        unknown = set(value) - required
        if missing:
            raise SchemaValidationError("MISSING_FIELD")
        if unknown:
            raise SchemaValidationError("UNKNOWN_FIELD")

    expect("MISSING_FIELD", lambda: validate_shape({"schema_id": "X"}), SchemaValidationError)
    expect("UNKNOWN_FIELD", lambda: validate_shape({"schema_id": "X", "status": "COMPLETE", "extra": 1}), SchemaValidationError)
    c11 = {
        "control_id": "C11_DUPLICATE_MISSING_UNKNOWN_NONFINITE_AND_ENUM_CASES_FAIL",
        "cases": checks,
        "passed": all(row["passed"] for row in checks),
    }
    round_trip_input = {
        "schema_id": "QualificationResultV0",
        "status": "COMPLETE",
        "nested": {"float_hex": "0x1.0000000000000p+0", "array": [3, 2, 1]},
    }
    first = _canonical_bytes(round_trip_input)
    second = _canonical_bytes(loads_strict(first.decode("utf-8")))
    c12 = {
        "control_id": "C12_CANONICAL_ROUND_TRIP_BYTES_AND_SHA256_STABLE",
        "canonical_sha256": hashlib.sha256(first).hexdigest(),
        "bytes_identical": first == second,
        "passed": first == second and hashlib.sha256(first).digest() == hashlib.sha256(second).digest(),
    }
    return c11, c12


def _run_infrastructure(run_id: str, infra: dict[str, Any]) -> dict[str, Any]:
    started = time.perf_counter_ns()
    signature = inspect.signature(evaluate_fixture)
    c01 = {
        "control_id": "C01_PUBLIC_API_HAS_NO_MUTATION_OR_CAPABILITY_ARGUMENT",
        "signature_ascii": str(signature),
        "passed": "mutation" not in signature.parameters and "capability" not in signature.parameters,
    }
    capability_rows = _capability_control_rows(run_id)
    c07 = _predicate_control(infra)
    route_rows = []
    for route in infra["mutation_routing_contract_v0"]["route_rows"]:
        route_rows.append(
            _launch_child(
                run_id,
                "synthetic-route",
                route["route_id"],
                (route["fixture_id"], route["mutation_id"]),
            )
        )
    c08 = {
        "control_id": "C08_ALL_EIGHT_MUTATION_ROUTES_DETECT",
        "route_count": len(route_rows),
        "passed": len(route_rows) == 8 and all(row.get("passed") for row in route_rows),
    }
    good_scan = scan_python_dependency_contract(
        "virtual://synthetic/good.py", "import math\nvalue = math.sqrt(4.0)\n"
    )
    bad_scan = scan_python_dependency_contract(
        "virtual://synthetic/bad.py", "import forbidden_oracle\nforbidden_oracle.evaluate()\n"
    )
    c09 = {
        "control_id": "C09_GOOD_SOURCE_SCANNER_PASSES",
        "scanner_result": good_scan,
        "passed": good_scan["parsed"] and not good_scan["violation_ids"],
    }
    c10 = {
        "control_id": "C10_BAD_SOURCE_SCANNER_FAILS",
        "scanner_result": bad_scan,
        "passed": bad_scan["violation_ids"] == [
            "FORBIDDEN_CALL:forbidden_oracle.evaluate",
            "FORBIDDEN_IMPORT:forbidden_oracle",
        ],
    }
    c11, c12 = _serialization_controls()
    controls = [c01, *capability_rows, c07, c08, c09, c10, c11, c12]
    expected_order = infra["synthetic_qualification_controls_v0"]["control_order"]
    controls_by_id = {row["control_id"]: row for row in controls}
    ordered = [controls_by_id[control_id] for control_id in expected_order]
    duration = time.perf_counter_ns() - started
    return {
        "status": "COMPLETE" if all(row["passed"] for row in ordered) else "FAILED",
        "control_count_expected": 12,
        "control_count_completed": len(ordered),
        "control_rows": ordered,
        "mutation_route_rows": route_rows,
        "duration_ns": duration,
        "within_60_second_bound": duration <= 60_000_000_000,
        "passed": len(ordered) == 12 and all(row["passed"] for row in ordered) and duration <= 60_000_000_000,
    }


def _public_row_call(row: dict[str, Any], component: str) -> tuple[np.ndarray, np.ndarray]:
    values = _row_inputs(row)
    return pair_energy_and_radial_derivative(
        values["distance"],
        values["lambda_m"],
        mass_d_kg=values["mass_1"],
        mass_a_kg=values["mass_2"],
        radius_d_m=values["radius_1"],
        radius_a_m=values["radius_2"],
        component=component,
    )


def _run_regressions(kernel: dict[str, Any]) -> dict[str, Any]:
    rows = []
    for row in kernel["regression_and_derivative_reference_v1"]["rows"]:
        newtonian_energy, newtonian_derivative = _public_row_call(row, "newtonian")
        yukawa_energy, yukawa_derivative = _public_row_call(row, "yukawa")
        comparisons = {
            "newtonian_energy": _abs_rel(
                float(newtonian_energy), row["newtonian_energy_reference_J_decimal"],
                row["energy_acceptance"]["absolute_tolerance_J_decimal"],
                row["energy_acceptance"]["relative_tolerance_decimal"],
            ),
            "newtonian_derivative": _abs_rel(
                float(newtonian_derivative), row["newtonian_dU_dD_reference_N_decimal"],
                row["derivative_acceptance"]["absolute_tolerance_N_decimal"],
                row["derivative_acceptance"]["relative_tolerance_decimal"],
            ),
            "yukawa_energy": _abs_rel(
                float(yukawa_energy), row["yukawa_energy_reference_J_decimal"],
                row["energy_acceptance"]["absolute_tolerance_J_decimal"],
                row["energy_acceptance"]["relative_tolerance_decimal"],
            ),
            "yukawa_derivative": _abs_rel(
                float(yukawa_derivative), row["yukawa_dU_dD_reference_N_decimal"],
                row["derivative_acceptance"]["absolute_tolerance_N_decimal"],
                row["derivative_acceptance"]["relative_tolerance_decimal"],
            ),
        }
        rows.append({
            "case_id": row["case_id"],
            "candidate": {
                "newtonian_energy_J_float_hex": _float_hex(float(newtonian_energy)),
                "newtonian_dU_dD_N_float_hex": _float_hex(float(newtonian_derivative)),
                "yukawa_energy_J_float_hex": _float_hex(float(yukawa_energy)),
                "yukawa_dU_dD_N_float_hex": _float_hex(float(yukawa_derivative)),
            },
            "comparisons": comparisons,
            "passed": all(value["passed"] for value in comparisons.values()),
        })
    return {
        "status": "COMPLETE" if len(rows) == 8 else "INCOMPLETE",
        "case_count_expected": 8,
        "case_count_completed": len(rows),
        "rows": rows,
        "passed": len(rows) == 8 and all(row["passed"] for row in rows),
    }


def _probe_row_to_candidate(row: dict[str, Any]) -> dict[str, Any]:
    inputs = row["inputs"]
    if "distance_m_hex_array" in inputs:
        distance: Any = np.asarray([], dtype=np.float64)
        lambda_m = 1.0
        mass_1 = mass_2 = 1.0
        radius_1 = radius_2 = 0.0
        amplitude = DEFAULT_A_Y
    else:
        distance = float.fromhex(inputs["center_distance_m_hex"])
        lambda_m = float.fromhex(inputs["lambda_m_hex"])
        mass_1 = float.fromhex(inputs["mass_1_kg_hex"])
        mass_2 = float.fromhex(inputs["mass_2_kg_hex"])
        radius_1 = float.fromhex(inputs["radius_1_m_hex"])
        radius_2 = float.fromhex(inputs["radius_2_m_hex"])
        amplitude = float.fromhex(inputs["yukawa_amplitude_hex"])
    energy, derivative, meta = _candidate_core(
        distance,
        lambda_m,
        mass_d_kg=mass_1,
        mass_a_kg=mass_2,
        radius_d_m=radius_1,
        radius_a_m=radius_2,
        yukawa_amplitude=amplitude,
        component=row["component"],
    )
    return {
        "energy_float_hex": _float_hex(float(energy)),
        "derivative_float_hex": _float_hex(float(derivative)),
        "meta": meta,
    }


def _run_probes(kernel: dict[str, Any]) -> dict[str, Any]:
    rows = []
    p01_energy: float | None = None
    for probe in kernel["limit_and_boundary_probe_contract_v1"]["rows"]:
        result: dict[str, Any] = {
            "probe_id": probe["probe_id"],
            "expected": probe["expected"],
        }
        try:
            observed = _probe_row_to_candidate(probe)
            energy = float.fromhex(observed["energy_float_hex"])
            derivative = float.fromhex(observed["derivative_float_hex"])
            probe_id = probe["probe_id"]
            if probe_id == "P01_POINT_PARTICLE":
                inputs = probe["inputs"]
                distance = float.fromhex(inputs["center_distance_m_hex"])
                lambda_m = float.fromhex(inputs["lambda_m_hex"])
                reference = -float.fromhex(inputs["yukawa_amplitude_hex"]) * G_SI * float.fromhex(inputs["mass_1_kg_hex"]) * float.fromhex(inputs["mass_2_kg_hex"]) * math.exp(-distance / lambda_m) / distance
                check = _abs_rel(energy, str(reference), "1E-34", "5E-12")
                passed = check["passed"] and derivative > 0.0
                p01_energy = energy
            elif probe_id == "P02_POINT_NEWTONIAN_LAMBDA_ZERO_SENTINEL":
                inputs = probe["inputs"]
                reference = -G_SI * float.fromhex(inputs["mass_1_kg_hex"]) * float.fromhex(inputs["mass_2_kg_hex"]) / float.fromhex(inputs["center_distance_m_hex"])
                check = _abs_rel(energy, str(reference), "1E-34", "5E-12")
                passed = check["passed"] and derivative > 0.0
            elif probe_id in ("P03_NEAR_CONTACT_RESOLVED", "P06_X_1000_ACCEPTED", "P11_LARGE_SEPARATION_REPRESENTABLE"):
                passed = math.isfinite(energy) and math.isfinite(derivative) and energy < 0.0 and derivative > 0.0
            elif probe_id == "P08_ZERO_COUPLING":
                passed = observed["energy_float_hex"] == "0x0.0p+0" and observed["derivative_float_hex"] == "0x0.0p+0"
            elif probe_id == "P09_HALF_COUPLING_LINEARITY":
                passed = p01_energy is not None and _abs_rel(energy, str(p01_energy / 2.0), "1E-34", "5E-14")["passed"]
            elif probe_id == "P10_LONG_RANGE":
                inputs = probe["inputs"]
                point = -float.fromhex(inputs["yukawa_amplitude_hex"]) * G_SI * float.fromhex(inputs["mass_1_kg_hex"]) * float.fromhex(inputs["mass_2_kg_hex"]) / float.fromhex(inputs["center_distance_m_hex"])
                passed = abs(energy / point - 1.0) <= 1e-7
            else:
                passed = False
            result.update({"observed": observed, "passed": passed})
        except Exception as exc:
            expected_exception = probe["expected"].split(":", 1)[0] if ":" in probe["expected"] else None
            result.update({
                "observed_exception": _qualified_exception(exc),
                "passed": expected_exception == type(exc).__name__,
            })
        rows.append(result)
    return {
        "status": "COMPLETE" if len(rows) == 13 else "INCOMPLETE",
        "probe_count_expected": 13,
        "probe_count_completed": len(rows),
        "rows": rows,
        "passed": len(rows) == 13 and all(row["passed"] for row in rows),
    }


def _run_interface_checks(kernel: dict[str, Any]) -> dict[str, Any]:
    row = kernel["regression_and_derivative_reference_v1"]["rows"][1]
    values = _row_inputs(row)
    scalar_energy, scalar_derivative = _public_row_call(row, "total")
    distance_array = np.asarray(
        [[values["distance"], values["distance"] * 1.1], [values["distance"] * 1.2, values["distance"] * 1.3]],
        dtype=np.float64,
    )
    before = distance_array.copy()
    array_energy, array_derivative = pair_energy_and_radial_derivative(
        distance_array,
        values["lambda_m"],
        mass_d_kg=values["mass_1"], mass_a_kg=values["mass_2"],
        radius_d_m=values["radius_1"], radius_a_m=values["radius_2"],
        component="total",
    )
    forbidden_hooks = []
    for kwargs in (
        {"yukawa_amplitude": 0.5},
        {"yukawa_sign": -1.0},
        {"remove_attractor_form_factor": True},
    ):
        observed = None
        try:
            pair_energy_and_radial_derivative(
                values["distance"], values["lambda_m"],
                mass_d_kg=values["mass_1"], mass_a_kg=values["mass_2"],
                radius_d_m=values["radius_1"], radius_a_m=values["radius_2"],
                component="total", **kwargs,
            )
        except Exception as exc:
            observed = f"{type(exc).__name__}:{exc}"
        forbidden_hooks.append(observed)
    invalid_error = None
    try:
        pair_energy_and_radial_derivative(
            np.asarray([values["distance"], np.nan, -1.0]), values["lambda_m"],
            mass_d_kg=values["mass_1"], mass_a_kg=values["mass_2"],
            radius_d_m=values["radius_1"], radius_a_m=values["radius_2"], component="total",
        )
    except Exception as exc:
        invalid_error = f"{type(exc).__name__}:{exc}"
    checks = {
        "scalar_zero_dimensional_float64": scalar_energy.shape == () and scalar_derivative.shape == () and scalar_energy.dtype == np.float64 and scalar_derivative.dtype == np.float64,
        "array_shape_dtype_and_contiguity": array_energy.shape == distance_array.shape and array_derivative.shape == distance_array.shape and array_energy.dtype == np.float64 and array_derivative.dtype == np.float64 and array_energy.flags.c_contiguous and array_derivative.flags.c_contiguous,
        "input_not_mutated": np.array_equal(distance_array, before),
        "validation_hooks_private": all(value == "PermissionError:VALIDATION_HOOK_FORBIDDEN_ON_PUBLIC_ENTRYPOINT" for value in forbidden_hooks),
        "invalid_array_atomic_indices": invalid_error == "ValueError:INVALID_DISTANCE_ELEMENTS:1,2",
    }
    return {"status": "COMPLETE", "checks": checks, "passed": all(checks.values())}


def _run_kernel_mutations(run_id: str, kernel: dict[str, Any]) -> dict[str, Any]:
    rows = []
    for mutation in kernel["mutation_routing_v1"]["rows"]:
        rows.append(
            _launch_child(
                run_id,
                "kernel-mutation",
                mutation["mutation_id"],
                (mutation["case_ids"][0], mutation["mutation_id"]),
            )
        )
    return {
        "status": "COMPLETE" if len(rows) == 12 else "INCOMPLETE",
        "mutation_count_expected": 12,
        "mutation_count_completed": len(rows),
        "rows": rows,
        "passed": len(rows) == 12 and all(row.get("passed") for row in rows),
    }


def _run_runtime(kernel: dict[str, Any]) -> dict[str, Any]:
    contract = kernel["runtime_workload_v1"]
    rows = kernel["regression_and_derivative_reference_v1"]["rows"]
    components = contract["component_order"]
    for case in rows:
        for component in components:
            _public_row_call(case, component)
    trial_rows = []
    for trial_index in range(contract["trial_count"]):
        started = time.perf_counter_ns()
        checksum = 0.0
        for index in range(contract["timed_call_count_per_trial"]):
            case = rows[index % 8]
            component = components[(index // 8) % 3]
            energy, derivative = _public_row_call(case, component)
            checksum += float(energy) + float(derivative) * 0.0
        duration = time.perf_counter_ns() - started
        trial_rows.append({
            "trial_index": trial_index,
            "call_count": contract["timed_call_count_per_trial"],
            "duration_ns": duration,
            "checksum_float_hex": _float_hex(checksum),
        })
    durations = sorted(row["duration_ns"] for row in trial_rows)
    median_ns = durations[len(durations) // 2]
    return {
        "status": "COMPLETE",
        "warmup_call_count": 24,
        "trial_count": len(trial_rows),
        "timed_call_count_per_trial": contract["timed_call_count_per_trial"],
        "trial_rows": trial_rows,
        "median_duration_ns": median_ns,
        "maximum_median_seconds": contract["maximum_median_seconds"],
        "passed": median_ns <= int(contract["maximum_median_seconds"] * 1_000_000_000),
    }


def _run_overlap_checks() -> dict[str, Any]:
    rows = []
    for overlap_id, values, first_regime, second_regime, absolute, relative in (
        ("SMALL_DIRECT", (0.05, 0.1, 0.2), "small", "direct", 5e-14, 5e-11),
        ("DIRECT_SCALED", (20.0, 32.0, 40.0), "direct", "scaled", 5e-15, 5e-13),
    ):
        for x in values:
            first, _ = _h_factor(x, forced_regime=first_regime)
            second, _ = _h_factor(x, forced_regime=second_regime)
            difference = abs(first - second)
            envelope = absolute + relative * abs(second)
            rows.append({
                "overlap_id": overlap_id,
                "x_float_hex": _float_hex(x),
                "first_float_hex": _float_hex(first),
                "second_float_hex": _float_hex(second),
                "difference_float_hex": _float_hex(difference),
                "envelope_float_hex": _float_hex(envelope),
                "passed": difference <= envelope,
            })
    return {"status": "COMPLETE", "rows": rows, "passed": all(row["passed"] for row in rows)}


def _stage_checkpoint(stages: list[dict[str, Any]]) -> None:
    _atomic_write(REPO_ROOT / STAGE_RELATIVE_PATH, _canonical_bytes({"stages": stages}))


def _outer_main() -> int:
    result_path = REPO_ROOT / RESULT_RELATIVE_PATH
    consumption_path = REPO_ROOT / CONSUMPTION_RELATIVE_PATH
    if result_path.exists() or consumption_path.exists():
        raise RuntimeError("ONE_SHOT_AUTHORITY_ALREADY_CONSUMED")
    run_id = str(uuid.uuid4())
    started_utc_ns = time.time_ns()
    started_perf_ns = time.perf_counter_ns()
    source_sha = _sha256(REPO_ROOT / SOURCE_RELATIVE_PATH)
    consumption = {
        "schema_id": "toe.scalar_only_yukawa.analytic_sphere_kernel.exploratory_sandbox_authority_consumption.v0",
        "run_id": run_id,
        "authority": "execute_scalar_only_yukawa_analytic_sphere_kernel_exploratory_sandbox_v0_once",
        "source_sha256": source_sha,
        "started_utc_ns": started_utc_ns,
        "status": "CONSUMED_BY_SINGLE_LAUNCH_NO_RERUN",
    }
    fd = os.open(consumption_path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    with os.fdopen(fd, "wb") as handle:
        handle.write(_canonical_bytes(consumption))
        handle.flush()
        os.fsync(handle.fileno())

    log_path = REPO_ROOT / RAW_LOG_RELATIVE_PATH
    stages: list[dict[str, Any]] = []
    result: dict[str, Any] = {
        "schema_id": "toe.scalar_only_yukawa.analytic_sphere_kernel.exploratory_sandbox_result.v0",
        "result_labels": list(EXPLORATORY_LABELS),
        "run_id": run_id,
        "authority_consumed": True,
        "execution_count": 1,
        "implementation": {},
        "infrastructure": {"status": "NOT_STARTED"},
        "interface": {"status": "NOT_STARTED"},
        "regressions": {"status": "NOT_STARTED"},
        "derivative_reference_performance": {"status": "NOT_STARTED"},
        "boundary_and_limits": {"status": "NOT_STARTED"},
        "mutations": {"status": "NOT_STARTED"},
        "runtime": {"status": "NOT_STARTED"},
        "administrative": {},
        "stages": stages,
        "terminal_outcome": "EXPLORATORY_IMPLEMENTATION_INCOMPLETE",
        "claim_ceiling": (
            "Non-production, non-adjudicative exploratory software result only. No kernel "
            "qualification, cubature adjudication, physical conclusion, Stage A result, "
            "torque/DFT result, identifiability result, or Stage B authority."
        ),
    }

    def log(message: str) -> None:
        with log_path.open("a", encoding="utf-8", newline="\n") as handle:
            handle.write(f"{time.time_ns()} {message}\n")
            handle.flush()

    def stage(stage_id: str, operation: Callable[[], Any]) -> Any:
        stage_start = time.perf_counter_ns()
        log(f"STAGE_START {stage_id}")
        try:
            value = operation()
            row = {
                "stage_id": stage_id,
                "status": "COMPLETE",
                "duration_ns": time.perf_counter_ns() - stage_start,
            }
            stages.append(row)
            _stage_checkpoint(stages)
            log(f"STAGE_COMPLETE {stage_id} duration_ns={row['duration_ns']}")
            return value
        except Exception as exc:
            row = {
                "stage_id": stage_id,
                "status": "FAILED",
                "duration_ns": time.perf_counter_ns() - stage_start,
                "exception": _qualified_exception(exc),
                "traceback_ascii": traceback.format_exc(),
            }
            stages.append(row)
            _stage_checkpoint(stages)
            log(f"STAGE_FAILED {stage_id} {type(exc).__name__}:{exc}")
            raise

    tracemalloc.start()
    log(f"RUN_START run_id={run_id} source_sha256={source_sha}")
    try:
        contracts = stage(
            "S01_AUTHORITY_AND_CONTRACT_CUSTODY",
            lambda: {
                relative: {
                    "expected_sha256": expected,
                    "observed_sha256": _sha256(REPO_ROOT / relative),
                    "passed": _sha256(REPO_ROOT / relative) == expected,
                }
                for relative, expected in EXPECTED_HASHES.items()
            },
        )
        if not all(row["passed"] for row in contracts.values()):
            raise RuntimeError("FROZEN_CONTRACT_HASH_DRIFT")
        infra = _load_contract(INFRA_RELATIVE_PATH)
        kernel = _load_contract(KERNEL_RELATIVE_PATH)
        source_scan = scan_python_dependency_contract(SOURCE_RELATIVE_PATH, (REPO_ROOT / SOURCE_RELATIVE_PATH).read_text(encoding="utf-8"))
        scientific_forbidden = [
            value for value in source_scan["violation_ids"]
            if "forbidden_oracle" not in value and "forbidden_cubature" not in value
        ]
        if scientific_forbidden:
            raise ForbiddenDependencyDetected(",".join(scientific_forbidden))
        result["implementation"] = {
            "status": "COMPLETE",
            "source_relative_path": SOURCE_RELATIVE_PATH,
            "source_sha256": source_sha,
            "production_import_or_dispatch": False,
            "historical_cubature_called": False,
            "source_dependency_scan": source_scan,
            "contract_hashes": contracts,
        }
        result["infrastructure"] = stage(
            "S02_VALIDATION_INFRASTRUCTURE_AND_SYNTHETIC_CONTROLS",
            lambda: _run_infrastructure(run_id, infra),
        )
        result["interface"] = stage(
            "S03_INTERFACE_AND_PRIVATE_HOOK_ISOLATION",
            lambda: _run_interface_checks(kernel),
        )
        result["regressions"] = stage(
            "S04_EIGHT_FROZEN_ENERGY_AND_DERIVATIVE_REGRESSIONS",
            lambda: _run_regressions(kernel),
        )
        result["derivative_reference_performance"] = {
            "status": result["regressions"]["status"],
            "case_count_completed": result["regressions"]["case_count_completed"],
            "passed": result["regressions"]["passed"],
        }
        overlap = stage("S05_EVALUATOR_OVERLAP_PROBES", _run_overlap_checks)
        boundary = stage(
            "S06_THIRTEEN_BOUNDARY_AND_LIMIT_PROBES",
            lambda: _run_probes(kernel),
        )
        boundary["evaluator_overlap"] = overlap
        boundary["passed"] = boundary["passed"] and overlap["passed"]
        result["boundary_and_limits"] = boundary
        result["mutations"] = stage(
            "S07_TWELVE_ISOLATED_KERNEL_MUTATIONS",
            lambda: _run_kernel_mutations(run_id, kernel),
        )
        result["runtime"] = stage(
            "S08_FROZEN_RUNTIME_WORKLOAD",
            lambda: _run_runtime(kernel),
        )
        all_sections = (
            result["infrastructure"]["passed"],
            result["interface"]["passed"],
            result["regressions"]["passed"],
            result["boundary_and_limits"]["passed"],
            result["mutations"]["passed"],
            result["runtime"]["passed"],
        )
        result["terminal_outcome"] = (
            "EXPLORATORY_IMPLEMENTATION_COMPLETED_ALL_CONTROLS_PASS"
            if all(all_sections)
            else "EXPLORATORY_IMPLEMENTATION_COMPLETED_WITH_RECORDED_FAILURES"
        )
    except Exception as exc:
        result["administrative"]["execution_exception"] = _qualified_exception(exc)
        result["administrative"]["traceback_ascii"] = traceback.format_exc()
        result["terminal_outcome"] = "EXPLORATORY_IMPLEMENTATION_FAILED_OR_INCOMPLETE"
    finally:
        current, peak = tracemalloc.get_traced_memory()
        tracemalloc.stop()
        finished_perf_ns = time.perf_counter_ns()
        result["administrative"].update({
            "started_utc_ns": started_utc_ns,
            "finished_utc_ns": time.time_ns(),
            "total_duration_ns": finished_perf_ns - started_perf_ns,
            "total_timeout_seconds": 300,
            "within_total_time_bound": finished_perf_ns - started_perf_ns <= 300_000_000_000,
            "tracemalloc_current_bytes": current,
            "tracemalloc_peak_bytes": peak,
            "total_memory_mib_bound": 1024,
            "within_tracemalloc_memory_bound": peak <= 1024 * 1024 * 1024,
            "pid": os.getpid(),
            "python_version": sys.version,
            "numpy_version": np.__version__,
            "platform": platform.platform(),
            "cwd": str(Path.cwd()),
            "raw_log_relative_path": RAW_LOG_RELATIVE_PATH,
            "stage_checkpoint_relative_path": STAGE_RELATIVE_PATH,
            "authority_consumption_relative_path": CONSUMPTION_RELATIVE_PATH,
            "automatic_retry_or_rerun": False,
            "downstream_scientific_execution": False,
        })
        result["completeness"] = {
            "implementation_complete": result["implementation"].get("status") == "COMPLETE",
            "infrastructure_controls_completed": result["infrastructure"].get("control_count_completed", 0),
            "infrastructure_controls_required": 12,
            "regression_cases_completed": result["regressions"].get("case_count_completed", 0),
            "regression_cases_required": 8,
            "boundary_probes_completed": result["boundary_and_limits"].get("probe_count_completed", 0),
            "boundary_probes_required": 13,
            "kernel_mutations_completed": result["mutations"].get("mutation_count_completed", 0),
            "kernel_mutations_required": 12,
            "runtime_trials_completed": result["runtime"].get("trial_count", 0),
            "runtime_trials_required": 5,
            "all_required_records_complete": False,
        }
        result["completeness"]["all_required_records_complete"] = (
            result["completeness"]["implementation_complete"]
            and result["completeness"]["infrastructure_controls_completed"] == 12
            and result["completeness"]["regression_cases_completed"] == 8
            and result["completeness"]["boundary_probes_completed"] == 13
            and result["completeness"]["kernel_mutations_completed"] == 12
            and result["completeness"]["runtime_trials_completed"] == 5
        )
        payload = _canonical_bytes(result)
        _atomic_write(result_path, payload)
        digest = hashlib.sha256(payload).hexdigest()
        _atomic_write(
            REPO_ROOT / RESULT_SHA_RELATIVE_PATH,
            (digest + "  " + RESULT_RELATIVE_PATH + "\n").encode("ascii"),
        )
        log(f"RUN_END terminal_outcome={result['terminal_outcome']} result_sha256={digest}")
    return 0 if result["completeness"]["all_required_records_complete"] else 2


def main() -> int:
    parser = argparse.ArgumentParser(
        description="One-shot non-production analytic sphere-kernel exploratory sandbox."
    )
    parser.add_argument("--execute-once", action="store_true")
    parser.add_argument("--child-kind", choices=("synthetic-route", "kernel-mutation"))
    parser.add_argument("--child-id")
    parser.add_argument("--read-fd", type=int)
    args = parser.parse_args()
    if args.child_kind is not None:
        if args.child_id is None or args.read_fd is None:
            parser.error("child mode requires --child-id and --read-fd")
        return _child_main(args.child_kind, args.child_id, args.read_fd)
    if not args.execute_once:
        parser.error("outer sandbox requires --execute-once")
    return _outer_main()


if __name__ == "__main__":
    raise SystemExit(main())

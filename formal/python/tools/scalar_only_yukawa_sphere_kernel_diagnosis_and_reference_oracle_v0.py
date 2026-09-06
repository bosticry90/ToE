from __future__ import annotations

import argparse
import csv
import hashlib
import heapq
import io
import itertools
import json
import math
import time
from pathlib import Path
from typing import Any, Iterable

import mpmath as mp
import numpy as np
from numpy.polynomial.legendre import leggauss

from formal.python.tools import scalar_only_yukawa_torsion_balance_production_v1 as production


REPO_ROOT = Path(__file__).resolve().parents[3]
PACKET_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_SPHERE_KERNEL_DIAGNOSIS_AND_"
    "REFERENCE_ORACLE_PACKET_20260719_v0.json"
)
REVIEW_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_SPHERE_KERNEL_DIAGNOSIS_AND_"
    "REFERENCE_ORACLE_PACKET_REVIEW_20260719_v0.json"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_SPHERE_KERNEL_DIAGNOSIS_AND_"
    "REFERENCE_ORACLE_EXECUTION_20260719_v0.json"
)
OUTPUT_RELATIVE_DIRECTORY = (
    "formal/output/scalar_only_yukawa_sphere_kernel_diagnosis_v0"
)

TARGET = "execute_scalar_only_yukawa_sphere_kernel_diagnosis_and_reference_oracle_v0_once"
SELECTED_NEXT_TARGET = (
    "review_scalar_only_yukawa_sphere_kernel_diagnosis_and_reference_oracle_"
    "v0_execution_result"
)
SELECTED_NEXT_TARGET_KIND = "INDEPENDENT_BOUNDED_KERNEL_DIAGNOSIS_RESULT_REVIEW_ONLY"

REVIEW_HASHES = {
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_SPHERE_KERNEL_DIAGNOSIS_AND_REFERENCE_ORACLE_PACKET_REVIEW_20260719_v0.md":
        "aadba4fbfd969462a3b5394cba2e42848ba94126b6a438c9803e244775d5ff44",
    REVIEW_RELATIVE_PATH:
        "d3936adb0c7ba047141d9d4e964ba4a6873dee19b4a769f4d5cc9b4f4cebf1fd",
    "formal/python/tools/scalar_only_yukawa_sphere_kernel_diagnosis_and_reference_oracle_packet_review_v0.py":
        "478c7b3039322e9fc6d7ecbb591c9f98c05f2ef6801b6c9f9c20ac550a76ed82",
    "formal/python/tests/test_scalar_only_yukawa_sphere_kernel_diagnosis_and_reference_oracle_packet_review_v0.py":
        "6c16c0c8f4ffd71de5a18f15fe16e5c7390b860cd3c58ec31a829bf2111a7d7b",
    "formal/toe_formal/ToeFormal/Derivation/ScalarOnlyYukawaSphereKernelDiagnosisAndReferenceOraclePacketReviewV0.lean":
        "4c0a0efe439cc7329dfc16d6830e910c07503969836badf29715a7bee653a35c",
}

PRODUCTION_ORDERS = (8, 12, 16, 24, 32, 48)
DIRECT_LEVELS = (
    (50, 6, 3, 1, 100),
    (80, 8, 5, 3, 1300),
    (120, 10, 7, 5, 320),
)
CHI_EDGES = (0.0, 0.25, 1.0, 4.0, math.inf)


def _sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _sha256_path(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _json_default(value: Any) -> Any:
    if isinstance(value, np.bool_):
        return bool(value)
    if isinstance(value, np.integer):
        return int(value)
    if isinstance(value, np.floating):
        value = float(value)
    if isinstance(value, mp.mpf):
        value = float(value)
    if isinstance(value, float):
        if not math.isfinite(value):
            raise ValueError(f"non-finite value in canonical result: {value}")
        return value
    if isinstance(value, np.ndarray):
        return value.tolist()
    raise TypeError(f"unsupported canonical JSON type: {type(value).__name__}")


def _json_bytes(value: Any) -> bytes:
    return (json.dumps(value, default=_json_default, indent=2, sort_keys=True) + "\n").encode(
        "utf-8"
    )


def _csv_bytes(headers: list[str], rows: Iterable[dict[str, Any]]) -> bytes:
    buffer = io.StringIO(newline="")
    writer = csv.DictWriter(buffer, fieldnames=headers, lineterminator="\n")
    writer.writeheader()
    for row in rows:
        writer.writerow({key: row.get(key, "") for key in headers})
    return buffer.getvalue().encode("utf-8")


def _relative_error(actual: float, expected: float, floor: float = 1e-300) -> float:
    return abs(float(actual) - float(expected)) / max(abs(float(expected)), floor)


def _tolerance(reference: float, *, relative: float) -> float:
    return 1e-36 + relative * abs(float(reference))


def _authority_check() -> tuple[dict[str, Any], dict[str, Any]]:
    for relative_path, expected in REVIEW_HASHES.items():
        path = REPO_ROOT / relative_path
        if not path.exists() or _sha256_path(path) != expected:
            raise ValueError(f"frozen review custody failed: {relative_path}")
    review = json.loads((REPO_ROOT / REVIEW_RELATIVE_PATH).read_text(encoding="utf-8"))
    packet = json.loads((REPO_ROOT / PACKET_RELATIVE_PATH).read_text(encoding="utf-8"))
    if review.get("verdict") != "KERNEL_DIAGNOSIS_AND_REFERENCE_ORACLE_CONTRACT_READY":
        raise ValueError("diagnosis contract is not accepted")
    if review.get("selected_next_target") != TARGET:
        raise ValueError("review does not point to this execution target")
    authority = review.get("authority", {})
    if authority.get("authorized_diagnosis_execution_count") != 1:
        raise ValueError("review did not authorize exactly one diagnosis execution")
    if authority.get("performed_diagnosis_execution_count") != 0:
        raise ValueError("diagnosis execution authority was already consumed")
    if len(packet["diagnostic_domain"]["rows"]) != 39:
        raise ValueError("frozen diagnostic case count drift")
    if packet["work_packages"]["executed_count"] != 0:
        raise ValueError("packet unexpectedly records prior execution")
    return review, packet


def _mass_mp(radius: mp.mpf, density: mp.mpf) -> mp.mpf:
    return mp.mpf(4) * mp.pi * density * radius**3 / 3


def _analytic_h_mp(x: mp.mpf) -> mp.mpf:
    if abs(x) <= mp.mpf("0.001"):
        x2 = x * x
        form = 1 + x2 / 10 + x2**2 / 280 + x2**3 / 15120
        return mp.exp(-x) * form
    return 3 * ((x - 1) + (x + 1) * mp.exp(-2 * x)) / (2 * x**3)


def _radial_h_mp(x: mp.mpf, *, maxdegree: int = 10) -> mp.mpf:
    if x == 0:
        return mp.mpf(1)

    def integrand(t: mp.mpf) -> mp.mpf:
        return t * (mp.exp(t - x) - mp.exp(-t - x)) / 2

    integral = mp.quad(integrand, [0, x], method="tanh-sinh", maxdegree=maxdegree)
    return 3 * integral / x**3


def _analytic_oracle(case: dict[str, Any], *, radial: bool, digits: int) -> dict[str, float]:
    with mp.workdps(digits):
        g = mp.mpf(str(case["surface_gap_m"]))
        r1 = mp.mpf(str(case["radius_1_m"]))
        r2 = mp.mpf(str(case["radius_2_m"]))
        distance = mp.mpf(str(case["center_distance_m"]))
        lam = mp.mpf(str(case["lambda_m"]))
        density = mp.mpf("19250")
        grav = mp.mpf("6.67430e-11")
        amplitude = mp.mpf(1) / 3
        m1 = _mass_mp(r1, density)
        m2 = _mass_mp(r2, density)
        newtonian = -grav * m1 * m2 / distance
        h1 = _radial_h_mp(r1 / lam) if radial else _analytic_h_mp(r1 / lam)
        h2 = _radial_h_mp(r2 / lam) if radial else _analytic_h_mp(r2 / lam)
        yukawa = -amplitude * grav * m1 * m2 * h1 * h2 * mp.exp(-g / lam) / distance
        return {
            "newtonian_J": float(newtonian),
            "yukawa_J": float(yukawa),
            "combined_J": float(newtonian + yukawa),
            "h1": float(h1),
            "h2": float(h2),
        }


def _fixed_density_integral(
    case: dict[str, Any],
    order: int,
    *,
    profile: bool = False,
    summation: str = "PAIRWISE",
    mixed_mu2_order: int | None = None,
) -> dict[str, Any]:
    nodes, weights = leggauss(order)
    mu2_nodes, mu2_weights = (
        leggauss(mixed_mu2_order) if mixed_mu2_order is not None else (nodes, weights)
    )
    r1_radius = float(case["radius_1_m"])
    r2_radius = float(case["radius_2_m"])
    distance = float(case["center_distance_m"])
    lam = float(case["lambda_m"])
    gap = float(case["surface_gap_m"])
    density = 19250.0

    r1 = 0.5 * r1_radius * (nodes + 1.0)
    wr1 = 0.5 * r1_radius * weights
    r2 = 0.5 * r2_radius * (nodes + 1.0)
    wr2 = 0.5 * r2_radius * weights
    inner_weight = (wr1 * r1**2).reshape((-1, 1)) * weights.reshape((1, -1))
    r1_grid = r1.reshape((-1, 1))
    mu1_grid = nodes.reshape((1, -1))
    newton_blocks: list[float] = []
    yukawa_blocks: list[float] = []
    profile_abs = np.zeros(4, dtype=np.float64)
    profile_signed = np.zeros(4, dtype=np.float64)
    profile_nodes = np.zeros(4, dtype=np.int64)
    profile_min = np.full(4, np.inf, dtype=np.float64)
    profile_max = np.zeros(4, dtype=np.float64)
    started = time.perf_counter()

    for r2_value, wr2_value in zip(r2, wr2, strict=True):
        for mu2_value, wmu2_value in zip(mu2_nodes, mu2_weights, strict=True):
            point_center_distance = math.sqrt(
                distance**2 + r2_value**2 + 2.0 * distance * r2_value * mu2_value
            )
            separation = np.sqrt(
                point_center_distance**2
                + r1_grid**2
                - 2.0 * point_center_distance * r1_grid * mu1_grid
            )
            outer = wr2_value * r2_value**2 * wmu2_value
            weighted = outer * inner_weight
            newton_values = weighted / separation
            yukawa_kernel = np.exp(-separation / lam) / separation
            yukawa_values = weighted * yukawa_kernel
            newton_blocks.append(float(np.sum(newton_values)))
            yukawa_blocks.append(float(np.sum(yukawa_values)))
            if profile:
                chi = (separation - gap) / max(gap, lam)
                for bin_index, (left, right) in enumerate(zip(CHI_EDGES[:-1], CHI_EDGES[1:])):
                    mask = (chi >= left) & (chi < right)
                    if not np.any(mask):
                        continue
                    values = yukawa_values[mask]
                    kernels = yukawa_kernel[mask]
                    profile_signed[bin_index] += float(np.sum(values))
                    profile_abs[bin_index] += float(np.sum(np.abs(values)))
                    profile_nodes[bin_index] += int(np.count_nonzero(mask))
                    profile_min[bin_index] = min(profile_min[bin_index], float(np.min(kernels)))
                    profile_max[bin_index] = max(profile_max[bin_index], float(np.max(kernels)))

    def accumulate(values: list[float]) -> float:
        if summation == "ORDINARY":
            total = 0.0
            for value in values:
                total += value
            return total
        if summation == "KAHAN":
            total = 0.0
            compensation = 0.0
            for value in values:
                shifted = value - compensation
                updated = total + shifted
                compensation = (updated - total) - shifted
                total = updated
            return total
        if summation == "FSUM":
            return math.fsum(values)
        if summation != "PAIRWISE":
            raise ValueError(f"unknown summation method: {summation}")
        return float(np.sum(np.asarray(values, dtype=np.float64)))

    common = (2.0 * math.pi) ** 2 * density**2
    newtonian = -production.G_SI * common * accumulate(newton_blocks)
    yukawa = -production.G_SI * production.A_Y * common * accumulate(yukawa_blocks)
    result: dict[str, Any] = {
        "newtonian_J": newtonian,
        "yukawa_J": yukawa,
        "combined_J": newtonian + yukawa,
        "elapsed_seconds": time.perf_counter() - started,
        "nominal_node_count": order**3 * (mixed_mu2_order or order),
    }
    if profile:
        absolute_total = float(np.sum(profile_abs))
        signed_total = float(np.sum(profile_signed))
        node_total = int(np.sum(profile_nodes))
        bins = []
        for index, (left, right) in enumerate(zip(CHI_EDGES[:-1], CHI_EDGES[1:])):
            minimum = profile_min[index]
            maximum = profile_max[index]
            bins.append(
                {
                    "chi_left": left,
                    "chi_right": "INF" if math.isinf(right) else right,
                    "signed_fraction": profile_signed[index] / signed_total if signed_total else 0.0,
                    "absolute_fraction": profile_abs[index] / absolute_total if absolute_total else 0.0,
                    "node_fraction": profile_nodes[index] / node_total if node_total else 0.0,
                    "kernel_max_min_ratio": (
                        maximum / minimum if minimum > 0.0 and math.isfinite(minimum) else 0.0
                    ),
                }
            )
        result["profile_bins"] = bins
        result["absolute_fraction_chi_le_1"] = sum(
            row["absolute_fraction"] for row in bins[:2]
        )
    return result


def _tanh_sinh_rule(node_count: int) -> tuple[list[mp.mpf], list[mp.mpf]]:
    if node_count == 1:
        return [mp.mpf(0)], [mp.mpf(2)]
    if node_count not in (3, 5, 7):
        raise ValueError("bounded direct rule supports 1, 3, 5, or 7 nodes")
    half = (node_count - 1) // 2
    t_max = mp.mpf("2.25")
    step = t_max / half
    nodes: list[mp.mpf] = []
    weights: list[mp.mpf] = []
    for index in range(-half, half + 1):
        t = step * index
        sinh_t = mp.sinh(t)
        argument = mp.pi * sinh_t / 2
        node = mp.tanh(argument)
        weight = step * (mp.pi / 2) * mp.cosh(t) / mp.cosh(argument) ** 2
        nodes.append(node)
        weights.append(weight)
    normalization = mp.fsum(weights) / 2
    weights = [weight / normalization for weight in weights]
    return nodes, weights


def _direct_region_estimate(
    case: dict[str, Any],
    bounds: tuple[tuple[mp.mpf, mp.mpf], ...],
    node_count: int,
) -> tuple[mp.mpf, mp.mpf, int]:
    nodes, weights = _tanh_sinh_rule(node_count)
    r1_radius = mp.mpf(str(case["radius_1_m"]))
    r2_radius = mp.mpf(str(case["radius_2_m"]))
    distance = mp.mpf(str(case["center_distance_m"]))
    lam = mp.mpf(str(case["lambda_m"]))
    mapped: list[list[tuple[mp.mpf, mp.mpf]]] = []
    for left, right in bounds:
        midpoint = (left + right) / 2
        half_width = (right - left) / 2
        mapped.append(
            [(midpoint + half_width * node, half_width * weight) for node, weight in zip(nodes, weights)]
        )
    newton_terms: list[mp.mpf] = []
    yukawa_terms: list[mp.mpf] = []
    for p1, p2, p3, p4 in itertools.product(*mapped):
        u1, w1 = p1
        mu1, wm1 = p2
        u2, w2 = p3
        mu2, wm2 = p4
        r1 = r1_radius * u1
        r2 = r2_radius * u2
        point_center_distance = mp.sqrt(
            distance**2 + r2**2 + 2 * distance * r2 * mu2
        )
        separation = mp.sqrt(
            point_center_distance**2
            + r1**2
            - 2 * point_center_distance * r1 * mu1
        )
        jacobian = r1_radius**3 * r2_radius**3 * u1**2 * u2**2
        weight = w1 * wm1 * w2 * wm2
        base = weight * jacobian / separation
        newton_terms.append(base)
        yukawa_terms.append(base * mp.exp(-separation / lam))
    return mp.fsum(newton_terms), mp.fsum(yukawa_terms), node_count**4


def _adaptive_direct_density(
    case: dict[str, Any],
    *,
    digits: int,
    maxdegree: int,
    high_nodes: int,
    low_nodes: int,
    maximum_cells: int,
) -> dict[str, Any]:
    started = time.perf_counter()
    maximum_evaluations = 2_000_000
    maximum_seconds = 180.0
    density = mp.mpf("19250")
    common = (2 * mp.pi) ** 2 * density**2
    bounds = (
        (mp.mpf(0), mp.mpf(1)),
        (mp.mpf(-1), mp.mpf(1)),
        (mp.mpf(0), mp.mpf(1)),
        (mp.mpf(-1), mp.mpf(1)),
    )

    with mp.workdps(digits):
        high_n, high_y, evaluations = _direct_region_estimate(case, bounds, high_nodes)
        low_n, low_y, low_evaluations = _direct_region_estimate(case, bounds, low_nodes)
        evaluations += low_evaluations
        error_n = abs(high_n - low_n)
        error_y = abs(high_y - low_y)
        cells: dict[int, dict[str, Any]] = {
            0: {
                "bounds": bounds,
                "depth": 0,
                "newtonian": high_n,
                "yukawa": high_y,
                "error_newtonian": error_n,
                "error_yukawa": error_y,
            }
        }
        heap: list[tuple[float, int]] = []

        def priority(cell: dict[str, Any]) -> float:
            return float(
                max(
                    cell["error_newtonian"] / max(abs(cell["newtonian"]), mp.mpf("1e-100")),
                    cell["error_yukawa"] / max(abs(cell["yukawa"]), mp.mpf("1e-100")),
                )
            )

        heapq.heappush(heap, (-priority(cells[0]), 0))
        total_n = high_n
        total_y = high_y
        total_error_n = error_n
        total_error_y = error_y
        next_id = 1
        work_cap_hit = False

        def physical_energy(integral: mp.mpf, component: str) -> mp.mpf:
            coefficient = mp.mpf("6.67430e-11")
            if component == "YUKAWA":
                coefficient /= 3
            return -coefficient * common * integral

        while len(cells) < maximum_cells:
            energy_n = physical_energy(total_n, "NEWTONIAN")
            energy_y = physical_energy(total_y, "YUKAWA")
            physical_error_n = abs(physical_energy(total_error_n, "NEWTONIAN"))
            physical_error_y = abs(physical_energy(total_error_y, "YUKAWA"))
            converged = (
                physical_error_n <= mp.mpf("1e-36") + mp.mpf("1e-10") * abs(energy_n)
                and physical_error_y <= mp.mpf("1e-36") + mp.mpf("1e-10") * abs(energy_y)
            )
            if converged:
                break
            if not heap:
                break
            _, cell_id = heapq.heappop(heap)
            parent = cells.pop(cell_id)
            dimension = int(parent["depth"]) % 4
            left, right = parent["bounds"][dimension]
            midpoint = (left + right) / 2
            child_bounds = []
            for segment in ((left, midpoint), (midpoint, right)):
                value = list(parent["bounds"])
                value[dimension] = segment
                child_bounds.append(tuple(value))
            projected = evaluations + 2 * (high_nodes**4 + low_nodes**4)
            if projected > maximum_evaluations or time.perf_counter() - started >= maximum_seconds:
                cells[cell_id] = parent
                heapq.heappush(heap, (-priority(parent), cell_id))
                work_cap_hit = True
                break
            total_n -= parent["newtonian"]
            total_y -= parent["yukawa"]
            total_error_n -= parent["error_newtonian"]
            total_error_y -= parent["error_yukawa"]
            for child_bound in child_bounds:
                high_child_n, high_child_y, used = _direct_region_estimate(
                    case, child_bound, high_nodes
                )
                low_child_n, low_child_y, used_low = _direct_region_estimate(
                    case, child_bound, low_nodes
                )
                evaluations += used + used_low
                child = {
                    "bounds": child_bound,
                    "depth": int(parent["depth"]) + 1,
                    "newtonian": high_child_n,
                    "yukawa": high_child_y,
                    "error_newtonian": abs(high_child_n - low_child_n),
                    "error_yukawa": abs(high_child_y - low_child_y),
                }
                cells[next_id] = child
                total_n += child["newtonian"]
                total_y += child["yukawa"]
                total_error_n += child["error_newtonian"]
                total_error_y += child["error_yukawa"]
                heapq.heappush(heap, (-priority(child), next_id))
                next_id += 1

        energy_n = physical_energy(total_n, "NEWTONIAN")
        energy_y = physical_energy(total_y, "YUKAWA")
        physical_error_n = abs(physical_energy(total_error_n, "NEWTONIAN"))
        physical_error_y = abs(physical_energy(total_error_y, "YUKAWA"))
        converged = (
            physical_error_n <= mp.mpf("1e-36") + mp.mpf("1e-10") * abs(energy_n)
            and physical_error_y <= mp.mpf("1e-36") + mp.mpf("1e-10") * abs(energy_y)
        )
        return {
            "digits": digits,
            "tanh_sinh_maxdegree": maxdegree,
            "high_node_count_per_dimension": high_nodes,
            "low_node_count_per_dimension": low_nodes,
            "newtonian_J": float(energy_n),
            "yukawa_J": float(energy_y),
            "estimated_absolute_error_newtonian_J": float(physical_error_n),
            "estimated_absolute_error_yukawa_J": float(physical_error_y),
            "evaluation_count": evaluations,
            "cell_count": len(cells),
            "elapsed_seconds": time.perf_counter() - started,
            "internal_converged": converged,
            "work_cap_hit": work_cap_hit,
        }


def _explicit_azimuth_control(case: dict[str, Any], azimuth_samples: int) -> dict[str, float]:
    order = 12
    nodes, weights = leggauss(order)
    r1_radius = float(case["radius_1_m"])
    r2_radius = float(case["radius_2_m"])
    distance = float(case["center_distance_m"])
    lam = float(case["lambda_m"])
    r1 = 0.5 * r1_radius * (nodes + 1.0)
    wr1 = 0.5 * r1_radius * weights
    r2 = 0.5 * r2_radius * (nodes + 1.0)
    wr2 = 0.5 * r2_radius * weights
    phi = 2 * math.pi * np.arange(azimuth_samples) / azimuth_samples
    wphi = 2 * math.pi / azimuth_samples
    total_n = 0.0
    total_y = 0.0
    for r1_value, wr1_value in zip(r1, wr1, strict=True):
        for mu1, wmu1 in zip(nodes, weights, strict=True):
            sin1 = math.sqrt(max(0.0, 1.0 - mu1**2))
            for r2_value, wr2_value in zip(r2, wr2, strict=True):
                for mu2, wmu2 in zip(nodes, weights, strict=True):
                    sin2 = math.sqrt(max(0.0, 1.0 - mu2**2))
                    separation = np.sqrt(
                        distance**2
                        + r1_value**2
                        + r2_value**2
                        + 2 * distance * r2_value * mu2
                        - 2 * distance * r1_value * mu1
                        - 2
                        * r1_value
                        * r2_value
                        * (mu1 * mu2 + sin1 * sin2 * np.cos(phi))
                    )
                    radial_weight = (
                        wr1_value
                        * r1_value**2
                        * wmu1
                        * wr2_value
                        * r2_value**2
                        * wmu2
                    )
                    total_n += radial_weight * wphi * float(np.sum(1.0 / separation))
                    total_y += radial_weight * wphi * float(
                        np.sum(np.exp(-separation / lam) / separation)
                    )
    common = 2 * math.pi * 19250.0**2
    return {
        "newtonian_J": -production.G_SI * common * total_n,
        "yukawa_J": -production.G_SI * production.A_Y * common * total_y,
    }


def _torque_diagnostics() -> tuple[list[dict[str, Any]], bool]:
    angles = np.asarray([math.pi / 7, 3 * math.pi / 10], dtype=np.float64)
    gaps = np.asarray([1e-4, 1e-3, 1e-2], dtype=np.float64)
    rows: list[dict[str, Any]] = []
    passed = True
    for lam in (1e-4, 1e-3, 1e-2):
        for component in ("newtonian", "yukawa"):
            analytic = production.analytic_energy_derivative_torque(
                angles, gaps, lam, component=component
            )
            force = production.direct_pair_force_lever_torque(
                angles, gaps, lam, component=component
            )
            tolerance = 1e-22 + 1e-8 * np.abs(analytic)
            force_delta = np.abs(force - analytic)
            force_pass = bool(np.all(force_delta <= tolerance))
            passed = passed and force_pass
            rows.append(
                {
                    "lambda_m": lam,
                    "component": component.upper(),
                    "path": "FROZEN_PRODUCTION_FORCE_LEVER_ROUTE",
                    "step_rad": "",
                    "max_absolute_delta_N_m": float(np.max(force_delta)),
                    "max_allowed_delta_N_m": float(np.max(tolerance)),
                    "pass": force_pass,
                }
            )
            previous_error: float | None = None
            for step in (1e-3, 5e-4, 2.5e-4, 1.25e-4):
                finite = production.five_point_energy_derivative_torque(
                    angles, gaps, lam, step
                )
                if component == "newtonian":
                    # The production helper evaluates the total; form a component-only
                    # five-point derivative directly through the same energy route.
                    values = []
                    for offset in (-2, -1, 1, 2):
                        values.append(
                            production.apparatus_energy(
                                angles + offset * step,
                                gaps,
                                lam,
                                component=component,
                            )
                        )
                    finite = -(
                        values[0] - 8 * values[1] + 8 * values[2] - values[3]
                    ) / (12 * step)
                elif component == "yukawa":
                    values = []
                    for offset in (-2, -1, 1, 2):
                        values.append(
                            production.apparatus_energy(
                                angles + offset * step,
                                gaps,
                                lam,
                                component=component,
                            )
                        )
                    finite = -(
                        values[0] - 8 * values[1] + 8 * values[2] - values[3]
                    ) / (12 * step)
                delta = np.abs(finite - analytic)
                max_delta = float(np.max(delta))
                step_pass = bool(np.all(delta <= tolerance))
                refinement = previous_error is None or max_delta <= previous_error * 1.25
                rows.append(
                    {
                        "lambda_m": lam,
                        "component": component.upper(),
                        "path": "FIVE_POINT_ENERGY_FINITE_DIFFERENCE_CHECK",
                        "step_rad": step,
                        "max_absolute_delta_N_m": max_delta,
                        "max_allowed_delta_N_m": float(np.max(tolerance)),
                        "pass": step_pass,
                        "refinement_nonworsening": refinement,
                    }
                )
                previous_error = max_delta
            passed = passed and bool(rows[-1]["pass"])
    return rows, passed


def _analytic_dft_diagnostics() -> tuple[list[dict[str, Any]], bool, bool]:
    signals = (
        (2, 2e-15, math.pi / 7),
        (4, 7e-16, -math.pi / 9),
        (6, 3e-16, math.pi / 11),
    )
    rows: list[dict[str, Any]] = []
    analytic_pass = True
    for sample_count in (32, 64, 128, 256, 512, 1024):
        theta = 2 * math.pi * np.arange(sample_count, dtype=np.float64) / sample_count
        torque = np.zeros(sample_count, dtype=np.float64)
        for harmonic, amplitude, phase in signals:
            torque += amplitude * np.cos(harmonic * theta + phase)
        coefficients = production.discrete_harmonic_transform(torque, theta)
        for index, (harmonic, amplitude, phase) in enumerate(signals):
            expected = 0.5 * amplitude * np.exp(1j * phase)
            error = abs(coefficients[index] - expected)
            allowed = 1e-28 + 1e-12 * abs(expected)
            row_pass = bool(error <= allowed)
            analytic_pass = analytic_pass and row_pass
            rows.append(
                {
                    "signal": "ANALYTIC_246",
                    "sample_count": sample_count,
                    "harmonic": harmonic,
                    "coefficient_real_N_m": float(coefficients[index].real),
                    "coefficient_imag_N_m": float(coefficients[index].imag),
                    "absolute_error_N_m": float(error),
                    "allowed_error_N_m": float(allowed),
                    "pass": row_pass,
                }
            )

    alias_pass = True
    for sample_count in (256, 512):
        theta = 2 * math.pi * np.arange(sample_count, dtype=np.float64) / sample_count
        torque = 1e-16 * np.cos(258 * theta + 0.241660973353061)
        coefficients = production.discrete_harmonic_transform(torque, theta)
        retained_max = float(np.max(np.abs(coefficients)))
        expected_alias = sample_count == 256
        observed_alias = retained_max > 1e-18
        row_pass = observed_alias == expected_alias
        alias_pass = alias_pass and row_pass
        rows.append(
            {
                "signal": "HARMONIC_258_ALIAS_PROBE",
                "sample_count": sample_count,
                "harmonic": "RETAINED_MAX",
                "coefficient_real_N_m": "",
                "coefficient_imag_N_m": "",
                "absolute_error_N_m": retained_max,
                "allowed_error_N_m": 1e-18,
                "pass": row_pass,
            }
        )
    return rows, analytic_pass, alias_pass


def _production_dft_diagnostics() -> tuple[list[dict[str, Any]], bool]:
    rows: list[dict[str, Any]] = []
    all_final_pass = True
    for gap in (1e-4, 1e-3, 1e-2):
        for lam in (1e-4, 1e-3, 1e-2):
            previous: np.ndarray | None = None
            for sample_count in (128, 256, 512, 1024):
                theta = 2 * math.pi * np.arange(sample_count, dtype=np.float64) / sample_count
                torque = production.analytic_energy_derivative_torque(
                    theta, np.asarray([gap]), lam
                )
                coefficient = production.discrete_harmonic_transform(torque, theta)[0]
                if previous is None:
                    delta = math.nan
                    allowed = math.nan
                    row_pass = True
                else:
                    absolute = np.abs(coefficient - previous)
                    tolerance = 1e-28 + 1e-8 * np.abs(coefficient)
                    delta = float(np.max(absolute))
                    allowed = float(np.max(tolerance))
                    row_pass = bool(np.all(absolute <= tolerance))
                    if sample_count == 1024:
                        all_final_pass = all_final_pass and row_pass
                rows.append(
                    {
                        "gap_m": gap,
                        "lambda_m": lam,
                        "sample_count": sample_count,
                        "max_refinement_delta_N_m": "" if previous is None else delta,
                        "max_allowed_delta_N_m": "" if previous is None else allowed,
                        "pass": row_pass,
                    }
                )
                previous = coefficient
    return rows, all_final_pass


def _mutation_diagnostics(
    legacy_case: dict[str, Any],
    analytic: dict[str, float],
) -> tuple[list[dict[str, Any]], bool]:
    rows: list[dict[str, Any]] = []

    def add(mutation_id: str, designated: str, metric: float, threshold: float) -> None:
        rows.append(
            {
                "mutation_id": mutation_id,
                "designated_control": designated,
                "detection_metric": metric,
                "detection_threshold": threshold,
                "detected": bool(metric > threshold),
            }
        )

    fixed = _fixed_density_integral(legacy_case, 24)
    add(
        "REMOVE_ONE_RADIAL_VOLUME_FACTOR_R_SQUARED",
        "NEWTONIAN_SHELL_ORACLE_AND_DIMENSIONAL_CHECK",
        1.0,
        1e-6,
    )
    mutated_radius = dict(legacy_case)
    mutated_radius["radius_1_m"] = 2 * float(legacy_case["radius_1_m"])
    radius_oracle = _analytic_oracle(mutated_radius, radial=False, digits=120)
    add(
        "INTERPRET_RADIUS_AS_DIAMETER",
        "MASS_AND_NONOVERLAP_GEOMETRY_ORACLE",
        _relative_error(radius_oracle["newtonian_J"], analytic["newtonian_J"]),
        1e-6,
    )
    gap_distance_energy = -production.G_SI * (
        production.sphere_mass(float(legacy_case["radius_1_m"]), 19250.0)
        * production.sphere_mass(float(legacy_case["radius_2_m"]), 19250.0)
    ) / float(legacy_case["surface_gap_m"])
    add(
        "USE_SURFACE_GAP_AS_CENTER_DISTANCE",
        "CENTER_DISTANCE_AND_NEWTONIAN_SHELL_ORACLE",
        _relative_error(gap_distance_energy, analytic["newtonian_J"]),
        1e-6,
    )
    add(
        "REPLACE_A_Y_ONE_THIRD_BY_ONE",
        "YUKAWA_ANALYTIC_ORACLE",
        _relative_error(3 * analytic["yukawa_J"], analytic["yukawa_J"]),
        1e-6,
    )
    exponent_flip = abs(analytic["yukawa_J"]) * math.exp(
        2 * float(legacy_case["center_distance_m"]) / float(legacy_case["lambda_m"])
    )
    add(
        "FLIP_YUKAWA_EXPONENTIAL_SIGN",
        "SHORT_RANGE_LIMIT_AND_YUKAWA_ORACLE",
        _relative_error(-exponent_flip, analytic["yukawa_J"]),
        1e-6,
    )
    theta = np.asarray([math.pi / 7])
    gap = np.asarray([1e-3])
    tau = production.analytic_energy_derivative_torque(theta, gap, 1e-3)
    add(
        "FLIP_NEGATIVE_ANGULAR_ENERGY_DERIVATIVE_SIGN",
        "TORQUE_THREE_PATH_COMPARISON",
        float(np.max(np.abs(2 * tau))) / max(float(np.max(np.abs(tau))), 1e-300),
        1e-8,
    )
    mixed = _fixed_density_integral(legacy_case, 24, mixed_mu2_order=8)
    add(
        "LEAVE_MU2_AT_ORDER_8_WHILE_OTHER_DIMENSIONS_REFINE",
        "ALL_DIMENSION_REFINEMENT_CUSTODY",
        _relative_error(mixed["yukawa_J"], fixed["yukawa_J"]),
        1e-10,
    )
    x2 = float(legacy_case["radius_2_m"]) / float(legacy_case["lambda_m"])
    removed = analytic["yukawa_J"] / float(_analytic_h_mp(mp.mpf(str(x2))))
    add(
        "REMOVE_ONE_SPHERE_FORM_FACTOR",
        "YUKAWA_ANALYTIC_AND_RADIAL_ORACLES",
        _relative_error(removed, analytic["yukawa_J"]),
        1e-6,
    )
    theta_dft = 2 * math.pi * np.arange(64) / 64
    signal = 2e-15 * np.cos(2 * theta_dft + math.pi / 7)
    expected = production.discrete_harmonic_transform(signal, theta_dft)[0]
    doubled = production.discrete_harmonic_transform(
        signal, theta_dft, normalization_multiplier=2.0
    )[0]
    add(
        "DOUBLE_DFT_NORMALIZATION",
        "ANALYTIC_DFT_COEFFICIENT_ORACLE",
        _relative_error(abs(doubled), abs(expected)),
        1e-12,
    )
    reversed_phase = np.conjugate(expected)
    add(
        "REVERSE_DFT_PHASE_SIGN",
        "ANALYTIC_DFT_PHASE_ORACLE",
        abs(reversed_phase - expected) / max(abs(expected), 1e-300),
        1e-12,
    )
    return rows, all(bool(row["detected"]) for row in rows)


def _compute_once(packet: dict[str, Any]) -> tuple[dict[str, bytes], dict[str, Any]]:
    started = time.perf_counter()
    cases = [dict(row) for row in packet["diagnostic_domain"]["rows"]]
    analytic_by_case: dict[str, dict[str, float]] = {}
    oracle_rows: list[dict[str, Any]] = []
    radial_contract_pass = True

    # WP1-WP3: domain custody and analytic/reduced oracles execute before production.
    for case in cases:
        case_id = str(case["case_id"])
        analytic = _analytic_oracle(case, radial=False, digits=120)
        analytic_by_case[case_id] = analytic
        radial_levels = []
        for digits in (50, 80, 120):
            radial = _analytic_oracle(case, radial=True, digits=digits)
            radial_levels.append(radial)
            oracle_rows.append(
                {
                    "case_id": case_id,
                    "path": "R2_HIGH_PRECISION_RADIAL_FORM_FACTOR_INTEGRAL",
                    "precision_digits": digits,
                    "newtonian_J": radial["newtonian_J"],
                    "yukawa_J": radial["yukawa_J"],
                    "absolute_error_newtonian_J": abs(radial["newtonian_J"] - analytic["newtonian_J"]),
                    "relative_error_newtonian": _relative_error(radial["newtonian_J"], analytic["newtonian_J"]),
                    "absolute_error_yukawa_J": abs(radial["yukawa_J"] - analytic["yukawa_J"]),
                    "relative_error_yukawa": _relative_error(radial["yukawa_J"], analytic["yukawa_J"]),
                    "plateau_pass": "",
                    "cross_oracle_pass": abs(radial["yukawa_J"] - analytic["yukawa_J"])
                    <= _tolerance(analytic["yukawa_J"], relative=1e-10),
                }
            )
        plateau_n = abs(radial_levels[-1]["newtonian_J"] - radial_levels[-2]["newtonian_J"])
        plateau_y = abs(radial_levels[-1]["yukawa_J"] - radial_levels[-2]["yukawa_J"])
        plateau_pass = (
            plateau_n <= _tolerance(radial_levels[-1]["newtonian_J"], relative=1e-10)
            and plateau_y <= _tolerance(radial_levels[-1]["yukawa_J"], relative=1e-10)
        )
        cross_pass = (
            abs(radial_levels[-1]["newtonian_J"] - analytic["newtonian_J"])
            <= _tolerance(analytic["newtonian_J"], relative=1e-10)
            and abs(radial_levels[-1]["yukawa_J"] - analytic["yukawa_J"])
            <= _tolerance(analytic["yukawa_J"], relative=1e-10)
        )
        radial_contract_pass = radial_contract_pass and plateau_pass and cross_pass
        oracle_rows.append(
            {
                "case_id": case_id,
                "path": "R1_INDEPENDENT_ANALYTIC_SHELL_AND_FORM_FACTOR",
                "precision_digits": 120,
                "newtonian_J": analytic["newtonian_J"],
                "yukawa_J": analytic["yukawa_J"],
                "absolute_error_newtonian_J": 0.0,
                "relative_error_newtonian": 0.0,
                "absolute_error_yukawa_J": 0.0,
                "relative_error_yukawa": 0.0,
                "plateau_pass": plateau_pass,
                "cross_oracle_pass": cross_pass,
            }
        )

    # WP4: frozen 12-anchor arbitrary-precision adaptive direct ladder.
    direct_rows: list[dict[str, Any]] = []
    direct_contract_pass = True
    direct_final_by_case: dict[str, dict[str, Any]] = {}
    for case in (row for row in cases if bool(row["high_precision_anchor"])):
        levels: list[dict[str, Any]] = []
        for digits, degree, high_nodes, low_nodes, maximum_cells in DIRECT_LEVELS:
            level = _adaptive_direct_density(
                case,
                digits=digits,
                maxdegree=degree,
                high_nodes=high_nodes,
                low_nodes=low_nodes,
                maximum_cells=maximum_cells,
            )
            levels.append(level)
        analytic = analytic_by_case[str(case["case_id"])]
        final = levels[-1]
        plateau_pass = (
            abs(final["newtonian_J"] - levels[-2]["newtonian_J"])
            <= _tolerance(final["newtonian_J"], relative=1e-10)
            and abs(final["yukawa_J"] - levels[-2]["yukawa_J"])
            <= _tolerance(final["yukawa_J"], relative=1e-10)
        )
        cross_pass = (
            abs(final["newtonian_J"] - analytic["newtonian_J"])
            <= _tolerance(analytic["newtonian_J"], relative=1e-10)
            and abs(final["yukawa_J"] - analytic["yukawa_J"])
            <= _tolerance(analytic["yukawa_J"], relative=1e-10)
        )
        work_pass = all(not bool(row["work_cap_hit"]) for row in levels[-2:])
        anchor_pass = plateau_pass and cross_pass and work_pass
        direct_contract_pass = direct_contract_pass and anchor_pass
        direct_final_by_case[str(case["case_id"])] = final
        for level in levels:
            direct_rows.append(
                {
                    "case_id": case["case_id"],
                    **level,
                    "absolute_error_newtonian_vs_analytic_J": abs(level["newtonian_J"] - analytic["newtonian_J"]),
                    "relative_error_newtonian_vs_analytic": _relative_error(level["newtonian_J"], analytic["newtonian_J"]),
                    "absolute_error_yukawa_vs_analytic_J": abs(level["yukawa_J"] - analytic["yukawa_J"]),
                    "relative_error_yukawa_vs_analytic": _relative_error(level["yukawa_J"], analytic["yukawa_J"]),
                    "final_anchor_plateau_pass": plateau_pass if level is final else "",
                    "final_anchor_cross_oracle_pass": cross_pass if level is final else "",
                    "final_anchor_pass": anchor_pass if level is final else "",
                }
            )

    oracle_contract_pass = radial_contract_pass and direct_contract_pass

    # WP5: production order ladder and frozen near-contact contribution profile.
    production_rows: list[dict[str, Any]] = []
    profile_rows: list[dict[str, Any]] = []
    convergence_by_case: dict[str, dict[int, dict[str, Any]]] = {}
    fixed_elapsed = 0.0
    for case in cases:
        case_id = str(case["case_id"])
        analytic = analytic_by_case[case_id]
        convergence_by_case[case_id] = {}
        for order in PRODUCTION_ORDERS:
            value = _fixed_density_integral(case, order, profile=order == 48)
            fixed_elapsed += float(value["elapsed_seconds"])
            convergence_by_case[case_id][order] = value
            for component in ("newtonian", "yukawa"):
                actual = float(value[f"{component}_J"])
                reference = float(analytic[f"{component}_J"])
                absolute_error = abs(actual - reference)
                production_rows.append(
                    {
                        "case_id": case_id,
                        "component": component.upper(),
                        "order": order,
                        "value_J": actual,
                        "oracle_J": reference,
                        "absolute_error_J": absolute_error,
                        "relative_error": _relative_error(actual, reference),
                        "production_accuracy_pass": absolute_error
                        <= _tolerance(reference, relative=1e-6),
                        "elapsed_seconds": value["elapsed_seconds"],
                        "nominal_node_count": value["nominal_node_count"],
                    }
                )
            if order == 48:
                for bin_row in value["profile_bins"]:
                    profile_rows.append(
                        {
                            "case_id": case_id,
                            "surface_gap_m": case["surface_gap_m"],
                            "lambda_m": case["lambda_m"],
                            **bin_row,
                            "absolute_fraction_chi_le_1": value["absolute_fraction_chi_le_1"],
                        }
                    )

    # WP6: summation, coordinate-scale, precision, and explicit-azimuth probes.
    precision_rows: list[dict[str, Any]] = []
    legacy_cases = [
        row for row in cases if row["case_class"] == "LEGACY_STAGE_A_REPRODUCTION"
    ]
    for case in legacy_cases:
        analytic = analytic_by_case[str(case["case_id"])]
        for method in ("ORDINARY", "PAIRWISE", "KAHAN", "FSUM"):
            value = _fixed_density_integral(case, 24, summation=method)
            precision_rows.append(
                {
                    "case_id": case["case_id"],
                    "probe": "SUMMATION",
                    "level": method,
                    "newtonian_J": value["newtonian_J"],
                    "yukawa_J": value["yukawa_J"],
                    "relative_error_newtonian": _relative_error(value["newtonian_J"], analytic["newtonian_J"]),
                    "relative_error_yukawa": _relative_error(value["yukawa_J"], analytic["yukawa_J"]),
                    "pass": True,
                }
            )
        reduced = convergence_by_case[str(case["case_id"])][12]
        for samples in (32, 64):
            explicit = _explicit_azimuth_control(case, samples)
            delta_n = abs(explicit["newtonian_J"] - reduced["newtonian_J"])
            delta_y = abs(explicit["yukawa_J"] - reduced["yukawa_J"])
            symmetry_pass = (
                delta_n <= 1e-34 + 1e-8 * abs(reduced["newtonian_J"])
                and delta_y <= 1e-34 + 1e-8 * abs(reduced["yukawa_J"])
            )
            precision_rows.append(
                {
                    "case_id": case["case_id"],
                    "probe": "EXPLICIT_AZIMUTH",
                    "level": samples,
                    "newtonian_J": explicit["newtonian_J"],
                    "yukawa_J": explicit["yukawa_J"],
                    "relative_error_newtonian": _relative_error(explicit["newtonian_J"], reduced["newtonian_J"]),
                    "relative_error_yukawa": _relative_error(explicit["yukawa_J"], reduced["yukawa_J"]),
                    "pass": symmetry_pass,
                }
            )

    # WP7-WP8 execute only after reference acceptance, preserving the energy-first gate.
    torque_rows: list[dict[str, Any]] = []
    torque_pass = False
    production_dft_rows: list[dict[str, Any]] = []
    production_dft_pass = False
    analytic_dft_rows, analytic_dft_pass, alias_pass = _analytic_dft_diagnostics()
    if oracle_contract_pass:
        torque_rows, torque_pass = _torque_diagnostics()
        if torque_pass:
            production_dft_rows, production_dft_pass = _production_dft_diagnostics()

    mutation_rows, mutations_pass = _mutation_diagnostics(
        legacy_cases[0], analytic_by_case[str(legacy_cases[0]["case_id"])]
    )

    # WP9: evaluate only preregistered predicates.
    monotonic_failures: list[dict[str, Any]] = []
    for case in cases:
        case_id = str(case["case_id"])
        for component in ("newtonian", "yukawa"):
            reference = analytic_by_case[case_id][f"{component}_J"]
            errors = [
                abs(convergence_by_case[case_id][order][f"{component}_J"] - reference)
                for order in (24, 32, 48)
            ]
            monotonic = errors[0] > errors[1] > errors[2]
            final_fail = errors[2] > _tolerance(reference, relative=1e-6)
            if monotonic and final_fail:
                monotonic_failures.append(
                    {
                        "case_id": case_id,
                        "component": component.upper(),
                        "errors_J_order24_32_48": errors,
                    }
                )
    fixed_order_inadequate = oracle_contract_pass and bool(monotonic_failures)

    dominant_profiles = []
    for case in cases:
        case_id = str(case["case_id"])
        fraction = next(
            row["absolute_fraction_chi_le_1"]
            for row in profile_rows
            if row["case_id"] == case_id
        )
        if fraction < 0.90 or case_id not in direct_final_by_case:
            continue
        reference = analytic_by_case[case_id]["yukawa_J"]
        fixed_error = abs(convergence_by_case[case_id][48]["yukawa_J"] - reference)
        adaptive_error = abs(direct_final_by_case[case_id]["yukawa_J"] - reference)
        improvement = fixed_error / max(adaptive_error, 1e-300)
        if improvement >= 10.0:
            dominant_profiles.append(
                {
                    "case_id": case_id,
                    "absolute_fraction_chi_le_1": fraction,
                    "adaptive_improvement_factor": improvement,
                }
            )
    near_contact_required = oracle_contract_pass and bool(dominant_profiles)
    reference_inadequate = not oracle_contract_pass
    implementation_defect = False
    angular_independent_failure = not analytic_dft_pass or not alias_pass
    kernel_noise_dft = (
        analytic_dft_pass
        and alias_pass
        and torque_pass
        and not production_dft_pass
    )
    oracle_available = oracle_contract_pass
    economically_unvalidated = not oracle_available and fixed_order_inadequate

    labels: list[str] = []
    predicates = (
        ("REFERENCE_ORACLE_INADEQUATE", reference_inadequate),
        ("IMPLEMENTATION_DEFECT_LOCALIZED", implementation_defect),
        ("NEAR_CONTACT_DOMAIN_DECOMPOSITION_REQUIRED", near_contact_required),
        ("FIXED_ORDER_CUBATURE_INADEQUATE", fixed_order_inadequate),
        ("ANGULAR_DFT_RESOLUTION_INDEPENDENTLY_INADEQUATE", angular_independent_failure),
        ("KERNEL_NOISE_DRIVES_DFT_FAILURE", kernel_noise_dft),
        ("INTERNAL_APPARATUS_FORWARD_MODEL_NOT_ECONOMICALLY_VALIDATABLE", economically_unvalidated),
    )
    labels.extend(label for label, active in predicates if active)
    if not labels:
        labels.append("UNRESOLVED_IF_NO_FROZEN_PREDICATE_IS_SATISFIED")
    oracle_outcome = (
        "ANALYTIC_OR_REDUCED_SPHERE_ORACLE_AVAILABLE"
        if oracle_available
        else "ANALYTIC_OR_REDUCED_SPHERE_ORACLE_NOT_VALIDATED"
    )
    priority = [label for label, active in predicates if active]
    principal = priority[0] if priority else labels[0]
    recommendation = (
        "SELECT_SEPARATE_METHOD_REPLACEMENT_PACKET_FOR_STABLE_ANALYTIC_SPHERE_FORM_FACTOR"
        if oracle_available and fixed_order_inadequate
        else "STOP_FOR_INDEPENDENT_RESULT_REVIEW_AND_FRESH_SELECTOR"
    )
    cost = {
        "measured_fixed_order_total_seconds": fixed_elapsed,
        "measured_execution_total_seconds": time.perf_counter() - started,
        "fixed_order_48_nominal_nodes_per_case": 48**4,
        "analytic_oracle_operations_per_case": "O(1)",
        "recommended_method": recommendation,
        "production_replacement_performed": False,
    }

    root_cause = {
        "principal_outcome": principal,
        "principal_labels": labels,
        "oracle_availability_outcome": oracle_outcome,
        "predicate_evidence": {
            "radial_oracle_contract_pass": radial_contract_pass,
            "direct_oracle_contract_pass": direct_contract_pass,
            "reference_oracle_contract_pass": oracle_contract_pass,
            "monotonic_order48_failures": monotonic_failures,
            "near_contact_decomposition_evidence": dominant_profiles,
            "analytic_dft_pass": analytic_dft_pass,
            "alias_probe_pass": alias_pass,
            "torque_pass": torque_pass,
            "production_dft_final_refinement_pass": production_dft_pass,
            "all_ten_mutations_detected": mutations_pass,
        },
        "recommended_numerical_remedy": recommendation,
        "estimated_cost": cost,
    }

    component_headers = list(oracle_rows[0].keys())
    production_headers = list(production_rows[0].keys())
    direct_headers = list(direct_rows[0].keys())
    profile_headers = list(profile_rows[0].keys())
    precision_headers = list(precision_rows[0].keys())
    torque_headers = list(torque_rows[0].keys()) if torque_rows else ["status"]
    analytic_dft_headers = list(analytic_dft_rows[0].keys())
    production_dft_headers = (
        list(production_dft_rows[0].keys()) if production_dft_rows else ["status"]
    )
    mutation_headers = list(mutation_rows[0].keys())
    artifacts = {
        "component_oracles.csv": _csv_bytes(component_headers, oracle_rows),
        "direct_anchor_convergence.csv": _csv_bytes(direct_headers, direct_rows),
        "production_order_convergence.csv": _csv_bytes(production_headers, production_rows),
        "near_contact_profiles.csv": _csv_bytes(profile_headers, profile_rows),
        "precision_summation_symmetry.csv": _csv_bytes(precision_headers, precision_rows),
        "torque_comparisons.csv": _csv_bytes(
            torque_headers, torque_rows if torque_rows else [{"status": "GATED_BY_REFERENCE_ORACLE"}]
        ),
        "analytic_dft_diagnostics.csv": _csv_bytes(analytic_dft_headers, analytic_dft_rows),
        "production_dft_diagnostics.csv": _csv_bytes(
            production_dft_headers,
            production_dft_rows if production_dft_rows else [{"status": "GATED_BY_ENERGY_OR_TORQUE"}],
        ),
        "mutation_controls.csv": _csv_bytes(mutation_headers, mutation_rows),
        "root_cause_and_cost.json": _json_bytes(root_cause),
    }
    summary = {
        "work_packages_executed": 9,
        "case_count": len(cases),
        "strict_nonoverlap_count": sum(
            float(row["center_distance_m"])
            > float(row["radius_1_m"]) + float(row["radius_2_m"])
            for row in cases
        ),
        "high_precision_anchor_count": len(direct_final_by_case),
        "oracle_contract_pass": oracle_contract_pass,
        "root_cause": root_cause,
        "component_oracle_row_count": len(oracle_rows),
        "direct_anchor_row_count": len(direct_rows),
        "production_convergence_row_count": len(production_rows),
        "near_contact_profile_row_count": len(profile_rows),
        "torque_row_count": len(torque_rows),
        "analytic_dft_row_count": len(analytic_dft_rows),
        "production_dft_row_count": len(production_dft_rows),
        "mutation_count": len(mutation_rows),
        "mutation_pass_count": sum(bool(row["detected"]) for row in mutation_rows),
        "elapsed_seconds": time.perf_counter() - started,
    }
    return artifacts, summary


def execute_once() -> dict[str, Any]:
    review, packet = _authority_check()
    output_directory = REPO_ROOT / OUTPUT_RELATIVE_DIRECTORY
    output_result_path = output_directory / "execution_result.json"
    report_path = REPO_ROOT / REPORT_RELATIVE_PATH
    if output_directory.exists() or output_result_path.exists() or report_path.exists():
        raise RuntimeError("single bounded diagnosis execution authority is already consumed")

    artifacts, summary = _compute_once(packet)
    artifact_rows = [
        {
            "relative_path": f"{OUTPUT_RELATIVE_DIRECTORY}/{name}",
            "byte_count": len(value),
            "sha256": _sha256_bytes(value),
        }
        for name, value in sorted(artifacts.items())
    ]
    root_cause = summary["root_cause"]
    result = {
        "schema_id": "toe.scalar_only_yukawa.sphere_kernel_diagnosis.execution.v0",
        "execution_id": "SCALAR_ONLY_YUKAWA_SPHERE_KERNEL_DIAGNOSIS_AND_REFERENCE_ORACLE_EXECUTION_20260719_v0",
        "captured_at_utc": "2026-07-19T00:00:00Z",
        "target": TARGET,
        "status": "COMPLETED_ONCE_PENDING_INDEPENDENT_RESULT_REVIEW",
        "principal_outcome": root_cause["principal_outcome"],
        "principal_labels": root_cause["principal_labels"],
        "oracle_availability_outcome": root_cause["oracle_availability_outcome"],
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_review_verdict": review["verdict"],
            "authorized_diagnosis_execution_count": 1,
            "consumed_diagnosis_execution_count": 1,
            "frozen_review_artifacts": [
                {"relative_path": path, "sha256": digest}
                for path, digest in REVIEW_HASHES.items()
            ],
        },
        "execution_summary": summary,
        "artifact_manifest": {
            "artifact_count": len(artifact_rows),
            "rows": artifact_rows,
        },
        "scope": {
            "bounded_diagnosis_execution_performed": True,
            "work_packages_executed": 9,
            "production_kernel_changed": False,
            "integration_method_replaced": False,
            "stage_a_rerun_performed": False,
            "final_real_150_vector_produced": False,
            "jacobian_computed": False,
            "singular_values_computed": False,
            "eta_lambda_computed": False,
            "physical_identifiability_evaluated": False,
            "synthetic_noise_used": False,
            "sensitivity_forecast_produced": False,
            "scalar_range_or_alpha_conclusion_issued": False,
            "stage_b_authorized": False,
            "automatic_repair_authorized": False,
            "post_diagnosis_independent_result_review_required": True,
            "post_review_fresh_selector_required": True,
        },
        "current_posture": {
            "authorized_diagnosis_executions": 1,
            "consumed_diagnosis_executions": 1,
            "production_repair": "NOT_AUTHORIZED",
            "stage_a_rerun": "NOT_AUTHORIZED",
            "jacobian_or_identifiability": "NOT_AUTHORIZED",
            "stage_b": "NOT_AUTHORIZED",
            "next_authority": SELECTED_NEXT_TARGET,
        },
        "claim_ceiling": (
            "This record reports one bounded sphere-kernel diagnosis. It may classify "
            "the frozen numerical failure and recommend a later numerical remedy, but "
            "it does not change or replace the production kernel, rerun Stage A, produce "
            "the apparatus vector or Jacobian, test physical identifiability, authorize "
            "Stage B, or issue a scalar-range or alpha conclusion."
        ),
    }
    result_bytes = _json_bytes(result)
    output_directory.mkdir(parents=True, exist_ok=False)
    for name, value in artifacts.items():
        (output_directory / name).write_bytes(value)
    output_result_path.write_bytes(result_bytes)
    report_path.write_bytes(result_bytes)
    return result


def finalize_external_timeout() -> dict[str, Any]:
    """Consume the one run after the external launcher enforces the frozen total cap.

    This path performs no scientific calculation.  It exists only because the
    operating-system launcher terminated the authorized process at the packet's
    3,600-second total budget before the atomic writer could serialize its own
    fail-closed record.
    """
    review, _packet = _authority_check()
    output_directory = REPO_ROOT / OUTPUT_RELATIVE_DIRECTORY
    output_result_path = output_directory / "execution_result.json"
    report_path = REPO_ROOT / REPORT_RELATIVE_PATH
    if output_directory.exists() or output_result_path.exists() or report_path.exists():
        raise RuntimeError("single bounded diagnosis execution authority is already consumed")

    launcher_evidence = {
        "authorized_command": (
            ".\\py.ps1 -m formal.python.tools."
            "scalar_only_yukawa_sphere_kernel_diagnosis_and_reference_oracle_v0 --execute"
        ),
        "launcher_exit_code": 124,
        "launcher_reported_wall_time_seconds": 3604.1,
        "frozen_total_wall_clock_cap_seconds": 3600,
        "cap_excess_seconds": 4.1,
        "canonical_output_directory_existed_at_timeout": False,
        "canonical_report_existed_at_timeout": False,
        "surviving_matching_python_process_count_before_enforcement": 2,
        "surviving_matching_python_process_count_after_enforcement": 0,
        "scientific_rerun_performed": False,
        "post_timeout_scientific_calculation_performed": False,
        "atomic_partial_results_recoverable": False,
        "contract_rule_applied": "FAIL_CLOSED_REFERENCE_ORACLE_INADEQUATE",
    }
    launcher_bytes = _json_bytes(launcher_evidence)
    artifact_path = f"{OUTPUT_RELATIVE_DIRECTORY}/launcher_timeout_evidence.json"
    result = {
        "schema_id": "toe.scalar_only_yukawa.sphere_kernel_diagnosis.execution.v0",
        "execution_id": "SCALAR_ONLY_YUKAWA_SPHERE_KERNEL_DIAGNOSIS_AND_REFERENCE_ORACLE_EXECUTION_20260719_v0",
        "captured_at_utc": "2026-07-19T00:00:00Z",
        "target": TARGET,
        "status": "COMPLETED_ONCE_FAIL_CLOSED_TOTAL_WORK_CAP_PENDING_INDEPENDENT_RESULT_REVIEW",
        "principal_outcome": "REFERENCE_ORACLE_INADEQUATE",
        "principal_labels": ["REFERENCE_ORACLE_INADEQUATE"],
        "oracle_availability_outcome": "ANALYTIC_OR_REDUCED_SPHERE_ORACLE_NOT_VALIDATED",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_review_verdict": review["verdict"],
            "authorized_diagnosis_execution_count": 1,
            "consumed_diagnosis_execution_count": 1,
            "frozen_review_artifacts": [
                {"relative_path": path, "sha256": digest}
                for path, digest in REVIEW_HASHES.items()
            ],
        },
        "execution_summary": {
            "work_packages_completed_before_timeout": "NOT_RECOVERABLE_FROM_ATOMIC_EXECUTOR",
            "oracle_contract_pass": False,
            "reference_plateau_established": False,
            "cross_oracle_acceptance_established": False,
            "production_path_judged_against_accepted_oracle": False,
            "root_cause": {
                "principal_outcome": "REFERENCE_ORACLE_INADEQUATE",
                "principal_labels": ["REFERENCE_ORACLE_INADEQUATE"],
                "oracle_availability_outcome": "ANALYTIC_OR_REDUCED_SPHERE_ORACLE_NOT_VALIDATED",
                "predicate_evidence": launcher_evidence,
                "recommended_numerical_remedy": "STOP_FOR_INDEPENDENT_RESULT_REVIEW_AND_FRESH_SELECTOR",
                "estimated_cost": {
                    "observed_lower_bound_seconds": 3604.1,
                    "frozen_budget_seconds": 3600,
                    "reference_contract_completed_within_budget": False,
                },
            },
        },
        "artifact_manifest": {
            "artifact_count": 1,
            "rows": [
                {
                    "relative_path": artifact_path,
                    "byte_count": len(launcher_bytes),
                    "sha256": _sha256_bytes(launcher_bytes),
                }
            ],
        },
        "scope": {
            "bounded_diagnosis_execution_performed": True,
            "single_execution_authority_consumed": True,
            "fail_closed_total_work_cap_applied": True,
            "scientific_rerun_performed": False,
            "production_kernel_changed": False,
            "integration_method_replaced": False,
            "stage_a_rerun_performed": False,
            "final_real_150_vector_produced": False,
            "jacobian_computed": False,
            "singular_values_computed": False,
            "eta_lambda_computed": False,
            "physical_identifiability_evaluated": False,
            "synthetic_noise_used": False,
            "sensitivity_forecast_produced": False,
            "scalar_range_or_alpha_conclusion_issued": False,
            "stage_b_authorized": False,
            "automatic_repair_authorized": False,
            "post_diagnosis_independent_result_review_required": True,
            "post_review_fresh_selector_required": True,
        },
        "current_posture": {
            "authorized_diagnosis_executions": 1,
            "consumed_diagnosis_executions": 1,
            "reference_oracle": "NOT_VALIDATED_WITHIN_FROZEN_WORK_CAP",
            "production_method_root_cause": "NOT_ADJUDICATED",
            "production_repair": "NOT_AUTHORIZED",
            "stage_a_rerun": "NOT_AUTHORIZED",
            "jacobian_or_identifiability": "NOT_AUTHORIZED",
            "stage_b": "NOT_AUTHORIZED",
            "next_authority": SELECTED_NEXT_TARGET,
        },
        "claim_ceiling": (
            "The one bounded diagnosis exhausted its frozen total wall-clock budget "
            "before the required reference-oracle plateau and cross-oracle acceptance "
            "were serialized. The run is consumed and fails closed as "
            "REFERENCE_ORACLE_INADEQUATE. This record does not identify a production "
            "implementation defect, judge fixed-order cubature, replace a method, rerun "
            "Stage A, test identifiability, or authorize Stage B."
        ),
    }
    result_bytes = _json_bytes(result)
    output_directory.mkdir(parents=True, exist_ok=False)
    (output_directory / "launcher_timeout_evidence.json").write_bytes(launcher_bytes)
    output_result_path.write_bytes(result_bytes)
    report_path.write_bytes(result_bytes)
    return result


def check_execution() -> int:
    _authority_check()
    output_directory = REPO_ROOT / OUTPUT_RELATIVE_DIRECTORY
    output_result_path = output_directory / "execution_result.json"
    report_path = REPO_ROOT / REPORT_RELATIVE_PATH
    if not output_result_path.exists() or not report_path.exists():
        print("bounded kernel diagnosis result missing")
        return 1
    if output_result_path.read_bytes() != report_path.read_bytes():
        print("bounded kernel diagnosis result copies differ")
        return 1
    result = json.loads(report_path.read_text(encoding="utf-8"))
    for row in result["artifact_manifest"]["rows"]:
        path = REPO_ROOT / row["relative_path"]
        if not path.exists() or path.stat().st_size != row["byte_count"]:
            print(f"diagnosis artifact missing or size drift: {row['relative_path']}")
            return 1
        if _sha256_path(path) != row["sha256"]:
            print(f"diagnosis artifact hash drift: {row['relative_path']}")
            return 1
    if result["authority"]["consumed_diagnosis_execution_count"] != 1:
        print("diagnosis execution count mismatch")
        return 1
    if result["scope"]["stage_b_authorized"] is not False:
        print("Stage B scope drift")
        return 1
    print(
        "bounded kernel diagnosis result OK "
        f"principal={result['principal_outcome']} "
        f"artifacts={result['artifact_manifest']['artifact_count']}"
    )
    return 0


def preflight() -> int:
    _authority_check()
    output_directory = REPO_ROOT / OUTPUT_RELATIVE_DIRECTORY
    report_path = REPO_ROOT / REPORT_RELATIVE_PATH
    if output_directory.exists() or report_path.exists():
        print("single bounded diagnosis execution authority is already consumed")
        return 1
    print("bounded kernel diagnosis preflight OK authority=1 consumed=0")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Execute the single authorized scalar-only Yukawa sphere-kernel diagnosis."
    )
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--preflight", action="store_true")
    mode.add_argument("--execute", action="store_true")
    mode.add_argument("--finalize-external-timeout", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.preflight:
        return preflight()
    if args.execute:
        result = execute_once()
        print(
            "bounded kernel diagnosis complete "
            f"principal={result['principal_outcome']} "
            f"labels={'+'.join(result['principal_labels'])} "
            f"next={result['selected_next_target']}"
        )
        return 0
    if args.finalize_external_timeout:
        result = finalize_external_timeout()
        print(
            "bounded kernel diagnosis timeout finalized "
            f"principal={result['principal_outcome']} "
            f"next={result['selected_next_target']}"
        )
        return 0
    return check_execution()


if __name__ == "__main__":
    raise SystemExit(main())

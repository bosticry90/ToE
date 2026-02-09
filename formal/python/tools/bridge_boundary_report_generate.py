from __future__ import annotations

"""Bridge boundary report generator (quarantine-safe).

Goal
- Produce a deterministic, bounded domain-scan report for the current bridge family.

Policy alignment
- Deterministic mapping only (no runtime discovery).
- Bookkeeping only; does not upgrade epistemic status.
- Does not import from the archive directory.

Report schema (v1)
{
  "schema_version": 1,
  "items": [
    {
      "ticket_id": "BRIDGE_TICKET_0002",
      "scan_id": "slope_boundary_scan_v1",
      "inputs": {"locks": [...], "contracts": [...]},
      "evidence": {"pytest_nodes": [...]},
      "derived": {...},
      "samples": [...],
      "summary": {...}
    },
    {
      "ticket_id": "BRIDGE_TICKET_0004",
      "scan_id": "curvature_grid_density_scan_v1",
      "inputs": {"locks": [...], "contracts": [...]},
      "evidence": {"pytest_nodes": [...]},
      "derived": {...},
      "grids": [...],
      "summary": {...}
    }
  ],
  "artifact_sha256": "..."
}
"""

if __name__ == "__main__" and (__package__ is None or __package__ == ""):
    from pathlib import Path as _Path

    _tool = _Path(__file__).stem
    raise SystemExit(
        "Do not run this tool as a script.\n"
        "Run it as a module so package imports resolve.\n\n"
        f"  .\\py.ps1 -m formal.python.tools.{_tool} --help\n"
    )

import argparse
import hashlib
import json
from pathlib import Path
from typing import Optional

import numpy as np

from formal.python.toe.ucff.core_front_door import UcffCoreParams, ucff_dispersion_omega2_numeric


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    if p.is_file():
        p = p.parent
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def _sha256_bytes(data: bytes) -> str:
    h = hashlib.sha256()
    h.update(data)
    return h.hexdigest()


def _load_first_json_block_from_markdown(path: Path) -> dict:
    text = path.read_text(encoding="utf-8")
    parts = text.split("```json")
    if len(parts) < 2:
        raise AssertionError(f"No ```json block found in {path}")
    rest = parts[1]
    end = rest.find("```")
    if end < 0:
        raise AssertionError(f"Unterminated ```json block in {path}")
    blob = rest[:end].strip()
    return json.loads(blob)


def _q(x: float, *, sig: int = 12) -> float:
    """Quantize floats for stable JSON across platforms."""

    return float(f"{float(x):.{int(sig)}g}")


def _fit_slope_through_origin(*, x: np.ndarray, y: np.ndarray) -> float:
    x = np.asarray(x, dtype=float)
    y = np.asarray(y, dtype=float)
    assert x.shape == y.shape
    if x.ndim != 1:
        raise AssertionError("Expected 1D arrays")

    denom = float(np.dot(x, x))
    if denom == 0.0:
        raise AssertionError("Cannot fit slope with all-zero x")
    return float(np.dot(x, y) / denom)


def _ucff_lowk_slope_from_c(*, c: float) -> float:
    params = UcffCoreParams(rho0=1.0, g=float(c**2), lam=0.0, beta=0.0)
    k = np.array([0.0, 0.001, 0.002, 0.005, 0.01], dtype=float)
    omega2 = ucff_dispersion_omega2_numeric(k=k, params=params)
    omega = np.sqrt(omega2)
    return _fit_slope_through_origin(x=k[1:], y=omega[1:])


def _uniform_grid(*, k_max: float, n: int) -> np.ndarray:
    if n < 3:
        raise ValueError("n must be >= 3")
    if k_max <= 0:
        raise ValueError("k_max must be > 0")
    return np.linspace(0.0, float(k_max), int(n), dtype=float)


def _build_slope_boundary_item(*, repo_root: Path) -> dict:
    lock_rel = Path("formal/markdown/locks/observables/OV-BR-05_bragg_lowk_slope_summary_OVERRIDE.md")
    payload = _load_first_json_block_from_markdown(repo_root / lock_rel)

    assert payload["schema"] == "OV-BR-05_bragg_lowk_slope_summary/v1"
    assert payload["observable_id"] == "OV-BR-05"
    assert payload["status"]["blocked"] is False

    rows = payload.get("rows")
    assert isinstance(rows, list) and rows

    by_condition: dict[str, dict] = {}
    for row in rows:
        if not isinstance(row, dict):
            continue
        key = row.get("condition_key")
        if isinstance(key, str):
            by_condition[key] = row

    a = by_condition["condition_A"]
    b = by_condition["condition_B"]

    s_a = float(a["s_kHz_per_um_inv"])
    se_a = float(a["se_kHz_per_um_inv"])
    s_b = float(b["s_kHz_per_um_inv"])
    se_b = float(b["se_kHz_per_um_inv"])

    ia_lo, ia_hi = s_a - se_a, s_a + se_a
    ib_lo, ib_hi = s_b - se_b, s_b + se_b

    inter_lo = max(ia_lo, ib_lo)
    inter_hi = min(ia_hi, ib_hi)
    assert inter_hi > inter_lo

    width = inter_hi - inter_lo

    fracs_inside = [0.02, 0.25, 0.50, 0.75, 0.98]
    fracs_outside_near = [-0.02, 1.02]
    fracs_outside_far = [-0.50, 1.50]

    samples: list[dict] = []

    def add_sample(*, label: str, c: float) -> None:
        in_a = ia_lo <= c <= ia_hi
        in_b = ib_lo <= c <= ib_hi
        in_overlap = bool(in_a and in_b)

        slope_ucff = _ucff_lowk_slope_from_c(c=c)
        abs_err = abs(slope_ucff - c)

        slope_tol = 1e-3 * max(1.0, abs(c))
        slope_ok = abs_err <= slope_tol

        passed = bool(in_overlap and slope_ok)

        if not in_overlap:
            reason = "FAIL_BRAGG_OVERLAP_WINDOW"
        elif not slope_ok:
            reason = "FAIL_UCFF_SLOPE_REPRO"
        else:
            reason = "PASS"

        samples.append(
            {
                "label": label,
                "c": _q(c),
                "in_condition_A_1sigma": bool(in_a),
                "in_condition_B_1sigma": bool(in_b),
                "in_intersection_1sigma": bool(in_overlap),
                "slope_ucff": _q(slope_ucff),
                "abs_error": _q(abs_err),
                "passed": passed,
                "reason_code": reason,
            }
        )

    for f in fracs_inside:
        c = inter_lo + f * width
        add_sample(label=f"inside_frac_{f}", c=c)

    for f in fracs_outside_near:
        c = inter_lo + f * width
        add_sample(label=f"outside_near_frac_{f}", c=c)

    for f in fracs_outside_far:
        c = inter_lo + f * width
        add_sample(label=f"outside_far_frac_{f}", c=c)

    passed = [s for s in samples if s["passed"]]
    failed = [s for s in samples if not s["passed"]]

    return {
        "ticket_id": "BRIDGE_TICKET_0002",
        "scan_id": "slope_boundary_scan_v1",
        "inputs": {"locks": [lock_rel.as_posix()], "contracts": ["formal/docs/ucff_core_front_door_contract.md"]},
        "evidence": {
            "pytest_nodes": [
                "formal/python/tests/test_bridge_br05_ucff_lowk_slope_boundary_scan.py::test_bridge_br05_ucff_lowk_slope_boundary_scan",  # noqa: E501
            ]
        },
        "derived": {
            "ia_lo": _q(ia_lo),
            "ia_hi": _q(ia_hi),
            "ib_lo": _q(ib_lo),
            "ib_hi": _q(ib_hi),
            "inter_lo": _q(inter_lo),
            "inter_hi": _q(inter_hi),
            "width": _q(width),
            "k_grid": [0.0, 0.001, 0.002, 0.005, 0.01],
            "slope_tol_rel": 1e-3,
        },
        "samples": samples,
        "summary": {
            "n_samples": len(samples),
            "n_pass": len(passed),
            "n_fail": len(failed),
            "fail_reason_counts": {
                "FAIL_BRAGG_OVERLAP_WINDOW": sum(1 for s in failed if s["reason_code"] == "FAIL_BRAGG_OVERLAP_WINDOW"),
                "FAIL_UCFF_SLOPE_REPRO": sum(1 for s in failed if s["reason_code"] == "FAIL_UCFF_SLOPE_REPRO"),
            },
        },
    }


def _build_curvature_grid_density_item(*, repo_root: Path) -> dict:
    ovbr04a_rel = Path("formal/markdown/locks/observables/OV-BR-04a_bragg_lowk_slope_conditionA_OVERRIDE.md")
    ovbr04a = _load_first_json_block_from_markdown(repo_root / ovbr04a_rel)
    assert ovbr04a["observable_id"] == "OV-BR-04A"
    assert ovbr04a["status"]["blocked"] is False

    sel = dict(ovbr04a.get("selection", {}))
    params = dict(sel.get("parameters", {}))
    k_max = float(params["k_um_inv_max"])

    ucff_params = UcffCoreParams(rho0=1.0, g=2.0, lam=0.25, beta=0.125)

    eps = 1e-12
    negctl_threshold = 1e-8

    grids: list[dict] = []
    for n in [5, 7, 9]:
        k = _uniform_grid(k_max=k_max, n=n)
        omega2 = ucff_dispersion_omega2_numeric(k=k, params=ucff_params)
        diff2 = omega2[2:] - 2.0 * omega2[1:-1] + omega2[:-2]

        min_diff2 = float(np.min(diff2))
        convex_ok = bool(min_diff2 >= -eps)

        diff2_wrong = -diff2
        min_wrong = float(np.min(diff2_wrong))
        negative_control_fails = bool(min_wrong < -negctl_threshold)

        if convex_ok and negative_control_fails:
            reason = "PASS"
        elif not convex_ok:
            reason = "FAIL_CONVEXITY"
        else:
            reason = "FAIL_NEGATIVE_CONTROL_NOT_TRIGGERING"

        grids.append(
            {
                "n": int(n),
                "k_max": _q(k_max),
                "min_diff2": _q(min_diff2),
                "min_diff2_wrong": _q(min_wrong),
                "convex_ok": convex_ok,
                "negative_control_fails": negative_control_fails,
                "passed": bool(reason == "PASS"),
                "reason_code": reason,
            }
        )

    return {
        "ticket_id": "BRIDGE_TICKET_0004",
        "scan_id": "curvature_grid_density_scan_v1",
        "inputs": {
            "locks": [
                ovbr04a_rel.as_posix(),
                "formal/markdown/locks/observables/OV-BR-04b_bragg_lowk_slope_conditionB_OVERRIDE.md",
            ],
            "contracts": ["formal/docs/ucff_core_front_door_contract.md"],
        },
        "evidence": {
            "pytest_nodes": [
                "formal/python/tests/test_bridge_br05_ucff_lowk_curvature_grid_density_scan.py::test_bridge_br05_ucff_lowk_curvature_grid_density_scan",  # noqa: E501
            ]
        },
        "derived": {
            "k_max": _q(k_max),
            "ucff_params": {"rho0": 1.0, "g": 2.0, "lam": 0.25, "beta": 0.125},
            "convexity_eps": eps,
            "negative_control_min_threshold": negctl_threshold,
        },
        "grids": grids,
        "summary": {
            "n_grids": len(grids),
            "n_pass": sum(1 for g in grids if g["passed"]),
            "fail_reason_counts": {
                "FAIL_CONVEXITY": sum(1 for g in grids if g["reason_code"] == "FAIL_CONVEXITY"),
                "FAIL_NEGATIVE_CONTROL_NOT_TRIGGERING": sum(
                    1 for g in grids if g["reason_code"] == "FAIL_NEGATIVE_CONTROL_NOT_TRIGGERING"
                ),
            },
        },
    }


def build_bridge_boundary_report_payload(*, repo_root: Path) -> dict:
    items = [
        _build_slope_boundary_item(repo_root=repo_root),
        _build_curvature_grid_density_item(repo_root=repo_root),
    ]

    payload = {
        "schema_version": 1,
        "items": items,
    }

    out_text = json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    payload["artifact_sha256"] = _sha256_bytes(out_text.encode("utf-8"))
    return payload


def main(argv: Optional[list[str]] = None) -> int:
    p = argparse.ArgumentParser(description="Generate the deterministic bridge boundary report JSON (schema v1).")
    p.add_argument(
        "--out",
        default="formal/quarantine/bridge_tickets/BRIDGE_BOUNDARY_REPORT.json",
        help=(
            "Repo-relative output JSON path (default: formal/quarantine/bridge_tickets/BRIDGE_BOUNDARY_REPORT.json)"
        ),
    )
    p.add_argument("--no-write", action="store_true", help="Do not write the file; just validate generation")

    args = p.parse_args(argv)
    repo_root = _find_repo_root(Path(__file__))

    payload = build_bridge_boundary_report_payload(repo_root=repo_root)
    out_text = json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"

    if not args.no_write:
        out_path = repo_root / str(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(out_text, encoding="utf-8")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())

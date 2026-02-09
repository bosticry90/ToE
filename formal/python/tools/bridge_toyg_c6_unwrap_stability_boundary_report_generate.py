from __future__ import annotations

"""Boundary report for BRIDGE_TICKET_TOYG_0003 (quarantine-safe)."""

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

from formal.python.tools.bridge_toyg_c6_unwrap_stability import evaluate_toyg_c6_unwrap_stability


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


def _q(x: float, *, sig: int = 12) -> float:
    return float(f"{float(x):.{int(sig)}g}")


def build_bridge_toyg_c6_unwrap_stability_boundary_report(*, repo_root: Path) -> dict:
    _ = repo_root

    loop_length = float(2.0 * np.pi)
    tol_step_mean = 0.05
    tol_step_std = 0.05
    min_near_pi_fraction = 0.8
    pi_edge_eps = 0.15

    probes = [
        {
            "probe_id": "interior_unwrap_target_n7",
            "grid_n": 7,
            "unwrap_target": 3.5,
            "amplitude_mod_eps": 0.0,
            "phase_shear_eps": 0.0,
        },
        {
            "probe_id": "edge_near_unwrap_target_n7",
            "grid_n": 7,
            "unwrap_target": 3.5,
            "amplitude_mod_eps": 0.0,
            "phase_shear_eps": 0.01,
        },
        {
            "probe_id": "just_outside_unwrap_target_n7",
            "grid_n": 7,
            "unwrap_target": 3.0,
            "amplitude_mod_eps": 0.0,
            "phase_shear_eps": 0.0,
        },
        {
            "probe_id": "high_shear_unstable_n7",
            "grid_n": 7,
            "unwrap_target": 3.5,
            "amplitude_mod_eps": 0.0,
            "phase_shear_eps": 0.1,
        },
    ]

    samples: list[dict] = []
    for p in probes:
        rep = evaluate_toyg_c6_unwrap_stability(
            grid_n=int(p["grid_n"]),
            loop_length=loop_length,
            unwrap_target=float(p["unwrap_target"]),
            tol_step_mean=tol_step_mean,
            tol_step_std=tol_step_std,
            min_near_pi_fraction=min_near_pi_fraction,
            pi_edge_eps=pi_edge_eps,
            amplitude_mod_eps=float(p["amplitude_mod_eps"]),
            phase_shear_eps=float(p["phase_shear_eps"]),
        )
        samples.append(
            {
                "probe_id": str(p["probe_id"]),
                "grid_n": int(p["grid_n"]),
                "unwrap_target": _q(float(p["unwrap_target"])),
                "phase_shear_eps": _q(float(p["phase_shear_eps"])),
                "near_pi_fraction": _q(float(rep["metrics"]["near_pi_fraction"])),
                "mean_abs_step_error": _q(float(rep["metrics"]["mean_abs_step_error"])),
                "step_std": _q(float(rep["metrics"]["step_std"])),
                "admissible": bool(rep["status"]["admissible"]),
                "reason_code": str(rep["reason_code"]),
            }
        )

    passed = [s for s in samples if bool(s["admissible"])]
    failed = [s for s in samples if not bool(s["admissible"])]

    item = {
        "ticket_id": "BRIDGE_TICKET_TOYG_0003",
        "scan_id": "c6_unwrap_stability_boundary_scan_v1",
        "inputs": {
            "loop_length": _q(loop_length),
            "tol_step_mean": _q(tol_step_mean),
            "tol_step_std": _q(tol_step_std),
            "min_near_pi_fraction": _q(min_near_pi_fraction),
            "pi_edge_eps": _q(pi_edge_eps),
            "probes": [
                {
                    "probe_id": str(p["probe_id"]),
                    "grid_n": int(p["grid_n"]),
                    "unwrap_target": _q(float(p["unwrap_target"])),
                    "phase_shear_eps": _q(float(p["phase_shear_eps"])),
                }
                for p in probes
            ],
        },
        "evidence": {
            "pytest_nodes": [
                "formal/python/tests/test_bridge_toyg_c6_unwrap_stability_perturbation_stability.py::test_bridge_toyg_c6_unwrap_stability_perturbation_stability",
                "formal/python/tests/test_bridge_toyg_c6_unwrap_stability_negative_controls.py::test_bridge_toyg_c6_unwrap_stability_negative_control_not_boundary_sensitive",
                "formal/python/tests/test_bridge_toyg_c6_unwrap_stability_resolution_scan.py::test_bridge_toyg_c6_unwrap_stability_resolution_scan",
            ]
        },
        "samples": samples,
        "summary": {
            "n_samples": len(samples),
            "n_pass": len(passed),
            "n_fail": len(failed),
            "fail_reason_counts": {
                "fail_not_boundary_sensitive": sum(
                    1 for s in failed if s["reason_code"] == "fail_not_boundary_sensitive"
                ),
                "fail_unwrap_step_mean_mismatch": sum(
                    1 for s in failed if s["reason_code"] == "fail_unwrap_step_mean_mismatch"
                ),
                "fail_unwrap_step_variance_high": sum(
                    1 for s in failed if s["reason_code"] == "fail_unwrap_step_variance_high"
                ),
            },
        },
    }

    payload = {
        "schema_version": 1,
        "items": [item],
    }
    out_text = json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    payload["artifact_sha256"] = _sha256_bytes(out_text.encode("utf-8"))
    return payload


def main(argv: Optional[list[str]] = None) -> int:
    p = argparse.ArgumentParser(description="Generate deterministic Toy-G C6 unwrap-stability boundary report.")
    p.add_argument(
        "--out",
        default="formal/quarantine/bridge_tickets/BRIDGE_TOYG_C6_unwrap_stability_BOUNDARY_REPORT.json",
        help=(
            "Repo-relative output JSON path (default: "
            "formal/quarantine/bridge_tickets/BRIDGE_TOYG_C6_unwrap_stability_BOUNDARY_REPORT.json)"
        ),
    )
    p.add_argument("--no-write", action="store_true", help="Do not write the file; just validate generation")

    args = p.parse_args(argv)
    repo_root = _find_repo_root(Path(__file__))

    payload = build_bridge_toyg_c6_unwrap_stability_boundary_report(repo_root=repo_root)
    out_text = json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"

    if not args.no_write:
        out_path = repo_root / str(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(out_text, encoding="utf-8")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())

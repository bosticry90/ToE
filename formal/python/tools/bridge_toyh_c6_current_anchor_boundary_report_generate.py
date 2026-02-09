from __future__ import annotations

"""Boundary report for BRIDGE_TICKET_TOYH_0004 (quarantine-safe)."""

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

from formal.python.tools.bridge_toyh_c6_current_anchor import evaluate_toyh_c6_current_anchor


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


def build_bridge_toyh_c6_current_anchor_boundary_report(*, repo_root: Path) -> dict:
    _ = repo_root

    tol_invariance = 1e-10
    tol_current_anchor = 1e-7
    min_anchor_response = 1e-8

    probes = [
        {
            "probe_id": "baseline_theta_pi_over_3_alpha_0_5_n11",
            "theta": float(np.pi / 3.0),
            "grid_n": 11,
            "amplitude_scale": 1.0,
            "local_phase_shear_alpha": 0.5,
            "anchor_sign": 1.0,
        },
        {
            "probe_id": "small_alpha_control_n11",
            "theta": float(np.pi / 3.0),
            "grid_n": 11,
            "amplitude_scale": 1.0,
            "local_phase_shear_alpha": 1e-6,
            "anchor_sign": 1.0,
        },
        {
            "probe_id": "zero_alpha_response_fail_n11",
            "theta": float(np.pi / 3.0),
            "grid_n": 11,
            "amplitude_scale": 1.0,
            "local_phase_shear_alpha": 0.0,
            "anchor_sign": 1.0,
        },
        {
            "probe_id": "amplitude_scale_fail_n11",
            "theta": float(np.pi / 3.0),
            "grid_n": 11,
            "amplitude_scale": 1.1,
            "local_phase_shear_alpha": 0.5,
            "anchor_sign": 1.0,
        },
        {
            "probe_id": "wrong_anchor_operator_fail_n11",
            "theta": float(np.pi / 3.0),
            "grid_n": 11,
            "amplitude_scale": 1.0,
            "local_phase_shear_alpha": 1e-6,
            "anchor_sign": -1.0,
        },
    ]

    samples: list[dict] = []
    for p in probes:
        rep = evaluate_toyh_c6_current_anchor(
            theta=float(p["theta"]),
            grid_n=int(p["grid_n"]),
            amplitude_scale=float(p["amplitude_scale"]),
            local_phase_shear_alpha=float(p["local_phase_shear_alpha"]),
            tol_invariance=tol_invariance,
            tol_current_anchor=tol_current_anchor,
            min_anchor_response=min_anchor_response,
            anchor_sign=float(p["anchor_sign"]),
        )
        samples.append(
            {
                "probe_id": str(p["probe_id"]),
                "theta": _q(float(p["theta"])),
                "grid_n": int(p["grid_n"]),
                "amplitude_scale": _q(float(p["amplitude_scale"])),
                "local_phase_shear_alpha": _q(float(p["local_phase_shear_alpha"])),
                "anchor_sign": _q(float(p["anchor_sign"])),
                "current_l2_rel": _q(float(rep["metrics"]["current_l2_rel"])),
                "anchor_response": _q(float(rep["metrics"]["anchor_response"])),
                "anchor_error": _q(float(rep["metrics"]["anchor_error"])),
                "admissible": bool(rep["status"]["admissible"]),
                "reason_code": str(rep["reason_code"]),
            }
        )

    passed = [s for s in samples if bool(s["admissible"])]
    failed = [s for s in samples if not bool(s["admissible"])]

    item = {
        "ticket_id": "BRIDGE_TICKET_TOYH_0004",
        "scan_id": "c6_current_anchor_boundary_scan_v1",
        "inputs": {
            "tolerance": _q(tol_invariance),
            "current_anchor_tolerance": _q(tol_current_anchor),
            "min_anchor_response": _q(min_anchor_response),
            "probes": [
                {
                    "probe_id": str(p["probe_id"]),
                    "theta": _q(float(p["theta"])),
                    "grid_n": int(p["grid_n"]),
                    "amplitude_scale": _q(float(p["amplitude_scale"])),
                    "local_phase_shear_alpha": _q(float(p["local_phase_shear_alpha"])),
                    "anchor_sign": _q(float(p["anchor_sign"])),
                }
                for p in probes
            ],
        },
        "evidence": {
            "pytest_nodes": [
                "formal/python/tests/test_bridge_toyh_c6_current_anchor_determinism.py::test_bridge_toyh_c6_current_anchor_resolves_small_alpha_control_case",
                "formal/python/tests/test_bridge_toyh_c6_current_anchor_negative_controls.py::test_bridge_toyh_c6_current_anchor_negative_control_zero_alpha_response_min",
                "formal/python/tests/test_bridge_toyh_c6_current_anchor_negative_controls.py::test_bridge_toyh_c6_current_anchor_negative_control_amplitude_scaling",
                "formal/python/tests/test_bridge_toyh_c6_current_anchor_negative_controls.py::test_bridge_toyh_c6_current_anchor_negative_control_wrong_operator_sign",
                "formal/python/tests/test_bridge_toyh_c6_current_anchor_resolution_scan.py::test_bridge_toyh_c6_current_anchor_resolution_scan",
            ]
        },
        "samples": samples,
        "summary": {
            "n_samples": len(samples),
            "n_pass": len(passed),
            "n_fail": len(failed),
            "fail_reason_counts": {
                "FAIL_CURRENT_INVARIANCE_TOL": sum(1 for s in failed if s["reason_code"] == "FAIL_CURRENT_INVARIANCE_TOL"),
                "FAIL_CURRENT_ANCHOR_RESPONSE_MIN": sum(
                    1 for s in failed if s["reason_code"] == "FAIL_CURRENT_ANCHOR_RESPONSE_MIN"
                ),
                "FAIL_CURRENT_ANCHOR_MISMATCH": sum(
                    1 for s in failed if s["reason_code"] == "FAIL_CURRENT_ANCHOR_MISMATCH"
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
    p = argparse.ArgumentParser(description="Generate deterministic Toy-H C6 current-anchor boundary report.")
    p.add_argument(
        "--out",
        default="formal/quarantine/bridge_tickets/BRIDGE_TOYH_C6_current_anchor_BOUNDARY_REPORT.json",
        help=(
            "Repo-relative output JSON path (default: "
            "formal/quarantine/bridge_tickets/BRIDGE_TOYH_C6_current_anchor_BOUNDARY_REPORT.json)"
        ),
    )
    p.add_argument("--no-write", action="store_true", help="Do not write the file; just validate generation")

    args = p.parse_args(argv)
    repo_root = _find_repo_root(Path(__file__))

    payload = build_bridge_toyh_c6_current_anchor_boundary_report(repo_root=repo_root)
    out_text = json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"

    if not args.no_write:
        out_path = repo_root / str(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(out_text, encoding="utf-8")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())


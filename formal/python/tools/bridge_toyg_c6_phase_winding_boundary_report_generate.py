from __future__ import annotations

"""Boundary report for BRIDGE_TICKET_TOYG_0001 (quarantine-safe)."""

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

from formal.python.tools.bridge_toyg_c6_phase_winding import evaluate_toyg_c6_phase_winding


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


def build_bridge_toyg_c6_phase_winding_boundary_report(*, repo_root: Path) -> dict:
    _ = repo_root

    loop_length = float(2.0 * np.pi)
    tol_winding = 0.05
    unwrap_margin = 1e-6

    probes = [
        {"probe_id": "interior_quantized_n1", "grid_n": 11, "winding_target": 1.0, "amplitude_mod_eps": 0.0},
        {
            "probe_id": "edge_near_quantized_n1_plus",
            "grid_n": 11,
            "winding_target": 1.0 + 0.95 * tol_winding,
            "amplitude_mod_eps": 0.0,
        },
        {
            "probe_id": "just_outside_quantized_n1_plus",
            "grid_n": 11,
            "winding_target": 1.0 + 1.25 * tol_winding,
            "amplitude_mod_eps": 0.0,
        },
        {
            "probe_id": "unwrap_guard_fail_high_winding",
            "grid_n": 7,
            "winding_target": 3.5,
            "amplitude_mod_eps": 0.0,
        },
    ]

    samples: list[dict] = []
    for p in probes:
        rep = evaluate_toyg_c6_phase_winding(
            grid_n=int(p["grid_n"]),
            loop_length=loop_length,
            winding_target=float(p["winding_target"]),
            tol_winding=tol_winding,
            unwrap_margin=unwrap_margin,
            amplitude_mod_eps=float(p["amplitude_mod_eps"]),
        )
        samples.append(
            {
                "probe_id": str(p["probe_id"]),
                "grid_n": int(p["grid_n"]),
                "winding_target": _q(p["winding_target"]),
                "raw_winding": _q(rep["metrics"]["raw_winding"]),
                "nearest_int": int(rep["metrics"]["nearest_int"]),
                "integer_distance": _q(rep["metrics"]["integer_distance"]),
                "max_abs_delta": _q(rep["metrics"]["max_abs_delta"]),
                "admissible": bool(rep["status"]["admissible"]),
                "reason_code": str(rep["reason_code"]),
            }
        )

    passed = [s for s in samples if bool(s["admissible"])]
    failed = [s for s in samples if not bool(s["admissible"])]

    item = {
        "ticket_id": "BRIDGE_TICKET_TOYG_0001",
        "scan_id": "c6_phase_winding_quantization_boundary_scan_v1",
        "inputs": {
            "loop_length": _q(loop_length),
            "tol_winding": _q(tol_winding),
            "unwrap_margin": _q(unwrap_margin),
            "probes": [
                {
                    "probe_id": str(p["probe_id"]),
                    "grid_n": int(p["grid_n"]),
                    "winding_target": _q(p["winding_target"]),
                }
                for p in probes
            ],
        },
        "evidence": {
            "pytest_nodes": [
                "formal/python/tests/test_bridge_toyg_c6_phase_winding_perturbation_stability.py::test_bridge_toyg_c6_phase_winding_perturbation_stability",
                "formal/python/tests/test_bridge_toyg_c6_phase_winding_negative_controls.py::test_bridge_toyg_c6_phase_winding_negative_control_quantization_failure",
                "formal/python/tests/test_bridge_toyg_c6_phase_winding_resolution_scan.py::test_bridge_toyg_c6_phase_winding_resolution_scan",
            ]
        },
        "samples": samples,
        "summary": {
            "n_samples": len(samples),
            "n_pass": len(passed),
            "n_fail": len(failed),
            "fail_reason_counts": {
                "fail_not_integer_close": sum(1 for s in failed if s["reason_code"] == "fail_not_integer_close"),
                "fail_unwrap_discontinuity_guard": sum(
                    1 for s in failed if s["reason_code"] == "fail_unwrap_discontinuity_guard"
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
    p = argparse.ArgumentParser(description="Generate the deterministic Toy-G C6 phase-winding boundary report.")
    p.add_argument(
        "--out",
        default="formal/quarantine/bridge_tickets/BRIDGE_TOYG_C6_phase_winding_BOUNDARY_REPORT.json",
        help=(
            "Repo-relative output JSON path (default: "
            "formal/quarantine/bridge_tickets/BRIDGE_TOYG_C6_phase_winding_BOUNDARY_REPORT.json)"
        ),
    )
    p.add_argument("--no-write", action="store_true", help="Do not write the file; just validate generation")

    args = p.parse_args(argv)
    repo_root = _find_repo_root(Path(__file__))

    payload = build_bridge_toyg_c6_phase_winding_boundary_report(repo_root=repo_root)
    out_text = json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"

    if not args.no_write:
        out_path = repo_root / str(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(out_text, encoding="utf-8")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())

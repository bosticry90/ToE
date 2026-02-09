from __future__ import annotations

"""Boundary report for BRIDGE_TICKET_TOYHG_0001 (quarantine-safe)."""

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

from formal.python.tools.bridge_toyhg_c6_pair_compatibility import (
    evaluate_toyhg_c6_pair_compatibility,
)


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


def build_bridge_toyhg_c6_pair_compatibility_boundary_report(*, repo_root: Path) -> dict:
    _ = repo_root

    probes = [
        {
            "probe_id": "baseline_all_pass",
            "toyh_phase_bridge_pass": True,
            "toyh_current_bridge_pass": True,
            "toyg_bridge_pass": True,
        },
        {
            "probe_id": "stress_c6_amplitude_scale_pair",
            "toyh_phase_bridge_pass": False,
            "toyh_current_bridge_pass": False,
            "toyg_bridge_pass": True,
        },
        {
            "probe_id": "stress_toyh_current_only_pair",
            "toyh_phase_bridge_pass": True,
            "toyh_current_bridge_pass": False,
            "toyg_bridge_pass": True,
        },
        {
            "probe_id": "stress_toyg_only_pair",
            "toyh_phase_bridge_pass": True,
            "toyh_current_bridge_pass": True,
            "toyg_bridge_pass": False,
        },
        {
            "probe_id": "all_fail_consistent",
            "toyh_phase_bridge_pass": False,
            "toyh_current_bridge_pass": False,
            "toyg_bridge_pass": False,
        },
    ]

    samples: list[dict] = []
    for p in probes:
        rep = evaluate_toyhg_c6_pair_compatibility(
            toyh_phase_bridge_pass=bool(p["toyh_phase_bridge_pass"]),
            toyh_current_bridge_pass=bool(p["toyh_current_bridge_pass"]),
            toyg_bridge_pass=bool(p["toyg_bridge_pass"]),
        )
        metrics = dict(rep.get("metrics", {}))
        status = dict(rep.get("status", {}))
        samples.append(
            {
                "probe_id": str(p["probe_id"]),
                "toyh_phase_bridge_pass": bool(p["toyh_phase_bridge_pass"]),
                "toyh_current_bridge_pass": bool(p["toyh_current_bridge_pass"]),
                "toyg_bridge_pass": bool(p["toyg_bridge_pass"]),
                "signature": str(metrics.get("signature", "")),
                "signed_margin": float(metrics.get("signed_margin", 0.0)),
                "admissible": bool(status.get("admissible")),
                "localization_note": str(status.get("localization_note", "")),
                "reason_code": str(rep.get("reason_code", "")),
            }
        )

    passed = [s for s in samples if bool(s["admissible"])]
    failed = [s for s in samples if not bool(s["admissible"])]

    item = {
        "ticket_id": "BRIDGE_TICKET_TOYHG_0001",
        "scan_id": "c6_pair_compatibility_boundary_scan_v1",
        "inputs": {
            "joint_rule": "all_three_channels_must_match",
            "probes": [
                {
                    "probe_id": str(p["probe_id"]),
                    "toyh_phase_bridge_pass": bool(p["toyh_phase_bridge_pass"]),
                    "toyh_current_bridge_pass": bool(p["toyh_current_bridge_pass"]),
                    "toyg_bridge_pass": bool(p["toyg_bridge_pass"]),
                }
                for p in probes
            ],
        },
        "evidence": {
            "pytest_nodes": [
                "formal/python/tests/test_bridge_toyhg_c6_pair_compatibility_determinism.py::test_bridge_toyhg_c6_pair_compatibility_deterministic",
                "formal/python/tests/test_bridge_toyhg_c6_pair_compatibility_negative_controls.py::test_bridge_toyhg_c6_pair_compatibility_negative_control_phase_current_vs_toyg",
                "formal/python/tests/test_bridge_toyhg_c6_pair_compatibility_negative_controls.py::test_bridge_toyhg_c6_pair_compatibility_negative_control_current_only",
                "formal/python/tests/test_bridge_toyhg_c6_pair_compatibility_resolution_scan.py::test_bridge_toyhg_c6_pair_compatibility_resolution_signature_map",
            ]
        },
        "samples": samples,
        "summary": {
            "n_samples": len(samples),
            "n_pass": len(passed),
            "n_fail": len(failed),
            "fail_reason_counts": {
                "FAIL_PAIR_TOYG_MISMATCH": sum(1 for s in failed if s["reason_code"] == "FAIL_PAIR_TOYG_MISMATCH"),
                "FAIL_PAIR_CURRENT_MISMATCH": sum(1 for s in failed if s["reason_code"] == "FAIL_PAIR_CURRENT_MISMATCH"),
                "FAIL_PAIR_PHASE_MISMATCH": sum(1 for s in failed if s["reason_code"] == "FAIL_PAIR_PHASE_MISMATCH"),
                "FAIL_PAIR_MIXED": sum(1 for s in failed if s["reason_code"] == "FAIL_PAIR_MIXED"),
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
    p = argparse.ArgumentParser(description="Generate deterministic Toy-H/Toy-G pair-compatibility boundary report.")
    p.add_argument(
        "--out",
        default="formal/quarantine/bridge_tickets/BRIDGE_TOYHG_C6_pair_compatibility_BOUNDARY_REPORT.json",
        help=(
            "Repo-relative output JSON path (default: "
            "formal/quarantine/bridge_tickets/BRIDGE_TOYHG_C6_pair_compatibility_BOUNDARY_REPORT.json)"
        ),
    )
    p.add_argument("--no-write", action="store_true", help="Do not write the file; just validate generation")

    args = p.parse_args(argv)
    repo_root = _find_repo_root(Path(__file__))

    payload = build_bridge_toyhg_c6_pair_compatibility_boundary_report(repo_root=repo_root)
    out_text = json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"

    if not args.no_write:
        out_path = repo_root / str(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(out_text, encoding="utf-8")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())


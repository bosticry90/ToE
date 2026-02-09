from __future__ import annotations

"""Deterministic mismatch-localization report for Toy-H ↔ C6 orthogonality.

Goal
- Convert orthogonality disagreements (pass_fail / fail_pass) into a bounded,
  deterministic report with signed margins and deterministic reason codes.
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

from formal.python.tools.bridge_toyh_c6_orthogonality_report_generate import (
    build_bridge_toyh_c6_orthogonality_report,
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


def _q(x: float, *, sig: int = 12) -> float:
    return float(f"{float(x):.{int(sig)}g}")


def _phase_invariance_margin(*, metrics: dict, tol: float) -> float:
    return float(
        tol
        - max(
            float(metrics["norm_rel"]),
            float(metrics["energy_rel"]),
            float(metrics["rhs_rel"]),
        )
    )


def _phase_control_margin(*, theta: float, metrics: dict, phase_control_min: float) -> Optional[float]:
    if abs(float(theta)) <= 1e-18:
        return None
    return float(float(metrics["phase_sensitive_delta"]) - phase_control_min)


def _current_invariance_margin(*, metrics: dict, tol: float) -> float:
    return float(tol - float(metrics["current_l2_rel"]))


def _current_control_margin(*, metrics: dict, current_control_min: float) -> float:
    return float(float(metrics["local_phase_shear_rel"]) - current_control_min)


def _failure_reason_and_margin(
    *,
    pair_status: str,
    phase_reason: str,
    current_reason: str,
    phase_inv_margin: float,
    phase_control_margin: Optional[float],
    current_inv_margin: float,
    current_control_margin: float,
    near_boundary_eps: float,
) -> tuple[str, float]:
    if pair_status == "fail_pass":
        if phase_reason == "FAIL_PHASE_INVARIANCE_TOL":
            return "phase_invariance_violation", phase_inv_margin
        if phase_reason == "FAIL_PHASE_CHANNEL_CONTROL_MIN":
            m = float(-1.0 if phase_control_margin is None else phase_control_margin)
            if abs(m) <= near_boundary_eps:
                return "phase_threshold_margin_small", m
            return "phase_observable_sensitivity", m
        m = float(min(phase_inv_margin, phase_control_margin if phase_control_margin is not None else 1.0))
        return "phase_unclassified_fail", m

    if pair_status == "pass_fail":
        if current_reason == "FAIL_CURRENT_INVARIANCE_TOL":
            return "current_invariance_violation", current_inv_margin
        if current_reason == "FAIL_CURRENT_CHANNEL_CONTROL_MIN":
            m = float(current_control_margin)
            if abs(m) <= near_boundary_eps:
                return "current_threshold_margin_small", m
            return "current_observable_sensitivity", m
        return "current_unclassified_fail", float(min(current_inv_margin, current_control_margin))

    raise ValueError(f"Unexpected pair_status for mismatch report: {pair_status!r}")


def build_bridge_toyh_c6_orthogonality_mismatch_report(*, repo_root: Path) -> dict:
    source = build_bridge_toyh_c6_orthogonality_report(repo_root=repo_root)

    shared = dict(source.get("shared_probe_set", {}))
    tol = float(shared.get("tolerance", 1e-10))
    phase_control_min = float(shared.get("phase_channel_control_min", 1e-3))
    current_control_min = float(shared.get("current_channel_control_min", 1e-3))
    near_boundary_eps = 1e-3

    src_items = list(source.get("items", []))
    mismatch_items: list[dict] = []

    for it in src_items:
        pair_status = str(it.get("pair_status", ""))
        if pair_status not in {"pass_fail", "fail_pass"}:
            continue

        phase = dict(it.get("phase_channel", {}))
        current = dict(it.get("current_channel", {}))
        phase_metrics = dict(phase.get("metrics", {}))
        current_metrics = dict(current.get("metrics", {}))
        theta = float(it.get("theta"))

        phase_inv_margin = _phase_invariance_margin(metrics=phase_metrics, tol=tol)
        phase_ctrl_margin = _phase_control_margin(
            theta=theta,
            metrics=phase_metrics,
            phase_control_min=phase_control_min,
        )
        current_inv_margin = _current_invariance_margin(metrics=current_metrics, tol=tol)
        current_ctrl_margin = _current_control_margin(
            metrics=current_metrics,
            current_control_min=current_control_min,
        )

        reason_code, signed_margin = _failure_reason_and_margin(
            pair_status=pair_status,
            phase_reason=str(phase.get("reason_code", "")),
            current_reason=str(current.get("reason_code", "")),
            phase_inv_margin=phase_inv_margin,
            phase_control_margin=phase_ctrl_margin,
            current_inv_margin=current_inv_margin,
            current_control_margin=current_ctrl_margin,
            near_boundary_eps=near_boundary_eps,
        )

        mismatch_items.append(
            {
                "probe_id": str(it.get("probe_id")),
                "probe_kind": str(it.get("probe_kind")),
                "pair_status": pair_status,
                "theta": _q(theta),
                "grid_n": int(it.get("grid_n")),
                "amplitude_scale": _q(float(it.get("amplitude_scale"))),
                "local_phase_shear_alpha": _q(float(it.get("local_phase_shear_alpha"))),
                "phase_reason_code": str(phase.get("reason_code")),
                "current_reason_code": str(current.get("reason_code")),
                "signed_margin": _q(signed_margin),
                "failure_reason_code": reason_code,
                "near_boundary": bool(abs(signed_margin) <= near_boundary_eps),
                "localization_note": str(it.get("localization_note")),
                "phase_invariance_margin": _q(phase_inv_margin),
                "phase_control_margin": None if phase_ctrl_margin is None else _q(phase_ctrl_margin),
                "current_invariance_margin": _q(current_inv_margin),
                "current_control_margin": _q(current_ctrl_margin),
            }
        )

    pair_counts = {
        "pass_fail": sum(1 for it in mismatch_items if it["pair_status"] == "pass_fail"),
        "fail_pass": sum(1 for it in mismatch_items if it["pair_status"] == "fail_pass"),
    }

    reason_counts = {
        reason: sum(1 for it in mismatch_items if it["failure_reason_code"] == reason)
        for reason in sorted({str(it["failure_reason_code"]) for it in mismatch_items})
    }

    payload = {
        "schema_version": 1,
        "report_id": "BRIDGE_TOYH_C6_ORTHOGONALITY_MISMATCH_REPORT",
        "source_report": {
            "report_id": str(source.get("report_id", "")),
            "artifact_sha256": str(source.get("artifact_sha256", "")),
            "summary_counts": dict(source.get("summary", {}).get("counts", {})),
            "nonredundant": bool(source.get("summary", {}).get("nonredundant", False)),
        },
        "thresholds": {
            "tolerance": tol,
            "phase_channel_control_min": phase_control_min,
            "current_channel_control_min": current_control_min,
            "near_boundary_eps": near_boundary_eps,
        },
        "evidence": {
            "pytest_nodes": [
                "formal/python/tests/test_bridge_toyh_c6_orthogonality_mismatch_semantics.py::test_bridge_toyh_c6_orthogonality_mismatch_report_contains_only_disagreements",
                "formal/python/tests/test_bridge_toyh_c6_orthogonality_mismatch_semantics.py::test_bridge_toyh_c6_orthogonality_mismatch_report_has_signed_margins_and_reason_codes",
                "formal/python/tests/test_bridge_toyh_c6_orthogonality_robustness_guard.py::test_bridge_toyh_c6_orthogonality_nonredundancy_robustness_guard",
            ]
        },
        "items": mismatch_items,
        "summary": {
            "n_mismatch": len(mismatch_items),
            "pair_counts": pair_counts,
            "failure_reason_counts": reason_counts,
            "localization_counts": {
                "toyh_observable_construction": sum(
                    1 for it in mismatch_items if it["localization_note"] == "toyh_observable_construction"
                ),
                "c6_side_constraint": sum(1 for it in mismatch_items if it["localization_note"] == "c6_side_constraint"),
                "mixed": sum(1 for it in mismatch_items if it["localization_note"] == "mixed"),
                "none": sum(1 for it in mismatch_items if it["localization_note"] == "none"),
            },
            "note": "Mismatch report includes pass_fail and fail_pass probes only.",
        },
    }

    out_text = json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    payload["artifact_sha256"] = _sha256_bytes(out_text.encode("utf-8"))
    return payload


def main(argv: Optional[list[str]] = None) -> int:
    p = argparse.ArgumentParser(
        description="Generate deterministic Toy-H↔C6 orthogonality mismatch-localization report."
    )
    p.add_argument(
        "--out",
        default="formal/quarantine/bridge_tickets/BRIDGE_TOYH_C6_ORTHOGONALITY_MISMATCH_REPORT.json",
        help=(
            "Repo-relative output JSON path (default: "
            "formal/quarantine/bridge_tickets/BRIDGE_TOYH_C6_ORTHOGONALITY_MISMATCH_REPORT.json)"
        ),
    )
    p.add_argument("--no-write", action="store_true", help="Do not write the file; just validate generation")

    args = p.parse_args(argv)
    repo_root = _find_repo_root(Path(__file__))

    payload = build_bridge_toyh_c6_orthogonality_mismatch_report(repo_root=repo_root)
    out_text = json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"

    if not args.no_write:
        out_path = repo_root / str(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(out_text, encoding="utf-8")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())

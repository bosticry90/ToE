from __future__ import annotations

"""Mismatch-localization report for bridge-program orthogonality (Toy-H + Toy-G)."""

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

from formal.python.tools.bridge_program_orthogonality_report_generate import build_bridge_program_orthogonality_report


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


def _phase_legacy_signed_margin(*, probe: dict, shared: dict) -> float:
    phase = dict(probe["toyh_phase"])
    metrics = dict(phase.get("metrics", {}))
    tol = float(shared["toyh_tolerance"])
    phase_ctrl_min = float(shared["phase_channel_control_min"])

    inv_margin = tol - max(
        float(metrics["norm_rel"]),
        float(metrics["energy_rel"]),
        float(metrics["rhs_rel"]),
    )
    ctrl_margin = float(metrics["phase_sensitive_delta"]) - phase_ctrl_min
    reason = str(phase["reason_code"])

    if reason == "FAIL_PHASE_INVARIANCE_TOL":
        return float(inv_margin)
    if reason == "FAIL_PHASE_CHANNEL_CONTROL_MIN":
        return float(ctrl_margin)
    return float(min(inv_margin, ctrl_margin))


def _phase_anchor_signed_margin(*, probe: dict, shared: dict) -> float:
    phase_anchor = dict(probe["toyh_phase_anchor"])
    metrics = dict(phase_anchor.get("metrics", {}))
    tol = float(shared["toyh_tolerance"])
    phase_anchor_tol = float(shared.get("phase_anchor_tolerance", 1e-7))
    min_anchor_magnitude = 1e-8

    inv_margin = tol - max(
        float(metrics["norm_rel"]),
        float(metrics["energy_rel"]),
        float(metrics["rhs_rel"]),
    )
    anchor_phase_margin = phase_anchor_tol - float(metrics["anchor_phase_error"])
    anchor_mag_margin = float(metrics["anchor_magnitude_ratio"]) - min_anchor_magnitude
    reason = str(phase_anchor["reason_code"])

    if reason == "FAIL_PHASE_INVARIANCE_TOL":
        return float(inv_margin)
    if reason == "FAIL_ANCHOR_PHASE_MISMATCH":
        return float(anchor_phase_margin)
    if reason == "FAIL_ANCHOR_MAGNITUDE_MIN":
        return float(anchor_mag_margin)
    return float(min(inv_margin, anchor_phase_margin, anchor_mag_margin))


def _phase_bridge_signed_margin(*, legacy_margin: float, anchor_margin: float) -> float:
    # Toy-H phase bridge channel passes if either legacy phase channel or
    # phase-anchor channel passes.
    return float(max(float(legacy_margin), float(anchor_margin)))


def _current_signed_margin(*, probe: dict, shared: dict) -> float:
    current = dict(probe["toyh_current"])
    metrics = dict(current.get("metrics", {}))
    tol = float(shared["toyh_tolerance"])
    control_min = float(shared["current_channel_control_min"])

    inv_margin = tol - float(metrics["current_l2_rel"])
    ctrl_margin = float(metrics["local_phase_shear_rel"]) - control_min
    reason = str(current["reason_code"])

    if reason == "FAIL_CURRENT_INVARIANCE_TOL":
        return float(inv_margin)
    if reason == "FAIL_CURRENT_CHANNEL_CONTROL_MIN":
        return float(ctrl_margin)
    return float(min(inv_margin, ctrl_margin))


def _current_anchor_signed_margin(*, probe: dict, shared: dict) -> float:
    current_anchor = dict(probe.get("toyh_current_anchor", {}))
    metrics = dict(current_anchor.get("metrics", {}))
    tol = float(shared.get("toyh_tolerance", 1e-10))
    anchor_tol = float(shared.get("current_anchor_tolerance", 1e-7))
    min_anchor_response = float(shared.get("current_anchor_min_response", 1e-8))

    inv_margin = tol - float(metrics.get("current_l2_rel", 0.0))
    anchor_response_margin = float(metrics.get("anchor_response", 0.0)) - min_anchor_response
    anchor_match_margin = anchor_tol - float(metrics.get("anchor_error", 0.0))
    reason = str(current_anchor.get("reason_code", ""))

    if reason == "FAIL_CURRENT_INVARIANCE_TOL":
        return float(inv_margin)
    if reason == "FAIL_CURRENT_ANCHOR_RESPONSE_MIN":
        return float(anchor_response_margin)
    if reason == "FAIL_CURRENT_ANCHOR_MISMATCH":
        return float(anchor_match_margin)
    return float(min(inv_margin, anchor_response_margin, anchor_match_margin))


def _current_bridge_signed_margin(*, current_margin: float, current_anchor_margin: float) -> float:
    # Toy-H current bridge channel passes if either legacy current channel or
    # current-anchor channel passes.
    return float(max(float(current_margin), float(current_anchor_margin)))


def _winding_signed_margin(*, probe: dict, shared: dict) -> float:
    winding = dict(probe["toyg_winding"])
    metrics = dict(winding.get("metrics", {}))
    tol_winding = float(shared["toyg_tol_winding"])
    unwrap_margin = float(shared["toyg_unwrap_margin"])
    reason = str(winding["reason_code"])

    integer_margin = tol_winding - float(metrics["integer_distance"])
    unwrap_guard_limit = float(np.pi - unwrap_margin)
    unwrap_guard_margin = unwrap_guard_limit - float(metrics["max_abs_delta"])

    if reason == "fail_not_integer_close":
        return float(integer_margin)
    if reason == "fail_unwrap_discontinuity_guard":
        return float(unwrap_guard_margin)
    return float(min(integer_margin, unwrap_guard_margin))


def _mode_signed_margin(*, probe: dict, shared: dict) -> float:
    mode = dict(probe["toyg_mode"])
    metrics = dict(mode.get("metrics", {}))
    tol_mode = float(shared["toyg_tol_mode"])
    peak_fraction_min = float(shared["toyg_peak_fraction_min"])
    reason = str(mode["reason_code"])

    integer_margin = tol_mode - float(metrics["integer_distance"])
    peak_margin = float(metrics["peak_fraction"]) - peak_fraction_min
    index_margin = 0.5 - abs(float(metrics["peak_index_signed"]) - float(metrics["nearest_int"]))

    if reason == "fail_not_integer_close":
        return float(integer_margin)
    if reason == "fail_peak_fraction_low":
        return float(peak_margin)
    if reason == "fail_mode_index_mismatch":
        return float(index_margin)
    return float(min(integer_margin, peak_margin, index_margin))


def _unwrap_signed_margin(*, probe: dict, shared: dict) -> float:
    unwrap = dict(probe["toyg_unwrap"])
    metrics = dict(unwrap.get("metrics", {}))
    tol_step_mean = float(shared["toyg_tol_unwrap_step_mean"])
    tol_step_std = float(shared["toyg_tol_unwrap_step_std"])
    min_near_pi_fraction = float(shared["toyg_min_near_pi_fraction"])
    reason = str(unwrap["reason_code"])

    mean_margin = tol_step_mean - float(metrics["mean_abs_step_error"])
    std_margin = tol_step_std - float(metrics["step_std"])
    near_pi_margin = float(metrics["near_pi_fraction"]) - min_near_pi_fraction

    if reason == "fail_not_boundary_sensitive":
        return float(near_pi_margin)
    if reason == "fail_unwrap_step_mean_mismatch":
        return float(mean_margin)
    if reason == "fail_unwrap_step_variance_high":
        return float(std_margin)
    return float(min(mean_margin, std_margin, near_pi_margin))


def _bridge_signed_margin(*, winding_margin: float, mode_margin: float, unwrap_margin: float) -> float:
    # Toy-G bridge channel passes if any of winding/mode/unwrap channels passes.
    return float(max(float(winding_margin), float(mode_margin), float(unwrap_margin)))


def _pair_signed_margin(*, probe: dict) -> float:
    pair = dict(probe.get("toyhg_pair_bridge", {}))
    metrics = dict(pair.get("metrics", {}))
    if "signed_margin" in metrics:
        return float(metrics["signed_margin"])
    return 0.1 if bool(pair.get("pass")) else -0.1


def _mismatch_reason_code(*, phase_pass: bool, current_pass: bool, pair_pass: bool) -> str:
    fails = []
    if not phase_pass:
        fails.append("phase")
    if not current_pass:
        fails.append("current")
    if not pair_pass:
        fails.append("pair")

    if fails == ["phase"]:
        return "mismatch_toyh_phase_only"
    if fails == ["current"]:
        return "mismatch_toyh_current_only"
    if fails == ["pair"]:
        return "mismatch_toyhg_pair_only"
    if fails == ["phase", "current"]:
        return "mismatch_toyh_pair_only"
    if fails == ["phase", "pair"]:
        return "mismatch_phase_and_pair"
    if fails == ["current", "pair"]:
        return "mismatch_current_and_pair"
    return "mismatch_mixed"


def build_bridge_program_orthogonality_mismatch_report(*, repo_root: Path, tolerance_profile: str = "baseline") -> dict:
    src = build_bridge_program_orthogonality_report(repo_root=repo_root, tolerance_profile=str(tolerance_profile))
    shared = dict(src["shared_probe_set"])

    mismatch_items: list[dict] = []
    for probe in src.get("items", []):
        phase_pass = bool(probe["toyh_phase_bridge"]["pass"])
        current_pass = bool(dict(probe.get("toyh_current_bridge", probe["toyh_current"])).get("pass"))
        pair_pass = bool(dict(probe.get("toyhg_pair_bridge", probe["toyg_bridge"])).get("pass"))
        toyg_bridge_pass = bool(probe["toyg_bridge"]["pass"])

        if len({phase_pass, current_pass, pair_pass}) <= 1:
            continue

        phase_legacy_margin = _phase_legacy_signed_margin(probe=probe, shared=shared)
        phase_anchor_margin = _phase_anchor_signed_margin(probe=probe, shared=shared)
        phase_bridge_margin = _phase_bridge_signed_margin(
            legacy_margin=phase_legacy_margin,
            anchor_margin=phase_anchor_margin,
        )

        current_margin = _current_signed_margin(probe=probe, shared=shared)
        current_anchor_margin = _current_anchor_signed_margin(probe=probe, shared=shared)
        current_bridge_margin = _current_bridge_signed_margin(
            current_margin=current_margin,
            current_anchor_margin=current_anchor_margin,
        )
        winding_margin = _winding_signed_margin(probe=probe, shared=shared)
        mode_margin = _mode_signed_margin(probe=probe, shared=shared)
        unwrap_margin = _unwrap_signed_margin(probe=probe, shared=shared)
        bridge_margin = _bridge_signed_margin(
            winding_margin=winding_margin,
            mode_margin=mode_margin,
            unwrap_margin=unwrap_margin,
        )
        pair_margin = _pair_signed_margin(probe=probe)

        mismatch_items.append(
            {
                "probe_id": str(probe["probe_id"]),
                "probe_kind": str(probe["probe_kind"]),
                "signature": str(probe["signature"]),
                "reason_code": _mismatch_reason_code(
                    phase_pass=phase_pass,
                    current_pass=current_pass,
                    pair_pass=pair_pass,
                ),
                "channels": {
                    "toyh_phase_bridge": {
                        "pass": phase_pass,
                        "reason_code": str(probe["toyh_phase_bridge"]["reason_code"]),
                        "signed_margin": _q(phase_bridge_margin),
                    },
                    "toyh_phase": {
                        "pass": bool(probe["toyh_phase"]["pass"]),
                        "reason_code": str(probe["toyh_phase"]["reason_code"]),
                        "signed_margin": _q(phase_legacy_margin),
                    },
                    "toyh_phase_anchor": {
                        "pass": bool(probe["toyh_phase_anchor"]["pass"]),
                        "reason_code": str(probe["toyh_phase_anchor"]["reason_code"]),
                        "signed_margin": _q(phase_anchor_margin),
                    },
                    "toyh_current": {
                        "pass": bool(probe["toyh_current"]["pass"]),
                        "reason_code": str(probe["toyh_current"]["reason_code"]),
                        "signed_margin": _q(current_margin),
                    },
                    "toyh_current_anchor": {
                        "pass": bool(probe["toyh_current_anchor"]["pass"]),
                        "reason_code": str(probe["toyh_current_anchor"]["reason_code"]),
                        "signed_margin": _q(current_anchor_margin),
                    },
                    "toyh_current_bridge": {
                        "pass": current_pass,
                        "reason_code": str(probe["toyh_current_bridge"]["reason_code"]),
                        "signed_margin": _q(current_bridge_margin),
                    },
                    "toyg_bridge": {
                        "pass": toyg_bridge_pass,
                        "reason_code": str(probe["toyg_bridge"]["reason_code"]),
                        "signed_margin": _q(bridge_margin),
                    },
                    "toyhg_pair_bridge": {
                        "pass": pair_pass,
                        "reason_code": str(probe["toyhg_pair_bridge"]["reason_code"]),
                        "signed_margin": _q(pair_margin),
                    },
                    "toyg_winding": {
                        "pass": bool(probe["toyg_winding"]["pass"]),
                        "reason_code": str(probe["toyg_winding"]["reason_code"]),
                        "signed_margin": _q(winding_margin),
                    },
                    "toyg_mode": {
                        "pass": bool(probe["toyg_mode"]["pass"]),
                        "reason_code": str(probe["toyg_mode"]["reason_code"]),
                        "signed_margin": _q(mode_margin),
                    },
                    "toyg_unwrap": {
                        "pass": bool(probe["toyg_unwrap"]["pass"]),
                        "reason_code": str(probe["toyg_unwrap"]["reason_code"]),
                        "signed_margin": _q(unwrap_margin),
                    },
                },
                "localization_note": str(probe["localization_note"]),
            }
        )

    reason_codes = sorted({str(it["reason_code"]) for it in mismatch_items})
    reason_counts = {rc: sum(1 for it in mismatch_items if it["reason_code"] == rc) for rc in reason_codes}

    payload = {
        "schema_version": 1,
        "report_id": "BRIDGE_PROGRAM_ORTHOGONALITY_MISMATCH_REPORT",
        "tolerance_profile_selected_v5": str(tolerance_profile),
        "source_report": {
            "report_id": str(src["report_id"]),
            "artifact_sha256": str(src["artifact_sha256"]),
            "summary": dict(src["summary"]),
        },
        "evidence": {
            "pytest_nodes": [
                "formal/python/tests/test_bridge_program_orthogonality_mismatch_semantics.py::test_bridge_program_orthogonality_mismatch_report_contains_only_signature_disagreements",
                "formal/python/tests/test_bridge_program_orthogonality_mismatch_semantics.py::test_bridge_program_orthogonality_mismatch_signed_margins_are_structured",
                "formal/python/tests/test_bridge_program_orthogonality_robustness_guard.py::test_bridge_program_orthogonality_nonredundancy_robustness_guard",
            ]
        },
        "items": mismatch_items,
        "summary": {
            "n_mismatch": len(mismatch_items),
            "reason_code_counts": reason_counts,
            "note": "Contains only probes where channel pass/fail outcomes disagree.",
        },
    }

    out_text = json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    payload["artifact_sha256"] = _sha256_bytes(out_text.encode("utf-8"))
    return payload


def main(argv: Optional[list[str]] = None) -> int:
    p = argparse.ArgumentParser(description="Generate deterministic bridge-program orthogonality mismatch report.")
    p.add_argument(
        "--out",
        default="formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_MISMATCH_REPORT.json",
        help=(
            "Repo-relative output JSON path (default: "
            "formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_MISMATCH_REPORT.json)"
        ),
    )
    p.add_argument("--no-write", action="store_true", help="Do not write the file; just validate generation")
    p.add_argument(
        "--tolerance-profile",
        default="baseline",
        choices=["baseline", "v5_t1", "v5_t2"],
        help="Pinned tolerance profile (default: baseline).",
    )

    args = p.parse_args(argv)
    repo_root = _find_repo_root(Path(__file__))

    payload = build_bridge_program_orthogonality_mismatch_report(
        repo_root=repo_root,
        tolerance_profile=str(args.tolerance_profile),
    )
    out_text = json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"

    if not args.no_write:
        out_path = repo_root / str(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(out_text, encoding="utf-8")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())

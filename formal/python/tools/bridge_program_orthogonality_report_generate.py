from __future__ import annotations

"""Bridge-program orthogonality report (Toy-H + Toy-G on C6, quarantine-safe)."""

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

from formal.python.tools.bridge_toyg_c6_mode_index_quantization import (
    evaluate_toyg_c6_mode_index_quantization,
)
from formal.python.tools.bridge_toyg_c6_phase_winding import evaluate_toyg_c6_phase_winding
from formal.python.tools.bridge_toyg_c6_unwrap_stability import evaluate_toyg_c6_unwrap_stability
from formal.python.tools.bridge_toyh_c6_current_anchor import evaluate_toyh_c6_current_anchor
from formal.python.tools.bridge_toyh_c6_orthogonality_report_generate import _current_channel, _phase_channel
from formal.python.tools.bridge_toyh_c6_phase_anchor import evaluate_toyh_c6_phase_anchor
from formal.python.tools.bridge_toyhg_c6_pair_compatibility import (
    evaluate_toyhg_c6_pair_compatibility,
)

_V5_TOLERANCE_PROFILES = {
    "baseline": {
        "toyh_tolerance": 1e-10,
        "phase_anchor_tolerance": 1e-7,
        "current_anchor_tolerance": 1e-7,
        "current_anchor_min_response": 1e-8,
    },
    "v5_t1": {
        "toyh_tolerance": 5e-11,
        "phase_anchor_tolerance": 5e-8,
        "current_anchor_tolerance": 5e-8,
        "current_anchor_min_response": 1.1e-8,
    },
    "v5_t2": {
        "toyh_tolerance": 1e-15,
        "phase_anchor_tolerance": 2e-8,
        "current_anchor_tolerance": 2e-8,
        "current_anchor_min_response": 1.25e-8,
    },
}


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


def _signature(*, phase_bridge_pass: bool, current_bridge_pass: bool, pair_bridge_pass: bool) -> str:
    p = "P" if phase_bridge_pass else "F"
    c = "P" if current_bridge_pass else "F"
    g = "P" if pair_bridge_pass else "F"
    return f"{p}-{c}-{g}"


def _failing_channels(*, phase_bridge_pass: bool, current_bridge_pass: bool, pair_bridge_pass: bool) -> list[str]:
    out: list[str] = []
    if not phase_bridge_pass:
        out.append("toyh_phase_bridge")
    if not current_bridge_pass:
        out.append("toyh_current_bridge")
    if not pair_bridge_pass:
        out.append("toyhg_pair_bridge")
    return out


def _localization_note(fails: list[str]) -> str:
    if not fails:
        return "none"
    if fails == ["toyh_phase_bridge"]:
        return "toyh_phase_channel"
    if fails == ["toyh_current_bridge"]:
        return "toyh_current_channel"
    if fails == ["toyhg_pair_bridge"]:
        return "pair_compatibility_channel"
    if fails == ["toyh_phase_bridge", "toyh_current_bridge"]:
        return "c6_side_constraint"
    if fails == ["toyh_phase_bridge", "toyhg_pair_bridge"]:
        return "phase_pair_interaction"
    if fails == ["toyh_current_bridge", "toyhg_pair_bridge"]:
        return "current_pair_interaction"
    return "mixed"


def _toyh_phase_bridge_reason(
    *,
    phase_pass: bool,
    anchor_pass: bool,
    phase_reason: str,
    anchor_reason: str,
) -> str:
    tags = [
        "P" if phase_pass else "p0",
        "A" if anchor_pass else "a0",
    ]
    status = "PASS" if (phase_pass or anchor_pass) else "FAIL"
    return f"{status}__{'_'.join(tags)}__{phase_reason}__{anchor_reason}"


def _toyg_bridge_reason(
    *,
    winding_pass: bool,
    mode_pass: bool,
    unwrap_pass: bool,
    winding_reason: str,
    mode_reason: str,
    unwrap_reason: str,
) -> str:
    tags = [
        "W" if winding_pass else "w0",
        "M" if mode_pass else "m0",
        "U" if unwrap_pass else "u0",
    ]
    status = "PASS" if (winding_pass or mode_pass or unwrap_pass) else "FAIL"
    return f"{status}__{'_'.join(tags)}__{winding_reason}__{mode_reason}__{unwrap_reason}"


def _toyh_current_bridge_reason(
    *,
    current_pass: bool,
    current_anchor_pass: bool,
    current_reason: str,
    current_anchor_reason: str,
) -> str:
    tags = [
        "C" if current_pass else "c0",
        "A" if current_anchor_pass else "a0",
    ]
    status = "PASS" if (current_pass or current_anchor_pass) else "FAIL"
    return f"{status}__{'_'.join(tags)}__{current_reason}__{current_anchor_reason}"


def _resolve_v5_tolerance_profile(profile: str) -> dict:
    key = str(profile).strip().lower()
    if key not in _V5_TOLERANCE_PROFILES:
        known = ", ".join(sorted(_V5_TOLERANCE_PROFILES.keys()))
        raise ValueError(f"Unknown tolerance profile: {profile!r}. Expected one of: {known}")
    return {k: float(v) for k, v in _V5_TOLERANCE_PROFILES[key].items()}


def build_bridge_program_orthogonality_report(
    *,
    repo_root: Path,
    grid_sizes: Optional[list[int]] = None,
    toyh_tol: Optional[float] = None,
    toyh_phase_anchor_tol: Optional[float] = None,
    toyh_current_anchor_tol: Optional[float] = None,
    toyh_current_anchor_min_response: Optional[float] = None,
    toyg_tol_winding: float = 0.05,
    toyg_tol_mode: float = 0.1,
    toyg_peak_fraction_min: float = 0.7,
    toyg_tol_unwrap_step_mean: float = 0.05,
    toyg_tol_unwrap_step_std: float = 0.05,
    toyg_min_near_pi_fraction: float = 0.8,
    toyg_pi_edge_eps: float = 0.15,
    tolerance_profile: str = "baseline",
) -> dict:
    _ = repo_root
    resolved_profile = _resolve_v5_tolerance_profile(tolerance_profile)
    toyh_tol = float(resolved_profile["toyh_tolerance"]) if toyh_tol is None else float(toyh_tol)
    toyh_phase_anchor_tol = (
        float(resolved_profile["phase_anchor_tolerance"])
        if toyh_phase_anchor_tol is None
        else float(toyh_phase_anchor_tol)
    )
    toyh_current_anchor_tol = (
        float(resolved_profile["current_anchor_tolerance"])
        if toyh_current_anchor_tol is None
        else float(toyh_current_anchor_tol)
    )
    toyh_current_anchor_min_response = (
        float(resolved_profile["current_anchor_min_response"])
        if toyh_current_anchor_min_response is None
        else float(toyh_current_anchor_min_response)
    )
    use_phase_stabilized_lane_l1 = str(tolerance_profile).strip().lower() == "v5_t2"

    grid_sizes = [7, 9, 11] if grid_sizes is None else list(dict.fromkeys(int(n) for n in grid_sizes))
    grid_hi = int(max(grid_sizes))
    grid_lo = int(min(grid_sizes))

    phase_sensitive_min = 1e-3
    current_control_min = 1e-3
    loop_length = float(2.0 * np.pi)
    unwrap_margin = 1e-6

    probes = [
        {
            "probe_id": "baseline_all_pass",
            "probe_kind": "baseline",
            "theta": float(np.pi / 3.0),
            "grid_n": grid_hi,
            "amplitude_scale": 1.0,
            "local_phase_shear_alpha": 0.5,
            "winding_target": 1.0,
            "mode_target": 1.0,
            "amplitude_mod_eps": 0.0,
            "unwrap_target": 1.0,
            "phase_shear_eps": 0.0,
        },
        {
            "probe_id": "stress_toyh_phase_control",
            "probe_kind": "toyh_phase_control_stress",
            "theta": 1e-6,
            "grid_n": grid_hi,
            "amplitude_scale": 1.0,
            "local_phase_shear_alpha": 0.5,
            "winding_target": 1.0,
            "mode_target": 1.0,
            "amplitude_mod_eps": 0.0,
            "unwrap_target": 1.0,
            "phase_shear_eps": 0.0,
        },
        {
            "probe_id": "stress_toyh_current_control",
            "probe_kind": "toyh_current_control_stress",
            "theta": float(np.pi / 3.0),
            "grid_n": grid_hi,
            "amplitude_scale": 1.0,
            "local_phase_shear_alpha": 1e-6,
            "winding_target": 1.0,
            "mode_target": 1.0,
            "amplitude_mod_eps": 0.0,
            "unwrap_target": 1.0,
            "phase_shear_eps": 0.0,
        },
        {
            "probe_id": "stress_toyh_current_control_alpha_0p125",
            "probe_kind": "toyh_current_control_stress_expansion_v2",
            "theta": float(np.pi / 3.0),
            "grid_n": grid_hi,
            "amplitude_scale": 1.0,
            "local_phase_shear_alpha": 0.125,
            "winding_target": 1.0,
            "mode_target": 1.0,
            "amplitude_mod_eps": 0.0,
            "unwrap_target": 1.0,
            "phase_shear_eps": 0.0,
        },
        {
            "probe_id": "stress_toyh_current_control_alpha_0p500",
            "probe_kind": "toyh_current_control_stress_expansion_v2",
            "theta": float(np.pi / 3.0),
            "grid_n": grid_hi,
            "amplitude_scale": 1.0,
            "local_phase_shear_alpha": 0.5,
            "winding_target": 1.0,
            "mode_target": 1.0,
            "amplitude_mod_eps": 0.0,
            "unwrap_target": 1.0,
            "phase_shear_eps": 0.0,
        },
        {
            "probe_id": "stress_toyh_current_control_alpha_1p000",
            "probe_kind": "toyh_current_control_stress_expansion_v2",
            "theta": float(np.pi / 3.0),
            "grid_n": grid_hi,
            "amplitude_scale": 1.0,
            "local_phase_shear_alpha": 1.0,
            "winding_target": 1.0,
            "mode_target": 1.0,
            "amplitude_mod_eps": 0.0,
            "unwrap_target": 1.0,
            "phase_shear_eps": 0.0,
        },
        {
            "probe_id": "stress_toyh_theta_set_pi_over_6",
            "probe_kind": "theta_set_stress_expansion_v3",
            "theta": float(np.pi / 6.0),
            "grid_n": grid_hi,
            "amplitude_scale": 1.0,
            "local_phase_shear_alpha": 0.5,
            "winding_target": 1.0,
            "mode_target": 1.0,
            "amplitude_mod_eps": 0.0,
            "unwrap_target": 1.0,
            "phase_shear_eps": 0.0,
        },
        {
            "probe_id": "stress_toyh_theta_set_pi_over_2",
            "probe_kind": "theta_set_stress_expansion_v3",
            "theta": float(np.pi / 2.0),
            "grid_n": grid_hi,
            "amplitude_scale": 1.0,
            "local_phase_shear_alpha": 0.5,
            "winding_target": 1.0,
            "mode_target": 1.0,
            "amplitude_mod_eps": 0.0,
            "unwrap_target": 1.0,
            "phase_shear_eps": 0.0,
        },
        {
            "probe_id": "stress_toyh_theta_set_2pi_over_3",
            "probe_kind": "theta_set_stress_expansion_v3",
            "theta": float(2.0 * np.pi / 3.0),
            "grid_n": grid_hi,
            "amplitude_scale": 1.0,
            "local_phase_shear_alpha": 0.5,
            "winding_target": 1.0,
            "mode_target": 1.0,
            "amplitude_mod_eps": 0.0,
            "unwrap_target": 1.0,
            "phase_shear_eps": 0.0,
        },
        {
            "probe_id": "stress_toyh_grid_size_n13",
            "probe_kind": "grid_size_stress_expansion_v4",
            "theta": float(np.pi / 3.0),
            "grid_n": 13,
            "amplitude_scale": 1.0,
            "local_phase_shear_alpha": 0.5,
            "winding_target": 1.0,
            "mode_target": 1.0,
            "amplitude_mod_eps": 0.0,
            "unwrap_target": 1.0,
            "phase_shear_eps": 0.0,
        },
        {
            "probe_id": "stress_toyh_grid_size_n15",
            "probe_kind": "grid_size_stress_expansion_v4",
            "theta": float(np.pi / 3.0),
            "grid_n": 15,
            "amplitude_scale": 1.0,
            "local_phase_shear_alpha": 0.5,
            "winding_target": 1.0,
            "mode_target": 1.0,
            "amplitude_mod_eps": 0.0,
            "unwrap_target": 1.0,
            "phase_shear_eps": 0.0,
        },
        {
            "probe_id": "stress_toyg_integer",
            "probe_kind": "toyg_integer_stress",
            "theta": float(np.pi / 3.0),
            "grid_n": grid_hi,
            "amplitude_scale": 1.0,
            "local_phase_shear_alpha": 0.5,
            "winding_target": 1.0 + 1.25 * float(toyg_tol_winding),
            "mode_target": 1.0 + 1.25 * float(toyg_tol_winding),
            "amplitude_mod_eps": 0.0,
            "unwrap_target": 1.0 + 1.25 * float(toyg_tol_winding),
            "phase_shear_eps": 0.0,
        },
        {
            "probe_id": "stress_toyg_unwrap",
            "probe_kind": "toyg_unwrap_stress",
            "theta": float(np.pi / 3.0),
            "grid_n": grid_lo,
            "amplitude_scale": 1.0,
            "local_phase_shear_alpha": 0.5,
            "winding_target": 3.5,
            "mode_target": 3.5,
            "amplitude_mod_eps": 0.0,
            "unwrap_target": 3.5,
            "phase_shear_eps": 0.0,
        },
        {
            "probe_id": "stress_c6_amplitude_scale",
            "probe_kind": "c6_side_stress",
            "theta": float(np.pi / 3.0),
            "grid_n": grid_hi,
            "amplitude_scale": 1.1,
            "local_phase_shear_alpha": 0.5,
            "winding_target": 1.0,
            "mode_target": 1.0,
            "amplitude_mod_eps": 0.0,
            "unwrap_target": 1.0,
            "phase_shear_eps": 0.0,
        },
        {
            "probe_id": "stress_c6_amplitude_scale_1p02",
            "probe_kind": "c6_side_stress_amplitude_expansion_v1",
            "theta": float(np.pi / 3.0),
            "grid_n": grid_hi,
            "amplitude_scale": 1.02,
            "local_phase_shear_alpha": 0.5,
            "winding_target": 1.0,
            "mode_target": 1.0,
            "amplitude_mod_eps": 0.0,
            "unwrap_target": 1.0,
            "phase_shear_eps": 0.0,
        },
        {
            "probe_id": "stress_c6_amplitude_scale_1p05",
            "probe_kind": "c6_side_stress_amplitude_expansion_v1",
            "theta": float(np.pi / 3.0),
            "grid_n": grid_hi,
            "amplitude_scale": 1.05,
            "local_phase_shear_alpha": 0.5,
            "winding_target": 1.0,
            "mode_target": 1.0,
            "amplitude_mod_eps": 0.0,
            "unwrap_target": 1.0,
            "phase_shear_eps": 0.0,
        },
        {
            "probe_id": "stress_c6_amplitude_scale_1p20",
            "probe_kind": "c6_side_stress_amplitude_expansion_v1",
            "theta": float(np.pi / 3.0),
            "grid_n": grid_hi,
            "amplitude_scale": 1.2,
            "local_phase_shear_alpha": 0.5,
            "winding_target": 1.0,
            "mode_target": 1.0,
            "amplitude_mod_eps": 0.0,
            "unwrap_target": 1.0,
            "phase_shear_eps": 0.0,
        },
    ]

    items: list[dict] = []
    for p in probes:
        phase = _phase_channel(
            theta=float(p["theta"]),
            Nx=int(p["grid_n"]),
            amplitude_scale=float(p["amplitude_scale"]),
            phase_sensitive_min=phase_sensitive_min,
            tol=float(toyh_tol),
            use_stable_invariance=bool(use_phase_stabilized_lane_l1),
        )
        phase_anchor = evaluate_toyh_c6_phase_anchor(
            theta=float(p["theta"]),
            grid_n=int(p["grid_n"]),
            amplitude_scale=float(p["amplitude_scale"]),
            tol_invariance=float(toyh_tol),
            tol_phase_anchor=float(toyh_phase_anchor_tol),
            min_anchor_magnitude=1e-8,
            anchor_sign=1.0,
            use_stable_invariance=bool(use_phase_stabilized_lane_l1),
        )
        current = _current_channel(
            theta=float(p["theta"]),
            Nx=int(p["grid_n"]),
            amplitude_scale=float(p["amplitude_scale"]),
            local_phase_shear_alpha=float(p["local_phase_shear_alpha"]),
            control_min=current_control_min,
            tol=float(toyh_tol),
        )
        current_anchor = evaluate_toyh_c6_current_anchor(
            theta=float(p["theta"]),
            grid_n=int(p["grid_n"]),
            amplitude_scale=float(p["amplitude_scale"]),
            local_phase_shear_alpha=float(p["local_phase_shear_alpha"]),
            tol_invariance=float(toyh_tol),
            tol_current_anchor=float(toyh_current_anchor_tol),
            min_anchor_response=float(toyh_current_anchor_min_response),
            anchor_sign=1.0,
        )
        winding = evaluate_toyg_c6_phase_winding(
            grid_n=int(p["grid_n"]),
            loop_length=loop_length,
            winding_target=float(p["winding_target"]),
            tol_winding=float(toyg_tol_winding),
            unwrap_margin=unwrap_margin,
            amplitude_mod_eps=float(p["amplitude_mod_eps"]),
        )
        mode = evaluate_toyg_c6_mode_index_quantization(
            grid_n=int(p["grid_n"]),
            loop_length=loop_length,
            mode_target=float(p["mode_target"]),
            tol_mode=float(toyg_tol_mode),
            min_peak_fraction=float(toyg_peak_fraction_min),
            amplitude_mod_eps=float(p["amplitude_mod_eps"]),
        )
        unwrap = evaluate_toyg_c6_unwrap_stability(
            grid_n=int(p["grid_n"]),
            loop_length=loop_length,
            unwrap_target=float(p["unwrap_target"]),
            tol_step_mean=float(toyg_tol_unwrap_step_mean),
            tol_step_std=float(toyg_tol_unwrap_step_std),
            min_near_pi_fraction=float(toyg_min_near_pi_fraction),
            pi_edge_eps=float(toyg_pi_edge_eps),
            amplitude_mod_eps=float(p["amplitude_mod_eps"]),
            phase_shear_eps=float(p["phase_shear_eps"]),
        )

        phase_pass = bool(phase["pass"])
        phase_anchor_pass = bool(phase_anchor["status"]["admissible"])
        phase_bridge_pass = bool(phase_pass or phase_anchor_pass)
        phase_bridge_reason = _toyh_phase_bridge_reason(
            phase_pass=phase_pass,
            anchor_pass=phase_anchor_pass,
            phase_reason=str(phase["reason_code"]),
            anchor_reason=str(phase_anchor["reason_code"]),
        )

        current_pass = bool(current["pass"])
        current_anchor_pass = bool(current_anchor["status"]["admissible"])
        current_bridge_pass = bool(current_pass or current_anchor_pass)
        current_bridge_reason = _toyh_current_bridge_reason(
            current_pass=current_pass,
            current_anchor_pass=current_anchor_pass,
            current_reason=str(current["reason_code"]),
            current_anchor_reason=str(current_anchor["reason_code"]),
        )

        winding_pass = bool(winding["status"]["admissible"])
        mode_pass = bool(mode["status"]["admissible"])
        unwrap_pass = bool(unwrap["status"]["admissible"])
        toyg_bridge_pass = bool(winding_pass or mode_pass or unwrap_pass)
        toyg_bridge_reason = _toyg_bridge_reason(
            winding_pass=winding_pass,
            mode_pass=mode_pass,
            unwrap_pass=unwrap_pass,
            winding_reason=str(winding["reason_code"]),
            mode_reason=str(mode["reason_code"]),
            unwrap_reason=str(unwrap["reason_code"]),
        )

        pair_bridge = evaluate_toyhg_c6_pair_compatibility(
            toyh_phase_bridge_pass=phase_bridge_pass,
            toyh_current_bridge_pass=current_bridge_pass,
            toyg_bridge_pass=toyg_bridge_pass,
            toyh_phase_reason=phase_bridge_reason,
            toyh_current_reason=current_bridge_reason,
            toyg_reason=toyg_bridge_reason,
        )
        pair_bridge_pass = bool(pair_bridge["status"]["admissible"])

        raw_sig = _signature(
            phase_bridge_pass=phase_bridge_pass,
            current_bridge_pass=current_bridge_pass,
            pair_bridge_pass=toyg_bridge_pass,
        )
        sig = _signature(
            phase_bridge_pass=phase_bridge_pass,
            current_bridge_pass=current_bridge_pass,
            pair_bridge_pass=pair_bridge_pass,
        )
        fails = _failing_channels(
            phase_bridge_pass=phase_bridge_pass,
            current_bridge_pass=current_bridge_pass,
            pair_bridge_pass=pair_bridge_pass,
        )

        items.append(
            {
                "probe_id": str(p["probe_id"]),
                "probe_kind": str(p["probe_kind"]),
                "theta": _q(float(p["theta"])),
                "grid_n": int(p["grid_n"]),
                "amplitude_scale": _q(float(p["amplitude_scale"])),
                "local_phase_shear_alpha": _q(float(p["local_phase_shear_alpha"])),
                "winding_target": _q(float(p["winding_target"])),
                "mode_target": _q(float(p["mode_target"])),
                "unwrap_target": _q(float(p["unwrap_target"])),
                "toyh_phase": phase,
                "toyh_phase_anchor": {
                    "pass": bool(phase_anchor_pass),
                    "reason_code": str(phase_anchor["reason_code"]),
                    "metrics": {
                        "norm_rel": _q(float(phase_anchor["metrics"]["norm_rel"])),
                        "energy_rel": _q(float(phase_anchor["metrics"]["energy_rel"])),
                        "rhs_rel": _q(float(phase_anchor["metrics"]["rhs_rel"])),
                        "anchor_phase_error": _q(float(phase_anchor["metrics"]["anchor_phase_error"])),
                        "anchor_magnitude_ratio": _q(float(phase_anchor["metrics"]["anchor_magnitude_ratio"])),
                    },
                },
                "toyh_phase_bridge": {
                    "pass": bool(phase_bridge_pass),
                    "reason_code": phase_bridge_reason,
                },
                "toyh_current": current,
                "toyh_current_anchor": {
                    "pass": bool(current_anchor_pass),
                    "reason_code": str(current_anchor["reason_code"]),
                    "metrics": {
                        "current_l2_rel": _q(float(current_anchor["metrics"]["current_l2_rel"])),
                        "anchor_response": _q(float(current_anchor["metrics"]["anchor_response"])),
                        "anchor_error": _q(float(current_anchor["metrics"]["anchor_error"])),
                    },
                },
                "toyh_current_bridge": {
                    "pass": bool(current_bridge_pass),
                    "reason_code": current_bridge_reason,
                },
                "toyg_winding": {
                    "pass": bool(winding_pass),
                    "reason_code": str(winding["reason_code"]),
                    "metrics": {
                        "raw_winding": _q(float(winding["metrics"]["raw_winding"])),
                        "integer_distance": _q(float(winding["metrics"]["integer_distance"])),
                        "max_abs_delta": _q(float(winding["metrics"]["max_abs_delta"])),
                    },
                },
                "toyg_mode": {
                    "pass": bool(mode_pass),
                    "reason_code": str(mode["reason_code"]),
                    "metrics": {
                        "peak_index_signed": int(mode["metrics"]["peak_index_signed"]),
                        "nearest_int": int(mode["metrics"]["nearest_int"]),
                        "peak_fraction": _q(float(mode["metrics"]["peak_fraction"])),
                        "integer_distance": _q(float(mode["metrics"]["integer_distance"])),
                    },
                },
                "toyg_unwrap": {
                    "pass": bool(unwrap_pass),
                    "reason_code": str(unwrap["reason_code"]),
                    "metrics": {
                        "mean_abs_step_error": _q(float(unwrap["metrics"]["mean_abs_step_error"])),
                        "step_std": _q(float(unwrap["metrics"]["step_std"])),
                        "near_pi_fraction": _q(float(unwrap["metrics"]["near_pi_fraction"])),
                    },
                },
                "toyg_bridge": {
                    "pass": bool(toyg_bridge_pass),
                    "reason_code": toyg_bridge_reason,
                },
                "toyhg_pair_bridge": {
                    "pass": bool(pair_bridge_pass),
                    "reason_code": str(pair_bridge["reason_code"]),
                    "metrics": {
                        "signature": str(pair_bridge["metrics"]["signature"]),
                        "signed_margin": _q(float(pair_bridge["metrics"]["signed_margin"])),
                        "n_pass_channels": int(pair_bridge["metrics"]["n_pass_channels"]),
                        "n_fail_channels": int(pair_bridge["metrics"]["n_fail_channels"]),
                    },
                },
                "signature_raw": raw_sig,
                "signature": sig,
                "failing_channels": fails,
                "localization_note": _localization_note(fails),
            }
        )

    signature_keys = ["P-P-P", "F-P-P", "P-F-P", "P-P-F", "F-F-P", "F-P-F", "P-F-F", "F-F-F"]
    signature_counts = {k: sum(1 for it in items if it["signature"] == k) for k in signature_keys}
    signature_counts_raw = {k: sum(1 for it in items if it["signature_raw"] == k) for k in signature_keys}

    def _pairwise_disagree(a_key: str, b_key: str) -> int:
        return sum(1 for it in items if bool(it[a_key]["pass"]) != bool(it[b_key]["pass"]))

    pairwise = {
        "phase_vs_current": _pairwise_disagree("toyh_phase_bridge", "toyh_current_bridge"),
        "phase_vs_toyg_bridge": _pairwise_disagree("toyh_phase_bridge", "toyg_bridge"),
        "current_vs_toyg_bridge": _pairwise_disagree("toyh_current_bridge", "toyg_bridge"),
    }

    nonredundant = bool(pairwise["phase_vs_toyg_bridge"] > 0 and pairwise["current_vs_toyg_bridge"] > 0)

    pairwise_frontier = {
        "phase_vs_current": _pairwise_disagree("toyh_phase_bridge", "toyh_current_bridge"),
        "phase_vs_pair_bridge": _pairwise_disagree("toyh_phase_bridge", "toyhg_pair_bridge"),
        "current_vs_pair_bridge": _pairwise_disagree("toyh_current_bridge", "toyhg_pair_bridge"),
    }

    targeted_resolution_count = sum(
        1
        for it in items
        if it["toyg_winding"]["reason_code"] == "fail_not_integer_close"
        and bool(it["toyg_mode"]["pass"])
        and bool(it["toyg_bridge"]["pass"])
    )
    unwrap_resolution_count = sum(
        1
        for it in items
        if it["toyg_winding"]["reason_code"] == "fail_unwrap_discontinuity_guard"
        and not bool(it["toyg_mode"]["pass"])
        and bool(it["toyg_unwrap"]["pass"])
        and bool(it["toyg_bridge"]["pass"])
    )
    phase_anchor_resolution_count = sum(
        1
        for it in items
        if it["toyh_phase"]["reason_code"] == "FAIL_PHASE_CHANNEL_CONTROL_MIN"
        and bool(it["toyh_phase_anchor"]["pass"])
        and bool(it["toyh_phase_bridge"]["pass"])
    )
    current_anchor_resolution_count = sum(
        1
        for it in items
        if it["toyh_current"]["reason_code"] == "FAIL_CURRENT_CHANNEL_CONTROL_MIN"
        and bool(it["toyh_current_anchor"]["pass"])
        and bool(it["toyh_current_bridge"]["pass"])
    )
    pair_resolution_count = sum(
        1
        for it in items
        if not bool(it["toyh_phase_bridge"]["pass"])
        and not bool(it["toyh_current_bridge"]["pass"])
        and bool(it["toyg_bridge"]["pass"])
        and not bool(it["toyhg_pair_bridge"]["pass"])
    )
    effective_tolerances_v5 = {
        "toyh_tolerance": float(toyh_tol),
        "phase_anchor_tolerance": float(toyh_phase_anchor_tol),
        "current_anchor_tolerance": float(toyh_current_anchor_tol),
        "current_anchor_min_response": float(toyh_current_anchor_min_response),
    }

    payload = {
        "schema_version": 1,
        "report_id": "BRIDGE_PROGRAM_ORTHOGONALITY_REPORT",
        "bridge_program": "Toy-H_Toy-G_C6",
        "shared_probe_set": {
            "grid_sizes": list(grid_sizes),
            "toyh_tolerance": float(toyh_tol),
            "phase_channel_control_min": phase_sensitive_min,
            "phase_anchor_tolerance": float(toyh_phase_anchor_tol),
            "current_channel_control_min": current_control_min,
            "current_anchor_tolerance": float(toyh_current_anchor_tol),
            "current_anchor_min_response": float(toyh_current_anchor_min_response),
            "amplitude_scales_frontier_expansion_v1": [1.02, 1.05, 1.1, 1.2],
            "current_control_alphas_frontier_expansion_v2": [0.125, 0.5, 1.0],
            "current_control_negative_anchor_sign_frontier_expansion_v2": -1.0,
            "theta_values_frontier_expansion_v3": [
                float(np.pi / 6.0),
                float(np.pi / 2.0),
                float(2.0 * np.pi / 3.0),
            ],
            "theta_negative_anchor_sign_frontier_expansion_v3": -1.0,
            "grid_sizes_frontier_expansion_v4": [13, 15],
            "grid_size_negative_amplitude_scale_frontier_expansion_v4": 1.1,
            "tolerance_profile_frontier_expansion_v5": {
                name: {k: float(v) for k, v in profile.items()} for name, profile in _V5_TOLERANCE_PROFILES.items()
            },
            "tolerance_profile_selected_v5": str(tolerance_profile),
            "effective_tolerances_v5": dict(effective_tolerances_v5),
            "phase_stabilization_lane_l1_enabled": bool(use_phase_stabilized_lane_l1),
            "toyg_loop_length": loop_length,
            "toyg_tol_winding": float(toyg_tol_winding),
            "toyg_unwrap_margin": unwrap_margin,
            "toyg_tol_mode": float(toyg_tol_mode),
            "toyg_peak_fraction_min": float(toyg_peak_fraction_min),
            "toyg_tol_unwrap_step_mean": float(toyg_tol_unwrap_step_mean),
            "toyg_tol_unwrap_step_std": float(toyg_tol_unwrap_step_std),
            "toyg_min_near_pi_fraction": float(toyg_min_near_pi_fraction),
            "toyg_pi_edge_eps": float(toyg_pi_edge_eps),
        },
        "evidence": {
            "pytest_nodes": [
                "formal/python/tests/test_bridge_program_orthogonality_semantics.py::test_bridge_program_orthogonality_expected_probe_signatures",
                "formal/python/tests/test_bridge_program_orthogonality_semantics.py::test_bridge_program_orthogonality_nonredundancy_summary",
                "formal/python/tests/test_bridge_program_orthogonality_semantics.py::test_bridge_program_orthogonality_mode_index_resolves_targeted_winding_mismatch",
                "formal/python/tests/test_bridge_program_orthogonality_semantics.py::test_bridge_program_orthogonality_unwrap_resolves_targeted_bridge_only_mismatch",
                "formal/python/tests/test_bridge_program_orthogonality_semantics.py::test_bridge_program_orthogonality_phase_anchor_resolves_targeted_phase_control_mismatch",
                "formal/python/tests/test_bridge_program_orthogonality_semantics.py::test_bridge_program_orthogonality_current_anchor_resolves_targeted_current_control_mismatch",
                "formal/python/tests/test_bridge_program_orthogonality_semantics.py::test_bridge_program_orthogonality_pair_channel_resolves_targeted_pair_vs_bridge_mismatch",
                "formal/python/tests/test_bridge_program_orthogonality_semantics.py::test_bridge_program_orthogonality_amplitude_expansion_negative_controls",
                "formal/python/tests/test_bridge_program_orthogonality_semantics.py::test_bridge_program_orthogonality_current_control_expansion_presence",
                "formal/python/tests/test_bridge_program_orthogonality_semantics.py::test_bridge_program_orthogonality_current_control_expansion_negative_controls",
                "formal/python/tests/test_bridge_program_orthogonality_semantics.py::test_bridge_program_orthogonality_theta_set_expansion_presence",
                "formal/python/tests/test_bridge_program_orthogonality_semantics.py::test_bridge_program_orthogonality_theta_set_expansion_negative_controls",
                "formal/python/tests/test_bridge_program_orthogonality_semantics.py::test_bridge_program_orthogonality_grid_size_expansion_presence",
                "formal/python/tests/test_bridge_program_orthogonality_semantics.py::test_bridge_program_orthogonality_grid_size_expansion_negative_controls",
                "formal/python/tests/test_bridge_program_orthogonality_semantics.py::test_bridge_program_orthogonality_v5_tolerance_profile_application",
                "formal/python/tests/test_bridge_program_orthogonality_semantics.py::test_bridge_program_orthogonality_v5_t1_negative_controls_preserve_reason_codes",
                "formal/python/tests/test_bridge_program_orthogonality_semantics.py::test_bridge_program_orthogonality_v5_t2_expected_breaks_are_tolerance_driven",
                "formal/python/tests/test_bridge_toyh_phase_stabilization_unit.py::test_bridge_toyh_phase_stabilization_residual_is_stable_near_zero",
                "formal/python/tests/test_bridge_program_v5_t2_phase_stabilized_lane_l1.py::test_bridge_program_v5_t2_phase_stabilized_restores_repro_capsule",
                "formal/python/tests/test_bridge_program_v5_t2_phase_stabilized_lane_l1.py::test_bridge_program_v5_t2_frontier_lock_after_l1",
                "formal/python/tests/test_bridge_program_v5_t2_phase_stabilized_lane_l1.py::test_bridge_program_v5_t2_negative_controls_preserved_phase_wrong_sign",
                "formal/python/tests/test_bridge_program_v5_t2_phase_stabilized_lane_l1.py::test_bridge_program_v5_t2_negative_controls_preserved_grid_amplitude_scale",
                "formal/python/tests/test_bridge_program_orthogonality_robustness_guard.py::test_bridge_program_orthogonality_nonredundancy_robustness_guard",
            ]
        },
        "items": items,
        "summary": {
            "n_probes": len(items),
            "signature_counts": signature_counts,
            "signature_counts_raw": signature_counts_raw,
            "pairwise_disagreement_counts": pairwise,
            "pairwise_disagreement_counts_frontier": pairwise_frontier,
            "nonredundant": bool(nonredundant),
            "targeted_resolution": {
                "n_winding_not_integer_close_resolved_by_mode": int(targeted_resolution_count),
                "n_winding_unwrap_guard_resolved_by_unwrap": int(unwrap_resolution_count),
                "n_phase_control_fail_resolved_by_phase_anchor": int(phase_anchor_resolution_count),
                "n_current_control_fail_resolved_by_current_anchor": int(current_anchor_resolution_count),
                "n_pair_vs_bridge_resolved_by_pair_channel": int(pair_resolution_count),
                "note": (
                    "Counts probes where winding fail_not_integer_close is resolved by mode, winding "
                    "fail_unwrap_discontinuity_guard with mode failure is resolved by unwrap channel, and "
                    "Toy-H phase/current control failures are resolved by anchor channels, and the Toy-H-pair-vs-Toy-G "
                    "mismatch is resolved by the pair-compatibility channel."
                ),
            },
            "note": (
                "nonredundant=true iff raw Toy-G bridge outcome disagrees with each Toy-H bridge channel on at least one "
                "pinned probe."
            ),
        },
    }

    out_text = json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    payload["artifact_sha256"] = _sha256_bytes(out_text.encode("utf-8"))
    return payload


def main(argv: Optional[list[str]] = None) -> int:
    p = argparse.ArgumentParser(description="Generate deterministic bridge-program orthogonality report.")
    p.add_argument(
        "--out",
        default="formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_REPORT.json",
        help=(
            "Repo-relative output JSON path (default: "
            "formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_REPORT.json)"
        ),
    )
    p.add_argument("--no-write", action="store_true", help="Do not write the file; just validate generation")
    p.add_argument(
        "--tolerance-profile",
        default="baseline",
        choices=sorted(_V5_TOLERANCE_PROFILES.keys()),
        help="Pinned tolerance profile (default: baseline).",
    )

    args = p.parse_args(argv)
    repo_root = _find_repo_root(Path(__file__))

    payload = build_bridge_program_orthogonality_report(
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

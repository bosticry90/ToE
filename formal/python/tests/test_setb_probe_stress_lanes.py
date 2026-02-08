from __future__ import annotations

import os
from pathlib import Path

from formal.python.tools.ptc_nlse_v1_run import (
    build_ptc_nlse_v1_hooks,
    build_ptc_nlse_v1_report,
    input_from_dict,
    load_manifest,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
_TOL_PROFILE_ENV = "TOE_NUMERIC_TOLERANCE_PROFILE"
_TOL_PROFILES: dict[str, dict[str, float]] = {
    # Tight lane for pinned single-environment reproducibility.
    "pinned": {
        "omega_error": 1e-10,
        "omega_drift": 1e-10,
        "norm_abs": 1e-12,
        "sym_phase": 1e-12,
        "sym_constancy": 1e-12,
        "sample_match": 1e-12,
        "diss_delta_match": 1e-10,
    },
    # Looser lane for portable multi-environment execution (FFT/platform variance).
    "portable": {
        "omega_error": 1e-8,
        "omega_drift": 1e-8,
        "norm_abs": 1e-10,
        "sym_phase": 1e-10,
        "sym_constancy": 1e-10,
        "sample_match": 1e-10,
        "diss_delta_match": 1e-8,
    },
}


def _tol(name: str) -> float:
    profile = os.environ.get(_TOL_PROFILE_ENV, "pinned").strip().lower()
    if profile not in _TOL_PROFILES:
        raise AssertionError(
            f"Unknown {_TOL_PROFILE_ENV} value: {profile!r}. "
            f"Allowed: {sorted(_TOL_PROFILES.keys())}"
        )
    return float(_TOL_PROFILES[profile][name])


def _base_case(case_id: str) -> dict:
    manifest = load_manifest(repo_root=REPO_ROOT)
    raw = dict(manifest["cases"][case_id])
    raw["case_id"] = case_id
    return raw


def _report(raw: dict) -> dict:
    return build_ptc_nlse_v1_report(inp=input_from_dict(raw))


def _hooks(raw: dict) -> dict:
    return build_ptc_nlse_v1_hooks(inp=input_from_dict(raw))


def _is_monotone_nonincreasing(xs: list[float], *, tol: float = 1e-12) -> bool:
    return all(float(xs[i + 1]) <= float(xs[i]) + tol for i in range(len(xs) - 1))


def test_setb_ct01_plane_wave_dispersion_survives_resolution_stress():
    """
    Set B CT-01 stress: broaden grid/timestep while preserving front-door dispersion identity.
    """
    base = _base_case("conservative_plane_wave")

    refined = dict(base)
    refined["case_id"] = "setb_ct01_refined"
    refined["n"] = 64
    refined["dt"] = 0.0005
    refined["steps"] = 400
    refined["sample_every"] = 40

    coarse = dict(base)
    coarse["case_id"] = "setb_ct01_coarse"
    coarse["n"] = 64
    coarse["dt"] = 0.002
    coarse["steps"] = 100
    coarse["sample_every"] = 10

    rep_base = _report(base)
    rep_refined = _report(refined)
    rep_coarse = _report(coarse)

    assert rep_base["derived"]["rac_energy_class"] == "conservative"
    assert rep_refined["derived"]["rac_energy_class"] == "conservative"
    assert rep_coarse["derived"]["rac_energy_class"] == "conservative"

    # The conservative plane-wave dispersion identity should remain numerically closed.
    assert abs(float(rep_base["output"]["omega_error"])) < _tol("omega_error")
    assert abs(float(rep_refined["output"]["omega_error"])) < _tol("omega_error")
    assert abs(float(rep_coarse["output"]["omega_error"])) < _tol("omega_error")

    # Stress variants should not drift off the pinned conservative frequency surface.
    omega0 = float(rep_base["output"]["omega_hat"])
    assert abs(float(rep_refined["output"]["omega_hat"]) - omega0) < _tol("omega_drift")
    assert abs(float(rep_coarse["output"]["omega_hat"]) - omega0) < _tol("omega_drift")


def test_setb_sym01_phase_path_invariance_on_report_and_hooks():
    """
    Set B SYM-01 stress: nontrivial phase-path sweep must preserve phase-invariant lanes.
    """
    base = _base_case("conservative_plane_wave")
    phase_path = [0.0, 0.5, 1.1, 2.3]

    reports: list[dict] = []
    hooks: list[dict] = []
    for phase in phase_path:
        raw = dict(base)
        raw["case_id"] = f"setb_sym_phase_{phase}"
        raw["phase"] = float(phase)
        reports.append(_report(raw))
        hooks.append(_hooks(raw))

    omega_hats = [float(r["output"]["omega_hat"]) for r in reports]
    norm_deltas = [float(r["output"]["norm_delta"]) for r in reports]

    assert max(omega_hats) - min(omega_hats) < _tol("omega_drift")
    assert max(abs(x) for x in norm_deltas) < _tol("norm_abs")

    sym_phase = [float(h["hooks"]["sym01_phase_residual"]) for h in hooks]
    sym_conj = [float(h["hooks"]["sym01_conjugation_residual"]) for h in hooks]
    par_res = [float(h["hooks"]["par01_parity_residual"]) for h in hooks]

    assert max(sym_phase) < _tol("sym_phase")
    assert max(sym_conj) - min(sym_conj) < _tol("sym_constancy")
    assert max(par_res) - min(par_res) < _tol("sym_constancy")


def test_setb_caus01_dissipative_time_order_stress_monotone_and_sampling_consistent():
    """
    Set B CAUS-01 stress: dissipative traces remain time-ordered under sample-density changes.
    """
    base = _base_case("dissipative_plane_wave")

    dense = dict(base)
    dense["case_id"] = "setb_caus_dense_sampling"
    dense["sample_every"] = 10

    refined = dict(base)
    refined["case_id"] = "setb_caus_refined_dt"
    refined["dt"] = 0.0005
    refined["steps"] = 400
    refined["sample_every"] = 40

    rep_base = _report(base)
    rep_dense = _report(dense)
    rep_refined = _report(refined)

    for payload in [rep_base, rep_dense, rep_refined]:
        e = [float(v) for v in payload["output"]["energy_trace"]]
        n = [float(v) for v in payload["output"]["norm_trace"]]
        assert _is_monotone_nonincreasing(e)
        assert _is_monotone_nonincreasing(n)

    dense_energy = [float(v) for v in rep_dense["output"]["energy_trace"]]
    base_energy = [float(v) for v in rep_base["output"]["energy_trace"]]
    dense_norm = [float(v) for v in rep_dense["output"]["norm_trace"]]
    base_norm = [float(v) for v in rep_base["output"]["norm_trace"]]

    assert len(dense_energy) == 2 * len(base_energy) - 1
    assert len(dense_norm) == 2 * len(base_norm) - 1

    for idx, val in enumerate(base_energy):
        assert abs(dense_energy[2 * idx] - val) < _tol("sample_match")
    for idx, val in enumerate(base_norm):
        assert abs(dense_norm[2 * idx] - val) < _tol("sample_match")

    # Refinement should preserve the aggregate dissipative effect at fixed end time.
    assert abs(float(rep_refined["output"]["energy_delta"]) - float(rep_base["output"]["energy_delta"])) < _tol(
        "diss_delta_match"
    )
    assert abs(float(rep_refined["output"]["norm_delta"]) - float(rep_base["output"]["norm_delta"])) < _tol(
        "diss_delta_match"
    )

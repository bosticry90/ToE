from __future__ import annotations

import json
from pathlib import Path

from formal.python.toe.dr01_fit_quality import dr01_quality_through_origin_from_sample_kw


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))


def _load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _as_sample_kw(sample_kw_raw) -> tuple[tuple[float, float], ...]:
    return tuple((float(k), float(w)) for (k, w) in sample_kw_raw)


def test_dr_fit_quality_present_deterministic_and_reasonable():
    base = REPO_ROOT / "formal" / "external_evidence" / "bec_bragg_steinhauer_2001"

    for name in ["dr01_fit_artifact.json", "dr03_fit_artifact.json", "dr04_fit_artifact.json"]:
        d = _load_json(base / name)

        assert d.get("fit_quality") is not None, f"Missing fit_quality in {name}"
        q = d["fit_quality"]

        # Minimal presence checks
        for key in ["n_points", "rmse_omega_rad_s", "slope_stderr_m_per_s", "r2_through_origin"]:
            assert key in q, f"Missing fit_quality.{key} in {name}"

        # Minimal reasonableness checks
        assert int(q["n_points"]) >= 3
        assert float(q["rmse_omega_rad_s"]) >= 0.0
        assert float(q["slope_stderr_m_per_s"]) >= 0.0
        r2 = float(q["r2_through_origin"])
        assert r2 <= 1.0 + 1e-12

        # Determinism check: recompute from sample_kw, compare to stamped values
        sample_kw = _as_sample_kw(d["sample_kw"])
        computed = dr01_quality_through_origin_from_sample_kw(sample_kw)

        assert int(q["n_points"]) == computed.n_points
        assert abs(float(q["rmse_omega_rad_s"]) - computed.rmse_omega_rad_s) < 1e-12
        assert abs(float(q["slope_stderr_m_per_s"]) - computed.slope_stderr_m_per_s) < 1e-18
        assert abs(float(q["r2_through_origin"]) - computed.r2_through_origin) < 1e-12

        # Fingerprint checks
        assert d.get("fit_quality_fingerprint") == computed.fingerprint()

        # Fingerprint must change if quality fields change.
        tampered = {
            "n_points": computed.n_points,
            "rmse_omega_rad_s": computed.rmse_omega_rad_s + 1.0,
            "slope_stderr_m_per_s": computed.slope_stderr_m_per_s,
            "r2_through_origin": computed.r2_through_origin,
        }
        assert computed.fingerprint() != (
            dr01_quality_through_origin_from_sample_kw(sample_kw).__class__(
                n_points=int(tampered["n_points"]),
                rmse_omega_rad_s=float(tampered["rmse_omega_rad_s"]),
                slope_stderr_m_per_s=float(tampered["slope_stderr_m_per_s"]),
                r2_through_origin=float(tampered["r2_through_origin"]),
            ).fingerprint()
        )

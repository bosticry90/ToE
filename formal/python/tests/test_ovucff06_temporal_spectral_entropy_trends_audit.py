from __future__ import annotations

import json

import pytest

from formal.python.toe.observables.ovucff06_temporal_spectral_entropy_trends_audit import (
    default_demo_inputs,
    load_pinned_input_payload,
    ovucff06_temporal_spectral_entropy_trends_audit,
    write_ovucff06_entropy_trends_artifact,
)


def test_demo_constant_has_zero_entropy_and_zero_trend() -> None:
    demo = default_demo_inputs()
    rep = ovucff06_temporal_spectral_entropy_trends_audit(X=demo["constant"], n_bands=8, dt=1.0)

    assert rep.entropy_norm_mean == pytest.approx(0.0, abs=1e-6)
    assert rep.entropy_norm_mean_abs_delta == pytest.approx(0.0, abs=1e-12)
    assert rep.entropy_norm_trend_slope == pytest.approx(0.0, abs=1e-12)


def test_demo_noise_has_higher_entropy_than_constant() -> None:
    demo = default_demo_inputs()
    rep_const = ovucff06_temporal_spectral_entropy_trends_audit(X=demo["constant"], n_bands=8, dt=1.0)
    rep_noise = ovucff06_temporal_spectral_entropy_trends_audit(X=demo["noise"], n_bands=8, dt=1.0)

    assert rep_noise.entropy_norm_mean > rep_const.entropy_norm_mean


def test_demo_mixed_has_nonzero_entropy_delta() -> None:
    demo = default_demo_inputs()
    rep = ovucff06_temporal_spectral_entropy_trends_audit(X=demo["mixed"], n_bands=8, dt=1.0)

    assert rep.entropy_norm_mean_abs_delta > 0.0


def test_pinned_input_loads_and_report_schema() -> None:
    pinned = load_pinned_input_payload()
    X = pinned["X"]
    assert X.ndim == 2
    assert X.shape[1] == 256
    assert X.shape[0] >= 2

    rep = ovucff06_temporal_spectral_entropy_trends_audit(
        X=X,
        n_bands=8,
        dt=pinned["dt"],
    )

    assert rep.schema == "OV-UCFF-06/entropy_trends_report/v1"


def test_artifact_write_json(tmp_path) -> None:
    out = tmp_path / "ucff_entropy_trends.json"
    wrote = write_ovucff06_entropy_trends_artifact(path=out)
    assert wrote == out

    payload = json.loads(out.read_text(encoding="utf-8"))
    assert payload["schema"] == "OV-UCFF-06/entropy_trends_artifact/v1"
    assert "fingerprint" in payload
    assert payload["reports"]["demo_constant"]["schema"] == "OV-UCFF-06/entropy_trends_report/v1"

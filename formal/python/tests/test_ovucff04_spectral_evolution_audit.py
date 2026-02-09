from __future__ import annotations

import json
import math

import pytest

from formal.python.toe.observables.ovucff04_spectral_evolution_audit import (
    default_demo_inputs,
    load_pinned_input_payload,
    ovucff04_spectral_evolution_audit,
    write_ovucff04_spectral_evolution_artifact,
)


def test_demo_constant_has_zero_drift() -> None:
    demo = default_demo_inputs()
    rep = ovucff04_spectral_evolution_audit(X=demo["constant"], n_bands=8)

    assert rep.l2_drift_mean == pytest.approx(0.0, abs=1e-12)
    assert rep.cosine_dist_mean == pytest.approx(0.0, abs=1e-12)
    assert rep.js_div_mean == pytest.approx(0.0, abs=1e-12)

    assert rep.delta_entropy_norm_mean == pytest.approx(0.0, abs=1e-12)
    assert rep.delta_energy_slope_mean == pytest.approx(0.0, abs=1e-12)


def test_demo_drift_has_nonzero_drift() -> None:
    demo = default_demo_inputs()
    rep_const = ovucff04_spectral_evolution_audit(X=demo["constant"], n_bands=8)
    rep_drift = ovucff04_spectral_evolution_audit(X=demo["drift"], n_bands=8)

    assert rep_drift.l2_drift_mean > rep_const.l2_drift_mean
    assert rep_drift.js_div_mean > rep_const.js_div_mean


def test_pinned_input_loads_and_metrics_in_bounds() -> None:
    pinned = load_pinned_input_payload()
    X = pinned["X"]
    assert X.shape == (2, 256)

    rep = ovucff04_spectral_evolution_audit(
        X=X,
        n_bands=8,
        dx=pinned["dx"],
        legacy_k_low=2.0,
        legacy_k_mid=6.0,
    )

    # JS divergence is bounded by ln(2) for base-e when comparing discrete distributions.
    assert 0.0 <= rep.js_div_mean <= math.log(2.0) + 1e-9
    assert 0.0 <= rep.js_div_max <= math.log(2.0) + 1e-9

    assert 0.0 <= rep.l2_drift_mean
    assert 0.0 <= rep.cosine_dist_mean


def test_artifact_write_json(tmp_path) -> None:
    out = tmp_path / "ucff_spectral_evolution.json"
    wrote = write_ovucff04_spectral_evolution_artifact(path=out)
    assert wrote == out

    payload = json.loads(out.read_text(encoding="utf-8"))
    assert payload["schema"] == "OV-UCFF-04/spectral_evolution_artifact/v1"
    assert "fingerprint" in payload
    assert "reports" in payload

    assert payload["reports"]["demo_constant"]["schema"] == "OV-UCFF-04/spectral_evolution_report/v1"

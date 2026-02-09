from __future__ import annotations

import json

import pytest

from formal.python.toe.observables.ovucff05_temporal_band_modulation_audit import (
    default_demo_inputs,
    load_pinned_input_payload,
    ovucff05_temporal_band_modulation_audit,
    write_ovucff05_temporal_band_modulation_artifact,
)


def test_demo_constant_has_zero_variation() -> None:
    demo = default_demo_inputs()
    rep = ovucff05_temporal_band_modulation_audit(X=demo["constant"], n_bands=8, dt=1.0)

    assert rep.dom_strength_max == pytest.approx(0.0, abs=1e-12)
    assert max(rep.per_band_mean_abs_delta) == pytest.approx(0.0, abs=1e-12)
    assert max(rep.per_band_std) == pytest.approx(0.0, abs=1e-12)


def test_demo_modulated_has_nonzero_modulation() -> None:
    demo = default_demo_inputs()
    rep_const = ovucff05_temporal_band_modulation_audit(X=demo["constant"], n_bands=8, dt=1.0)
    rep_mod = ovucff05_temporal_band_modulation_audit(X=demo["modulated"], n_bands=8, dt=1.0)

    assert rep_mod.dom_strength_max > rep_const.dom_strength_max
    assert max(rep_mod.per_band_std) > max(rep_const.per_band_std)

    # At least one band should show a meaningful harmonic peak.
    assert rep_mod.dom_strength_max > 0.25


def test_pinned_input_loads_and_report_schema() -> None:
    pinned = load_pinned_input_payload()
    X = pinned["X"]
    assert X.ndim == 2
    assert X.shape[1] == 256
    assert X.shape[0] >= 2

    rep = ovucff05_temporal_band_modulation_audit(
        X=X,
        n_bands=8,
        dt=pinned["dt"],
        dx=pinned["dx"],
        legacy_k_low=2.0,
        legacy_k_mid=6.0,
    )

    assert rep.schema == "OV-UCFF-05/temporal_band_modulation_report/v1"


def test_artifact_write_json(tmp_path) -> None:
    out = tmp_path / "ucff_temporal_band_modulation.json"
    wrote = write_ovucff05_temporal_band_modulation_artifact(path=out)
    assert wrote == out

    payload = json.loads(out.read_text(encoding="utf-8"))
    assert payload["schema"] == "OV-UCFF-05/temporal_band_modulation_artifact/v1"
    assert "fingerprint" in payload
    assert payload["reports"]["demo_constant"]["schema"] == "OV-UCFF-05/temporal_band_modulation_report/v1"

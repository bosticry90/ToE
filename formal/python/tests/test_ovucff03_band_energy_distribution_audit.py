from __future__ import annotations

import json

import numpy as np
import pytest

from formal.python.toe.observables.ovucff03_band_energy_distribution_audit import (
    default_demo_inputs,
    load_pinned_input_X,
    ovucff03_band_energy_distribution_audit,
    write_ovucff03_band_energy_distribution_artifact,
)


def test_demo_noise_has_higher_entropy_than_dc() -> None:
    demo = default_demo_inputs()
    rep_dc = ovucff03_band_energy_distribution_audit(X=demo["dc"], n_bands=8)
    rep_noise = ovucff03_band_energy_distribution_audit(X=demo["noise"], n_bands=8)

    assert rep_dc.entropy_norm_mean == pytest.approx(0.0, abs=1e-6)
    assert rep_noise.entropy_norm_mean > rep_dc.entropy_norm_mean


def test_demo_noise_has_higher_flatness_than_dc() -> None:
    demo = default_demo_inputs()
    rep_dc = ovucff03_band_energy_distribution_audit(X=demo["dc"], n_bands=8)
    rep_noise = ovucff03_band_energy_distribution_audit(X=demo["noise"], n_bands=8)

    assert rep_dc.flatness_mean < rep_noise.flatness_mean


def test_pinned_input_loads_and_metrics_in_bounds() -> None:
    X = load_pinned_input_X()
    assert X.shape == (2, 256)

    rep = ovucff03_band_energy_distribution_audit(X=X, n_bands=8)

    assert 0.0 <= rep.entropy_norm_mean <= 1.0
    assert 0.0 <= rep.entropy_norm_min <= 1.0
    assert 0.0 <= rep.flatness_mean <= 1.0
    assert 0.0 <= rep.flatness_min <= 1.0

    assert len(rep.band_energy_mean) == 8
    assert len(rep.band_energy_norm_mean) == 8
    assert abs(sum(rep.band_energy_norm_mean) - 1.0) < 1e-6


def test_legacy_three_band_partition_dc_is_low_dominated() -> None:
    demo = default_demo_inputs()
    rep = ovucff03_band_energy_distribution_audit(
        X=demo["dc"],
        n_bands=8,
        dx=1.0,
        legacy_k_low=2.0,
        legacy_k_mid=6.0,
    )

    assert rep.legacy_E_frac_low_mean == pytest.approx(1.0, abs=1e-6)
    assert rep.legacy_E_frac_mid_mean == pytest.approx(0.0, abs=1e-6)
    assert rep.legacy_E_frac_high_mean == pytest.approx(0.0, abs=1e-6)


def test_artifact_write_json(tmp_path) -> None:
    out = tmp_path / "ucff_band_energy_distribution.json"
    wrote = write_ovucff03_band_energy_distribution_artifact(path=out)
    assert wrote == out

    payload = json.loads(out.read_text(encoding="utf-8"))
    assert payload["schema"] == "OV-UCFF-03/band_energy_distribution_artifact/v1"
    assert "fingerprint" in payload
    assert "reports" in payload

    # Report schema bump (includes optional legacy 3-band partition summaries)
    assert payload["reports"]["demo_dc"]["schema"] == "OV-UCFF-03/band_energy_distribution_report/v2"

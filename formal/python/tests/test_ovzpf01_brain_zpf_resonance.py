from __future__ import annotations

import json

import pytest

from formal.python.toe.observables.ovzpf01_brain_zpf_resonance_audit import (
    FrequencyBand,
    band_overlap,
    ovzpf01_brain_zpf_resonance_audit,
    write_ovzpf01_brain_zpf_resonance_artifact,
)


def test_band_overlap_basic_properties() -> None:
    a = FrequencyBand(name="a", f_low_hz=10.0, f_high_hz=20.0)
    b = FrequencyBand(name="b", f_low_hz=15.0, f_high_hz=25.0)

    o = band_overlap(a, b)
    assert o.overlap_width_hz == pytest.approx(5.0)
    assert o.frac_of_a == pytest.approx(0.5)
    assert o.frac_of_b == pytest.approx(0.5)
    assert o.jaccard == pytest.approx(5.0 / (10.0 + 10.0 - 5.0))


def test_ovzpf01_demo_modes_match_expected_bands() -> None:
    eeg = [
        FrequencyBand(name="beta", f_low_hz=13.0, f_high_hz=30.0),
        FrequencyBand(name="gamma", f_low_hz=30.0, f_high_hz=80.0),
    ]
    modes = [
        FrequencyBand(name="m_beta", f_low_hz=18.0, f_high_hz=22.0),
        FrequencyBand(name="m_gamma", f_low_hz=38.0, f_high_hz=42.0),
    ]

    rep = ovzpf01_brain_zpf_resonance_audit(
        eeg_bands=eeg,
        zpf_mode_bands=modes,
        temperature_K=295.0,
        min_mode_overlap_fraction=0.05,
    )

    # m_beta overlaps beta but not gamma.
    assert rep.mode_best_matches["m_beta"] == "beta"
    assert rep.mode_has_any_overlap["m_beta"] is True

    # m_gamma overlaps gamma but not beta.
    assert rep.mode_best_matches["m_gamma"] == "gamma"
    assert rep.mode_has_any_overlap["m_gamma"] is True


def test_ovzpf01_artifact_writes_and_is_json(tmp_path) -> None:
    out = tmp_path / "brain_zpf_resonance.json"
    wrote = write_ovzpf01_brain_zpf_resonance_artifact(path=out)
    assert wrote == out

    payload = json.loads(out.read_text(encoding="utf-8"))
    assert payload["schema"] == "OV-ZPF-01/brain_zpf_resonance_artifact/v1"
    assert "fingerprint" in payload
    assert "report" in payload

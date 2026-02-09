from __future__ import annotations

import json

import numpy as np
import pytest

from formal.python.toe.observables.ovucff07_cross_metric_coupling_audit import (
    default_demo_inputs,
    load_pinned_input_payload,
    ovucff07_cross_metric_coupling_audit,
    write_ovucff07_cross_metric_coupling_artifact,
)


def test_demo_constant_has_zero_modulation_and_zero_correlations() -> None:
    demo = default_demo_inputs()
    rep = ovucff07_cross_metric_coupling_audit(X=demo["constant"], n_bands=8, dt=1.0, max_lag=4)

    assert rep.entropy_norm_mean == pytest.approx(0.0, abs=1e-6)
    assert rep.modulation_mean == pytest.approx(0.0, abs=1e-12)
    assert rep.drift_js_mean == pytest.approx(0.0, abs=1e-12)

    assert rep.corr_entropy_modulation == pytest.approx(0.0, abs=1e-12)
    assert rep.corr_dentropy_modulation == pytest.approx(0.0, abs=1e-12)
    assert rep.best_corr_dentropy_modulation == pytest.approx(0.0, abs=1e-12)
    assert rep.corr_abs_dentropy_drift_js == pytest.approx(0.0, abs=1e-12)

    assert all(abs(v) < 1e-9 for v in rep.per_band_corr_entropy_frac)
    assert all(abs(v) < 1e-9 for v in rep.per_band_corr_dentropy_dfrac)


def test_demo_mixed_has_nonzero_modulation_and_some_coupling_signal() -> None:
    demo = default_demo_inputs()
    rep = ovucff07_cross_metric_coupling_audit(X=demo["mixed"], n_bands=8, dt=1.0, max_lag=6)

    assert rep.modulation_mean > 0.0
    assert rep.drift_js_mean > 0.0

    max_abs_band_corr = float(np.max(np.abs(np.asarray(rep.per_band_corr_entropy_frac, dtype=float))))
    assert max_abs_band_corr > 0.1


def test_pinned_input_loads_and_report_schema() -> None:
    pinned = load_pinned_input_payload()
    X = pinned["X"]
    assert X.ndim == 2
    assert X.shape[1] == 256
    assert X.shape[0] >= 2

    rep = ovucff07_cross_metric_coupling_audit(
        X=X,
        n_bands=8,
        dt=pinned["dt"],
        max_lag=4,
    )

    assert rep.schema == "OV-UCFF-07/cross_metric_coupling_report/v1"


def test_artifact_write_json(tmp_path) -> None:
    out = tmp_path / "ucff_cross_metric_coupling.json"
    wrote = write_ovucff07_cross_metric_coupling_artifact(path=out)
    assert wrote == out

    payload = json.loads(out.read_text(encoding="utf-8"))
    assert payload["schema"] == "OV-UCFF-07/cross_metric_coupling_artifact/v1"
    assert "fingerprint" in payload
    assert payload["reports"]["demo_constant"]["schema"] == "OV-UCFF-07/cross_metric_coupling_report/v1"

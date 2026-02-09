from __future__ import annotations

import json

import numpy as np
import pytest

from formal.python.toe.observables.ovucff02_framewise_variation_audit import (
    default_demo_inputs,
    load_pinned_input_X,
    ovucff02_framewise_variation_audit,
    write_ovucff02_framewise_variation_artifact,
)


def test_constant_frames_have_zero_variation() -> None:
    X = default_demo_inputs()["constant"]
    rep = ovucff02_framewise_variation_audit(X=X)

    assert rep.delta_energy_l2_max == pytest.approx(0.0)
    assert rep.delta_energy_l2_norm_max == pytest.approx(0.0)
    assert rep.cross_matrix_fro_delta_max == pytest.approx(0.0)


def test_drift_has_nonzero_variation() -> None:
    X = default_demo_inputs()["drift"]
    rep = ovucff02_framewise_variation_audit(X=X)

    assert rep.delta_energy_l2_mean > 0.0
    assert rep.delta_energy_l2_norm_mean > 0.0
    assert rep.cross_matrix_fro_delta_mean > 0.0


def test_pinned_input_loads_and_varies() -> None:
    X = load_pinned_input_X()
    assert X.shape[0] == 2
    assert X.shape[1] == 256

    rep = ovucff02_framewise_variation_audit(X=X)
    assert rep.delta_energy_l2_mean > 0.0
    assert rep.delta_energy_l2_norm_mean > 0.0


def test_artifact_write_json(tmp_path) -> None:
    out = tmp_path / "ucff_framewise_variation.json"
    wrote = write_ovucff02_framewise_variation_artifact(path=out)
    assert wrote == out

    payload = json.loads(out.read_text(encoding="utf-8"))
    assert payload["schema"] == "OV-UCFF-02/framewise_variation_artifact/v2"
    assert "fingerprint" in payload
    assert "reports" in payload
    assert "pinned_input" in payload


def test_cli_report_pinned_outputs_json(capsys) -> None:
    from formal.python.tools.ovucff02_framewise_variation_audit import main

    rc = main(["--report", "--pinned"])
    assert rc == 0

    out = capsys.readouterr().out
    payload = json.loads(out)
    assert payload["schema"] == "OV-UCFF-02/framewise_variation_report/v1"
    assert payload["n_frames"] == 2
    assert payload["n_bins"] == 256


def test_cli_write_reference_refuses_without_env_gate(monkeypatch, capsys) -> None:
    from formal.python.tools.ovucff02_framewise_variation_audit import main

    monkeypatch.delenv("TOE_ALLOW_REFERENCE_WRITES", raising=False)

    rc = main(["--write-reference", "--pinned", "--force"])
    assert rc != 0

    err = capsys.readouterr().err
    assert "REFUSE: reference writes are disabled" in err


def test_pinned_input_matches_frozen_reference_report() -> None:
    ref_path = "formal/python/artifacts/input/OV-UCFF-02/reference_ovucff02_pinned_report.json"
    ref_payload = json.loads(open(ref_path, "r", encoding="utf-8").read())
    ref = ref_payload["reference_report"]

    X = load_pinned_input_X()
    current = ovucff02_framewise_variation_audit(X=X).to_jsonable()

    numeric_fields = [
        "baseline_frame_energy_l2_mean",
        "delta_energy_l2_mean",
        "delta_energy_l2_max",
        "delta_energy_l2_norm_mean",
        "delta_energy_l2_norm_max",
        "cross_matrix_fro_delta_mean",
        "cross_matrix_fro_delta_max",
    ]

    assert current["schema"] == ref["schema"]
    assert current["n_frames"] == ref["n_frames"]
    assert current["n_bins"] == ref["n_bins"]

    for k in numeric_fields:
        assert float(current[k]) == pytest.approx(float(ref[k]), rel=1e-12, abs=1e-12)

from __future__ import annotations

import json

import pytest

from formal.python.toe.observables.ovucff03_band_energy_distribution_audit import (
    default_pinned_input_path as ovucff03_default_pinned_input_path,
    load_pinned_input_payload as ovucff03_load_pinned_input_payload,
    ovucff03_band_energy_distribution_audit,
)
from formal.python.toe.observables.ovucff03b_band_energy_tolerance_audit import (
    load_reference_report,
    ovucff03b_tolerance_check,
    write_reference_report_from_ovucff03,
)


def test_write_reference_report_json(tmp_path) -> None:
    out = tmp_path / "reference_ovucff03_pinned_report.json"
    wrote = write_reference_report_from_ovucff03(path=out)
    assert wrote == out

    payload = json.loads(out.read_text(encoding="utf-8"))
    assert payload["schema"] == "OV-UCFF-03B/reference_report/v1"
    assert "fingerprint" in payload
    assert "source" in payload
    assert "reference_report" in payload


def test_tolerance_check_passes_against_reference() -> None:
    ref = load_reference_report()

    pinned = ovucff03_load_pinned_input_payload(path=ovucff03_default_pinned_input_path())
    X = pinned["X"]
    dx = pinned["dx"]

    current = ovucff03_band_energy_distribution_audit(
        X=X,
        n_bands=8,
        dx=dx,
        legacy_k_low=2.0,
        legacy_k_mid=6.0,
    ).to_jsonable()

    check = ovucff03b_tolerance_check(
        current_report=current,
        reference_report=ref,
        rtol=1e-6,
        atol=1e-9,
    )

    assert check.pass_all is True


def test_tolerance_check_fails_when_reference_perturbed(tmp_path) -> None:
    # Start from the real reference, then perturb one value.
    ref_payload = {
        "schema": "OV-UCFF-03B/reference_report/v1",
        "notes": "test",
        "source": {"path": "x", "fingerprint": "y", "schema": "z", "report_key": "pinned"},
        "reference_report": load_reference_report(),
    }
    ref_payload["reference_report"]["entropy_norm_mean"] = float(ref_payload["reference_report"]["entropy_norm_mean"]) + 0.1
    ref_payload["fingerprint"] = "dummy"

    ref_path = tmp_path / "ref.json"
    ref_path.write_text(json.dumps(ref_payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    ref = json.loads(ref_path.read_text(encoding="utf-8"))["reference_report"]

    pinned = ovucff03_load_pinned_input_payload(path=ovucff03_default_pinned_input_path())
    X = pinned["X"]
    dx = pinned["dx"]

    current = ovucff03_band_energy_distribution_audit(
        X=X,
        n_bands=8,
        dx=dx,
        legacy_k_low=2.0,
        legacy_k_mid=6.0,
    ).to_jsonable()

    check = ovucff03b_tolerance_check(
        current_report=current,
        reference_report=ref,
        rtol=1e-12,
        atol=1e-12,
    )

    assert check.pass_all is False

    # Ensure the failing field is the perturbed one.
    failing = [c for c in check.comparisons if c.get("pass") is False]
    assert any(c.get("field") == "entropy_norm_mean" for c in failing)

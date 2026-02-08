from __future__ import annotations

import json
from pathlib import Path

from formal.python.toe.dr01_fit import DR01Fit1D


REPO_ROOT = Path(__file__).resolve().parents[3]


def _load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _as_sample_kw(raw_sample_kw: list[list[float]]) -> tuple[tuple[float, float], ...]:
    return tuple((float(k), float(w)) for (k, w) in raw_sample_kw)


def test_dr01_linear_artifact_contract_keys_and_fingerprint():
    path = REPO_ROOT / "formal" / "external_evidence" / "bec_bragg_steinhauer_2001" / "dr01_fit_artifact.json"
    payload = _load_json(path)

    required = {
        "u",
        "c_s",
        "tag",
        "source_kind",
        "source_ref",
        "fit_method_tag",
        "sample_kw",
        "data_fingerprint",
    }
    assert required.issubset(set(payload.keys()))
    assert payload["source_kind"] in {"csv", "manual", "synthetic", "unknown"}
    assert str(payload["data_fingerprint"])

    sample_kw = _as_sample_kw(payload["sample_kw"])
    expected = DR01Fit1D.data_fingerprint_from_sample(sample_kw)
    assert payload["data_fingerprint"] == expected


def test_dr01_curved_artifact_contract_keys_and_fingerprint():
    path = (
        REPO_ROOT
        / "formal"
        / "external_evidence"
        / "bec_bragg_steinhauer_2001"
        / "dr01_fit_artifact_curved.json"
    )
    payload = _load_json(path)

    required = {
        "u",
        "c0",
        "beta",
        "tag",
        "source_kind",
        "source_ref",
        "fit_method_tag",
        "sample_kw",
        "data_fingerprint",
    }
    assert required.issubset(set(payload.keys()))
    assert payload["source_kind"] in {"csv", "manual", "synthetic", "unknown"}
    assert str(payload["data_fingerprint"])

    sample_kw = _as_sample_kw(payload["sample_kw"])
    expected = DR01Fit1D.data_fingerprint_from_sample(sample_kw)
    assert payload["data_fingerprint"] == expected

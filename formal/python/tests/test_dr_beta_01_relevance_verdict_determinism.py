from __future__ import annotations

import json
from pathlib import Path

import pytest


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


def _beta_sign(beta: float) -> str:
    if abs(beta) < 1e-30:
        return "0"
    return "+" if beta > 0 else "-"


def test_dr_beta_01_curved_beta_metrics_are_locked():
    base = REPO_ROOT / "formal" / "external_evidence" / "bec_bragg_steinhauer_2001"

    spec = [
        (
            "DR-02",
            base / "dr01_fit_artifact_curved.json",
            9,
            "80c14686bbf4006939d1cdd9128ec4c7d6dffa90688c0b3463a6ff530e7ec5af",
            "10e33842da23f545d62614da36d260b6c703aa834535ba66e27574534c924f61",
            2.3789270790166762e-17,
            2.7529466483225495e-17,
            0.8641384606803861,
            "+",
        ),
        (
            "DR-03",
            base / "dr03_fit_artifact_curved.json",
            6,
            "eb6bbfa1d6abd0312156719da60a862a215f67e83e313f5586fe80e2082e4a24",
            "a951bc6ca97eaac6d691bfc5a4c0d53973ba6a833875da8ad36c16b5838a1218",
            2.0543090235917590e-17,
            9.5830763157086800e-17,
            0.2143684299189305,
            "+",
        ),
        (
            "DR-04d",
            base / "dr04d_fit_artifact_curved.json",
            5,
            "4625f1556255e06a1c16408ee1c820da25d846f3ab53f91e446a975d505397b8",
            "6dca51e7264fb7fa3847faab8645ccd6ea0933e70ea0c94649be5e420fd42b68",
            -6.1687621091483440e-17,
            1.5868946466088918e-16,
            0.3887316730402144,
            "-",
        ),
        (
            "DR-05",
            base / "dr05_fit_artifact_curved.json",
            5,
            "4625f1556255e06a1c16408ee1c820da25d846f3ab53f91e446a975d505397b8",
            "6dca51e7264fb7fa3847faab8645ccd6ea0933e70ea0c94649be5e420fd42b68",
            -6.1687621091483440e-17,
            1.5868946466088918e-16,
            0.3887316730402144,
            "-",
        ),
    ]

    seen_signs: list[str] = []
    fingerprints: dict[str, str] = {}

    for (
        label,
        path,
        n_expected,
        data_fp,
        quality_fp,
        beta_expected,
        beta_stderr_expected,
        beta_snr_expected,
        sign_expected,
    ) in spec:
        d = _load_json(path)
        q = d["fit_quality"]

        assert int(q["n_points"]) == n_expected
        assert d["data_fingerprint"] == data_fp
        assert d["fit_quality_fingerprint"] == quality_fp

        beta = float(d["beta"])
        beta_stderr = float(q["beta_stderr_s_per_m2"])
        beta_snr = abs(beta) / beta_stderr

        assert beta == pytest.approx(beta_expected, rel=0, abs=0)
        assert beta_stderr == pytest.approx(beta_stderr_expected, rel=0, abs=0)
        assert beta_snr == pytest.approx(beta_snr_expected, rel=0, abs=1e-15)

        assert abs(beta) <= 2.0 * beta_stderr

        sign = _beta_sign(beta)
        assert sign == sign_expected
        seen_signs.append(sign)
        fingerprints[label] = data_fp

    # DR-β-01 verdict stability checks
    assert "+" in seen_signs and "-" in seen_signs
    assert fingerprints["DR-04d"] == fingerprints["DR-05"]

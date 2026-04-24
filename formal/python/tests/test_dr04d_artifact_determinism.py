from __future__ import annotations

import json
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))


def _load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def test_dr04d_linear_artifact_fingerprints_are_locked():
    base = REPO_ROOT / "formal" / "external_evidence" / "bec_bragg_steinhauer_2001"
    d = _load_json(base / "dr04d_fit_artifact.json")

    assert d["fit_quality"]["n_points"] == 5
    assert d["data_fingerprint"] == "4625f1556255e06a1c16408ee1c820da25d846f3ab53f91e446a975d505397b8"
    assert d["fit_quality_fingerprint"] == "9c033241bf11553100766e5731e455f03baa81e8032f4df4c2c738eb818150d0"


def test_dr04d_curved_artifact_fingerprints_are_locked():
    base = REPO_ROOT / "formal" / "external_evidence" / "bec_bragg_steinhauer_2001"
    d = _load_json(base / "dr04d_fit_artifact_curved.json")

    assert d["fit_quality"]["n_points"] == 5
    assert d["data_fingerprint"] == "4625f1556255e06a1c16408ee1c820da25d846f3ab53f91e446a975d505397b8"
    assert d["fit_quality_fingerprint"] == "6dca51e7264fb7fa3847faab8645ccd6ea0933e70ea0c94649be5e420fd42b68"

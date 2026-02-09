from __future__ import annotations

import json

from formal.python.toe.observables.ovdq01_ds02_units_invariant import (
    default_artifact_path,
    ovdq01_ds02_units_invariant_record,
)


def test_ov_dq01_ds02_units_invariant_artifact_matches_computed() -> None:
    p = default_artifact_path()
    assert p.exists(), f"Missing canonical artifact: {p.as_posix()}"

    on_disk = json.loads(p.read_text(encoding="utf-8"))
    computed = ovdq01_ds02_units_invariant_record().to_jsonable()

    assert on_disk["schema"] == "OV-DQ-01_DS02_units_invariant/v1"
    assert isinstance(on_disk.get("fingerprint"), str)
    assert isinstance(on_disk.get("columns"), list) and len(on_disk["columns"]) > 0
    assert int(on_disk.get("n_rows", 0)) > 0
    assert on_disk == computed


def test_ov_dq01_ds02_units_invariant_verdict_and_flags() -> None:
    rec = ovdq01_ds02_units_invariant_record().to_jsonable()
    verdict = rec["verdict"]
    assert verdict["passes"] is True

    flags = list(rec.get("suspicion_flags", []))
    # DS-02 k is in um^-1, so a k-units conversion to m^-1 should be suspected.
    # The omega_over_2pi column name is legacy; values are interpreted as Hz.
    assert "k_units_mismatch_suspected" in flags
    assert "frequency_units_mismatch_suspected" not in flags

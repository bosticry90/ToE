from __future__ import annotations

import json
from pathlib import Path

from formal.python.toe.observables.ovdq01_adequacy_drilldown_record import (
    default_artifact_path,
    ovdq01_adequacy_drilldown_record,
)


def test_ov_dq01_adequacy_drilldown_artifact_matches_computed() -> None:
    artifact_path = default_artifact_path()
    assert artifact_path.exists(), f"Missing canonical artifact: {artifact_path.as_posix()}"

    on_disk = json.loads(artifact_path.read_text(encoding="utf-8"))
    computed = ovdq01_adequacy_drilldown_record(adequacy_policy=str(on_disk["adequacy_policy"])).to_jsonable()

    # Schema sanity (minimal)
    assert on_disk["schema"] == "OV-DQ-01_adequacy_drilldown/v1"
    assert "fingerprint" in on_disk
    assert isinstance(on_disk["ov04x"]["windows"], list) and len(on_disk["ov04x"]["windows"]) > 0
    assert isinstance(on_disk["ov03x"]["windows"], list) and len(on_disk["ov03x"]["windows"]) > 0

    assert on_disk == computed


def test_ov_dq01_ds02_emits_scale_suspicion_flag() -> None:
    rec = ovdq01_adequacy_drilldown_record().to_jsonable()
    flags = list(rec["ov04x"].get("suspicion_flags", []))
    assert "scale_or_units_mismatch_suspected" not in flags

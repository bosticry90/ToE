
from __future__ import annotations

import json
import re
from typing import Any, Dict

_JSON_BLOCK_RE = re.compile(r"```json\s*(\{.*?\})\s*```", re.DOTALL)

def _extract_json_block(md_text: str) -> Dict[str, Any]:
    m = _JSON_BLOCK_RE.search(md_text)
    if not m:
        raise AssertionError("No ```json ... ``` block found in markdown text")
    try:
        return json.loads(m.group(1))
    except json.JSONDecodeError as e:
        raise AssertionError(f"Failed to parse json block: {e}") from e

from pathlib import Path

import pytest

from formal.python.toe.observables.ovfnwt00_fn01_weight_policy_declarations_record import (
    ovfnwt00_weight_policy_declarations_record,
    render_ovfnwt00_lock_markdown,
)
from formal.python.toe.observables.ovfnwt01_fn01_weight_policy_pruning_table_record import (
    ovfnwt01_weight_policy_pruning_table_record,
)
from formal.python.toe.observables.ovbrfn00_fn01_metric_residual_prediction_declarations_record import (
    ovbrfn00_metric_residual_prediction_declarations_record,
    render_ovbrfn00_lock_markdown,
)
from formal.python.toe.observables.ovbrfn01_fn01_metric_residual_pruning_table_record import (
    ovbrfn01_metric_residual_pruning_table_record,
    render_ovbrfn01_lock_markdown,
)
from formal.python.toe.observables.ovdrbr01_candidate_pruning_table_record import ovdrbr01_candidate_pruning_table_record


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))


def test_ov_fn_wt01_override_manifest_yields_true_and_false(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    override = REPO_ROOT / "formal" / "markdown locks" / "gates" / "admissibility_manifest_ENABLED_OVERRIDE.json"
    assert override.exists(), "Expected enabled override manifest file to exist"

    # Preflight: check OV-DR-BR-01 status under override manifest
    rec_drbr01 = ovdrbr01_candidate_pruning_table_record(
        date="2026-01-25",
        admissibility_manifest_path=override,
    )
    print("DEBUG rec_drbr01.status:", rec_drbr01.status)
    assert rec_drbr01.status["blocked"] is False, f"rec_drbr01.status: {rec_drbr01.status}"

    # Do not rely on env var resolution; pass manifest path explicitly.
    monkeypatch.delenv("TOE_ADMISSIBILITY_MANIFEST", raising=False)

    # Create an OV-BR-FN-01 lock under the override manifest (so it is non-blocked) and feed it into OV-FN-WT-01.
    tmp_brfn00_lock = tmp_path / "OV-BR-FN-00_tmp_override.md"
    rec_brfn00 = ovbrfn00_metric_residual_prediction_declarations_record(
        date="2026-01-25",
        admissibility_manifest_path=override,
    )
    tmp_brfn00_lock.write_text(render_ovbrfn00_lock_markdown(rec_brfn00), encoding="utf-8")

    tmp_brfn01_lock = tmp_path / "OV-BR-FN-01_tmp_override.md"
    rec_brfn01 = ovbrfn01_metric_residual_pruning_table_record(
        date="2026-01-25",
        pred_decl_lock_path=tmp_brfn00_lock,
        admissibility_manifest_path=override,
    )
    print("DEBUG rec_brfn01.status:", rec_brfn01.status)
    assert rec_brfn01.status["blocked"] is False, f"rec_brfn01.status: {rec_brfn01.status}"
    tmp_brfn01_lock.write_text(render_ovbrfn01_lock_markdown(rec_brfn01), encoding="utf-8")

    # Create an OV-FN-WT-00 lock under the override manifest and feed it into OV-FN-WT-01.
    tmp_decl_lock = tmp_path / "OV-FN-WT-00_tmp_override.md"

    rec0 = ovfnwt00_weight_policy_declarations_record(
        date="2026-01-25",
        admissibility_manifest_path=override,
    )
    print("DEBUG rec_wt00.status:", rec0.status)
    assert rec0.status["blocked"] is False, f"rec_wt00.status: {rec0.status}"
    tmp_decl_lock.write_text(render_ovfnwt00_lock_markdown(rec0), encoding="utf-8")

    # Pinpoint input lock identity for WT-01
    brfn01_locked = _extract_json_block(tmp_brfn01_lock.read_text(encoding="utf-8"))
    wt00_locked = _extract_json_block(tmp_decl_lock.read_text(encoding="utf-8"))
    print("DEBUG brfn01_locked.schema:", brfn01_locked.get("schema"))
    print("DEBUG brfn01_locked.observable_id:", brfn01_locked.get("observable_id"))
    print("DEBUG wt00_locked.schema:", wt00_locked.get("schema"))
    print("DEBUG wt00_locked.observable_id:", wt00_locked.get("observable_id"))

    rec = ovfnwt01_weight_policy_pruning_table_record(
        date="2026-01-25",
        br_fn_pruning_lock_path=tmp_brfn01_lock,
        policy_decl_lock_path=tmp_decl_lock,
        admissibility_manifest_path=override,
    )
    print("DEBUG rec_fnwt01.status:", rec.status)
    if rec.status.get("blocked", False):
        for k in [
            "reasons",
            "required_gates",
            "missing_required_gates",
            "missing_inputs",
            "missing_fields",
            "admissibility_manifest",
        ]:
            if k in rec.status:
                print(f"DEBUG rec_fnwt01.status[{k}]:", rec.status[k])
    assert rec.status["blocked"] is False, f"rec_fnwt01.status: {rec.status}"

    statuses = [r.get("survives_fn_weight_policy_constraints") for r in rec.rows]
    assert "true" in statuses
    assert "false" in statuses

    assert all(r.get("computed_under_blocked_admissibility") is False for r in rec.rows)

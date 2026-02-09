from __future__ import annotations

import json
from pathlib import Path

import pytest

from formal.python.toe.observables.ovbrfn00_fn01_metric_residual_prediction_declarations_record import (
    ovbrfn00_metric_residual_prediction_declarations_record,
    render_ovbrfn00_lock_markdown,
)
from formal.python.toe.observables.ovbrfn01_fn01_metric_residual_pruning_table_record import (
    ovbrfn01_metric_residual_pruning_table_record,
    render_ovbrfn01_lock_markdown,
)
from formal.python.toe.observables.ovdrbr01_candidate_pruning_table_record import (
    ovdrbr01_candidate_pruning_table_record,
    render_ovdrbr01_lock_markdown,
)
from formal.python.toe.observables.ovfnwt00_fn01_weight_policy_declarations_record import (
    ovfnwt00_weight_policy_declarations_record,
    render_ovfnwt00_lock_markdown,
)
from formal.python.toe.observables.ovfnwt01_fn01_weight_policy_pruning_table_record import (
    ovfnwt01_weight_policy_pruning_table_record,
)


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))


def _write_json(path: Path, payload: dict) -> None:
    path.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")


def test_wt00_missing_br_candidate_id_is_wildcard_and_wt01_expands_deterministically(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    override = REPO_ROOT / "formal" / "markdown locks" / "gates" / "admissibility_manifest_ENABLED_OVERRIDE.json"
    assert override.exists()

    monkeypatch.delenv("TOE_ADMISSIBILITY_MANIFEST", raising=False)

    # Ensure we have a stable, local OV-DR-BR-01 input lock.
    rec_drbr01 = ovdrbr01_candidate_pruning_table_record(
        date="2026-01-25",
        admissibility_manifest_path=override,
    )
    assert rec_drbr01.status["blocked"] is False
    drbr01_lock = tmp_path / "OV-DR-BR-01_override_tmp.md"
    drbr01_lock.write_text(render_ovdrbr01_lock_markdown(rec_drbr01), encoding="utf-8")

    # Create OV-BR-FN-01 under override in tmp_path.
    brfn00_lock = tmp_path / "OV-BR-FN-00_override_tmp.md"
    rec_brfn00 = ovbrfn00_metric_residual_prediction_declarations_record(
        date="2026-01-25",
        admissibility_manifest_path=override,
    )
    brfn00_lock.write_text(render_ovbrfn00_lock_markdown(rec_brfn00), encoding="utf-8")

    brfn01_lock = tmp_path / "OV-BR-FN-01_override_tmp.md"
    rec_brfn01 = ovbrfn01_metric_residual_pruning_table_record(
        date="2026-01-25",
        pred_decl_lock_path=brfn00_lock,
        admissibility_manifest_path=override,
    )
    assert rec_brfn01.status["blocked"] is False
    brfn01_lock.write_text(render_ovbrfn01_lock_markdown(rec_brfn01), encoding="utf-8")

    # Declaration payload omits br_candidate_id -> should normalize to wildcard "*".
    decl_payload = {
        "schema": "FNWT01_weight_policy_declarations/v1",
        "version": 1,
        "candidates": {
            "policyA": {"fn_candidate_id": "fn01_make_P_cubic_artifact", "w_fn": 1.0, "max_score": 0.08},
            "policyB": {"fn_candidate_id": "fn01_make_P_cubic_artifact", "w_fn": 1.0, "max_score": 0.05},
        },
    }
    decl_json = tmp_path / "decl_missing_br_candidate_id.json"
    _write_json(decl_json, decl_payload)

    rec_wt00 = ovfnwt00_weight_policy_declarations_record(
        date="2026-01-25",
        declarations_path=decl_json,
        admissibility_manifest_path=override,
    )
    assert rec_wt00.status["blocked"] is False
    assert all(r.get("br_candidate_id") == "*" for r in rec_wt00.rows)

    wt00_lock = tmp_path / "OV-FN-WT-00_override_tmp.md"
    wt00_lock.write_text(render_ovfnwt00_lock_markdown(rec_wt00), encoding="utf-8")

    # WT-01 expands wildcard policies across BR candidates deterministically (sorted).
    rec_wt01_a = ovfnwt01_weight_policy_pruning_table_record(
        date="2026-01-25",
        br_pruning_lock_path=drbr01_lock,
        br_fn_pruning_lock_path=brfn01_lock,
        policy_decl_lock_path=wt00_lock,
        admissibility_manifest_path=override,
    )
    rec_wt01_b = ovfnwt01_weight_policy_pruning_table_record(
        date="2026-01-25",
        br_pruning_lock_path=drbr01_lock,
        br_fn_pruning_lock_path=brfn01_lock,
        policy_decl_lock_path=wt00_lock,
        admissibility_manifest_path=override,
    )

    assert rec_wt01_a.status["blocked"] is False
    assert rec_wt01_a.fingerprint() == rec_wt01_b.fingerprint()

    br_candidate_ids = sorted({r.get("candidate_id") for r in rec_drbr01.rows if isinstance(r, dict)})
    policy_ids = sorted({r.get("policy_id") for r in rec_wt00.rows if isinstance(r, dict)})

    # Expect one row per (policy_id, br_candidate_id).
    rows = list(rec_wt01_a.rows)
    assert len(rows) == len(br_candidate_ids) * len(policy_ids)

    # For each policy, rows should be in sorted BR candidate order.
    for policy_id in policy_ids:
        policy_rows = [r for r in rows if r.get("policy_id") == policy_id]
        got = [r.get("br_candidate_id") for r in policy_rows]
        assert got == br_candidate_ids

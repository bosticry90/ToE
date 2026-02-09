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
from formal.python.toe.observables.ovfnwt00_fn01_weight_policy_declarations_record import (
    ovfnwt00_weight_policy_declarations_record,
    render_ovfnwt00_lock_markdown,
)
from formal.python.toe.observables.ovfnwt01_fn01_weight_policy_pruning_table_record import (
    ovfnwt01_weight_policy_pruning_table_record,
    render_ovfnwt01_lock_markdown,
)
from formal.python.toe.observables.ovfnwt02_selected_weight_policy_record import (
    ovfnwt02_selected_weight_policy_record,
    render_ovfnwt02_lock_markdown,
)
from formal.python.toe.observables.ovfn02_weighted_residual_audit_record import (
    ovfn02_weighted_residual_audit_record,
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


def test_override_policy_switch_changes_downstream_audit(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    override = REPO_ROOT / "formal" / "markdown locks" / "gates" / "admissibility_manifest_ENABLED_OVERRIDE.json"
    assert override.exists()

    # Ensure env does not affect this test (explicit manifest path everywhere).
    monkeypatch.delenv("TOE_ADMISSIBILITY_MANIFEST", raising=False)

    # Build OV-BR-FN-01 under override in tmp_path.
    tmp_brfn00_lock = tmp_path / "OV-BR-FN-00_override.md"
    rec_brfn00 = ovbrfn00_metric_residual_prediction_declarations_record(
        date="2026-01-25",
        admissibility_manifest_path=override,
    )
    tmp_brfn00_lock.write_text(render_ovbrfn00_lock_markdown(rec_brfn00), encoding="utf-8")

    tmp_brfn01_lock = tmp_path / "OV-BR-FN-01_override.md"
    rec_brfn01 = ovbrfn01_metric_residual_pruning_table_record(
        date="2026-01-25",
        pred_decl_lock_path=tmp_brfn00_lock,
        admissibility_manifest_path=override,
    )
    tmp_brfn01_lock.write_text(render_ovbrfn01_lock_markdown(rec_brfn01), encoding="utf-8")
    assert rec_brfn01.status["blocked"] is False

    # Two declaration variants that flip which policy survives.
    policy_loose = {
        "schema": "FNWT01_weight_policy_declarations/v1",
        "version": 1,
        "candidates": {
            "fnwt01_policy_loose": {"fn_candidate_id": "fn01_make_P_cubic_artifact", "w_fn": 1.0, "max_score": 0.08},
            "fnwt01_policy_strict": {"fn_candidate_id": "fn01_make_P_cubic_artifact", "w_fn": 1.0, "max_score": 0.05},
        },
    }
    policy_strict = {
        "schema": "FNWT01_weight_policy_declarations/v1",
        "version": 1,
        "candidates": {
            "fnwt01_policy_loose": {"fn_candidate_id": "fn01_make_P_cubic_artifact", "w_fn": 1.0, "max_score": 0.05},
            "fnwt01_policy_strict": {"fn_candidate_id": "fn01_make_P_cubic_artifact", "w_fn": 1.0, "max_score": 0.08},
        },
    }

    def run_variant(name: str, decl_payload: dict) -> tuple[str, str, dict]:
        decl_json = tmp_path / f"{name}_decl.json"
        _write_json(decl_json, decl_payload)

        tmp_wt00_lock = tmp_path / f"{name}_OV-FN-WT-00.md"
        rec_wt00 = ovfnwt00_weight_policy_declarations_record(
            date="2026-01-25",
            declarations_path=decl_json,
            admissibility_manifest_path=override,
        )
        tmp_wt00_lock.write_text(render_ovfnwt00_lock_markdown(rec_wt00), encoding="utf-8")
        assert rec_wt00.status["blocked"] is False

        tmp_wt01_lock = tmp_path / f"{name}_OV-FN-WT-01.md"
        rec_wt01 = ovfnwt01_weight_policy_pruning_table_record(
            date="2026-01-25",
            br_fn_pruning_lock_path=tmp_brfn01_lock,
            policy_decl_lock_path=tmp_wt00_lock,
            admissibility_manifest_path=override,
        )
        tmp_wt01_lock.write_text(render_ovfnwt01_lock_markdown(rec_wt01), encoding="utf-8")
        assert rec_wt01.status["blocked"] is False

        tmp_wt02_lock = tmp_path / f"{name}_OV-FN-WT-02.md"
        rec_wt02 = ovfnwt02_selected_weight_policy_record(
            date="2026-01-25",
            pruning_lock_path=tmp_wt01_lock,
            admissibility_manifest_path=override,
        )
        tmp_wt02_lock.write_text(render_ovfnwt02_lock_markdown(rec_wt02), encoding="utf-8")
        assert rec_wt02.status["blocked"] is False

        rec_fn02 = ovfn02_weighted_residual_audit_record(
            date="2026-01-25",
            selection_lock_path=tmp_wt02_lock,
            admissibility_manifest_path=override,
        )
        assert rec_fn02.status["blocked"] is False

        selected = rec_wt02.selection.get("selected_policy_id")
        assert isinstance(selected, str)

        return selected, rec_fn02.fingerprint(), rec_fn02.fingerprint_payload()

    sel_loose, audit_fp_loose, audit_pre_loose = run_variant("loose", policy_loose)
    sel_strict, audit_fp_strict, _audit_pre_strict = run_variant("strict", policy_strict)

    assert sel_loose != sel_strict
    assert audit_fp_loose != audit_fp_strict

    # Determinism: same semantic payload, different filenames/paths.
    sel_loose2, audit_fp_loose2, audit_pre_loose2 = run_variant("loose2", policy_loose)
    assert sel_loose2 == sel_loose
    if audit_fp_loose2 != audit_fp_loose:
        # Failure-only hint: the audit fingerprint should not depend on paths.
        if audit_pre_loose2 != audit_pre_loose:
            raise AssertionError(
                "OV-FN-02 fingerprint preimage changed across semantically identical runs; "
                f"pre_loose={json.dumps(audit_pre_loose, sort_keys=True)} "
                f"pre_loose2={json.dumps(audit_pre_loose2, sort_keys=True)}"
            )
        raise AssertionError(
            "OV-FN-02 audit fingerprint changed across semantically identical runs; "
            f"audit_fp_loose={audit_fp_loose} audit_fp_loose2={audit_fp_loose2}"
        )

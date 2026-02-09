from __future__ import annotations

from pathlib import Path

import pytest

from formal.python.toe.observables.ovbrfn01_fn01_metric_residual_pruning_table_record import (
    ovbrfn01_metric_residual_pruning_table_record,
)
from formal.python.toe.observables.ovbrfn00_fn01_metric_residual_prediction_declarations_record import (
    ovbrfn00_metric_residual_prediction_declarations_record,
    render_ovbrfn00_lock_markdown,
)


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))


def test_ov_br_fn01_override_manifest_yields_true_and_false(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    override = REPO_ROOT / "formal" / "markdown locks" / "gates" / "admissibility_manifest_ENABLED_OVERRIDE.json"
    assert override.exists(), "Expected enabled override manifest file to exist"

    # Do not rely on env var resolution; pass manifest path explicitly.
    monkeypatch.delenv("TOE_ADMISSIBILITY_MANIFEST", raising=False)

    # Create an OV-BR-FN-00 lock under the override manifest and feed it into OV-BR-FN-01.
    tmp_lock = tmp_path / "OV-BR-FN-00_tmp_override.md"
    rec0 = ovbrfn00_metric_residual_prediction_declarations_record(
        date="2026-01-25",
        admissibility_manifest_path=override,
    )
    tmp_lock.write_text(render_ovbrfn00_lock_markdown(rec0), encoding="utf-8")

    rec = ovbrfn01_metric_residual_pruning_table_record(
        date="2026-01-25",
        pred_decl_lock_path=tmp_lock,
        admissibility_manifest_path=override,
    )

    assert rec.status["blocked"] is False

    statuses = [r.get("survives_br_fn_constraints") for r in rec.rows]
    assert "true" in statuses
    assert "false" in statuses

    # Under override manifest, rows must not be tagged as computed under blocked admissibility.
    assert all(r.get("computed_under_blocked_admissibility") is False for r in rec.rows)

    # tmp_path is cleaned up by pytest.

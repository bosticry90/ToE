from __future__ import annotations

import json
import re
from pathlib import Path

from formal.python.toe.observables.ovbrfn01_fn01_metric_residual_pruning_table_record import (
    ovbrfn01_metric_residual_pruning_table_record,
)


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))


def _extract_json_block(md_text: str) -> dict:
    m = re.search(r"```json\s*(\{.*?\})\s*```", md_text, flags=re.DOTALL)
    if m is None:
        raise AssertionError("Missing JSON record block")
    return json.loads(m.group(1))


def _extract_record_fingerprint(md_text: str) -> str:
    m = re.search(r"Record fingerprint:\s*`([0-9a-f]{64})`", md_text)
    if m is None:
        raise AssertionError("Missing record fingerprint line")
    return m.group(1)


def test_ov_br_fn01_lock_matches_computed_record() -> None:
    rec = ovbrfn01_metric_residual_pruning_table_record(date="2026-01-25")

    lock_path = (
        REPO_ROOT
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-BR-FN-01_fn01_metric_residual_pruning_table.md"
    )
    lock_text = lock_path.read_text(encoding="utf-8")
    locked = _extract_json_block(lock_text)

    assert locked["schema"] == "OV-BR-FN-01_fn01_metric_residual_pruning_table/v1"
    assert locked["observable_id"] == "OV-BR-FN-01"

    assert locked == rec.to_jsonable()
    assert _extract_record_fingerprint(lock_text) == rec.fingerprint()


def test_ov_br_fn01_blocks_if_residual_lock_missing() -> None:
    missing = REPO_ROOT / "formal" / "markdown" / "locks" / "functionals" / "_MISSING_FN01_RESIDUAL_.md"
    rec = ovbrfn01_metric_residual_pruning_table_record(date="2026-01-25", residual_lock_path=missing)

    assert rec.status["blocked"] is True
    assert rec.status["reasons"] == ["missing_input_lock_FN-01_cross_fit_metric_residual_DR02_DR03"]
    assert rec.rows == []


def test_ov_br_fn01_structural_mismatch_yields_false_with_missing_field_list(tmp_path: Path) -> None:
    # Create a synthetic residual lock that omits 'Score'.
    fake = tmp_path / "FN-01_cross_fit_metric_residual_DR02_DR03.md"
    fake.write_text(
        "# FN-01 cross-fit metric residual (DR-02a vs DR-03a)\n\n"
        "## Results (deterministic)\n\n"
        "- g_tt^02 = -1.0e-6\n"
        "- g_tt^03 = -2.0e-6\n"
        "- epsilon = 1e-12\n"
        "- R_metric = 0.5\n"
        "- W(FN) = 1.0\n",
        encoding="utf-8",
    )

    rec = ovbrfn01_metric_residual_pruning_table_record(date="2026-01-25", residual_lock_path=fake)

    # At least one declared candidate should fail due to missing Score.
    failed = [r for r in rec.rows if r.get("survives_br_fn_constraints") == "false"]
    assert failed, "Expected at least one failing row"

    # Ensure the explicit missing field list includes 'Score'.
    missing_lines = []
    for r in failed:
        for code in list(r.get("reason_codes") or []):
            if isinstance(code, str) and code.startswith("missing_fields:"):
                missing_lines.append(code)

    assert missing_lines, "Expected missing_fields:* reason code"
    assert any("Score" in s for s in missing_lines)

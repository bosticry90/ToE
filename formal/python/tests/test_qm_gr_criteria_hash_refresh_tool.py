from __future__ import annotations

from formal.python.tools import qm_gr_criteria_hash_refresh as tool


def test_hash_refresh_check_reports_no_drift_on_pinned_repo_state() -> None:
    drifts = tool.collect_drift(repo_root=tool.REPO_ROOT)
    assert drifts == []


def test_hash_refresh_write_is_idempotent_on_pinned_repo_state() -> None:
    changed = tool.apply_updates(repo_root=tool.REPO_ROOT)
    assert changed == []

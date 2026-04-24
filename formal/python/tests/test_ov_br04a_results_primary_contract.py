from __future__ import annotations

from pathlib import Path

from formal.python.toe.observables.ovbr04a_bragg_lowk_slope_conditionA_record import (
    _apply_results_primary_contract,
    ovbr04a_bragg_lowk_slope_conditionA_record,
)
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))


def test_br04a_unblocked_implies_results_primary_exists_under_override_manifest() -> None:
    override = REPO_ROOT / "formal" / "markdown locks" / "gates" / "admissibility_manifest_ENABLED_OVERRIDE.json"
    assert override.exists()

    rec = ovbr04a_bragg_lowk_slope_conditionA_record(date="2026-01-25", admissibility_manifest_path=override)

    assert rec.status["blocked"] is False
    assert isinstance(rec.results, dict)
    assert "primary" in rec.results


def test_br04a_missing_primary_fail_closed_sets_reason() -> None:
    status = {"blocked": False, "reasons": []}
    results = {}

    status2 = _apply_results_primary_contract(status=status, results=results)

    assert status2["blocked"] is True
    assert "missing_results_primary" in list(status2.get("reasons") or [])

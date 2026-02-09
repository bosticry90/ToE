from __future__ import annotations

from pathlib import Path

from formal.python.tools.bridge_toyh_c6_orthogonality_mismatch_report_generate import (
    build_bridge_toyh_c6_orthogonality_mismatch_report,
)
from formal.python.tools.bridge_toyh_c6_orthogonality_report_generate import (
    build_bridge_toyh_c6_orthogonality_report,
)


def _repo_root_from_test_file(p: Path) -> Path:
    p = p.resolve()
    if p.is_file():
        p = p.parent
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def test_bridge_toyh_c6_orthogonality_mismatch_report_contains_only_disagreements() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))

    source = build_bridge_toyh_c6_orthogonality_report(repo_root=repo_root)
    mismatch = build_bridge_toyh_c6_orthogonality_mismatch_report(repo_root=repo_root)

    source_ids = {
        str(it.get("probe_id"))
        for it in source.get("items", [])
        if str(it.get("pair_status")) in {"pass_fail", "fail_pass"}
    }
    mismatch_items = list(mismatch.get("items", []))
    mismatch_ids = {str(it.get("probe_id")) for it in mismatch_items}

    assert mismatch_ids == source_ids
    assert all(str(it.get("pair_status")) in {"pass_fail", "fail_pass"} for it in mismatch_items)

    summary = dict(mismatch.get("summary", {}))
    pair_counts = dict(summary.get("pair_counts", {}))
    assert summary.get("n_mismatch") == len(mismatch_items)
    assert pair_counts.get("pass_fail", 0) + pair_counts.get("fail_pass", 0) == len(mismatch_items)


def test_bridge_toyh_c6_orthogonality_mismatch_report_has_signed_margins_and_reason_codes() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))

    report = build_bridge_toyh_c6_orthogonality_mismatch_report(repo_root=repo_root)
    items = list(report.get("items", []))
    assert items, "Expected non-empty mismatch set"

    allowed_failure_reason_codes = {
        "phase_invariance_violation",
        "phase_threshold_margin_small",
        "phase_observable_sensitivity",
        "phase_unclassified_fail",
        "current_invariance_violation",
        "current_threshold_margin_small",
        "current_observable_sensitivity",
        "current_unclassified_fail",
    }

    near_eps = float(report.get("thresholds", {}).get("near_boundary_eps", 1e-3))
    for it in items:
        signed_margin = float(it.get("signed_margin"))
        reason_code = str(it.get("failure_reason_code"))

        assert signed_margin < 0.0
        assert reason_code in allowed_failure_reason_codes
        assert isinstance(it.get("near_boundary"), bool)

        if reason_code.endswith("threshold_margin_small"):
            assert abs(signed_margin) <= near_eps


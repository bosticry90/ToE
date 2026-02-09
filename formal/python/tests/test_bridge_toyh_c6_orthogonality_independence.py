from __future__ import annotations

from pathlib import Path

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


def test_bridge_toyh_c6_orthogonality_independence() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))

    report = build_bridge_toyh_c6_orthogonality_report(repo_root=repo_root)

    assert report.get("schema_version") == 1
    assert report.get("report_id") == "BRIDGE_TOYH_C6_ORTHOGONALITY_REPORT"

    items = list(report.get("items", []))
    summary = dict(report.get("summary", {}))
    counts = dict(summary.get("counts", {}))

    assert summary.get("n_probes") == len(items)
    assert counts.get("pass_fail", 0) >= 1
    assert counts.get("fail_pass", 0) >= 1
    assert summary.get("nonredundant") is True

    by_probe = {str(it.get("probe_id")): it for it in items}
    assert by_probe["stress_phase_control_small_theta_n11"]["pair_status"] == "fail_pass"
    assert by_probe["stress_current_control_small_alpha_n11"]["pair_status"] == "pass_fail"
    assert by_probe["stress_c6_side_amplitude_scale_n11"]["pair_status"] == "fail_fail"


def test_bridge_toyh_c6_orthogonality_localization_reason_codes_are_valid() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))

    report = build_bridge_toyh_c6_orthogonality_report(repo_root=repo_root)

    allowed_pairs = {"pass_pass", "pass_fail", "fail_pass", "fail_fail"}
    allowed_localization = {"none", "toyh_observable_construction", "c6_side_constraint", "mixed"}
    allowed_phase_reasons = {"PASS", "FAIL_PHASE_INVARIANCE_TOL", "FAIL_PHASE_CHANNEL_CONTROL_MIN"}
    allowed_current_reasons = {"PASS", "FAIL_CURRENT_INVARIANCE_TOL", "FAIL_CURRENT_CHANNEL_CONTROL_MIN"}

    items = list(report.get("items", []))
    assert items, "Orthogonality report produced no probe items"

    for item in items:
        assert item.get("pair_status") in allowed_pairs
        assert item.get("localization_note") in allowed_localization

        phase = dict(item.get("phase_channel", {}))
        current = dict(item.get("current_channel", {}))

        assert phase.get("reason_code") in allowed_phase_reasons
        assert current.get("reason_code") in allowed_current_reasons

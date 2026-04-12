from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_phase_d_untouched_lane_first_test_packet_report as tool


_CANONICAL_ANTI_ALIAS = {
    "QM-STAT": True,
    "GR-ROW-001": True,
    "EM-QFT": True,
    "SHARED-MODEL-CLASS": True,
    "QFT-GR": True,
}


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    first_test_signal_detected: bool = False,
    anti_alias_checks: dict[str, bool] | None = None,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "science_phase_d_untouched_lane_selection_report": "formal/output/reports/science_phase_d_untouched_lane_selection_20260412_v0.json",
                "science_closed_lane_non_reopen_reason_summary_report": "formal/output/reports/science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
                "science_closed_lane_reopen_eligibility_report": "formal/output/reports/science_closed_lane_reopen_eligibility_20260412_v0.json",
            },
            "first_test_policy": {
                "required_phase_d_selection_outcome": "UNTOUCHED_LANE_SELECTED_FOR_BOUNDED_FIRST_TEST",
                "required_selected_untouched_lane": "LANE-NEUTRINO-INTERFACE-001",
                "required_non_reopen_summary_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED",
                "required_reopen_eligibility_outcome": "CLOSED_LANE_REOPEN_NONE_ELIGIBLE",
                "target_lane": "LANE-NEUTRINO-INTERFACE-001",
                "single_attack_class": "neutrino_interface_phase_lock_probe",
                "one_execution_only": True,
                "one_immediate_ruling_only": True,
                "first_test_signal_detected": first_test_signal_detected,
                "anti_alias_checks": anti_alias_checks if anti_alias_checks is not None else dict(_CANONICAL_ANTI_ALIAS),
                "single_layer_only": True,
                "single_outcome_only": True,
            },
            "first_test_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_D_UNTOUCHED_LANE_FIRST_TEST_PACKET_OUTCOME",
                "no_loop_rule": "ONE_SCIENCE_PHASE_D_UNTOUCHED_LANE_FIRST_TEST_PACKET_LAYER_ONLY",
                "allowed_outcomes": [
                    "UNTOUCHED_LANE_FIRST_TEST_SIGNAL_DETECTED",
                    "UNTOUCHED_LANE_FIRST_TEST_NONDISCRIMINATIVE_HOLD",
                    "UNTOUCHED_LANE_FIRST_TEST_PATH_FALSIFIED",
                    "UNTOUCHED_LANE_FIRST_TEST_CONTRACT_VIOLATION",
                ],
                "default_outcome": "UNTOUCHED_LANE_FIRST_TEST_CONTRACT_VIOLATION",
            },
        },
    )


def _seed_inputs(root: Path, *, selected_lane: str = "LANE-NEUTRINO-INTERFACE-001") -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "science_phase_d_untouched_lane_selection_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "UNTOUCHED_LANE_SELECTED_FOR_BOUNDED_FIRST_TEST",
                "untouched_lane_candidate_id": selected_lane,
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
        {"summary": {"terminal_outcome": "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED"}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_closed_lane_reopen_eligibility_20260412_v0.json",
        {"summary": {"terminal_outcome": "CLOSED_LANE_REOPEN_NONE_ELIGIBLE"}},
    )


def test_reports_untouched_lane_first_test_nondiscriminative_hold(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_D_UNTOUCHED_LANE_FIRST_TEST_PACKET_20260412_v0.json"
    )
    _write_declaration(declaration_path, first_test_signal_detected=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "UNTOUCHED_LANE_FIRST_TEST_NONDISCRIMINATIVE_HOLD"


def test_reports_untouched_lane_first_test_signal_detected(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_D_UNTOUCHED_LANE_FIRST_TEST_PACKET_20260412_v0.json"
    )
    _write_declaration(declaration_path, first_test_signal_detected=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "UNTOUCHED_LANE_FIRST_TEST_SIGNAL_DETECTED"


def test_reports_contract_violation_when_anti_alias_check_fails(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_D_UNTOUCHED_LANE_FIRST_TEST_PACKET_20260412_v0.json"
    )
    anti_alias_checks = dict(_CANONICAL_ANTI_ALIAS)
    anti_alias_checks["QFT-GR"] = False
    _write_declaration(declaration_path, anti_alias_checks=anti_alias_checks)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "UNTOUCHED_LANE_FIRST_TEST_CONTRACT_VIOLATION"


def test_reports_contract_violation_when_selected_lane_mismatch(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path
        / "formal"
        / "docs"
        / "release"
        / "SCIENCE_PHASE_D_UNTOUCHED_LANE_FIRST_TEST_PACKET_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, selected_lane="LANE-OTHER-001")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "UNTOUCHED_LANE_FIRST_TEST_CONTRACT_VIOLATION"

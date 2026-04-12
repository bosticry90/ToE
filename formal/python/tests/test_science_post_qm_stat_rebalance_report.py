from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_post_qm_stat_rebalance_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    gr_ready: bool = True,
    em_qft_ready: bool = True,
    qft_gr_discovery_only: bool = True,
    require_rescoring: bool = False,
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "bridge_external_validation_policy_review_report": "formal/output/reports/bridge_external_validation_policy_review_20260412_v0.json",
                "bridge_admissibility_standard_review_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_admissibility_standard_review_20260412_v0.json",
                "bridge_repeatability_check_naming_review_report": "formal/output/reports/qm_stat_rl10_discrete_transition_bridge_repeatability_check_naming_review_20260412_v0.json",
            },
            "selection_policy": {
                "qm_stat_bridge_hold_required_outcome": "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD",
                "qm_stat_admissibility_hold_required_outcome": "LIMITED_HOLD_RETAINED",
                "qm_stat_naming_hold_required_outcome": "NO_SPECIFIC_CHECK_JUSTIFIED_YET",
                "gr_blocker_moving_ready": gr_ready,
                "em_qft_first_test_ready": em_qft_ready,
                "qft_gr_discovery_only_enforced": qft_gr_discovery_only,
                "require_rescoring_before_activation": require_rescoring,
                "default_next_action": "OPEN_SINGLE_GR_BLOCKER_MOVING_TRANCHE_PACKET",
            },
            "selection_contract": {
                "allowed_outcomes": [
                    "ACTIVATE_GR_BLOCKER_MOVING_TRANCHE",
                    "ACTIVATE_EM_QFT_SEAM_FIRST_TEST",
                    "KEEP_QFT_GR_DISCOVERY_ONLY",
                    "HOLD_AND_REQUIRE_RESCORING",
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SCIENCE_REBALANCE_OUTCOME",
                "no_loop_rule": "ONE_POST_QM_STAT_REBALANCE_ONLY",
                "default_outcome": "HOLD_AND_REQUIRE_RESCORING",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    external_policy_outcome: str = "EXTERNAL_VALIDATION_POLICY_INCOMPLETE_HOLD",
    admissibility_outcome: str = "LIMITED_HOLD_RETAINED",
    naming_outcome: str = "NO_SPECIFIC_CHECK_JUSTIFIED_YET",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "bridge_external_validation_policy_review_20260412_v0.json",
        {"summary": {"review_outcome": external_policy_outcome}},
    )
    _write_json(
        root
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_admissibility_standard_review_20260412_v0.json",
        {"summary": {"review_outcome": admissibility_outcome}},
    )
    _write_json(
        root
        / "formal"
        / "output"
        / "reports"
        / "qm_stat_rl10_discrete_transition_bridge_repeatability_check_naming_review_20260412_v0.json",
        {"summary": {"review_outcome": naming_outcome}},
    )


def test_rebalance_selects_gr_blocker_moving_tranche(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_POST_QM_STAT_REBALANCE_20260412_v0.json"
    )
    _write_declaration(declaration_path, gr_ready=True, em_qft_ready=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["selected_outcome"] == "ACTIVATE_GR_BLOCKER_MOVING_TRANCHE"


def test_rebalance_selects_em_qft_first_test_when_gr_not_ready(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_POST_QM_STAT_REBALANCE_20260412_v0.json"
    )
    _write_declaration(declaration_path, gr_ready=False, em_qft_ready=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["selected_outcome"] == "ACTIVATE_EM_QFT_SEAM_FIRST_TEST"


def test_rebalance_selects_qft_gr_discovery_only_when_others_not_ready(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_POST_QM_STAT_REBALANCE_20260412_v0.json"
    )
    _write_declaration(declaration_path, gr_ready=False, em_qft_ready=False, qft_gr_discovery_only=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["selected_outcome"] == "KEEP_QFT_GR_DISCOVERY_ONLY"


def test_rebalance_holds_and_requires_rescoring_on_hold_mismatch(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_POST_QM_STAT_REBALANCE_20260412_v0.json"
    )
    _write_declaration(declaration_path, gr_ready=True, em_qft_ready=True)
    _seed_inputs(tmp_path, external_policy_outcome="ADMISSIBLE_REPEATABILITY_STANDARD_DEFINED")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["selected_outcome"] == "HOLD_AND_REQUIRE_RESCORING"

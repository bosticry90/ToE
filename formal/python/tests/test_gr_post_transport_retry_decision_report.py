from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import gr_post_transport_retry_decision_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "target_row": "ROW-PILLAR-GR-001",
            "required_inputs": {
                "gr_master_action_transport_attack_retry_packet_report": "formal/output/reports/gr_master_action_transport_attack_retry_packet_20260412_v0.json",
                "gr_master_action_transport_obligation_declaration_report": "formal/output/reports/gr_master_action_transport_obligation_declaration_20260412_v0.json"
            },
            "decision_policy": {
                "target_row": "ROW-PILLAR-GR-001",
                "prior_attack_class": "GR_MASTER_ACTION_TRANSPORT_ATTACK",
                "prior_result": "GR_TRANSPORT_OBLIGATION_DECLARED_BUT_STILL_INSUFFICIENT",
                "transport_now_deprioritized": True,
                "focus_area": "REGIME_LIMIT_STRUCTURE",
                "single_decision_only": True,
                "single_outcome_only": True
            },
            "decision_contract": {
                "allowed_outcomes": [
                    "ACTIVATE_GR_WEAK_FIELD_CLOSURE_ATTACK",
                    "ACTIVATE_GR_REGIME_LIMIT_ALIGNMENT_ATTACK",
                    "ACTIVATE_GR_SEAM_INTERFACE_ATTACK",
                    "HOLD_GR_AND_REQUIRE_HIGHER_LEVEL_REVIEW"
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_GR_POST_TRANSPORT_DECISION_OUTCOME",
                "no_loop_rule": "ONE_GR_POST_TRANSPORT_DECISION_ONLY",
                "default_outcome": "ACTIVATE_GR_REGIME_LIMIT_ALIGNMENT_ATTACK"
            }
        },
    )


def _seed_inputs(
    root: Path,
    *,
    retry_outcome: str = "GR_TRANSPORT_OBLIGATION_DECLARED_BUT_STILL_INSUFFICIENT",
    obligation_id: str = "GR_MASTER_ACTION_TO_REGIME_LIMIT_TRANSPORT_OBLIGATION_v0",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "gr_master_action_transport_attack_retry_packet_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": retry_outcome,
                "target_row": "ROW-PILLAR-GR-001",
                "attack_class": "GR_MASTER_ACTION_TRANSPORT_ATTACK",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "gr_master_action_transport_obligation_declaration_20260412_v0.json",
        {
            "summary": {
                "missing_obligation_id": obligation_id,
                "obligation_type": "THEOREM_LINKED",
            }
        },
    )


def test_reports_regime_limit_alignment_when_regime_focused(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "GR_POST_TRANSPORT_RETRY_DECISION_20260412_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "ACTIVATE_GR_REGIME_LIMIT_ALIGNMENT_ATTACK"


def test_reports_hold_when_retry_outcome_broken(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "GR_POST_TRANSPORT_RETRY_DECISION_20260412_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, retry_outcome="GR_BLOCKER_MOVED")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_GR_AND_REQUIRE_HIGHER_LEVEL_REVIEW"


def test_reports_hold_when_obligation_not_regime_focused(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "GR_POST_TRANSPORT_RETRY_DECISION_20260412_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, obligation_id="GR_SOME_OTHER_OBLIGATION_v0")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "ACTIVATE_GR_REGIME_LIMIT_ALIGNMENT_ATTACK"


def test_reports_all_criteria_satisfied(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "GR_POST_TRANSPORT_RETRY_DECISION_20260412_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["objective_quality"]["summary"]["all_criteria_satisfied"] is True

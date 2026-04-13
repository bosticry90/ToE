from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_controlled_dormancy_protocol_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    policy_overrides: dict | None = None,
    include_full_policy_shape: bool = True,
) -> None:
    dormancy_policy = {
        "lane_execution_disallowed": True,
        "new_packet_execution_disallowed": True,
        "restart_front_door_required": True,
        "taxonomy_stability_required": True,
        "external_evidence_monitoring_allowed": True,
        "candidate_class_ideation_allowed": True,
    }
    if policy_overrides:
        dormancy_policy.update(policy_overrides)
    if not include_full_policy_shape:
        dormancy_policy.pop("candidate_class_ideation_allowed")

    _write_json(
        path,
        {
            "required_inputs": {
                "science_restart_trigger_contract_report": "formal/output/reports/science_restart_trigger_contract_20260412_v0.json",
                "science_post_phase_z_frontier_decision_report": "formal/output/reports/science_post_phase_z_frontier_decision_20260412_v0.json",
                "science_frontier_stop_state_summary_doc": "formal/docs/release/SCIENCE_FRONTIER_STOP_STATE_SUMMARY_20260412_v0.md",
            },
            "controlled_dormancy_contract": {
                "required_restart_trigger_outcome": "REMAIN_IN_GOVERNED_STOP_STATE",
                "required_post_phase_z_outcome": "PRESERVE_CURRENT_GOVERNED_STOP_STATE",
                "required_lane_reopen_authorized": False,
                "required_new_lane_or_packet_authorized_now": False,
                "forbid_closed_or_held_lane_reopen": True,
                "single_layer_only": True,
                "single_outcome_only": True,
                "dormancy_policy": dormancy_policy,
            },
            "controlled_dormancy_outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SCIENCE_CONTROLLED_DORMANCY_PROTOCOL_OUTCOME",
                "no_loop_rule": "ONE_SCIENCE_CONTROLLED_DORMANCY_PROTOCOL_LAYER_ONLY",
                "allowed_outcomes": [
                    "CONTROLLED_DORMANCY_PROTOCOL_ACTIVE",
                    "CONTROLLED_DORMANCY_PROTOCOL_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_CONTROLLED_DORMANCY_PROTOCOL_REPAIR",
                ],
                "default_outcome": "CONTROLLED_DORMANCY_PROTOCOL_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    restart_trigger_outcome: str = "REMAIN_IN_GOVERNED_STOP_STATE",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "science_restart_trigger_contract_20260412_v0.json",
        {"summary": {"terminal_outcome": restart_trigger_outcome}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_post_phase_z_frontier_decision_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "PRESERVE_CURRENT_GOVERNED_STOP_STATE",
                "lane_specific_reopen_authorized": False,
                "new_lane_or_packet_authorized_now": False,
            }
        },
    )
    _write_text(
        root / "formal" / "docs" / "release" / "SCIENCE_FRONTIER_STOP_STATE_SUMMARY_20260412_v0.md",
        "No currently governed lane is authorized to reopen.\n"
        "No currently screened future candidate is authorized for active execution.\n",
    )


def test_reports_controlled_dormancy_protocol_active(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_CONTROLLED_DORMANCY_PROTOCOL_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "CONTROLLED_DORMANCY_PROTOCOL_ACTIVE"


def test_reports_hold_pending_controlled_dormancy_protocol_repair(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_CONTROLLED_DORMANCY_PROTOCOL_20260412_v0.json"
    )
    _write_declaration(declaration_path, include_full_policy_shape=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_PENDING_CONTROLLED_DORMANCY_PROTOCOL_REPAIR"


def test_reports_controlled_dormancy_protocol_evidence_incomplete(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_CONTROLLED_DORMANCY_PROTOCOL_20260412_v0.json"
    )
    _write_declaration(
        declaration_path,
        policy_overrides={"lane_execution_disallowed": False},
    )
    _seed_inputs(tmp_path, restart_trigger_outcome="RESTART_TRIGGER_CONTRACT_EVIDENCE_INCOMPLETE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "CONTROLLED_DORMANCY_PROTOCOL_EVIDENCE_INCOMPLETE"

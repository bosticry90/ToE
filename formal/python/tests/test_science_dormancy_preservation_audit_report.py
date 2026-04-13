from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import science_dormancy_preservation_audit_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _write_declaration(path: Path, *, include_full_contract_shape: bool = True) -> None:
    contract = {
        "required_restart_trigger_outcome": "REMAIN_IN_GOVERNED_STOP_STATE",
        "required_controlled_dormancy_outcome": "CONTROLLED_DORMANCY_PROTOCOL_ACTIVE",
        "required_lane_reopen_authorized": False,
        "required_new_lane_or_packet_authorized_now": False,
        "required_direct_execution_authorized_now": False,
        "required_playbook_phrase": "is there a valid trigger family?",
        "required_restart_sequence_anchor": "Start at P75 restart trigger contract.",
        "forbid_lane_first_restart_sequencing": True,
        "single_layer_only": True,
        "single_outcome_only": True,
    }
    if not include_full_contract_shape:
        contract.pop("required_playbook_phrase")

    _write_json(
        path,
        {
            "required_inputs": {
                "science_restart_trigger_contract_report": "formal/output/reports/science_restart_trigger_contract_20260412_v0.json",
                "science_controlled_dormancy_protocol_report": "formal/output/reports/science_controlled_dormancy_protocol_20260412_v0.json",
                "science_dormancy_restart_playbook": "formal/docs/release/SCIENCE_DORMANCY_RESTART_PLAYBOOK_20260412_v0.md",
            },
            "dormancy_preservation_contract": contract,
            "dormancy_preservation_outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SCIENCE_DORMANCY_PRESERVATION_AUDIT_OUTCOME",
                "no_loop_rule": "ONE_SCIENCE_DORMANCY_PRESERVATION_AUDIT_LAYER_ONLY",
                "allowed_outcomes": [
                    "DORMANCY_PRESERVATION_AUDIT_PASS",
                    "DORMANCY_PRESERVATION_AUDIT_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_DORMANCY_PRESERVATION_REPAIR",
                ],
                "default_outcome": "DORMANCY_PRESERVATION_AUDIT_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    restart_outcome: str = "REMAIN_IN_GOVERNED_STOP_STATE",
    dormancy_outcome: str = "CONTROLLED_DORMANCY_PROTOCOL_ACTIVE",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "science_restart_trigger_contract_20260412_v0.json",
        {"summary": {"terminal_outcome": restart_outcome}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "science_controlled_dormancy_protocol_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": dormancy_outcome,
                "lane_specific_reopen_authorized": False,
                "new_lane_or_packet_authorized_now": False,
                "direct_execution_authorized_now": False,
            }
        },
    )
    _write_text(
        root / "formal" / "docs" / "release" / "SCIENCE_DORMANCY_RESTART_PLAYBOOK_20260412_v0.md",
        "Start at P75 restart trigger contract.\n"
        "is there a valid trigger family?\n"
        "Do not start restart by selecting a lane.\n",
    )


def test_reports_dormancy_preservation_audit_pass(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_DORMANCY_PRESERVATION_AUDIT_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "DORMANCY_PRESERVATION_AUDIT_PASS"


def test_reports_dormancy_preservation_audit_evidence_incomplete(
    tmp_path: Path, monkeypatch
) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_DORMANCY_PRESERVATION_AUDIT_20260412_v0.json"
    )
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, restart_outcome="OPEN_ONE_BOUNDED_PRE_SCREENING_RESTART_GATE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "DORMANCY_PRESERVATION_AUDIT_EVIDENCE_INCOMPLETE"


def test_reports_hold_pending_dormancy_preservation_repair(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = (
        tmp_path / "formal" / "docs" / "release" / "SCIENCE_DORMANCY_PRESERVATION_AUDIT_20260412_v0.json"
    )
    _write_declaration(declaration_path, include_full_contract_shape=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "HOLD_PENDING_DORMANCY_PRESERVATION_REPAIR"

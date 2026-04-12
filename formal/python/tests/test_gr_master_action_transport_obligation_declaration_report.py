from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import gr_master_action_transport_obligation_declaration_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(
    path: Path,
    *,
    scope_violation: bool = False,
    higher_policy: bool = False,
    justified: bool = True,
    declared: bool = True,
    obligation_type: str = "THEOREM_LINKED",
) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "gr_master_action_transport_attack_packet_report": "formal/output/reports/gr_master_action_transport_attack_packet_20260412_v0.json",
                "gr_master_action_transport_attack_packet_declaration": "formal/docs/release/GR_MASTER_ACTION_TRANSPORT_ATTACK_PACKET_20260412_v0.json",
                "gr_next_attack_class_selection_report": "formal/output/reports/gr_next_attack_class_selection_20260412_v0.json",
            },
            "obligation_policy": {
                "target_row": "ROW-PILLAR-GR-001",
                "missing_obligation_id": "GR_MASTER_ACTION_TO_REGIME_LIMIT_TRANSPORT_OBLIGATION_v0",
                "missing_obligation_statement": "Bounded master-action transport obligation for GR row closure.",
                "obligation_type": obligation_type,
                "scope_violation_detected": scope_violation,
                "requires_higher_level_policy": higher_policy,
                "obligation_justified": justified,
                "obligation_declared": declared,
            },
            "declaration_contract": {
                "allowed_outcomes": [
                    "GR_TRANSPORT_OBLIGATION_DECLARED",
                    "GR_TRANSPORT_OBLIGATION_REQUIRES_HIGHER_LEVEL_POLICY",
                    "GR_TRANSPORT_OBLIGATION_OUT_OF_SCOPE",
                    "GR_TRANSPORT_OBLIGATION_NOT_JUSTIFIED"
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_GR_TRANSPORT_OBLIGATION_DECLARATION_OUTCOME",
                "no_loop_rule": "ONE_GR_TRANSPORT_OBLIGATION_DECLARATION_ONLY",
                "default_outcome": "GR_TRANSPORT_OBLIGATION_NOT_JUSTIFIED"
            },
        },
    )


def _seed_inputs(
    root: Path,
    *,
    packet_outcome: str = "GR_MASTER_ACTION_TRANSPORT_REQUIRES_UNDECLARED_STRUCTURE",
    packet_target_row: str = "ROW-PILLAR-GR-001",
    selected_attack_class: str = "GR_MASTER_ACTION_TRANSPORT_ATTACK",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "gr_master_action_transport_attack_packet_20260412_v0.json",
        {"summary": {"terminal_outcome": packet_outcome, "target_row": packet_target_row}},
    )
    _write_json(
        root / "formal" / "docs" / "release" / "GR_MASTER_ACTION_TRANSPORT_ATTACK_PACKET_20260412_v0.json",
        {"attack_class": "GR_MASTER_ACTION_TRANSPORT_ATTACK"},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "gr_next_attack_class_selection_20260412_v0.json",
        {"summary": {"selected_attack_class": selected_attack_class}},
    )


def test_reports_obligation_declared(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "GR_MASTER_ACTION_TRANSPORT_OBLIGATION_DECLARATION_20260412_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "GR_TRANSPORT_OBLIGATION_DECLARED"


def test_reports_requires_higher_level_policy(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "GR_MASTER_ACTION_TRANSPORT_OBLIGATION_DECLARATION_20260412_v0.json"
    _write_declaration(declaration_path, higher_policy=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "GR_TRANSPORT_OBLIGATION_REQUIRES_HIGHER_LEVEL_POLICY"


def test_reports_out_of_scope(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "GR_MASTER_ACTION_TRANSPORT_OBLIGATION_DECLARATION_20260412_v0.json"
    _write_declaration(declaration_path, scope_violation=True)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "GR_TRANSPORT_OBLIGATION_OUT_OF_SCOPE"


def test_reports_not_justified(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "GR_MASTER_ACTION_TRANSPORT_OBLIGATION_DECLARATION_20260412_v0.json"
    _write_declaration(declaration_path, justified=False)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "GR_TRANSPORT_OBLIGATION_NOT_JUSTIFIED"

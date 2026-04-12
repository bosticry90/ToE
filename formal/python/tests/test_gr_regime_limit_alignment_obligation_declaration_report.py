from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import gr_regime_limit_alignment_obligation_declaration_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "target_row": "ROW-PILLAR-GR-001",
            "required_inputs": {
                "gr_regime_limit_alignment_attack_packet_report": "formal/output/reports/gr_regime_limit_alignment_attack_packet_20260412_v0.json",
                "gr_post_transport_retry_decision_report": "formal/output/reports/gr_post_transport_retry_decision_20260412_v0.json"
            },
            "obligation_policy": {
                "target_row": "ROW-PILLAR-GR-001",
                "missing_obligation_id": "GR_REGIME_LIMIT_TO_ALIGNMENT_BRIDGE_OBLIGATION_v0",
                "missing_obligation_statement": "GR row ROW-PILLAR-GR-001 requires explicit structural bridge obligation between regime-limit constraint system and alignment attack routing.",
                "obligation_type": "THEOREM_LINKED",
                "scope_violation_detected": False,
                "requires_higher_level_policy": False,
                "obligation_justified": True,
                "obligation_declared": True
            },
            "declaration_contract": {
                "allowed_outcomes": [
                    "GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_DECLARED",
                    "GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_REQUIRES_HIGHER_LEVEL_POLICY",
                    "GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_OUT_OF_SCOPE",
                    "GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_NOT_JUSTIFIED"
                ],
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_DECLARATION_OUTCOME",
                "no_loop_rule": "ONE_GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_DECLARATION_ONLY",
                "default_outcome": "GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_NOT_JUSTIFIED"
            }
        },
    )


def _seed_inputs(
    root: Path,
    *,
    packet_outcome: str = "GR_REGIME_LIMIT_ALIGNMENT_REQUIRES_UNDECLARED_STRUCTURE",
    decision_outcome: str = "ACTIVATE_GR_REGIME_LIMIT_ALIGNMENT_ATTACK",
) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "gr_regime_limit_alignment_attack_packet_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": packet_outcome,
                "target_row": "ROW-PILLAR-GR-001",
            }
        },
    )
    _write_json(
        root / "formal" / "output" / "reports" / "gr_post_transport_retry_decision_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": decision_outcome,
                "target_row": "ROW-PILLAR-GR-001",
            }
        },
    )


def test_reports_obligation_declared(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_DECLARATION_20260412_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_DECLARED"


def test_reports_out_of_scope_when_packet_target_mismatch(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_DECLARATION_20260412_v0.json"
    _write_declaration(declaration_path)
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "gr_regime_limit_alignment_attack_packet_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "GR_REGIME_LIMIT_ALIGNMENT_REQUIRES_UNDECLARED_STRUCTURE",
                "target_row": "ROW-PILLAR-QFT-001",
            }
        },
    )
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "gr_post_transport_retry_decision_20260412_v0.json",
        {
            "summary": {
                "terminal_outcome": "ACTIVATE_GR_REGIME_LIMIT_ALIGNMENT_ATTACK",
                "target_row": "ROW-PILLAR-GR-001",
            }
        },
    )

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_OUT_OF_SCOPE"


def test_reports_not_justified_when_decision_outcome_wrong(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_DECLARATION_20260412_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, decision_outcome="HOLD_GR_AND_REQUIRE_HIGHER_LEVEL_REVIEW")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["terminal_outcome"] == "GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_NOT_JUSTIFIED"


def test_reports_retry_justified_true_when_declared(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "GR_REGIME_LIMIT_ALIGNMENT_OBLIGATION_DECLARATION_20260412_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)
    assert report["summary"]["retry_justified"] is True

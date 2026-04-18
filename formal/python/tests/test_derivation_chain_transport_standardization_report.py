from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import derivation_chain_transport_standardization_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "foundational_derivation_chain_standard": "formal/docs/release/FOUNDATIONAL_DERIVATION_CHAIN_STANDARD_v0.md",
                "foundational_derivation_chain_execution_plan": "formal/docs/release/FOUNDATIONAL_DERIVATION_CHAIN_EXECUTION_PLAN_v0.md",
                "foundational_derivation_chain_matrix": "formal/docs/paper/FOUNDATIONAL_DERIVATION_CHAIN_MATRIX_v0.json",
                "master_action_packet01_transport_binding_recovery_report": "formal/output/reports/master_action_packet_01_transport_binding_recovery_20260418_v0.json"
            },
            "standardization_policy": {
                "required_phase4_terminal_outcome": "MASTER_ACTION_PACKET01_TRANSPORT_BINDING_RECOVERY_STATE_MATERIALIZED",
                "required_phase4_transport_read_token": "PACKET01_PRESERVED_BASELINE_PLUS_WITNESS_BINDING_PLUS_MINIMAL_UPSTREAM_UNIT_PLUS_EXPLICIT_BLOCKER",
                "required_next_action": "USE_CANONICAL_MASTER_ACTION_TRANSPORT_READ_FOR_PHASE5_DERIVATION_CHAIN_STANDARDIZATION",
                "required_matrix_version": 3,
                "required_admitted_pillar_count": 7,
                "required_phase_status": "COMPLETE_BOUNDED_v0",
                "required_m3_stage_status": "COMPLETE_BOUNDED_v0"
            },
            "outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_DERIVATION_CHAIN_TRANSPORT_STANDARDIZATION_OUTCOME",
                "no_loop_rule": "ONE_DERIVATION_CHAIN_TRANSPORT_STANDARDIZATION_LAYER_ONLY",
                "allowed_outcomes": [
                    "DERIVATION_CHAIN_TRANSPORT_STANDARDIZATION_MATERIALIZED",
                    "DERIVATION_CHAIN_TRANSPORT_STANDARDIZATION_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_DERIVATION_CHAIN_TRANSPORT_STANDARDIZATION_REPAIR"
                ],
                "default_outcome": "DERIVATION_CHAIN_TRANSPORT_STANDARDIZATION_EVIDENCE_INCOMPLETE"
            }
        }
    )


def _seed_inputs(root: Path, *, phase4_outcome: str = "MASTER_ACTION_PACKET01_TRANSPORT_BINDING_RECOVERY_STATE_MATERIALIZED") -> None:
    _write_text(root / "formal" / "docs" / "release" / "FOUNDATIONAL_DERIVATION_CHAIN_STANDARD_v0.md", "ACTION VARIATION BRIDGE OPERATOR TRANSPORT RESIDUAL_LAW REGIME_LIMIT")
    _write_text(root / "formal" / "docs" / "release" / "FOUNDATIONAL_DERIVATION_CHAIN_EXECUTION_PLAN_v0.md", "FOUNDATIONAL_DERIVATION_CHAIN_STANDARD_v0 FOUNDATIONAL_DERIVATION_CHAIN_MATRIX_v0")
    lanes = {}
    phase_rows = {}
    for pillar in ["QM", "GR", "STAT", "COSMO", "EM", "QFT", "SR"]:
        phase_rows[pillar] = {
            "m2": {"expected_status": "COMPLETE_BOUNDED_v0"},
            "m3": {"expected_status": "COMPLETE_BOUNDED_v0"},
            "m4": {"expected_status": "COMPLETE_BOUNDED_v0"},
        }
        lanes[f"{pillar}_M3"] = {suffix: "COMPLETE_BOUNDED_v0" for suffix in tool.CHAIN_SUFFIXES}
    _write_json(root / "formal" / "docs" / "paper" / "FOUNDATIONAL_DERIVATION_CHAIN_MATRIX_v0.json", {"matrix_version": 3, "phase_rows": phase_rows, "lanes": lanes})
    _write_json(root / "formal" / "output" / "reports" / "master_action_packet_01_transport_binding_recovery_20260418_v0.json", {"summary": {"terminal_outcome": phase4_outcome, "canonical_transport_read_token": "PACKET01_PRESERVED_BASELINE_PLUS_WITNESS_BINDING_PLUS_MINIMAL_UPSTREAM_UNIT_PLUS_EXPLICIT_BLOCKER", "target_row": "ROW-SEAM-QM-STAT-001", "target_seam": "SEAM-QM-STAT", "next_action": "USE_CANONICAL_MASTER_ACTION_TRANSPORT_READ_FOR_PHASE5_DERIVATION_CHAIN_STANDARDIZATION"}})


def test_reports_standardization_materialized(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "DERIVATION_CHAIN_TRANSPORT_STANDARDIZATION_20260418_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "DERIVATION_CHAIN_TRANSPORT_STANDARDIZATION_MATERIALIZED"
    assert report["summary"]["admitted_pillar_count"] == 7


def test_reports_evidence_incomplete_when_phase4_not_materialized(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "DERIVATION_CHAIN_TRANSPORT_STANDARDIZATION_20260418_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, phase4_outcome="MASTER_ACTION_PACKET01_TRANSPORT_BINDING_RECOVERY_EVIDENCE_INCOMPLETE")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "DERIVATION_CHAIN_TRANSPORT_STANDARDIZATION_EVIDENCE_INCOMPLETE"

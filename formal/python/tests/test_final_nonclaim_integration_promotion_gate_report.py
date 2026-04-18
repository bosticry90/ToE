from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import final_nonclaim_integration_promotion_gate_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "seam_executable_path_normalization_report": "formal/output/reports/seam_executable_path_normalization_20260418_v0.json",
                "master_action_packet01_transport_binding_recovery_report": "formal/output/reports/master_action_packet_01_transport_binding_recovery_20260418_v0.json",
                "derivation_chain_transport_standardization_report": "formal/output/reports/derivation_chain_transport_standardization_20260418_v0.json"
            },
            "gate_policy": {
                "required_phase3_terminal_outcome": "SEAM_EXECUTABLE_PATHS_NORMALIZED",
                "required_phase4_terminal_outcome": "MASTER_ACTION_PACKET01_TRANSPORT_BINDING_RECOVERY_STATE_MATERIALIZED",
                "required_phase5_terminal_outcome": "DERIVATION_CHAIN_TRANSPORT_STANDARDIZATION_MATERIALIZED",
                "required_single_executable_seam": "SEAM-COSMO-SR",
                "required_phase4_blocker": "NO_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE",
                "required_phase5_admitted_pillar_count": 7,
                "required_phase5_transport_read_token": "PACKET01_PRESERVED_BASELINE_PLUS_WITNESS_BINDING_PLUS_MINIMAL_UPSTREAM_UNIT_PLUS_EXPLICIT_BLOCKER"
            },
            "outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_FINAL_NONCLAIM_INTEGRATION_PROMOTION_GATE_OUTCOME",
                "no_loop_rule": "ONE_FINAL_NONCLAIM_INTEGRATION_PROMOTION_GATE_LAYER_ONLY",
                "allowed_outcomes": [
                    "FINAL_NONCLAIM_INTEGRATION_PROMOTION_GATE_SATISFIED",
                    "FINAL_NONCLAIM_INTEGRATION_PROMOTION_GATE_BLOCKED",
                    "HOLD_PENDING_FINAL_NONCLAIM_INTEGRATION_REPAIR"
                ],
                "default_outcome": "FINAL_NONCLAIM_INTEGRATION_PROMOTION_GATE_BLOCKED"
            }
        }
    )


def _seed_inputs(root: Path, *, phase5_ok: bool = True) -> None:
    _write_json(root / "formal" / "output" / "reports" / "seam_executable_path_normalization_20260418_v0.json", {"summary": {"terminal_outcome": "SEAM_EXECUTABLE_PATHS_NORMALIZED", "authorized_executable_seams": ["SEAM-COSMO-SR"]}})
    _write_json(root / "formal" / "output" / "reports" / "master_action_packet_01_transport_binding_recovery_20260418_v0.json", {"summary": {"terminal_outcome": "MASTER_ACTION_PACKET01_TRANSPORT_BINDING_RECOVERY_STATE_MATERIALIZED", "transport_binding_blocker": "NO_UNIFIED_THEOREM_TRANSPORT_RESIDUAL_PACKAGE"}})
    _write_json(root / "formal" / "output" / "reports" / "derivation_chain_transport_standardization_20260418_v0.json", {"summary": {"terminal_outcome": "DERIVATION_CHAIN_TRANSPORT_STANDARDIZATION_MATERIALIZED" if phase5_ok else "DERIVATION_CHAIN_TRANSPORT_STANDARDIZATION_EVIDENCE_INCOMPLETE", "admitted_pillar_count": 7, "canonical_transport_read_token": "PACKET01_PRESERVED_BASELINE_PLUS_WITNESS_BINDING_PLUS_MINIMAL_UPSTREAM_UNIT_PLUS_EXPLICIT_BLOCKER"}})


def test_reports_final_gate_satisfied(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "FINAL_NONCLAIM_INTEGRATION_PROMOTION_GATE_20260418_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "FINAL_NONCLAIM_INTEGRATION_PROMOTION_GATE_SATISFIED"


def test_reports_final_gate_blocked_when_phase5_missing(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "FINAL_NONCLAIM_INTEGRATION_PROMOTION_GATE_20260418_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, phase5_ok=False)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "FINAL_NONCLAIM_INTEGRATION_PROMOTION_GATE_BLOCKED"

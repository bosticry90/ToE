from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import seam_executable_path_normalization_report as tool


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _seed_inventory(path: Path) -> None:
    _write_text(
        path,
        "\n".join(
            [
                "# Inventory",
                "| seam_id | class | seam_class_token | witness_route_status | source_artifacts | promotion_candidate |",
                "| --- | --- | --- | --- | --- | --- |",
                "| `SEAM-EM-QFT` | `A` | `X` | `CLASS_A_PROMOTED_CYCLE03_v0` | `a` | `YES` |",
                "| `SEAM-GR-QM` | `A` | `X` | `CLASS_A_PROMOTED_CYCLE03_v0` | `a` | `NO` |",
                "| `SEAM-QFT-GR` | `B` | `X` | `HOLD_FOR_SCALAR_PUBLICATION_v0` | `a` | `NO` |",
                "| `SEAM-QM-STAT` | `B` | `X` | `COUNTERFACTUAL_BUNDLE_PINNED_v0` | `a` | `NO` |",
                "| `SEAM-STAT-QM` | `B` | `X` | `COUNTERFACTUAL_BUNDLE_PINNED_v0` | `a` | `NO` |",
                "| `SEAM-COSMO-SR` | `B` | `X` | `COUNTERFACTUAL_BUNDLE_PINNED_v0` | `a` | `NO` |",
                "| `SEAM-SR-COSMO` | `B` | `X` | `COUNTERFACTUAL_BUNDLE_PINNED_v0` | `a` | `NO` |",
                "",
                "| seam_id | governance_complete | physics_complete | status_read |",
                "| --- | --- | --- | --- |",
                "| `SEAM-EM-QFT` | `YES` | `NO` | `GOVERNANCE_COMPLETE_BUT_PHYSICS_INCOMPLETE` |",
                "| `SEAM-GR-QM` | `YES` | `YES` | `GOVERNANCE_COMPLETE_AND_PHYSICS_COMPLETE` |",
                "| `SEAM-QFT-GR` | `NO` | `NO` | `CLASS_B_HELD_FOR_SCALAR_PUBLICATION_NOT_GOVERNANCE_COMPLETE_NOT_PHYSICS_COMPLETE` |",
                "| `SEAM-QM-STAT` | `NO` | `NO` | `CLASS_B_TRACKED_NOT_GOVERNANCE_COMPLETE_NOT_PHYSICS_COMPLETE` |",
                "| `SEAM-STAT-QM` | `NO` | `NO` | `CLASS_B_TRACKED_NOT_GOVERNANCE_COMPLETE_NOT_PHYSICS_COMPLETE` |",
                "| `SEAM-COSMO-SR` | `NO` | `NO` | `CLASS_B_TRACKED_NOT_GOVERNANCE_COMPLETE_NOT_PHYSICS_COMPLETE` |",
                "| `SEAM-SR-COSMO` | `NO` | `NO` | `CLASS_B_TRACKED_NOT_GOVERNANCE_COMPLETE_NOT_PHYSICS_COMPLETE` |",
            ]
        ),
    )


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "seam_inventory": "formal/docs/paper/TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md",
                "seam_constraint_registry": "formal/docs/paper/TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md",
                "seam_resolution_sla_ledger_report": "formal/output/reports/seam_resolution_sla_ledger_20260416_v0.json",
                "qm_stat_seam_authorization_readiness_dossier_report": "formal/output/reports/qm_stat_seam_authorization_readiness_dossier_20260414_v0.json",
                "cosmo_sr_bounded_activation_authorization_report": "formal/output/reports/cosmo_sr_bounded_activation_authorization_20260418_v0.json",
            },
            "normalization_policy": {
                "single_authorized_path_class": "SINGLE_AUTHORIZED_NONLIVE_EXECUTABLE_PATH",
                "policy_blocked_path_class": "POLICY_BLOCKED_NONEXECUTABLE_PATH",
                "external_hold_path_class": "EXTERNAL_HOLD_NONEXECUTABLE_PATH",
                "mirror_only_path_class": "COUNTERFACTUAL_MIRROR_ONLY_NONEXECUTABLE_PATH",
                "closed_monitoring_path_class": "CLOSED_MONITORING_NONEXECUTABLE_PATH",
                "governance_complete_no_active_path_class": "GOVERNANCE_COMPLETE_NO_ACTIVE_EXECUTION_PATH",
                "active_execution_path_limit": 1,
                "single_active_path_rule": "AT_MOST_ONE_SEAM_MAY_BE_CLASSIFIED_AS_EXECUTABLE_UNDER_CURRENT_NONLIVE_CONTROL_SURFACES",
                "no_live_execution_rule": "NO_SEAM_PATH_CLASSIFICATION_MAY_INTRODUCE_EXECUTION_LIVE_TOKENS",
                "phase3_scope": "NORMALIZE_EXECUTABLE_PATH_READS_ONLY_WITHOUT_CHANGING_PHYSICS_COMPLETION_OR_CLASS_PROMOTION_SEMANTICS",
            },
            "expected_rows": {
                "SEAM-QFT-GR": {"required_path_class": "EXTERNAL_HOLD_NONEXECUTABLE_PATH", "required_next_action": "WAIT_FOR_SCALAR_PUBLICATION_RELEASE_ONLY"},
                "SEAM-QM-STAT": {"required_path_class": "POLICY_BLOCKED_NONEXECUTABLE_PATH", "required_next_action": "EXECUTE_ONE_BOUNDED_QM_STAT_CYCLE11_PRE_SCREENING_STEP_WITH_NO_DIRECT_EXECUTION_AUTHORIZATION"},
                "SEAM-COSMO-SR": {"required_path_class": "SINGLE_AUTHORIZED_NONLIVE_EXECUTABLE_PATH", "required_next_action": "EXECUTE_ONE_BOUNDED_COSMO_SR_CYCLE07_ACTIVATION_ONLY"},
                "SEAM-STAT-QM": {"required_path_class": "COUNTERFACTUAL_MIRROR_ONLY_NONEXECUTABLE_PATH", "required_next_action": "REMAIN_MIRROR_ONLY_UNTIL_A_CANONICAL_ROW_AND_AUTHORIZATION_SURFACE_EXIST"},
                "SEAM-SR-COSMO": {"required_path_class": "COUNTERFACTUAL_MIRROR_ONLY_NONEXECUTABLE_PATH", "required_next_action": "REMAIN_MIRROR_ONLY_UNTIL_A_CANONICAL_ROW_AND_AUTHORIZATION_SURFACE_EXIST"},
                "SEAM-GR-QM": {"required_path_class": "CLOSED_MONITORING_NONEXECUTABLE_PATH", "required_next_action": "REMAIN_IN_RECOMPUTE_MONITORING_ONLY"},
                "SEAM-EM-QFT": {"required_path_class": "GOVERNANCE_COMPLETE_NO_ACTIVE_EXECUTION_PATH", "required_next_action": "WAIT_FOR_EXPLICIT_NEW_EXECUTION_AUTHORIZATION_BEFORE_ANY_EM_QFT_REOPEN"}
            },
            "outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_SEAM_EXECUTABLE_PATH_NORMALIZATION_OUTCOME",
                "no_loop_rule": "ONE_SEAM_EXECUTABLE_PATH_NORMALIZATION_LAYER_ONLY",
                "allowed_outcomes": [
                    "SEAM_EXECUTABLE_PATHS_NORMALIZED",
                    "SEAM_EXECUTABLE_PATH_NORMALIZATION_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_SEAM_EXECUTABLE_PATH_NORMALIZATION_REPAIR"
                ],
                "default_outcome": "SEAM_EXECUTABLE_PATH_NORMALIZATION_EVIDENCE_INCOMPLETE"
            }
        }
    )


def _seed_inputs(root: Path, *, cosmo_outcome: str = "COSMO_SR_CYCLE07_SINGLE_LANE_ACTIVATION_AUTHORIZED_NONLIVE_v0") -> None:
    _seed_inventory(root / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md")
    _write_text(root / "formal" / "docs" / "paper" / "TOE_MASTER_ACTION_SEAM_CONSTRAINT_REGISTRY_v0.md", "registry")
    _write_json(
        root / "formal" / "output" / "reports" / "seam_resolution_sla_ledger_20260416_v0.json",
        {"entries": [
            {"row_id": "ROW-SEAM-QFT-GR-001", "decision_state": "HOLD_RETAINED_EXTERNAL_HOLD_RELEASE_REQUIRED"},
            {"row_id": "ROW-SEAM-QM-STAT-001", "decision_state": "ACTIVE_TRACK_PENDING_BRANCH_EXCEPTION_DECISION"},
            {"row_id": "ROW-SEAM-COSMO-SR-001", "decision_state": "ACTIVE_TRACK_PENDING_BRANCH_EXCEPTION_DECISION"},
            {"row_id": "ROW-SEAM-GR-QM-001", "decision_state": "CLOSED_RECOMPUTE_MONITORING_REQUIRED"},
        ]}
    )
    _write_json(
        root / "formal" / "output" / "reports" / "qm_stat_seam_authorization_readiness_dossier_20260414_v0.json",
        {"summary": {"terminal_outcome": "QM_STAT_SEAM_AUTHORIZATION_DOSSIER_READY_FOR_BOUNDED_PRE_SCREENING", "next_action": "EXECUTE_ONE_BOUNDED_QM_STAT_CYCLE11_PRE_SCREENING_STEP_WITH_NO_DIRECT_EXECUTION_AUTHORIZATION"}}
    )
    _write_json(
        root / "formal" / "output" / "reports" / "cosmo_sr_bounded_activation_authorization_20260418_v0.json",
        {"summary": {"terminal_outcome": cosmo_outcome, "next_action": "EXECUTE_ONE_BOUNDED_COSMO_SR_CYCLE07_ACTIVATION_ONLY"}}
    )


def test_reports_seam_executable_paths_normalized(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "SEAM_EXECUTABLE_PATH_NORMALIZATION_20260418_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "SEAM_EXECUTABLE_PATHS_NORMALIZED"
    assert report["summary"]["authorized_executable_seams"] == ["SEAM-COSMO-SR"]


def test_reports_seam_executable_path_evidence_incomplete_when_no_authorized_path(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "SEAM_EXECUTABLE_PATH_NORMALIZATION_20260418_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path, cosmo_outcome="COSMO_SR_BOUNDED_ACTIVATION_AUTHORIZATION_BLOCKED")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "SEAM_EXECUTABLE_PATH_NORMALIZATION_EVIDENCE_INCOMPLETE"

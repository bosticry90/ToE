from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import post_plan_theorem_gap_successor_family_authorization_review_report as tool


REPO_ROOT = find_repo_root(Path(__file__))


def _read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "fresh_movement_qualification_report": "formal/output/reports/qualification.json",
                "qm_dossier_report": "formal/output/reports/qm.json",
                "stat_dossier_report": "formal/output/reports/stat.json",
                "cosmo_dossier_report": "formal/output/reports/cosmo.json",
                "gr_dossier_report": "formal/output/reports/gr.json",
                "qft_dossier_report": "formal/output/reports/qft.json",
                "em_dossier_report": "formal/output/reports/em.json",
                "sr_dossier_report": "formal/output/reports/sr.json",
            },
            "authorization_policy": {
                "default_selected_row": "ROW-PILLAR-STAT-001",
                "alternate_selected_row": "ROW-PILLAR-COSMO-001",
            },
            "outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_POST_PLAN_THEOREM_GAP_SUCCESSOR_FAMILY_AUTHORIZATION_REVIEW_OUTCOME",
                "no_loop_rule": "ONE_POST_PLAN_THEOREM_GAP_SUCCESSOR_FAMILY_AUTHORIZATION_REVIEW_LAYER_ONLY",
                "allowed_outcomes": [
                    "POST_PLAN_THEOREM_GAP_SUCCESSOR_FAMILY_AUTHORIZATION_REVIEW_ONE_ROW_AUTHORIZED",
                    "POST_PLAN_THEOREM_GAP_SUCCESSOR_FAMILY_AUTHORIZATION_REVIEW_NO_ROW_AUTHORIZED",
                    "POST_PLAN_THEOREM_GAP_SUCCESSOR_FAMILY_AUTHORIZATION_REVIEW_CONTRACT_VIOLATION",
                    "POST_PLAN_THEOREM_GAP_SUCCESSOR_FAMILY_AUTHORIZATION_REVIEW_EVIDENCE_INCOMPLETE",
                ],
                "default_outcome": "POST_PLAN_THEOREM_GAP_SUCCESSOR_FAMILY_AUTHORIZATION_REVIEW_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _write_dossier(path: Path, *, row_id: str, count: int, fresh: bool, admissible: bool, non_qm_ok: bool = True) -> None:
    _write_json(
        path,
        {
            "summary": {
                "row_id": row_id,
                "historical_no_change_count": count,
                "fresh_movement_machine_pinned": fresh,
                "admissible_if_authorized": admissible,
                "non_qm_movement_required_satisfied": non_qm_ok,
                "reserve_until_first_selected_family_resolution": False,
                "bounded_execution_surface_declaration": f"formal/docs/release/{row_id}.json",
                "bounded_execution_surface_gate": f"formal/python/tests/{row_id}.py",
            }
        },
    )


def test_authorization_selects_stat_when_qualification_points_to_stat(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "AUTH.json"
    _write_declaration(declaration_path)
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qualification.json",
        {"summary": {"selected_row": "ROW-PILLAR-STAT-001", "default_selected_row": "ROW-PILLAR-STAT-001", "alternate_selected_row": "ROW-PILLAR-COSMO-001", "cosmo_override_condition_met": False}},
    )
    _write_dossier(tmp_path / "formal" / "output" / "reports" / "stat.json", row_id="ROW-PILLAR-STAT-001", count=1, fresh=True, admissible=True)
    _write_dossier(tmp_path / "formal" / "output" / "reports" / "cosmo.json", row_id="ROW-PILLAR-COSMO-001", count=2, fresh=False, admissible=True)
    for name, row in [("qm", "ROW-PILLAR-QM-001"), ("gr", "ROW-PILLAR-GR-001"), ("qft", "ROW-PILLAR-QFT-001"), ("em", "ROW-PILLAR-EM-001"), ("sr", "ROW-PILLAR-SR-001")]:
        _write_dossier(tmp_path / "formal" / "output" / "reports" / f"{name}.json", row_id=row, count=3, fresh=False, admissible=False)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_THEOREM_GAP_SUCCESSOR_FAMILY_AUTHORIZATION_REVIEW_ONE_ROW_AUTHORIZED"
    assert report["summary"]["selected_row"] == "ROW-PILLAR-STAT-001"


def test_authorization_fail_closes_qm_without_non_qm_movement(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "AUTH.json"
    _write_declaration(declaration_path)
    _write_json(
        tmp_path / "formal" / "output" / "reports" / "qualification.json",
        {"summary": {"selected_row": "ROW-PILLAR-QM-001", "default_selected_row": "ROW-PILLAR-STAT-001", "alternate_selected_row": "ROW-PILLAR-COSMO-001", "cosmo_override_condition_met": False}},
    )
    _write_dossier(tmp_path / "formal" / "output" / "reports" / "qm.json", row_id="ROW-PILLAR-QM-001", count=4, fresh=True, admissible=True, non_qm_ok=False)
    _write_dossier(tmp_path / "formal" / "output" / "reports" / "stat.json", row_id="ROW-PILLAR-STAT-001", count=1, fresh=False, admissible=True)
    _write_dossier(tmp_path / "formal" / "output" / "reports" / "cosmo.json", row_id="ROW-PILLAR-COSMO-001", count=2, fresh=False, admissible=True)
    for name, row in [("gr", "ROW-PILLAR-GR-001"), ("qft", "ROW-PILLAR-QFT-001"), ("em", "ROW-PILLAR-EM-001"), ("sr", "ROW-PILLAR-SR-001")]:
        _write_dossier(tmp_path / "formal" / "output" / "reports" / f"{name}.json", row_id=row, count=3, fresh=False, admissible=False)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_THEOREM_GAP_SUCCESSOR_FAMILY_AUTHORIZATION_REVIEW_CONTRACT_VIOLATION"


def test_live_authorization_review_records_no_row_authorized() -> None:
    report = _read_json(
        REPO_ROOT / "formal" / "output" / "reports" / "post_plan_theorem_gap_successor_family_authorization_review_20260419_v0.json"
    )
    assert report["summary"]["terminal_outcome"] == "POST_PLAN_THEOREM_GAP_SUCCESSOR_FAMILY_AUTHORIZATION_REVIEW_NO_ROW_AUTHORIZED"
    assert report["summary"]["selected_row"] == "NONE"

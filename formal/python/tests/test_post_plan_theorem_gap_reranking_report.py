from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import post_plan_theorem_gap_reranking_report as tool


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
                "successor_family_authorization_review_report": "formal/output/reports/auth.json",
                "blocker_burn_dashboard_report": "formal/output/reports/dashboard.json",
                "stat_dossier_report": "formal/output/reports/stat.json",
                "cosmo_dossier_report": "formal/output/reports/cosmo.json",
                "gr_dossier_report": "formal/output/reports/gr.json",
                "qft_dossier_report": "formal/output/reports/qft.json",
                "em_dossier_report": "formal/output/reports/em.json",
                "sr_dossier_report": "formal/output/reports/sr.json",
                "qm_dossier_report": "formal/output/reports/qm.json",
                "stat_reactivation_tranche_report": "formal/output/reports/stat_reactivation.json",
                "cosmo_reactivation_tranche_report": "formal/output/reports/cosmo_reactivation.json",
                "gr_reactivation_tranche_report": "formal/output/reports/gr_reactivation.json",
            },
            "reranking_policy": {
                "default_order": [
                    "ROW-PILLAR-STAT-001",
                    "ROW-PILLAR-COSMO-001",
                    "ROW-PILLAR-GR-001",
                    "ROW-PILLAR-QFT-001",
                    "ROW-PILLAR-EM-001",
                    "ROW-PILLAR-SR-001",
                    "ROW-PILLAR-QM-001",
                ],
                "qm_last_row": "ROW-PILLAR-QM-001",
            },
            "outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_POST_PLAN_THEOREM_GAP_RERANKING_OUTCOME",
                "no_loop_rule": "ONE_POST_PLAN_THEOREM_GAP_RERANKING_LAYER_ONLY",
                "allowed_outcomes": [
                    "POST_PLAN_THEOREM_GAP_RERANKING_RETAINED",
                    "POST_PLAN_THEOREM_GAP_RERANKING_UPDATED",
                    "POST_PLAN_THEOREM_GAP_RERANKING_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_POST_PLAN_THEOREM_GAP_RERANKING_REPAIR",
                ],
                "default_outcome": "POST_PLAN_THEOREM_GAP_RERANKING_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _write_dossier(path: Path, row_id: str) -> None:
    _write_json(path, {"summary": {"row_id": row_id, "policy_class": "X", "admissible_if_authorized": True}})


def _seed_common_inputs(root: Path, *, theorem_gap_delta: int = 0, stat_outcome: str = "POST_PLAN_STAT_THEOREM_GAP_REACTIVATION_TRANCHE_EVIDENCE_INCOMPLETE") -> None:
    _write_json(root / "formal" / "output" / "reports" / "qualification.json", {"summary": {"selected_row": "NONE"}})
    _write_json(root / "formal" / "output" / "reports" / "auth.json", {"summary": {"terminal_outcome": "POST_PLAN_THEOREM_GAP_SUCCESSOR_FAMILY_AUTHORIZATION_REVIEW_NO_ROW_AUTHORIZED", "selected_row": "NONE"}})
    _write_json(root / "formal" / "output" / "reports" / "dashboard.json", {"blocker_scoreboard": {"delta_by_class": {"THEOREM_GAP": theorem_gap_delta}}})
    for key, row in [
        ("stat", "ROW-PILLAR-STAT-001"),
        ("cosmo", "ROW-PILLAR-COSMO-001"),
        ("gr", "ROW-PILLAR-GR-001"),
        ("qft", "ROW-PILLAR-QFT-001"),
        ("em", "ROW-PILLAR-EM-001"),
        ("sr", "ROW-PILLAR-SR-001"),
        ("qm", "ROW-PILLAR-QM-001"),
    ]:
        _write_dossier(root / "formal" / "output" / "reports" / f"{key}.json", row)
    _write_json(root / "formal" / "output" / "reports" / "stat_reactivation.json", {"summary": {"terminal_outcome": stat_outcome, "target_row_id": "ROW-PILLAR-STAT-001"}})
    _write_json(root / "formal" / "output" / "reports" / "cosmo_reactivation.json", {"summary": {"terminal_outcome": "POST_PLAN_COSMO_THEOREM_GAP_REACTIVATION_TRANCHE_EVIDENCE_INCOMPLETE", "target_row_id": "ROW-PILLAR-COSMO-001"}})
    _write_json(root / "formal" / "output" / "reports" / "gr_reactivation.json", {"summary": {"terminal_outcome": "POST_PLAN_GR_DORMANT_NEW_STRUCTURE_REACTIVATION_TRANCHE_EVIDENCE_INCOMPLETE", "target_row_id": "ROW-PILLAR-GR-001"}})


def test_reranking_is_retained_without_blocker_delta_or_explicit_exhaustion(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "RERANK.json"
    _write_declaration(declaration_path)
    _seed_common_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_THEOREM_GAP_RERANKING_RETAINED"
    assert report["summary"]["ranking"][0] == "ROW-PILLAR-STAT-001"


def test_reranking_updates_after_explicit_exhaustion(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "RERANK.json"
    _write_declaration(declaration_path)
    _seed_common_inputs(tmp_path, stat_outcome="POST_PLAN_STAT_THEOREM_GAP_REACTIVATION_TRANCHE_EXPLICITLY_EXHAUSTED")

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "POST_PLAN_THEOREM_GAP_RERANKING_UPDATED"
    assert report["summary"]["ranking"][0] == "ROW-PILLAR-COSMO-001"


def test_live_reranking_retains_hold_order() -> None:
    report = _read_json(REPO_ROOT / "formal" / "output" / "reports" / "post_plan_theorem_gap_reranking_20260419_v0.json")
    assert report["summary"]["terminal_outcome"] == "POST_PLAN_THEOREM_GAP_RERANKING_RETAINED"
    assert report["summary"]["ranking"][0] == "ROW-PILLAR-STAT-001"
    assert report["summary"]["ranking"][-1] == "ROW-PILLAR-QM-001"

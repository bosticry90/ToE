from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import post_plan_theorem_gap_row_reopen_dossier_report as tool


REPO_ROOT = find_repo_root(Path(__file__))


def _read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _write_declaration(path: Path, *, row_id: str, policy_class: str, reserve: bool = False, requires_non_qm: bool = False) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "fresh_movement_qualification_report": "formal/output/reports/post_plan_theorem_gap_fresh_movement_qualification_20260419_v0.json",
                "post_plan_target_map_report": "formal/output/reports/post_plan_physics_advancement_target_map_20260418_v0.json",
                "completion_matrix": "formal/docs/release/TOE_GLOBAL_COMPLETION_MATRIX_v0.md",
                "latest_row_report": "formal/output/reports/latest_row.json",
            },
            "row_policy": {
                "row_id": row_id,
                "required_route_class": "THEOREM_GAP_PROGRAM",
                "default_rank": 1,
                "policy_class": policy_class,
                "historical_no_change_count": 1,
                "exhausted_family_history": ["OLD_NONPROMOTED"],
                "fresh_movement_hypothesis": "H",
                "measurable_blocker_delta_criterion": "C",
                "bounded_execution_surface_declaration": "formal/docs/release/ROW_REACTIVATION.json",
                "bounded_execution_surface_gate": "formal/python/tests/test_row_reactivation.py",
                "explicit_exhaustion_fallback": "F",
                "requires_non_qm_movement": requires_non_qm,
                "seam_linked_override_only": False,
                "dormant_package_only": False,
                "reserve_until_first_selected_family_resolution": reserve,
            },
            "outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_POST_PLAN_THEOREM_GAP_ROW_REOPEN_DOSSIER_OUTCOME",
                "no_loop_rule": "ONE_ROW_DOSSIER_LAYER_ONLY",
                "allowed_outcomes": [
                    "POST_PLAN_THEOREM_GAP_ROW_REOPEN_DOSSIER_MATERIALIZED",
                    "POST_PLAN_THEOREM_GAP_ROW_REOPEN_DOSSIER_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_POST_PLAN_THEOREM_GAP_ROW_REOPEN_DOSSIER_REPAIR",
                ],
                "default_outcome": "POST_PLAN_THEOREM_GAP_ROW_REOPEN_DOSSIER_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_common_inputs(root: Path, *, selected_row: str = "NONE", fresh_non_qm: bool = False) -> None:
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_theorem_gap_fresh_movement_qualification_20260419_v0.json",
        {"summary": {"default_selected_row": "ROW-PILLAR-STAT-001", "selected_row": selected_row, "fresh_non_qm_movement_recorded": fresh_non_qm}},
    )
    _write_json(
        root / "formal" / "output" / "reports" / "post_plan_physics_advancement_target_map_20260418_v0.json",
        {"routed_rows": [{"row_id": "ROW-PILLAR-QM-001", "route_class": "THEOREM_GAP_PROGRAM"}, {"row_id": "ROW-PILLAR-QFT-001", "route_class": "THEOREM_GAP_PROGRAM"}]},
    )
    _write_text(
        root / "formal" / "docs" / "release" / "TOE_GLOBAL_COMPLETION_MATRIX_v0.md",
        "\n".join(
            [
                "# Matrix",
                "| row_id | domain | lane | current_status | blocker_class | primary_target | primary_artifact | primary_gate | governance_checkpoint_status | physics_checkpoint_status | gate_runtime_status |",
                "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |",
                "| ROW-PILLAR-QM-001 | pillar | QM | THEOREM_GAP_CLOSURE_INCREMENT_EXECUTION_CHECKPOINT_PINNED | THEOREM_GAP | qm_doc | qm_artifact | qm_gate | N/A | THEOREM_GAP_OPEN | PINNED |",
                "| ROW-PILLAR-QFT-001 | pillar | QFT | THEOREM_GAP_CLOSURE_INCREMENT_EXECUTION_CHECKPOINT_PINNED | THEOREM_GAP | qft_doc | qft_artifact | qft_gate | N/A | THEOREM_GAP_OPEN | PINNED |",
            ]
        ),
    )
    _write_json(root / "formal" / "output" / "reports" / "latest_row.json", {"summary": {"terminal_outcome": "OLD_NONPROMOTED"}})


def test_qm_dossier_requires_non_qm_movement_before_becoming_admissible(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "DOSSIER_QM.json"
    _write_declaration(declaration_path, row_id="ROW-PILLAR-QM-001", policy_class="EXCLUDED_PENDING_NON_QM_MOVEMENT", requires_non_qm=True)
    _seed_common_inputs(tmp_path, selected_row="NONE", fresh_non_qm=False)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["requires_non_qm_movement"] is True
    assert report["summary"]["admissible_if_authorized"] is False


def test_qft_dossier_stays_closed_as_reserve_until_first_selected_family_resolves(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "DOSSIER_QFT.json"
    _write_declaration(declaration_path, row_id="ROW-PILLAR-QFT-001", policy_class="POST_CASCADE_RESERVE_CANDIDATE", reserve=True)
    _seed_common_inputs(tmp_path, selected_row="NONE", fresh_non_qm=True)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["reserve_until_first_selected_family_resolution"] is True
    assert report["summary"]["admissible_if_authorized"] is False


def test_live_dossier_reports_exist_for_all_seven_rows() -> None:
    expected = {
        "qm": "ROW-PILLAR-QM-001",
        "stat": "ROW-PILLAR-STAT-001",
        "cosmo": "ROW-PILLAR-COSMO-001",
        "gr": "ROW-PILLAR-GR-001",
        "qft": "ROW-PILLAR-QFT-001",
        "em": "ROW-PILLAR-EM-001",
        "sr": "ROW-PILLAR-SR-001",
    }
    for key, row_id in expected.items():
        report = _read_json(
            REPO_ROOT / "formal" / "output" / "reports" / f"post_plan_theorem_gap_row_reopen_dossier_{key}_20260419_v0.json"
        )
        assert report["summary"]["row_id"] == row_id
        assert report["summary"]["terminal_outcome"] == "POST_PLAN_THEOREM_GAP_ROW_REOPEN_DOSSIER_MATERIALIZED"

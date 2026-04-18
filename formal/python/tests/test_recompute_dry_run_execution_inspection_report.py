from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import recompute_dry_run_execution_inspection_report as tool


REPO_ROOT = find_repo_root(Path(__file__))
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "POST_PLAN_OBJECTIVE_QUALITY_PHYSICS_COMPLETION_PROGRAM_20260418_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _write_surface(path: Path, *, trigger_status: str, include_computed: bool) -> None:
    payload = {
        "schema_id": "SURFACE",
        "triggers": [{"trigger_id": path.stem.upper(), "status": trigger_status}],
    }
    if include_computed:
        payload["computed_state"] = {"state_change_from_baseline": 0.1}
        payload["execution_summary"] = {"classification": "RECOMPUTE_COMPLETED_WITH_OUTPUTS"}
    _write_json(path, payload)


def _write_declaration(path: Path) -> None:
    _write_json(
        path,
        {
            "required_inputs": {
                "recompute_live_writeback_contract_report": "formal/output/reports/recompute_live_writeback_contract_20260418_v0.json",
                "recompute_execute_all_tool": "formal/python/tools/recompute_execute_all.py",
                "dry_run_bundle_report": "formal/output/recompute_dry_run/latest/formal/output/reports/recompute_execution_bundle_20260418_v0.json",
                "dry_run_baseline_report": "formal/output/recompute_dry_run/latest/formal/output/reports/recompute_baseline_snapshot_20260418_v0.json",
                "state_mirror": "State_of_the_Theory.md",
                "roadmap_mirror": "formal/docs/paper/PHYSICS_ROADMAP_v0.md",
                "inventory_mirror": "formal/docs/paper/TOE_MATH_PHYSICS_INVENTORY_v0.md",
            },
            "phase_plan": [{"phase_id": phase_id, "phase_name": f"PHASE_{phase_id}", "requirement": "req"} for phase_id in range(9)],
            "execution_policy": {
                "required_contract_outcome": "RECOMPUTE_LIVE_WRITEBACK_CONTRACT_DRY_RUN_READY_LIVE_LOCKED",
                "required_bundle_execution_mode": "dry-run",
                "required_bundle_surfaces_completed": 3,
                "required_live_writeback_performed": False,
                "required_bundle_next_action": "RERUN_RECOMPUTE_OBSERVATION_REPORT",
                "required_canonical_trigger_status": "PENDING_RECOMPUTE",
                "required_dry_run_trigger_status": "COMPLETED",
                "required_next_action": "DEFINE_CANONICAL_LIVE_WRITEBACK_BASELINE_OR_APPROVAL_CONDITIONS",
            },
            "outcome_contract": {
                "single_terminal_outcome_rule": "EXACTLY_ONE_ALLOWED_RECOMPUTE_DRY_RUN_EXECUTION_INSPECTION_OUTCOME",
                "no_loop_rule": "ONE_RECOMPUTE_DRY_RUN_EXECUTION_INSPECTION_ONLY",
                "allowed_outcomes": [
                    "RECOMPUTE_DRY_RUN_EXECUTION_INSPECTION_MATERIALIZED_CANONICAL_PENDING",
                    "RECOMPUTE_DRY_RUN_EXECUTION_INSPECTION_BLOCKED",
                    "RECOMPUTE_DRY_RUN_EXECUTION_INSPECTION_EVIDENCE_INCOMPLETE",
                    "HOLD_PENDING_RECOMPUTE_DRY_RUN_EXECUTION_INSPECTION_REPAIR",
                ],
                "default_outcome": "RECOMPUTE_DRY_RUN_EXECUTION_INSPECTION_EVIDENCE_INCOMPLETE",
            },
        },
    )


def _seed_inputs(root: Path) -> None:
    _write_json(root / "formal" / "output" / "reports" / "recompute_live_writeback_contract_20260418_v0.json", {"summary": {"terminal_outcome": "RECOMPUTE_LIVE_WRITEBACK_CONTRACT_DRY_RUN_READY_LIVE_LOCKED"}, "objective_quality": {"inputs": {"monitoring_outcome": "POST_PLAN_RECOMPUTE_MONITORING_PATH_PENDING_COMPLETION"}}})
    _write_text(root / "formal" / "python" / "tools" / "recompute_execute_all.py", "placeholder\n")
    _write_json(root / "formal" / "output" / "recompute_dry_run" / "latest" / "formal" / "output" / "reports" / "recompute_execution_bundle_20260418_v0.json", {"summary": {"execution_mode": "dry-run", "surfaces_completed": 3, "live_writeback_performed": False, "next_action": "RERUN_RECOMPUTE_OBSERVATION_REPORT"}, "dry_run_workspace": {"workspace_root": "formal/output/recompute_dry_run/latest"}})
    _write_json(root / "formal" / "output" / "recompute_dry_run" / "latest" / "formal" / "output" / "reports" / "recompute_baseline_snapshot_20260418_v0.json", {"summary": {"baseline_surfaces": 3}})

    for rel_path in (
        "formal/output/recompute/qm_seam_coherence_under_revised_blocker.json",
        "formal/output/recompute/ledger_artifact_transport_under_revised_blocker.json",
        "formal/output/recompute/blocker_authority_transport_surface.json",
    ):
        _write_surface(root / rel_path, trigger_status="PENDING_RECOMPUTE", include_computed=False)
        _write_surface(root / "formal" / "output" / "recompute_dry_run" / "latest" / rel_path, trigger_status="COMPLETED", include_computed=True)

    mirror_refs = "\n".join(
        [
            "formal/docs/release/RECOMPUTE_DRY_RUN_EXECUTION_INSPECTION_20260418_v0.json",
            "formal/output/reports/recompute_dry_run_execution_inspection_20260418_v0.json",
            "formal/python/tools/recompute_dry_run_execution_inspection_report.py",
            "formal/python/tests/test_recompute_dry_run_execution_inspection_report.py",
        ]
    )
    _write_text(root / "State_of_the_Theory.md", mirror_refs)
    _write_text(root / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md", mirror_refs)
    _write_text(root / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md", mirror_refs)


def test_dry_run_execution_inspection_materializes_canonical_pending(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    monkeypatch.setattr(tool.recompute_execute_all, "DEFAULT_DRY_RUN_ROOT", tmp_path / "formal" / "output" / "recompute_dry_run" / "latest")
    monkeypatch.setattr(tool.helpers, "REPO_ROOT", tmp_path)
    declaration_path = tmp_path / "formal" / "docs" / "release" / "RECOMPUTE_DRY_RUN_EXECUTION_INSPECTION_20260418_v0.json"
    _write_declaration(declaration_path)
    _seed_inputs(tmp_path)

    report = tool.build_report(declaration_path=declaration_path, captured_at_utc=None)

    assert report["summary"]["terminal_outcome"] == "RECOMPUTE_DRY_RUN_EXECUTION_INSPECTION_MATERIALIZED_CANONICAL_PENDING"
    assert report["summary"]["dry_run_completed_surface_count"] == 3
    assert report["summary"]["canonical_pending_surface_count"] == 3


def test_live_dry_run_inspection_registered_in_mirrors() -> None:
    program_text = _read(PROGRAM_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    required_refs = [
        "formal/docs/release/RECOMPUTE_DRY_RUN_EXECUTION_INSPECTION_20260418_v0.json",
        "formal/output/reports/recompute_dry_run_execution_inspection_20260418_v0.json",
        "formal/python/tools/recompute_dry_run_execution_inspection_report.py",
        "formal/python/tests/test_recompute_dry_run_execution_inspection_report.py",
    ]

    for ref in required_refs:
        assert ref in program_text
        assert ref in state_text or ref in roadmap_text or ref in inventory_text

    report = _read_json(REPO_ROOT / "formal" / "output" / "reports" / "recompute_dry_run_execution_inspection_20260418_v0.json")
    assert report["summary"]["terminal_outcome"] == "RECOMPUTE_DRY_RUN_EXECUTION_INSPECTION_MATERIALIZED_CANONICAL_PENDING"
    assert report["summary"]["next_action"] == "DEFINE_CANONICAL_LIVE_WRITEBACK_BASELINE_OR_APPROVAL_CONDITIONS"
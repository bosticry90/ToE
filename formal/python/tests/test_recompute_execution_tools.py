from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import blocker_authority_transport_recompute_execute as authority_tool
from formal.python.tools import ledger_artifact_transport_recompute_execute as ledger_tool
from formal.python.tools import qm_seam_coherence_recompute_execute as qm_tool
from formal.python.tools import recompute_baseline_snapshot
from formal.python.tools import recompute_execute_all as orchestrator
from formal.python.tools import recompute_surface_helpers as helpers


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _seed_shared_inputs(root: Path) -> None:
    _write_json(root / "formal" / "output" / "reports" / "authority_promotion_registration_20260411_v0.json", {"summary": {"registration_completed": True}})
    _write_json(root / "formal" / "output" / "reports" / "post_plan_bounded_coupling_refinement_packet_chain_20260418_v0.json", {"summary": {"terminal_outcome": "POST_PLAN_BOUNDED_COUPLING_REFINEMENT_PACKET_CHAIN_PROMOTION_REGISTERED"}})
    for file_name, surface_name in (
        ("qm_seam_coherence_under_revised_blocker.json", "qm_seam_coherence_under_revised_blocker"),
        ("ledger_artifact_transport_under_revised_blocker.json", "ledger_artifact_transport_under_revised_blocker"),
        ("blocker_authority_transport_surface.json", "blocker_authority_transport_surface"),
    ):
        _write_json(
            root / "formal" / "output" / "recompute" / file_name,
            {
                "schema_id": surface_name.upper(),
                "triggers": [
                    {
                        "trigger_id": f"TRIGGER_{surface_name}_001",
                        "surface_name": surface_name,
                        "status": "PENDING_RECOMPUTE",
                        "revised_blocker_definition": "REVISED_BLOCKER_DEFINITION_20260411_v0",
                    }
                ],
            },
        )


def _patch_root(monkeypatch, tmp_path: Path) -> Path:
    monkeypatch.setattr(helpers, "REPO_ROOT", tmp_path)
    monkeypatch.setattr(helpers, "AUTHORITY_PROMOTION_REPORT_PATH", tmp_path / "formal" / "output" / "reports" / "authority_promotion_registration_20260411_v0.json")
    monkeypatch.setattr(helpers, "PACKET_CHAIN_REPORT_PATH", tmp_path / "formal" / "output" / "reports" / "post_plan_bounded_coupling_refinement_packet_chain_20260418_v0.json")
    monkeypatch.setattr(helpers, "BASELINE_REPORT_PATH", tmp_path / "formal" / "output" / "reports" / "recompute_baseline_snapshot_20260418_v0.json")
    monkeypatch.setattr(recompute_baseline_snapshot, "REPO_ROOT", tmp_path)
    monkeypatch.setattr(qm_tool, "REPO_ROOT", tmp_path)
    monkeypatch.setattr(ledger_tool, "REPO_ROOT", tmp_path)
    monkeypatch.setattr(authority_tool, "REPO_ROOT", tmp_path)
    monkeypatch.setattr(orchestrator, "REPO_ROOT", tmp_path)
    return tmp_path / "formal" / "output" / "reports" / "recompute_baseline_snapshot_20260418_v0.json"


def test_individual_recompute_tools_materialize_outputs(tmp_path: Path, monkeypatch) -> None:
    baseline_path = _patch_root(monkeypatch, tmp_path)
    _seed_shared_inputs(tmp_path)
    baseline_payload = recompute_baseline_snapshot.build_report(captured_at_utc="2026-04-18T20:10:00Z")
    helpers.write_json(baseline_path, baseline_payload)

    qm_payload = qm_tool.execute_surface(baseline_path=baseline_path, trigger_id=None, captured_at_utc="2026-04-18T20:10:01Z", surface_root=tmp_path)
    ledger_payload = ledger_tool.execute_surface(baseline_path=baseline_path, trigger_id=None, captured_at_utc="2026-04-18T20:10:02Z", surface_root=tmp_path)
    authority_payload = authority_tool.execute_surface(baseline_path=baseline_path, trigger_id=None, captured_at_utc="2026-04-18T20:10:03Z", surface_root=tmp_path)

    assert qm_payload["computed_state"]["state_change_from_baseline"] > 0
    assert ledger_payload["computed_state"]["state_change_from_baseline"] > 0
    assert authority_payload["computed_state"]["state_change_from_baseline"] > 0
    assert qm_payload["triggers"][-1]["status"] == "COMPLETED"
    assert ledger_payload["triggers"][-1]["status"] == "COMPLETED"
    assert authority_payload["triggers"][-1]["status"] == "COMPLETED"


def test_recompute_orchestrator_defaults_to_dry_run_workspace(tmp_path: Path, monkeypatch) -> None:
    baseline_path = _patch_root(monkeypatch, tmp_path)
    _seed_shared_inputs(tmp_path)
    monkeypatch.setattr(orchestrator, "DEFAULT_DRY_RUN_ROOT", tmp_path / "formal" / "output" / "recompute_dry_run" / "latest")

    payload = orchestrator.execute_all(baseline_path=None, captured_at_utc="2026-04-18T20:11:00Z")

    assert payload["summary"]["execution_mode"] == "dry-run"
    assert payload["summary"]["surfaces_completed"] == 3
    assert payload["summary"]["live_writeback_performed"] is False
    for rel_path in (
        "formal/output/recompute/qm_seam_coherence_under_revised_blocker.json",
        "formal/output/recompute/ledger_artifact_transport_under_revised_blocker.json",
        "formal/output/recompute/blocker_authority_transport_surface.json",
    ):
        surface_payload = helpers.read_json(tmp_path / rel_path)
        assert "computed_state" not in surface_payload
        assert surface_payload["triggers"][-1]["status"] == "PENDING_RECOMPUTE"
        dry_run_payload = helpers.read_json(tmp_path / "formal" / "output" / "recompute_dry_run" / "latest" / rel_path)
        assert "computed_state" in dry_run_payload
        assert dry_run_payload["triggers"][-1]["status"] == "COMPLETED"


def test_live_writeback_requires_explicit_opt_in(tmp_path: Path, monkeypatch) -> None:
    _patch_root(monkeypatch, tmp_path)
    _seed_shared_inputs(tmp_path)

    try:
        orchestrator.execute_all(
            baseline_path=tmp_path / "formal" / "output" / "reports" / "recompute_baseline_snapshot_20260418_v0.json",
            captured_at_utc="2026-04-18T20:12:00Z",
            execution_mode="live-writeback",
            allow_live_writeback=False,
            surface_root=tmp_path,
        )
    except ValueError as exc:
        assert str(exc) == "EXPLICIT_ALLOW_LIVE_WRITEBACK_TRUE"
    else:
        raise AssertionError("Expected explicit live writeback guard failure")


def test_live_writeback_mutates_canonical_surfaces_when_explicit_opt_in(tmp_path: Path, monkeypatch) -> None:
    baseline_path = _patch_root(monkeypatch, tmp_path)
    _seed_shared_inputs(tmp_path)

    payload = orchestrator.execute_all(
        baseline_path=baseline_path,
        captured_at_utc="2026-04-18T20:13:00Z",
        execution_mode="live-writeback",
        allow_live_writeback=True,
        surface_root=tmp_path,
    )

    assert payload["summary"]["execution_mode"] == "live-writeback"
    assert payload["summary"]["live_writeback_performed"] is True
    assert payload["summary"]["surfaces_completed"] == 3
    for rel_path in (
        "formal/output/recompute/qm_seam_coherence_under_revised_blocker.json",
        "formal/output/recompute/ledger_artifact_transport_under_revised_blocker.json",
        "formal/output/recompute/blocker_authority_transport_surface.json",
    ):
        surface_payload = helpers.read_json(tmp_path / rel_path)
        assert "computed_state" in surface_payload
        assert surface_payload["triggers"][-1]["status"] == "COMPLETED"

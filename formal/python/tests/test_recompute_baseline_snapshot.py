from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import recompute_baseline_snapshot as tool
from formal.python.tools import recompute_surface_helpers as helpers


def _write_json(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def _seed_surface(path: Path, surface_name: str) -> None:
    _write_json(
        path,
        {
            "schema_id": surface_name.upper(),
            "triggers": [
                {
                    "trigger_id": f"TRIGGER_{surface_name}_001",
                    "surface_name": surface_name,
                    "status": "PENDING_RECOMPUTE",
                }
            ],
        },
    )


def _seed_shared_inputs(root: Path) -> None:
    _write_json(root / "formal" / "output" / "reports" / "authority_promotion_registration_20260411_v0.json", {"summary": {"registration_completed": True}})
    _write_json(root / "formal" / "output" / "reports" / "post_plan_bounded_coupling_refinement_packet_chain_20260418_v0.json", {"summary": {"terminal_outcome": "POST_PLAN_BOUNDED_COUPLING_REFINEMENT_PACKET_CHAIN_PROMOTION_REGISTERED"}})
    _seed_surface(root / "formal" / "output" / "recompute" / "qm_seam_coherence_under_revised_blocker.json", "qm_seam_coherence_under_revised_blocker")
    _seed_surface(root / "formal" / "output" / "recompute" / "ledger_artifact_transport_under_revised_blocker.json", "ledger_artifact_transport_under_revised_blocker")
    _seed_surface(root / "formal" / "output" / "recompute" / "blocker_authority_transport_surface.json", "blocker_authority_transport_surface")


def test_baseline_snapshot_builds_surface_entries(tmp_path: Path, monkeypatch) -> None:
    monkeypatch.setattr(helpers, "REPO_ROOT", tmp_path)
    monkeypatch.setattr(tool, "REPO_ROOT", tmp_path)
    monkeypatch.setattr(helpers, "AUTHORITY_PROMOTION_REPORT_PATH", tmp_path / "formal" / "output" / "reports" / "authority_promotion_registration_20260411_v0.json")
    monkeypatch.setattr(helpers, "PACKET_CHAIN_REPORT_PATH", tmp_path / "formal" / "output" / "reports" / "post_plan_bounded_coupling_refinement_packet_chain_20260418_v0.json")
    monkeypatch.setattr(helpers, "BASELINE_REPORT_PATH", tmp_path / "formal" / "output" / "reports" / "recompute_baseline_snapshot_20260418_v0.json")
    _seed_shared_inputs(tmp_path)

    report = tool.build_report(captured_at_utc="2026-04-18T20:00:00Z")

    assert report["summary"]["baseline_surfaces"] == 3
    assert report["surface_baselines"]["qm_seam_coherence"]["latest_trigger_id"] == "TRIGGER_qm_seam_coherence_under_revised_blocker_001"
    assert "coherence_metric" in report["surface_baselines"]["qm_seam_coherence"]["baseline_values"]
    assert "artifact_flux" in report["surface_baselines"]["ledger_artifact_transport"]["baseline_values"]
    assert "propagation_latency" in report["surface_baselines"]["blocker_authority_transport"]["baseline_values"]

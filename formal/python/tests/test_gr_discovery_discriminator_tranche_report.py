from __future__ import annotations

from pathlib import Path

from formal.python.tools.gr_discovery_discriminator_tranche_report import build_report


def test_gr_discovery_discriminator_tranche_report_is_executable() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    declaration = (
        repo_root
        / "formal"
        / "docs"
        / "release"
        / "GR_DISCOVERY_DISCRIMINATOR_TRANCHE_EXECUTION_20260411_v0.json"
    )

    payload = build_report(declaration_path=declaration, captured_at_utc="2026-04-11T23:59:59Z")

    assert payload["schema_id"] == "GR_DISCOVERY_DISCRIMINATOR_TRANCHE_REPORT_20260411_v0"
    summary = payload["summary"]
    assert summary["target_row"] == "ROW-SEAM-COSMO-SR-001"
    assert summary["selected_route"] == "ACTIVATE_NEXT_RANKED_SEAM"
    assert summary["rank3_candidate"] == "ROW-SEAM-COSMO-SR-001"
    assert summary["next_route_alignment"] is True
    assert summary["terminal_outcome"] == "DISCRIMINATOR_PRODUCED"
    assert summary["terminal_outcome_allowed"] is True
    assert summary["required_fields_present"] is True
    assert summary["probe_lane_allowed"] is False
    assert summary["execution_classification"] == "DISCOVERY_TRANCHE_EXECUTABLE"

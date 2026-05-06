from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
TOOL_PATH = REPO_ROOT / "formal" / "python" / "tools" / "measure_state_core_compression_yield.py"
REPORT_PATH = REPO_ROOT / "formal" / "output" / "state_core_compression_yield_report_v0.json"


def _run_report_check() -> None:
    cmd = [
        sys.executable,
        str(TOOL_PATH),
    ]
    completed = subprocess.run(
        cmd,
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert completed.returncode == 0, (
        "Compression/yield report generation failed.\n"
        f"stdout:\n{completed.stdout}\n"
        f"stderr:\n{completed.stderr}"
    )


def test_state_core_compression_yield_gate_assets_exist() -> None:
    assert TOOL_PATH.exists(), "Missing compression/yield measurement tool."


def test_state_core_compression_yield_gate_report_generation_and_contract() -> None:
    before = REPORT_PATH.read_text(encoding="utf-8")
    _run_report_check()
    assert REPORT_PATH.exists(), "Missing generated compression/yield report artifact."
    assert REPORT_PATH.read_text(encoding="utf-8") == before

    report = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert report["artifact_id"] == "state_core_compression_yield_report_v0"

    metrics = report["metrics"]
    assert metrics["structured_source_count"] == 1
    assert metrics["legacy_manual_mirror_surface_count"] >= 4
    assert metrics["manual_surface_reduction_count"] >= 3
    assert metrics["manual_surface_compression_ratio"] >= 4.0
    assert metrics["status_family_chain_length"] >= 9
    assert metrics["status_family_entries_per_structured_source"] >= 9.0
    assert metrics["ws10_task_status_row_count"] >= 21
    assert metrics["ws10_task_status_rows_per_structured_source"] >= 21.0
    assert metrics["ws10_evidence_log_entry_count"] >= 9
    assert metrics["ws10_evidence_log_entries_per_structured_source"] >= 9.0
    assert metrics["ws10_scientific_artifact_lineage_entry_count"] >= 4
    assert metrics["ws10_scientific_artifact_lineage_entries_per_structured_source"] >= 4.0
    assert metrics["ws10_scientific_artifact_gate_metadata_entry_count"] >= 4
    assert metrics["ws10_scientific_artifact_gate_metadata_entries_per_structured_source"] >= 4.0
    assert metrics["ws10_additive_candidate_declaration_entry_count"] >= 8
    assert metrics["ws10_additive_candidate_declaration_entries_per_structured_source"] >= 8.0
    assert metrics["total_status_family_entries"] >= 30
    assert metrics["total_status_family_entries_per_structured_source"] >= 30.0
    assert metrics["total_control_family_entries"] >= 39
    assert metrics["total_control_family_entries_per_structured_source"] >= 39.0
    assert metrics["total_scientific_family_entries"] >= 16
    assert metrics["total_scientific_family_entries_per_structured_source"] >= 16.0
    assert metrics["total_migrated_family_entries"] >= 55
    assert metrics["total_migrated_family_entries_per_structured_source"] >= 55.0
    assert metrics["governance_gate_default_enforced"] is True

    scope = report["scope"]
    assert scope["lane"] == "QM_STAT"
    assert scope["active_tranche_id"].startswith("WS-10-")
    assert len(scope["recent_tranche_chain"]) >= 3

    non_claim = report["non_claim_boundary"]
    assert non_claim["operational_metric_only"] is True
    assert non_claim["scientific_truth_claimed"] is False
    assert non_claim["external_benchmark_claimed"] is False

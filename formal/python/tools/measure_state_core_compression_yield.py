from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_STATE_CORE = REPO_ROOT / "formal" / "docs" / "release" / "state_core_v0.json"
DEFAULT_GOV_SUITE = REPO_ROOT / "governance_suite.ps1"
DEFAULT_OUTPUT = REPO_ROOT / "formal" / "output" / "state_core_compression_yield_report_v0.json"


REQUIRED_GOVERNANCE_GATE_TOKENS = [
    "formal/python/tests/test_state_core_generation_integrity_gate.py",
    "formal/python/tests/test_state_core_generated_block_manual_edit_prohibition_gate.py",
]


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _measure(state_core: dict[str, Any], governance_suite_text: str) -> dict[str, Any]:
    active_lane = state_core["active_lane"]
    active_tranche_id = state_core["active_tranche_id"]
    mirror_target_count = len(state_core["mirror_targets"])

    structured_source_count = 1
    legacy_manual_mirror_surface_count = mirror_target_count
    manual_surface_reduction_count = legacy_manual_mirror_surface_count - structured_source_count
    manual_surface_compression_ratio = legacy_manual_mirror_surface_count / structured_source_count

    recent_chain = state_core["recent_tranche_chain_by_lane"][active_lane]
    recent_tranche_chain_length = len(recent_chain)
    status_family_chain_length = len(state_core["ws10_branch_boundary_status_family"]["decision_chain"])
    ws10_task_status_row_count = len(state_core["ws10_task_status_table_family"]["rows"])
    ws10_evidence_log_entry_count = len(state_core["ws10_evidence_log_family"]["entries"])
    ws10_scientific_artifact_lineage_entry_count = len(state_core["ws10_scientific_artifact_lineage_family"]["lineages"])
    ws10_scientific_artifact_gate_metadata_entry_count = len(state_core["ws10_scientific_artifact_gate_metadata_family"]["entries"])
    total_status_family_entries = status_family_chain_length + ws10_task_status_row_count
    total_control_family_entries = total_status_family_entries + ws10_evidence_log_entry_count
    total_scientific_family_entries = (
        ws10_scientific_artifact_lineage_entry_count
        + ws10_scientific_artifact_gate_metadata_entry_count
    )
    total_migrated_family_entries = total_control_family_entries + total_scientific_family_entries

    governance_gate_default_enforced = all(
        token in governance_suite_text for token in REQUIRED_GOVERNANCE_GATE_TOKENS
    )

    return {
        "artifact_id": "state_core_compression_yield_report_v0",
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "scope": {
            "lane": active_lane,
            "active_tranche_id": active_tranche_id,
            "recent_tranche_chain": recent_chain,
        },
        "metrics": {
            "structured_source_count": structured_source_count,
            "legacy_manual_mirror_surface_count": legacy_manual_mirror_surface_count,
            "manual_surface_reduction_count": manual_surface_reduction_count,
            "manual_surface_compression_ratio": manual_surface_compression_ratio,
            "recent_tranche_chain_length": recent_tranche_chain_length,
            "status_family_chain_length": status_family_chain_length,
            "ws10_task_status_row_count": ws10_task_status_row_count,
            "ws10_evidence_log_entry_count": ws10_evidence_log_entry_count,
            "ws10_scientific_artifact_lineage_entry_count": ws10_scientific_artifact_lineage_entry_count,
            "ws10_scientific_artifact_gate_metadata_entry_count": ws10_scientific_artifact_gate_metadata_entry_count,
            "total_status_family_entries": total_status_family_entries,
            "total_control_family_entries": total_control_family_entries,
            "total_scientific_family_entries": total_scientific_family_entries,
            "total_migrated_family_entries": total_migrated_family_entries,
            "mirrors_per_structured_source": mirror_target_count / structured_source_count,
            "tranches_tracked_per_structured_source": recent_tranche_chain_length / structured_source_count,
            "status_family_entries_per_structured_source": status_family_chain_length / structured_source_count,
            "ws10_task_status_rows_per_structured_source": ws10_task_status_row_count / structured_source_count,
            "ws10_evidence_log_entries_per_structured_source": ws10_evidence_log_entry_count / structured_source_count,
            "ws10_scientific_artifact_lineage_entries_per_structured_source": ws10_scientific_artifact_lineage_entry_count / structured_source_count,
            "ws10_scientific_artifact_gate_metadata_entries_per_structured_source": ws10_scientific_artifact_gate_metadata_entry_count / structured_source_count,
            "total_status_family_entries_per_structured_source": total_status_family_entries / structured_source_count,
            "total_control_family_entries_per_structured_source": total_control_family_entries / structured_source_count,
            "total_scientific_family_entries_per_structured_source": total_scientific_family_entries / structured_source_count,
            "total_migrated_family_entries_per_structured_source": total_migrated_family_entries / structured_source_count,
            "governance_gate_default_enforced": governance_gate_default_enforced,
        },
        "non_claim_boundary": {
            "scientific_truth_claimed": False,
            "operational_metric_only": True,
            "external_benchmark_claimed": False,
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Measure state-core cutover compression and operational yield.")
    parser.add_argument("--state-core", type=Path, default=DEFAULT_STATE_CORE)
    parser.add_argument("--governance-suite", type=Path, default=DEFAULT_GOV_SUITE)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--print", dest="print_mode", action="store_true")
    args = parser.parse_args()

    state_core = _read_json(args.state_core)
    governance_text = args.governance_suite.read_text(encoding="utf-8")

    result = _measure(state_core, governance_text)

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")

    if args.print_mode:
        print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()

from __future__ import annotations

import argparse
import json
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
CHECKPOINT_SCHEMA_ID = "WS10_T43_MAINTENANCE_SELECTION_REPORT_20260418_v0"
REGISTRY_SCHEMA_ID = "QFT_GR_SLICEB_INCREMENT_FAMILY_REGISTRY_20260418_v0"
DEFAULT_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "ws10_t43_maintenance_selection_checkpoint_20260418_v0.json"
DEFAULT_REGISTRY_PATH = REPO_ROOT / "formal" / "output" / "reports" / "qft_gr_sliceb_increment_family_registry_20260418_v0.json"
T42_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "ws10_t42_redteam_baseline_freeze_checkpoint_20260418_v0.json"
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
TEST_DIR = REPO_ROOT / "formal" / "python" / "tests"

QFT_GR_INCREMENT_PATTERN = re.compile(
    r"QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT(?:(?P<start>\d{2})_TO_(?P<end>\d{2})_SYNTHESIS_NOTE|(?P<single>\d{2})_(?P<kind>ASSESSMENT_NOTE|EXECUTION_PACKET|SCIENCE_VALIDATION_NOTE|SEMANTIC_DELTA_DECISION_NOTE))_v0\.md$"
)
QM_GATE_PATTERN = re.compile(r"test_qm_stat_class_b_seam_physics_pilot_cycle(?P<cycle>\d{2})_gate\.py$")
QM_SYNTH_PATTERN = re.compile(r"test_qm_stat_class_b_seam_physics_pilot_cycle(?P<from_cycle>\d{2})_to_(?P<to_cycle>\d{2})_synthesis_gate\.py$")


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def build_release_family_registry(*, captured_at_utc: str | None = None) -> dict[str, Any]:
    entries: list[dict[str, Any]] = []
    counts_by_kind = {
        "ASSESSMENT_NOTE": 0,
        "EXECUTION_PACKET": 0,
        "SCIENCE_VALIDATION_NOTE": 0,
        "SEMANTIC_DELTA_DECISION_NOTE": 0,
        "SYNTHESIS_NOTE": 0,
    }
    single_increments: list[int] = []
    synthesis_endpoints: list[int] = []

    for path in sorted(RELEASE_DIR.glob("QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT*_v0.md")):
        match = QFT_GR_INCREMENT_PATTERN.fullmatch(path.name)
        if match is None:
            continue
        if match.group("end"):
            end = int(match.group("end"))
            start = int(match.group("start"))
            counts_by_kind["SYNTHESIS_NOTE"] += 1
            synthesis_endpoints.append(end)
            entries.append(
                {
                    "file": _ptr(path),
                    "kind": "SYNTHESIS_NOTE",
                    "start_increment": start,
                    "end_increment": end,
                }
            )
        else:
            increment = int(match.group("single"))
            kind = str(match.group("kind"))
            counts_by_kind[kind] += 1
            single_increments.append(increment)
            entries.append(
                {
                    "file": _ptr(path),
                    "kind": kind,
                    "increment": increment,
                }
            )

    increment_span = sorted(set(single_increments))
    synthesis_span = sorted(set(synthesis_endpoints))
    return {
        "schema_id": REGISTRY_SCHEMA_ID,
        "artifact_id": "qft_gr_sliceb_increment_family_registry_20260418_v0",
        "status": "INDEXED_NONAUTHORITATIVE_MAINTENANCE_SURFACE_v0",
        "captured_at_utc": _ts(captured_at_utc),
        "family_id": "QFT_GR_SLICEB_INCREMENT_RELEASE_NOTES",
        "family_root": "formal/docs/release",
        "file_count": len(entries),
        "counts_by_kind": counts_by_kind,
        "increment_span": {
            "min_increment": min(increment_span) if increment_span else None,
            "max_increment": max(increment_span) if increment_span else None,
            "covered_increment_count": len(increment_span),
        },
        "synthesis_span": {
            "min_end_increment": min(synthesis_span) if synthesis_span else None,
            "max_end_increment": max(synthesis_span) if synthesis_span else None,
            "covered_end_increment_count": len(synthesis_span),
        },
        "operator_boundary": {
            "active_review_surface": "REGISTRY_INDEX_ONLY",
            "family_role": "TRACEABILITY_AND_HISTORY_COMPRESSION_AID",
            "non_claim_boundary": "This registry indexes existing release notes and does not alter seam status, theorem status, or claim posture.",
        },
        "entries": entries,
    }


def build_checkpoint(*, registry: dict[str, Any], captured_at_utc: str | None = None) -> dict[str, Any]:
    t42 = _read_json(T42_CHECKPOINT_PATH)
    direct_cycle_gates = sorted(path for path in TEST_DIR.glob("test_qm_stat_class_b_seam_physics_pilot_cycle*_gate.py") if QM_GATE_PATTERN.fullmatch(path.name))
    synthesis_gates = sorted(path for path in TEST_DIR.glob("test_qm_stat_class_b_seam_physics_pilot_cycle*_to_*_synthesis_gate.py") if QM_SYNTH_PATTERN.fullmatch(path.name))

    return {
        "schema_id": CHECKPOINT_SCHEMA_ID,
        "artifact_id": "ws10_t43_maintenance_selection_checkpoint_20260418_v0",
        "status": "ACTIVE_MAINTENANCE_SELECTION_AND_INDEXING_NONLIVE_v0",
        "captured_at_utc": _ts(captured_at_utc),
        "baseline_reference": {
            "t42_checkpoint": _ptr(T42_CHECKPOINT_PATH),
            "t42_release_surface_file_count": int(t42.get("baseline_metrics", {}).get("release_surface_file_count", 0)),
            "t42_governed_pytests_expected_count": int(t42.get("baseline_metrics", {}).get("governed_pytests_expected_count", 0)),
            "t42_active_theorem_gap_count": int(t42.get("baseline_metrics", {}).get("active_theorem_gap_count", 0)),
            "t42_active_seam_gap_count": int(t42.get("baseline_metrics", {}).get("active_seam_gap_count", 0)),
        },
        "selected_gate_family": {
            "family_id": "QM_STAT_CLASS_B_SEAM_PHYSICS_PILOT_GATE_STACK",
            "direct_cycle_gate_count": len(direct_cycle_gates),
            "synthesis_gate_count": len(synthesis_gates),
            "selected_direct_family_pattern": "formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycleNN_gate.py",
            "selected_synthesis_family_pattern": "formal/python/tests/test_qm_stat_class_b_seam_physics_pilot_cycleNN_to_NN_synthesis_gate.py",
            "proposed_helper_path": "formal/python/tests/qm_stat_class_b_cycle_gate_family_helper.py",
            "phase2a_next_action": "CONSOLIDATE_DIRECT_CYCLE_GATES_FIRST_THEN_SYNTHESIS_GATES",
        },
        "selected_release_family": {
            "family_id": registry.get("family_id"),
            "file_count": int(registry.get("file_count", 0)),
            "registry_pointer": _ptr(DEFAULT_REGISTRY_PATH),
            "counts_by_kind": dict(registry.get("counts_by_kind", {})),
            "phase2b_next_action": "USE_REGISTRY_AS_ACTIVE_REVIEW_SURFACE_AND_DEFER_RAW_INCREMENT_CHAIN_TO_ARCHIVAL_TRACEABILITY",
        },
        "summary": {
            "terminal_outcome": "MAINTENANCE_FAMILIES_SELECTED_AND_QFT_GR_RELEASE_FAMILY_INDEXED",
            "next_action": "START_QM_STAT_DIRECT_CYCLE_GATE_CONSOLIDATION_AND_OPERATOR_PACK_GENERATION",
            "selected_phase2a_lane": "QM_STAT_GATE_FAMILY",
            "selected_phase2b_lane": "QFT_GR_SLICEB_INCREMENT_RELEASE_NOTES",
        },
        "non_claim_boundary": "This checkpoint selects maintenance-reduction targets and indexes an existing release-note family. It does not change theorem status, seam status, or live scientific authority by itself.",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate the WS-10 T43 maintenance selection checkpoint and Slice B release-family registry.")
    parser.add_argument("--checkpoint-out", type=Path, default=DEFAULT_CHECKPOINT_PATH)
    parser.add_argument("--registry-out", type=Path, default=DEFAULT_REGISTRY_PATH)
    args = parser.parse_args()

    registry = build_release_family_registry()
    checkpoint = build_checkpoint(registry=registry)

    args.registry_out.parent.mkdir(parents=True, exist_ok=True)
    args.registry_out.write_text(json.dumps(registry, indent=2) + "\n", encoding="utf-8")
    args.checkpoint_out.parent.mkdir(parents=True, exist_ok=True)
    args.checkpoint_out.write_text(json.dumps(checkpoint, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
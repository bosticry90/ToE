from __future__ import annotations

import argparse
import json
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
SCHEMA_ID = "WS10_T44_QM_STAT_DIRECT_CYCLE_CONSOLIDATION_REPORT_20260418_v0"
DEFAULT_OUT_PATH = REPO_ROOT / "formal" / "output" / "ws10_t44_qm_stat_direct_cycle_consolidation_checkpoint_20260418_v0.json"
T43_CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "ws10_t43_maintenance_selection_checkpoint_20260418_v0.json"
HELPER_PATH = REPO_ROOT / "formal" / "python" / "tests" / "qm_stat_class_b_cycle_gate_family_helper.py"
PRE_REFACTOR_DIRECT_CYCLE_LINES = 1741


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


def _direct_cycle_paths() -> list[Path]:
    return [
        REPO_ROOT / "formal" / "python" / "tests" / f"test_qm_stat_class_b_seam_physics_pilot_cycle{cycle:02d}_gate.py"
        for cycle in range(1, 13)
    ]


def _helperized_cycle_paths() -> list[Path]:
    return [
        REPO_ROOT / "formal" / "python" / "tests" / f"test_qm_stat_class_b_seam_physics_pilot_cycle{cycle:02d}_gate.py"
        for cycle in range(2, 12)
    ]


def _line_count(path: Path) -> int:
    return len(path.read_text(encoding="utf-8").splitlines())


def build_report(*, captured_at_utc: str | None = None) -> dict[str, Any]:
    t43 = _read_json(T43_CHECKPOINT_PATH)
    helperized_paths = _helperized_cycle_paths()
    helper_backed_wrapper_count = 0
    helper_backed_wrapper_lines = 0
    for path in helperized_paths:
        text = path.read_text(encoding="utf-8")
        if "qm_stat_class_b_cycle_gate_family_helper" in text:
            helper_backed_wrapper_count += 1
        helper_backed_wrapper_lines += _line_count(path)

    helper_lines = _line_count(HELPER_PATH)
    total_post_refactor_lines = helper_backed_wrapper_lines + helper_lines
    all_direct_cycle_paths = _direct_cycle_paths()
    bespoke_paths = []
    for path in all_direct_cycle_paths:
        text = path.read_text(encoding="utf-8")
        if "qm_stat_class_b_cycle_gate_family_helper" not in text:
            bespoke_paths.append(path)

    net_line_reduction = PRE_REFACTOR_DIRECT_CYCLE_LINES - total_post_refactor_lines

    return {
        "schema_id": SCHEMA_ID,
        "artifact_id": "ws10_t44_qm_stat_direct_cycle_consolidation_checkpoint_20260418_v0",
        "status": "ACTIVE_QM_STAT_DIRECT_CYCLE_CONSOLIDATION_NONLIVE_v0",
        "captured_at_utc": _ts(captured_at_utc),
        "baseline_reference": {
            "t43_checkpoint": _ptr(T43_CHECKPOINT_PATH),
            "t43_selected_gate_family": t43.get("selected_gate_family", {}).get("family_id"),
            "t43_direct_cycle_gate_count": int(t43.get("selected_gate_family", {}).get("direct_cycle_gate_count", 0)),
            "pre_refactor_helperizable_direct_cycle_count": len(helperized_paths),
            "pre_refactor_helperizable_direct_cycle_lines": PRE_REFACTOR_DIRECT_CYCLE_LINES,
        },
        "consolidation_metrics": {
            "helper_path": _ptr(HELPER_PATH),
            "helper_lines": helper_lines,
            "helper_backed_wrapper_count": helper_backed_wrapper_count,
            "helper_backed_wrapper_lines": helper_backed_wrapper_lines,
            "post_refactor_total_lines": total_post_refactor_lines,
            "net_line_reduction": net_line_reduction,
            "reduction_ratio": round(net_line_reduction / PRE_REFACTOR_DIRECT_CYCLE_LINES, 6),
            "preserved_bespoke_direct_cycles": [_ptr(path) for path in bespoke_paths],
        },
        "summary": {
            "terminal_outcome": "QM_STAT_DIRECT_CYCLE_GATES_CONSOLIDATED_ON_SHARED_HELPER",
            "next_action": "GENERATE_OPERATOR_TRUTH_PACK_FROM_T42_T43_T44_AND_BLOCKER_SURFACES",
            "preserved_bespoke_boundary": "CYCLE01_BOOTSTRAP_AND_CYCLE12_CANDIDATE_REMAIN_UNCHANGED",
        },
        "non_claim_boundary": "This checkpoint records executable maintenance reduction only. It does not change theorem status, seam status, or live scientific authority by itself.",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate the WS-10 T44 QM-STAT direct-cycle consolidation checkpoint.")
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT_PATH)
    args = parser.parse_args()

    report = build_report()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
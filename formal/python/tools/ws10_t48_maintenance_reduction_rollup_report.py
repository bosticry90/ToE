from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "WS10_T48_MAINTENANCE_REDUCTION_ROLLUP_REPORT_20260418_v0"
DEFAULT_OUT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "ws10_maintenance_reduction_rollup_20260418_v0.json"
T44_PATH = REPO_ROOT / "formal" / "output" / "ws10_t44_qm_stat_direct_cycle_consolidation_checkpoint_20260418_v0.json"
T45_PATH = REPO_ROOT / "formal" / "output" / "reports" / "ws10_operator_truth_pack_20260418_v0.json"
T46_PATH = REPO_ROOT / "formal" / "output" / "ws10_t46_qm_stat_synthesis_gate_consolidation_checkpoint_20260418_v0.json"
T47_PATH = REPO_ROOT / "formal" / "output" / "reports" / "qft_gr_sliceb_increment_family_summary_views_20260418_v0.json"
INC05_SYNTH_PATH = REPO_ROOT / "formal" / "docs" / "release" / "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT01_TO_05_SYNTHESIS_NOTE_v0.md"
INC07_SYNTH_PATH = REPO_ROOT / "formal" / "docs" / "release" / "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT01_TO_07_SYNTHESIS_NOTE_v0.md"
INC06_ASSESS_PATH = REPO_ROOT / "formal" / "docs" / "release" / "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT06_ASSESSMENT_NOTE_v0.md"
INC06_EXEC_PATH = REPO_ROOT / "formal" / "docs" / "release" / "QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT06_EXECUTION_PACKET_v0.md"
ABSENT_INC06_SYNTH_POINTER = "formal/docs/release/QFT_GR_SEAM_REACTIVATION_SLICEB_INCREMENT01_TO_06_SYNTHESIS_NOTE_v0.md"


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


def build_report(*, captured_at_utc: str | None = None) -> dict[str, Any]:
    t44 = _read_json(T44_PATH)
    t45 = _read_json(T45_PATH)
    t46 = _read_json(T46_PATH)
    t47 = _read_json(T47_PATH)

    t44_base = int(t44.get("baseline_reference", {}).get("pre_refactor_helperizable_direct_cycle_lines", 0))
    t44_post = int(t44.get("consolidation_metrics", {}).get("post_refactor_total_lines", 0))
    t44_net = int(t44.get("consolidation_metrics", {}).get("net_line_reduction", 0))
    t46_base = int(t46.get("baseline_reference", {}).get("pre_refactor_helperizable_synthesis_gate_lines", 0))
    t46_post = int(t46.get("consolidation_metrics", {}).get("post_refactor_total_lines", 0))
    t46_net = int(t46.get("consolidation_metrics", {}).get("net_line_reduction", 0))

    combined_base = t44_base + t46_base
    combined_post = t44_post + t46_post
    combined_net = t44_net + t46_net
    combined_ratio = round(combined_net / combined_base, 6) if combined_base else 0.0

    missing_endpoints = t47.get("kind_span_views", {}).get("SYNTHESIS_NOTE", {}).get("missing_end_increments", [])

    return {
        "schema_id": SCHEMA_ID,
        "artifact_id": "ws10_maintenance_reduction_rollup_20260418_v0",
        "status": "DERIVED_ROLLUP_AND_EXECUTION_WINDOW_DEFAULTS_v0",
        "captured_at_utc": _ts(captured_at_utc),
        "derived_from": {
            "t44_checkpoint": _ptr(T44_PATH),
            "t45_review_pack": _ptr(T45_PATH),
            "t46_checkpoint": _ptr(T46_PATH),
            "t47_summary_views": _ptr(T47_PATH),
        },
        "maintenance_reduction_rollup": {
            "direct_cycle_family": {
                "pre_refactor_lines": t44_base,
                "post_refactor_lines": t44_post,
                "net_line_reduction": t44_net,
                "reduction_ratio": t44.get("consolidation_metrics", {}).get("reduction_ratio"),
            },
            "synthesis_gate_family": {
                "pre_refactor_lines": t46_base,
                "post_refactor_lines": t46_post,
                "net_line_reduction": t46_net,
                "reduction_ratio": t46.get("consolidation_metrics", {}).get("reduction_ratio"),
            },
            "combined": {
                "pre_refactor_lines": combined_base,
                "post_refactor_lines": combined_post,
                "net_line_reduction": combined_net,
                "reduction_ratio": combined_ratio,
                "helper_backed_wrapper_count": int(t44.get("consolidation_metrics", {}).get("helper_backed_wrapper_count", 0))
                + int(t46.get("consolidation_metrics", {}).get("helper_backed_wrapper_count", 0)),
            },
        },
        "execution_window_defaults": {
            "operator_review_surface": {
                "artifact_pointer": _ptr(T45_PATH),
                "status": t45.get("status"),
                "default_role": "CONTROL_SURFACE_AND_TRANCHE_STACK_REVIEW",
            },
            "release_family_review_surface": {
                "artifact_pointer": _ptr(T47_PATH),
                "status": t47.get("status"),
                "default_role": "QFT_GR_SLICEB_BANDED_AND_TERMINAL_REVIEW",
            },
            "authority_boundary": "Use T45 and T47 as default review accelerators while preserving the canonical documents, checkpoints, and release notes as sources of record.",
        },
        "synthesis_endpoint_06_adjudication": {
            "missing_end_increment": 6,
            "missing_from_summary_views": missing_endpoints,
            "absent_synthesis_pointer": ABSENT_INC06_SYNTH_POINTER,
            "pointer_exists": False,
            "adjudication": "INTENTIONAL_SYNTHESIS_CHECKPOINT_OMISSION_v0",
            "rationale": "Increment06 has bounded execution and assessment artifacts, while the synthesis checkpoint chain jumps from 01_TO_05 to 01_TO_07. The summary faithfully reflects the indexed release family rather than omitting an existing source.",
            "evidence": {
                "prior_synthesis_checkpoint": _ptr(INC05_SYNTH_PATH),
                "resume_synthesis_checkpoint": _ptr(INC07_SYNTH_PATH),
                "increment06_assessment": _ptr(INC06_ASSESS_PATH),
                "increment06_execution": _ptr(INC06_EXEC_PATH),
            },
        },
        "summary": {
            "terminal_outcome": "CUMULATIVE_MAINTENANCE_REDUCTION_AND_REVIEW_DEFAULTS_PINNED",
            "next_action": "SHIFT_BACK_TO_BLOCKER_MOVING_WORK_UNLESS_ANOTHER_LOW_RISK_REPETITIVE_FAMILY_CLEARLY_MEETS_THE_T44_T46_PATTERN",
        },
        "non_claim_boundary": "This rollup summarizes already-pinned maintenance reductions and review defaults. It does not create new scientific authority, assert blocker closure, or modify live release truth.",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate the WS-10 T48 maintenance reduction rollup artifact.")
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT_PATH)
    args = parser.parse_args()

    report = build_report()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
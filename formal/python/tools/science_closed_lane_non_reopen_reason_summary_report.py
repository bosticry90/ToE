from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "SCIENCE_CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_20260412_v0.json"
)


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    summary_policy = dict(declaration.get("summary_policy", {}))
    summary_contract = dict(declaration.get("summary_contract", {}))

    formalization_path = REPO_ROOT / str(required_inputs.get("probe_readiness_standard_formalization_report", "")).strip()
    reopen_path = REPO_ROOT / str(required_inputs.get("science_closed_lane_reopen_eligibility_report", "")).strip()
    shared_path = REPO_ROOT / str(required_inputs.get("shared_model_class_post_refinement_decision_report", "")).strip()
    qft_gr_path = REPO_ROOT / str(required_inputs.get("qft_gr_post_refinement_decision_report", "")).strip()
    gr_path = REPO_ROOT / str(required_inputs.get("gr_row_001_structural_gap_definition_report", "")).strip()
    em_qft_path = REPO_ROOT / str(required_inputs.get("em_qft_higher_level_structure_review_report", "")).strip()
    qm_stat_path = REPO_ROOT / str(required_inputs.get("bridge_external_validation_policy_review_report", "")).strip()

    formalization = _read_json(formalization_path)
    reopen = _read_json(reopen_path)
    shared = _read_json(shared_path)
    qft_gr = _read_json(qft_gr_path)
    gr = _read_json(gr_path)
    em_qft = _read_json(em_qft_path)
    qm_stat = _read_json(qm_stat_path)

    formalization_outcome = str(dict(formalization.get("summary", {})).get("terminal_outcome", "")).strip()
    reopen_outcome = str(dict(reopen.get("summary", {})).get("terminal_outcome", "")).strip()

    lane_outcomes = {
        "QM-STAT": str(dict(qm_stat.get("summary", {})).get("review_outcome", "")).strip(),
        "GR-ROW-001": str(dict(gr.get("summary", {})).get("terminal_outcome", "")).strip(),
        "EM-QFT": str(dict(em_qft.get("summary", {})).get("terminal_outcome", "")).strip(),
        "SHARED-MODEL-CLASS": str(dict(shared.get("summary", {})).get("terminal_outcome", "")).strip(),
        "QFT-GR": str(dict(qft_gr.get("summary", {})).get("terminal_outcome", "")).strip(),
    }

    required_formalization_outcome = str(summary_policy.get("required_formalization_outcome", "")).strip()
    required_reopen_outcome = str(summary_policy.get("required_reopen_eligibility_outcome", "")).strip()
    required_lane_outcomes = dict(summary_policy.get("required_lane_outcomes", {}))
    canonical_lanes = {"QM-STAT", "GR-ROW-001", "EM-QFT", "SHARED-MODEL-CLASS", "QFT-GR"}
    required_lane_coverage_ok = set(required_lane_outcomes) == canonical_lanes

    lane_matches = {
        lane: lane_outcomes.get(lane, "") == str(required_lane_outcomes.get(lane, "")).strip()
        for lane in required_lane_outcomes
    }

    preconditions_ok = (
        formalization_outcome == required_formalization_outcome
        and reopen_outcome == required_reopen_outcome
        and all(lane_matches.values())
        and required_lane_coverage_ok
    )

    lane_reasons = {
        "QM-STAT": "External-validation policy prerequisites remain incomplete under formalized standard.",
        "GR-ROW-001": "Current architecture still requires a new seam or model-class structure before probe-ready progression.",
        "EM-QFT": "Current interface alignment route still requires a new seam or model-class structure before probe-ready progression.",
        "SHARED-MODEL-CLASS": "Lane remains externally comparable but not probe-ready under formalized comparator/repeatability thresholds.",
        "QFT-GR": "Lane remains externally comparable but not probe-ready under formalized comparator/repeatability thresholds.",
    }

    allowed_outcomes = set(summary_contract.get("allowed_outcomes", []))
    default_outcome = str(
        summary_contract.get("default_outcome", "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_INCOMPLETE")
    ).strip()

    if not required_lane_coverage_ok:
        terminal_outcome = "HOLD_PENDING_REASON_SUMMARY_REPAIR"
        next_action = "REPAIR_REQUIRED_LANE_COVERAGE_IN_SUMMARY_POLICY"
    elif not preconditions_ok:
        terminal_outcome = "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_INCOMPLETE"
        next_action = "RESTORE_REASON_SUMMARY_PRECONDITIONS_AND_RERUN"
    elif len(lane_reasons) != 5:
        terminal_outcome = "HOLD_PENDING_REASON_SUMMARY_REPAIR"
        next_action = "REPAIR_REASON_SUMMARY_LANE_COVERAGE"
    elif not all(lane_matches.values()):
        terminal_outcome = "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_CONTRACT_VIOLATION"
        next_action = "REVIEW_REQUIRED_LANE_OUTCOME_MISMATCH"
    else:
        terminal_outcome = "CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LOCKED"
        next_action = "PRESERVE_SUMMARY_AND_USE_FOR_FUTURE_RESTART_DISCIPLINE"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "formalization_outcome_match": formalization_outcome == required_formalization_outcome,
            "reopen_eligibility_outcome_match": reopen_outcome == required_reopen_outcome,
            "all_required_lane_outcomes_match": all(lane_matches.values()),
            "required_lane_coverage_ok": required_lane_coverage_ok,
            "single_terminal_outcome_rule_declared": str(
                summary_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_OUTCOME",
            "no_loop_rule_declared": str(summary_contract.get("no_loop_rule", "")).strip()
            == "ONE_CLOSED_LANE_NON_REOPEN_REASON_SUMMARY_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "reason_summary_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "formalization_outcome": formalization_outcome,
                "required_formalization_outcome": required_formalization_outcome,
                "reopen_eligibility_outcome": reopen_outcome,
                "required_reopen_eligibility_outcome": required_reopen_outcome,
                "lane_outcomes": lane_outcomes,
                "required_lane_outcomes": required_lane_outcomes,
                "lane_matches": lane_matches,
                "required_lane_coverage_ok": required_lane_coverage_ok,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "closed_lane_non_reopen_reasons": lane_reasons,
        "summary": {
            "terminal_outcome": terminal_outcome,
            "next_action": next_action,
            "single_layer_only": bool(summary_policy.get("single_layer_only", True)),
            "single_outcome_only": bool(summary_policy.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "probe_readiness_standard_formalization_report": _ptr(formalization_path),
            "science_closed_lane_reopen_eligibility_report": _ptr(reopen_path),
            "shared_model_class_post_refinement_decision_report": _ptr(shared_path),
            "qft_gr_post_refinement_decision_report": _ptr(qft_gr_path),
            "gr_row_001_structural_gap_definition_report": _ptr(gr_path),
            "em_qft_higher_level_structure_review_report": _ptr(em_qft_path),
            "bridge_external_validation_policy_review_report": _ptr(qm_stat_path),
        },
        "non_claim_boundary": "Repository-local closed-lane non-reopen reason summary report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate concise closed-lane non-reopen reason summary report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "science_closed_lane_non_reopen_reason_summary_20260412_v0.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    declaration_path = ns.declaration if ns.declaration.is_absolute() else (REPO_ROOT / ns.declaration)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)

    payload = build_report(declaration_path=declaration_path, captured_at_utc=ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "science_closed_lane_non_reopen_reason_summary_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

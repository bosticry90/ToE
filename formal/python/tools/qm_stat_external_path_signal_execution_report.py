from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_EXTERNAL_PATH_SIGNAL_EXECUTION_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_EXTERNAL_PATH_SIGNAL_EXECUTION_20260411_v0.json"
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
    execution_contract = dict(declaration.get("execution_contract", {}))

    packet_path = REPO_ROOT / str(required_inputs.get("qm_stat_external_path_signal_packet_report", "")).strip()
    comparator_path = REPO_ROOT / str(required_inputs.get("qm_stat_single_baseline_comparator_report", "")).strip()
    interpretation_path = REPO_ROOT / str(required_inputs.get("qm_stat_discovery_interpretation_report", "")).strip()
    probe_execution_path = REPO_ROOT / str(
        required_inputs.get("qm_stat_discovery_numerical_probe_execution_report", "")
    ).strip()

    packet = _read_json(packet_path)
    comparator = _read_json(comparator_path)
    interpretation = _read_json(interpretation_path)
    probe_execution = _read_json(probe_execution_path)

    packet_summary = dict(packet.get("summary", {}))
    comparator_summary = dict(comparator.get("summary", {}))
    interpretation_summary = dict(interpretation.get("summary", {}))
    probe_summary = dict(probe_execution.get("summary", {}))

    packet_outcome = str(packet_summary.get("packet_outcome", "")).strip()
    comparator_status = str(comparator_summary.get("comparator_status", "")).strip()
    candidate_mapping_status = str(comparator_summary.get("candidate_mapping_status", "")).strip()
    interpretation_value = str(interpretation_summary.get("interpretation", "")).strip()
    probe_signal = str(probe_summary.get("probe_signal", "")).strip()
    path_falsification_observed = bool(probe_summary.get("path_falsification_observed", False))

    packet_ready = packet_outcome == "QM_STAT_EXTERNAL_PATH_SIGNAL_PACKET_MATERIALIZED"
    comparator_ready = comparator_status == "DECLARED_COMPLETE_SINGLE_BASELINE_ONLY"
    mapping_evaluable = candidate_mapping_status == "BASELINE_COMPARATOR_EVALUABLE"
    external_interpretation = interpretation_value in {"EXTERNALLY_COMPARABLE", "NUMERICAL_PROBE_READY"}

    if path_falsification_observed:
        execution_outcome = "PATH_FALSIFIED"
        classification_reason = "PROBE_EXECUTION_REPORTED_PATH_FALSIFICATION"
    elif packet_ready and comparator_ready and mapping_evaluable and external_interpretation:
        execution_outcome = "EXTERNAL_PATH_SIGNAL_PRODUCED"
        classification_reason = "BASELINE_COMPARATOR_EVALUABLE_AND_EXTERNAL_INTERPRETATION_PRESENT"
    else:
        execution_outcome = "INTERNAL_ONLY_REMAINS"
        classification_reason = "BASELINE_DECLARED_BUT_QM_STAT_NOT_YET_EXTERNALLY_COMPARABLE"

    next_action = (
        "REOPEN_DISCOVERY_EXPANSION_REVIEW_ONCE"
        if execution_outcome == "EXTERNAL_PATH_SIGNAL_PRODUCED"
        else "HOLD_QM_STAT_AS_INTERNAL_ONLY_UNTIL_STRONGER_EXTERNAL_MAPPING_EXISTS"
        if execution_outcome == "INTERNAL_ONLY_REMAINS"
        else "RETIRE_QM_STAT_EXTERNAL_PATH_CANDIDATE_AND_DO_NOT_LOOP"
    )

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "packet_ready": packet_ready,
            "comparator_ready": comparator_ready,
            "mapping_evaluable": mapping_evaluable,
            "path_falsification_observed": path_falsification_observed,
            "no_loop_rule_declared": str(execution_contract.get("no_loop_rule", "")).strip()
            == "ONE_QM_STAT_EXTERNAL_PATH_SIGNAL_EXECUTION_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": execution_outcome
                in {"EXTERNAL_PATH_SIGNAL_PRODUCED", "PATH_FALSIFIED", "INTERNAL_ONLY_REMAINS"},
                "packet_ready": packet_ready,
                "comparator_ready": comparator_ready,
                "execution_classification_bounded": True,
            },
            "inputs": {
                "packet_outcome": packet_outcome,
                "comparator_status": comparator_status,
                "candidate_mapping_status": candidate_mapping_status,
                "interpretation": interpretation_value,
                "probe_signal": probe_signal,
                "path_falsification_observed": path_falsification_observed,
                "allowed_outcomes": execution_contract.get("allowed_outcomes", []),
                "success_rule": execution_contract.get("success_rule"),
                "path_falsification_rule": execution_contract.get("path_falsification_rule"),
                "failure_rule": execution_contract.get("failure_rule"),
                "no_loop_rule": execution_contract.get("no_loop_rule"),
            },
            "summary": {
                "all_criteria_satisfied": packet_ready and comparator_ready,
                "phase_status": "COMPLETE" if packet_ready and comparator_ready else "INCOMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "execution_outcome": execution_outcome,
            "classification_reason": classification_reason,
            "packet_outcome": packet_outcome,
            "baseline_comparator_status": comparator_status,
            "candidate_mapping_status": candidate_mapping_status,
            "interpretation": interpretation_value,
            "probe_signal": probe_signal,
            "path_falsification_observed": path_falsification_observed,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "qm_stat_external_path_signal_packet_report": _ptr(packet_path),
            "qm_stat_single_baseline_comparator_report": _ptr(comparator_path),
            "qm_stat_discovery_interpretation_report": _ptr(interpretation_path),
            "qm_stat_discovery_numerical_probe_execution_report": _ptr(probe_execution_path),
        },
        "non_claim_boundary": "Repository-local QM-STAT external-path signal execution report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the QM-STAT external-path signal execution report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "qm_stat_external_path_signal_execution_20260411_v0.json",
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
        "qm_stat_external_path_signal_execution_report: "
        f"execution_outcome={payload['summary']['execution_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

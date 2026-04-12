from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_CLOSED_LANE_REOPEN_ELIGIBILITY_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "SCIENCE_CLOSED_LANE_REOPEN_ELIGIBILITY_20260412_v0.json"
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


def _normalized(value: str) -> str:
    return value.strip().upper().replace("_", "-")


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    eligibility_policy = dict(declaration.get("eligibility_policy", {}))
    eligibility_contract = dict(declaration.get("eligibility_contract", {}))

    formalization_path = REPO_ROOT / str(required_inputs.get("probe_readiness_standard_formalization_report", "")).strip()
    shared_path = REPO_ROOT / str(required_inputs.get("shared_model_class_post_refinement_decision_report", "")).strip()
    qft_gr_path = REPO_ROOT / str(required_inputs.get("qft_gr_post_refinement_decision_report", "")).strip()
    gr_path = REPO_ROOT / str(required_inputs.get("gr_row_001_structural_gap_definition_report", "")).strip()
    em_qft_path = REPO_ROOT / str(required_inputs.get("em_qft_higher_level_structure_review_report", "")).strip()
    qm_stat_path = REPO_ROOT / str(required_inputs.get("bridge_external_validation_policy_review_report", "")).strip()

    formalization = _read_json(formalization_path)
    shared = _read_json(shared_path)
    qft_gr = _read_json(qft_gr_path)
    gr = _read_json(gr_path)
    em_qft = _read_json(em_qft_path)
    qm_stat = _read_json(qm_stat_path)

    formalization_outcome = str(dict(formalization.get("summary", {})).get("terminal_outcome", "")).strip()
    shared_outcome = str(dict(shared.get("summary", {})).get("terminal_outcome", "")).strip()
    qft_gr_outcome = str(dict(qft_gr.get("summary", {})).get("terminal_outcome", "")).strip()
    gr_outcome = str(dict(gr.get("summary", {})).get("terminal_outcome", "")).strip()
    em_qft_outcome = str(dict(em_qft.get("summary", {})).get("terminal_outcome", "")).strip()
    qm_stat_outcome = str(dict(qm_stat.get("summary", {})).get("review_outcome", "")).strip()

    required_formalization_outcome = str(eligibility_policy.get("required_formalization_outcome", "")).strip()
    required_shared_outcome = str(eligibility_policy.get("required_shared_model_class_closed_outcome", "")).strip()
    required_qft_gr_outcome = str(eligibility_policy.get("required_qft_gr_closed_outcome", "")).strip()
    required_gr_outcome = str(eligibility_policy.get("required_gr_closed_outcome", "")).strip()
    required_em_qft_outcome = str(eligibility_policy.get("required_em_qft_closed_outcome", "")).strip()
    required_qm_stat_outcome = str(eligibility_policy.get("required_qm_stat_closed_outcome", "")).strip()

    selected_reopen_lane = str(eligibility_policy.get("selected_reopen_lane", "NONE")).strip()
    selected_reopen_lane_proof_declared = bool(eligibility_policy.get("selected_reopen_lane_proof_declared", False))

    preconditions_ok = (
        formalization_outcome == required_formalization_outcome
        and shared_outcome == required_shared_outcome
        and qft_gr_outcome == required_qft_gr_outcome
        and gr_outcome == required_gr_outcome
        and em_qft_outcome == required_em_qft_outcome
        and qm_stat_outcome == required_qm_stat_outcome
    )

    lane_status = {
        "SHARED-MODEL-CLASS": shared_outcome,
        "QFT-GR": qft_gr_outcome,
        "GR-ROW-001": gr_outcome,
        "EM-QFT": em_qft_outcome,
        "QM-STAT": qm_stat_outcome,
    }

    eligible_lanes: list[str] = []

    selected_norm = _normalized(selected_reopen_lane)
    selected_is_none = selected_norm in {"NONE", "UNSET", ""}

    allowed_outcomes = set(eligibility_contract.get("allowed_outcomes", []))
    default_outcome = str(
        eligibility_contract.get("default_outcome", "CLOSED_LANE_REOPEN_EVIDENCE_INCOMPLETE")
    ).strip()

    if not preconditions_ok:
        terminal_outcome = "CLOSED_LANE_REOPEN_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_FORMALIZATION_OR_CLOSED_LANE_PRECONDITIONS"
    elif selected_is_none and len(eligible_lanes) == 0:
        terminal_outcome = "CLOSED_LANE_REOPEN_NONE_ELIGIBLE"
        next_action = "MAINTAIN_CLOSED_LANES_AND_CONTINUE_POLICY_LANE_REFINEMENT"
    elif not selected_is_none and selected_norm not in lane_status:
        terminal_outcome = "CLOSED_LANE_REOPEN_CONTRACT_VIOLATION"
        next_action = "SELECT_VALID_CLOSED_LANE_OR_NONE"
    elif not selected_is_none and not selected_reopen_lane_proof_declared:
        terminal_outcome = "CLOSED_LANE_REOPEN_EVIDENCE_INCOMPLETE"
        next_action = "DECLARE_SELECTED_REOPEN_LANE_PROOF"
    elif not selected_is_none and selected_norm in lane_status and selected_reopen_lane_proof_declared:
        terminal_outcome = "CLOSED_LANE_REOPEN_ONE_LANE_AUTHORIZED"
        next_action = "OPEN_ONE_BOUNDED_REENTRY_EXECUTION_LAYER_FOR_SELECTED_LANE"
    else:
        terminal_outcome = "CLOSED_LANE_REOPEN_EVIDENCE_INCOMPLETE"
        next_action = "REVIEW_REOPEN_ELIGIBILITY_CONFIGURATION"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "formalization_outcome_match": formalization_outcome == required_formalization_outcome,
            "shared_model_class_closed_match": shared_outcome == required_shared_outcome,
            "qft_gr_closed_match": qft_gr_outcome == required_qft_gr_outcome,
            "gr_closed_match": gr_outcome == required_gr_outcome,
            "em_qft_closed_match": em_qft_outcome == required_em_qft_outcome,
            "qm_stat_closed_match": qm_stat_outcome == required_qm_stat_outcome,
            "single_terminal_outcome_rule_declared": str(
                eligibility_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_SCIENCE_CLOSED_LANE_REOPEN_ELIGIBILITY_OUTCOME",
            "no_loop_rule_declared": str(eligibility_contract.get("no_loop_rule", "")).strip()
            == "ONE_SCIENCE_CLOSED_LANE_REOPEN_ELIGIBILITY_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "eligibility_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "formalization_outcome": formalization_outcome,
                "required_formalization_outcome": required_formalization_outcome,
                "shared_model_class_outcome": shared_outcome,
                "qft_gr_outcome": qft_gr_outcome,
                "gr_outcome": gr_outcome,
                "em_qft_outcome": em_qft_outcome,
                "qm_stat_outcome": qm_stat_outcome,
                "selected_reopen_lane": selected_reopen_lane,
                "selected_reopen_lane_proof_declared": selected_reopen_lane_proof_declared,
                "eligible_lanes": eligible_lanes,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "reopen_eligibility": {
            "selected_reopen_lane": selected_reopen_lane,
            "selected_reopen_lane_proof_declared": selected_reopen_lane_proof_declared,
            "eligible_lanes": eligible_lanes,
            "authorization_mode": str(eligibility_policy.get("authorization_mode", "AT_MOST_ONE")).strip(),
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "next_action": next_action,
            "single_layer_only": bool(eligibility_policy.get("single_layer_only", True)),
            "single_outcome_only": bool(eligibility_policy.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "probe_readiness_standard_formalization_report": _ptr(formalization_path),
            "shared_model_class_post_refinement_decision_report": _ptr(shared_path),
            "qft_gr_post_refinement_decision_report": _ptr(qft_gr_path),
            "gr_row_001_structural_gap_definition_report": _ptr(gr_path),
            "em_qft_higher_level_structure_review_report": _ptr(em_qft_path),
            "bridge_external_validation_policy_review_report": _ptr(qm_stat_path),
        },
        "non_claim_boundary": "Repository-local closed-lane reopen-eligibility report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate closed-lane reopen-eligibility report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "science_closed_lane_reopen_eligibility_20260412_v0.json",
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
        "science_closed_lane_reopen_eligibility_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

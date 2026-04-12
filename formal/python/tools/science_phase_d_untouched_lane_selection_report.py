from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_PHASE_D_UNTOUCHED_LANE_SELECTION_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "SCIENCE_PHASE_D_UNTOUCHED_LANE_SELECTION_20260412_v0.json"
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


def _norm(value: str) -> str:
    return value.strip().upper().replace("_", "-")


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    selection_policy = dict(declaration.get("selection_policy", {}))
    selection_contract = dict(declaration.get("selection_contract", {}))

    reopen_path = REPO_ROOT / str(required_inputs.get("science_closed_lane_reopen_eligibility_report", "")).strip()
    formalization_path = REPO_ROOT / str(required_inputs.get("probe_readiness_standard_formalization_report", "")).strip()
    synthesis_path = REPO_ROOT / str(required_inputs.get("science_common_failure_modes_synthesis_report", "")).strip()

    reopen = _read_json(reopen_path)
    formalization = _read_json(formalization_path)
    synthesis = _read_json(synthesis_path)

    reopen_outcome = str(dict(reopen.get("summary", {})).get("terminal_outcome", "")).strip()
    formalization_outcome = str(dict(formalization.get("summary", {})).get("terminal_outcome", "")).strip()
    synthesis_outcome = str(dict(synthesis.get("summary", {})).get("terminal_outcome", "")).strip()

    required_reopen_outcome = str(selection_policy.get("required_reopen_eligibility_outcome", "")).strip()
    required_formalization_outcome = str(selection_policy.get("required_formalization_outcome", "")).strip()
    required_synthesis_outcome = str(selection_policy.get("required_synthesis_outcome", "")).strip()

    candidate_lane = str(selection_policy.get("untouched_lane_candidate_id", "")).strip()
    candidate_proof = bool(selection_policy.get("untouched_lane_non_consumption_proof_declared", False))
    consumed_aliases = list(selection_policy.get("consumed_lane_aliases", []))
    consumed_norm = {_norm(x) for x in consumed_aliases}
    candidate_is_consumed = _norm(candidate_lane) in consumed_norm

    preconditions_ok = (
        reopen_outcome == required_reopen_outcome
        and formalization_outcome == required_formalization_outcome
        and synthesis_outcome == required_synthesis_outcome
    )

    allowed_outcomes = set(selection_contract.get("allowed_outcomes", []))
    default_outcome = str(
        selection_contract.get("default_outcome", "UNTOUCHED_LANE_SELECTION_EVIDENCE_INCOMPLETE")
    ).strip()

    if not preconditions_ok:
        terminal_outcome = "UNTOUCHED_LANE_SELECTION_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_PHASE_D_PRECONDITIONS_AND_RERUN_SELECTION"
    elif not candidate_lane:
        terminal_outcome = "UNTOUCHED_LANE_SELECTION_EVIDENCE_INCOMPLETE"
        next_action = "DECLARE_UNTOUCHED_LANE_CANDIDATE"
    elif candidate_is_consumed:
        terminal_outcome = "UNTOUCHED_LANE_SELECTION_BLOCKED_CONSUMED_ALIAS"
        next_action = "CHOOSE_NON_CONSUMED_UNTOUCHED_LANE"
    elif not candidate_proof:
        terminal_outcome = "HOLD_PENDING_UNTOUCHED_CANDIDATE_REPAIR"
        next_action = "DECLARE_NON_CONSUMPTION_PROOF_FOR_CANDIDATE"
    else:
        terminal_outcome = "UNTOUCHED_LANE_SELECTED_FOR_BOUNDED_FIRST_TEST"
        next_action = "OPEN_ONE_BOUNDED_FIRST_TEST_PACKET_FOR_UNTOUCHED_LANE"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "reopen_eligibility_outcome_match": reopen_outcome == required_reopen_outcome,
            "formalization_outcome_match": formalization_outcome == required_formalization_outcome,
            "synthesis_outcome_match": synthesis_outcome == required_synthesis_outcome,
            "candidate_not_consumed": not candidate_is_consumed,
            "candidate_non_consumption_proof_declared": candidate_proof,
            "single_terminal_outcome_rule_declared": str(
                selection_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_SCIENCE_PHASE_D_UNTOUCHED_LANE_SELECTION_OUTCOME",
            "no_loop_rule_declared": str(selection_contract.get("no_loop_rule", "")).strip()
            == "ONE_SCIENCE_PHASE_D_UNTOUCHED_LANE_SELECTION_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "selection_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "reopen_eligibility_outcome": reopen_outcome,
                "required_reopen_eligibility_outcome": required_reopen_outcome,
                "formalization_outcome": formalization_outcome,
                "required_formalization_outcome": required_formalization_outcome,
                "synthesis_outcome": synthesis_outcome,
                "required_synthesis_outcome": required_synthesis_outcome,
                "untouched_lane_candidate_id": candidate_lane,
                "untouched_lane_non_consumption_proof_declared": candidate_proof,
                "consumed_lane_aliases": consumed_aliases,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "untouched_lane_candidate_id": candidate_lane,
            "next_action": next_action,
            "single_layer_only": bool(selection_policy.get("single_layer_only", True)),
            "single_outcome_only": bool(selection_policy.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "science_closed_lane_reopen_eligibility_report": _ptr(reopen_path),
            "probe_readiness_standard_formalization_report": _ptr(formalization_path),
            "science_common_failure_modes_synthesis_report": _ptr(synthesis_path),
        },
        "non_claim_boundary": "Repository-local untouched-lane selection report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate Phase D untouched-lane selection report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "science_phase_d_untouched_lane_selection_20260412_v0.json",
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
        "science_phase_d_untouched_lane_selection_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

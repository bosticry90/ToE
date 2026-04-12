from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SHARED_MODEL_CLASS_POST_SIGNAL_INTERPRETATION_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "SHARED_MODEL_CLASS_POST_SIGNAL_INTERPRETATION_20260412_v0.json"
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
    interpretation_policy = dict(declaration.get("interpretation_policy", {}))
    interpretation_contract = dict(declaration.get("interpretation_contract", {}))

    first_test_path = REPO_ROOT / str(
        required_inputs.get("shared_model_class_first_bounded_test_packet_report", "")
    ).strip()
    proposal_path = REPO_ROOT / str(
        required_inputs.get("shared_model_class_program_proposal_report", "")
    ).strip()
    gr_path = REPO_ROOT / str(required_inputs.get("gr_row_001_structural_gap_definition_report", "")).strip()
    em_qft_path = REPO_ROOT / str(required_inputs.get("em_qft_higher_level_structure_review_report", "")).strip()
    qm_stat_path = REPO_ROOT / str(required_inputs.get("bridge_external_validation_policy_review_report", "")).strip()

    first_test = _read_json(first_test_path)
    proposal = _read_json(proposal_path)
    gr = _read_json(gr_path)
    em_qft = _read_json(em_qft_path)
    qm_stat = _read_json(qm_stat_path)

    first_test_outcome = str(dict(first_test.get("summary", {})).get("terminal_outcome", "")).strip()
    first_test_next_action = str(dict(first_test.get("summary", {})).get("next_action", "")).strip()
    proposal_outcome = str(dict(proposal.get("summary", {})).get("terminal_outcome", "")).strip()
    gr_outcome = str(dict(gr.get("summary", {})).get("terminal_outcome", "")).strip()
    gr_frozen = bool(dict(gr.get("summary", {})).get("row_001_attack_class_cycling_frozen", False))
    em_qft_outcome = str(dict(em_qft.get("summary", {})).get("terminal_outcome", "")).strip()
    em_qft_frozen = bool(dict(em_qft.get("summary", {})).get("em_qft_attack_class_cycling_frozen", False))
    qm_stat_outcome = str(dict(qm_stat.get("summary", {})).get("review_outcome", "")).strip()

    required_first_test_outcome = str(interpretation_policy.get("required_first_test_outcome", "")).strip()
    required_first_test_next_action = str(interpretation_policy.get("required_first_test_next_action", "")).strip()
    required_proposal_outcome = str(interpretation_policy.get("required_proposal_outcome", "")).strip()
    qm_stat_required_review_outcome = str(interpretation_policy.get("qm_stat_required_review_outcome", "")).strip()
    gr_required_outcome = str(interpretation_policy.get("gr_required_outcome", "")).strip()
    em_qft_required_outcome = str(interpretation_policy.get("em_qft_required_outcome", "")).strip()

    signal_internal_coherence = bool(interpretation_policy.get("signal_internal_coherence", False))
    external_comparator_candidate_ready = bool(
        interpretation_policy.get("external_comparator_candidate_ready", False)
    )
    probe_readiness_ready = bool(interpretation_policy.get("probe_readiness_ready", False))
    signal_strength_sufficient = bool(interpretation_policy.get("signal_strength_sufficient", False))

    preconditions_ok = (
        first_test_outcome == required_first_test_outcome
        and first_test_next_action == required_first_test_next_action
        and proposal_outcome == required_proposal_outcome
        and qm_stat_outcome == qm_stat_required_review_outcome
        and gr_outcome == gr_required_outcome
        and em_qft_outcome == em_qft_required_outcome
        and gr_frozen
        and em_qft_frozen
    )

    allowed_outcomes = set(interpretation_contract.get("allowed_outcomes", []))
    default_outcome = str(
        interpretation_contract.get("default_outcome", "SHARED_MODEL_CLASS_SIGNAL_INSUFFICIENT_HOLD")
    ).strip()

    if not preconditions_ok:
        terminal_outcome = "SHARED_MODEL_CLASS_SIGNAL_INSUFFICIENT_HOLD"
        next_action = "RESTORE_POST_SIGNAL_INTERPRETATION_PRECONDITIONS"
    elif not signal_strength_sufficient:
        terminal_outcome = "SHARED_MODEL_CLASS_SIGNAL_INSUFFICIENT_HOLD"
        next_action = "HOLD_AND_RESTRICT_EXPANSION"
    elif probe_readiness_ready:
        terminal_outcome = "SHARED_MODEL_CLASS_PROBE_READY"
        next_action = "OPEN_ONE_BOUNDED_PROBE_READINESS_EXECUTION_LAYER"
    elif signal_internal_coherence and external_comparator_candidate_ready:
        terminal_outcome = "SHARED_MODEL_CLASS_EXTERNALLY_COMPARABLE_CANDIDATE"
        next_action = "OPEN_ONE_BOUNDED_COMPARATOR_BINDING_STEP"
    elif signal_internal_coherence:
        terminal_outcome = "SHARED_MODEL_CLASS_INTERNAL_SIGNAL_ONLY"
        next_action = "OPEN_INTERNAL_SIGNAL_STRENGTHENING_STEP"
    else:
        terminal_outcome = "SHARED_MODEL_CLASS_SIGNAL_INSUFFICIENT_HOLD"
        next_action = "HOLD_AND_RESTRICT_EXPANSION"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "first_test_outcome_match": first_test_outcome == required_first_test_outcome,
            "first_test_next_action_match": first_test_next_action == required_first_test_next_action,
            "proposal_outcome_match": proposal_outcome == required_proposal_outcome,
            "qm_stat_parked_match": qm_stat_outcome == qm_stat_required_review_outcome,
            "gr_frozen_match": gr_outcome == gr_required_outcome and gr_frozen,
            "em_qft_frozen_match": em_qft_outcome == em_qft_required_outcome and em_qft_frozen,
            "signal_internal_coherence": signal_internal_coherence,
            "external_comparator_candidate_ready": external_comparator_candidate_ready,
            "probe_readiness_ready": probe_readiness_ready,
            "single_terminal_outcome_rule_declared": str(
                interpretation_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_SHARED_MODEL_CLASS_POST_SIGNAL_INTERPRETATION_OUTCOME",
            "no_loop_rule_declared": str(interpretation_contract.get("no_loop_rule", "")).strip()
            == "ONE_SHARED_MODEL_CLASS_POST_SIGNAL_INTERPRETATION_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "interpretation_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "first_test_outcome": first_test_outcome,
                "required_first_test_outcome": required_first_test_outcome,
                "first_test_next_action": first_test_next_action,
                "required_first_test_next_action": required_first_test_next_action,
                "proposal_outcome": proposal_outcome,
                "required_proposal_outcome": required_proposal_outcome,
                "qm_stat_outcome": qm_stat_outcome,
                "qm_stat_required_review_outcome": qm_stat_required_review_outcome,
                "gr_outcome": gr_outcome,
                "gr_required_outcome": gr_required_outcome,
                "gr_frozen": gr_frozen,
                "em_qft_outcome": em_qft_outcome,
                "em_qft_required_outcome": em_qft_required_outcome,
                "em_qft_frozen": em_qft_frozen,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "next_action": next_action,
            "single_layer_only": bool(interpretation_policy.get("single_layer_only", True)),
            "single_outcome_only": bool(interpretation_policy.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "shared_model_class_first_bounded_test_packet_report": _ptr(first_test_path),
            "shared_model_class_program_proposal_report": _ptr(proposal_path),
            "gr_row_001_structural_gap_definition_report": _ptr(gr_path),
            "em_qft_higher_level_structure_review_report": _ptr(em_qft_path),
            "bridge_external_validation_policy_review_report": _ptr(qm_stat_path),
        },
        "non_claim_boundary": "Repository-local shared model-class post-signal interpretation report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate shared model-class post-signal interpretation report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "shared_model_class_post_signal_interpretation_20260412_v0.json",
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
        "shared_model_class_post_signal_interpretation_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SHARED_MODEL_CLASS_FIRST_BOUNDED_TEST_PACKET_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "SHARED_MODEL_CLASS_FIRST_BOUNDED_TEST_PACKET_20260412_v0.json"
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
    test_policy = dict(declaration.get("test_policy", {}))
    packet_contract = dict(declaration.get("packet_contract", {}))

    proposal_path = REPO_ROOT / str(required_inputs.get("shared_model_class_program_proposal_report", "")).strip()
    gr_path = REPO_ROOT / str(required_inputs.get("gr_row_001_structural_gap_definition_report", "")).strip()
    em_qft_path = REPO_ROOT / str(required_inputs.get("em_qft_higher_level_structure_review_report", "")).strip()
    qm_stat_path = REPO_ROOT / str(required_inputs.get("bridge_external_validation_policy_review_report", "")).strip()

    proposal = _read_json(proposal_path)
    gr = _read_json(gr_path)
    em_qft = _read_json(em_qft_path)
    qm_stat = _read_json(qm_stat_path)

    proposal_outcome = str(dict(proposal.get("summary", {})).get("terminal_outcome", "")).strip()
    proposal_next_action = str(dict(proposal.get("summary", {})).get("next_action", "")).strip()
    proposal_components = list(dict(proposal.get("proposal_payload", {})).get("minimum_model_class_components", []))

    gr_outcome = str(dict(gr.get("summary", {})).get("terminal_outcome", "")).strip()
    gr_frozen = bool(dict(gr.get("summary", {})).get("row_001_attack_class_cycling_frozen", False))
    em_qft_outcome = str(dict(em_qft.get("summary", {})).get("terminal_outcome", "")).strip()
    em_qft_frozen = bool(dict(em_qft.get("summary", {})).get("em_qft_attack_class_cycling_frozen", False))
    qm_stat_outcome = str(dict(qm_stat.get("summary", {})).get("review_outcome", "")).strip()

    required_proposal_outcome = str(test_policy.get("required_proposal_outcome", "")).strip()
    required_proposal_next_action = str(test_policy.get("required_proposal_next_action", "")).strip()
    qm_stat_required_review_outcome = str(test_policy.get("qm_stat_required_review_outcome", "")).strip()
    gr_required_outcome = str(test_policy.get("gr_required_outcome", "")).strip()
    em_qft_required_outcome = str(test_policy.get("em_qft_required_outcome", "")).strip()

    bound_minimum_components = list(test_policy.get("bound_minimum_components", []))
    tested_shared_structure = str(test_policy.get("tested_shared_structure", "")).strip()
    bounded_success_signal = str(test_policy.get("bounded_success_signal", "")).strip()

    shared_structure_declared = bool(test_policy.get("shared_structure_declared", False))
    touches_required_frozen_lanes = bool(test_policy.get("touches_required_frozen_lanes", False))
    comparator_binding_materialized = bool(test_policy.get("comparator_binding_materialized", False))
    movement_signal_detected = bool(test_policy.get("movement_signal_detected", False))
    valid_but_nonmoving = bool(test_policy.get("valid_but_nonmoving", False))
    requires_undeclared_structure = bool(test_policy.get("requires_undeclared_structure", False))
    path_falsified = bool(test_policy.get("path_falsified", False))

    components_aligned_with_proposal = all(component in proposal_components for component in bound_minimum_components)

    preconditions_ok = (
        proposal_outcome == required_proposal_outcome
        and proposal_next_action == required_proposal_next_action
        and qm_stat_outcome == qm_stat_required_review_outcome
        and gr_outcome == gr_required_outcome
        and em_qft_outcome == em_qft_required_outcome
        and gr_frozen
        and em_qft_frozen
    )

    allowed_outcomes = set(packet_contract.get("allowed_outcomes", []))
    default_outcome = str(
        packet_contract.get("default_outcome", "SHARED_MODEL_CLASS_REQUIRES_UNDECLARED_STRUCTURE")
    ).strip()

    if not preconditions_ok:
        terminal_outcome = "SHARED_MODEL_CLASS_PATH_FALSIFIED"
        next_action = "RESTORE_SHARED_MODEL_CLASS_PACKET_PRECONDITIONS"
    elif path_falsified:
        terminal_outcome = "SHARED_MODEL_CLASS_PATH_FALSIFIED"
        next_action = "CLOSE_SHARED_MODEL_CLASS_PATH_AND_REASSESS"
    elif requires_undeclared_structure:
        terminal_outcome = "SHARED_MODEL_CLASS_REQUIRES_UNDECLARED_STRUCTURE"
        next_action = "DECLARE_MISSING_SHARED_STRUCTURE_BEFORE_NEXT_PACKET"
    elif (
        shared_structure_declared
        and touches_required_frozen_lanes
        and comparator_binding_materialized
        and components_aligned_with_proposal
        and movement_signal_detected
    ):
        terminal_outcome = "SHARED_MODEL_CLASS_SIGNAL_PRODUCED"
        next_action = "OPEN_POST_SIGNAL_INTERPRETATION_LAYER"
    elif (
        shared_structure_declared
        and touches_required_frozen_lanes
        and comparator_binding_materialized
        and components_aligned_with_proposal
        and valid_but_nonmoving
    ):
        terminal_outcome = "SHARED_MODEL_CLASS_VALID_BUT_NONMOVING"
        next_action = "OPEN_POST_FIRST_TEST_DECISION_LAYER"
    else:
        terminal_outcome = "SHARED_MODEL_CLASS_REQUIRES_UNDECLARED_STRUCTURE"
        next_action = "DECLARE_MISSING_SHARED_STRUCTURE_BEFORE_NEXT_PACKET"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "proposal_alignment_match": proposal_outcome == required_proposal_outcome,
            "proposal_next_action_match": proposal_next_action == required_proposal_next_action,
            "qm_stat_parked_match": qm_stat_outcome == qm_stat_required_review_outcome,
            "gr_frozen_match": gr_outcome == gr_required_outcome and gr_frozen,
            "em_qft_frozen_match": em_qft_outcome == em_qft_required_outcome and em_qft_frozen,
            "components_aligned_with_proposal": components_aligned_with_proposal,
            "shared_structure_declared": shared_structure_declared,
            "touches_required_frozen_lanes": touches_required_frozen_lanes,
            "comparator_binding_materialized": comparator_binding_materialized,
            "single_terminal_outcome_rule_declared": str(
                packet_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_SHARED_MODEL_CLASS_FIRST_TEST_OUTCOME",
            "no_loop_rule_declared": str(packet_contract.get("no_loop_rule", "")).strip()
            == "ONE_SHARED_MODEL_CLASS_FIRST_TEST_PACKET_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "packet_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "proposal_outcome": proposal_outcome,
                "required_proposal_outcome": required_proposal_outcome,
                "proposal_next_action": proposal_next_action,
                "required_proposal_next_action": required_proposal_next_action,
                "qm_stat_outcome": qm_stat_outcome,
                "qm_stat_required_review_outcome": qm_stat_required_review_outcome,
                "gr_outcome": gr_outcome,
                "gr_required_outcome": gr_required_outcome,
                "gr_frozen": gr_frozen,
                "em_qft_outcome": em_qft_outcome,
                "em_qft_required_outcome": em_qft_required_outcome,
                "em_qft_frozen": em_qft_frozen,
                "tested_shared_structure": tested_shared_structure,
                "bounded_success_signal": bounded_success_signal,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "packet_payload": {
            "tested_shared_structure": tested_shared_structure,
            "bound_minimum_components": bound_minimum_components,
            "bounded_success_signal": bounded_success_signal,
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "next_action": next_action,
            "single_packet_only": bool(test_policy.get("single_packet_only", True)),
            "single_outcome_only": bool(test_policy.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "shared_model_class_program_proposal_report": _ptr(proposal_path),
            "gr_row_001_structural_gap_definition_report": _ptr(gr_path),
            "em_qft_higher_level_structure_review_report": _ptr(em_qft_path),
            "bridge_external_validation_policy_review_report": _ptr(qm_stat_path),
        },
        "non_claim_boundary": "Repository-local shared model-class first bounded test packet report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate shared model-class first bounded test packet report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "shared_model_class_first_bounded_test_packet_20260412_v0.json",
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
        "shared_model_class_first_bounded_test_packet_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

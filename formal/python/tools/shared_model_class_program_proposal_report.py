from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SHARED_MODEL_CLASS_PROGRAM_PROPOSAL_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "SHARED_MODEL_CLASS_PROGRAM_PROPOSAL_20260412_v0.json"
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
    proposal_policy = dict(declaration.get("proposal_policy", {}))
    proposal_contract = dict(declaration.get("proposal_contract", {}))

    convergence_path = REPO_ROOT / str(
        required_inputs.get("science_post_multi_lane_structure_convergence_review_report", "")
    ).strip()
    gr_path = REPO_ROOT / str(required_inputs.get("gr_row_001_structural_gap_definition_report", "")).strip()
    em_qft_path = REPO_ROOT / str(required_inputs.get("em_qft_higher_level_structure_review_report", "")).strip()
    qm_stat_path = REPO_ROOT / str(required_inputs.get("bridge_external_validation_policy_review_report", "")).strip()

    convergence = _read_json(convergence_path)
    gr = _read_json(gr_path)
    em_qft = _read_json(em_qft_path)
    qm_stat = _read_json(qm_stat_path)

    convergence_outcome = str(dict(convergence.get("summary", {})).get("terminal_outcome", "")).strip()
    gr_outcome = str(dict(gr.get("summary", {})).get("terminal_outcome", "")).strip()
    gr_frozen = bool(dict(gr.get("summary", {})).get("row_001_attack_class_cycling_frozen", False))
    em_qft_outcome = str(dict(em_qft.get("summary", {})).get("terminal_outcome", "")).strip()
    em_qft_frozen = bool(dict(em_qft.get("summary", {})).get("em_qft_attack_class_cycling_frozen", False))
    qm_stat_outcome = str(dict(qm_stat.get("summary", {})).get("review_outcome", "")).strip()

    required_convergence_outcome = str(proposal_policy.get("required_convergence_outcome", "")).strip()
    qm_stat_required_review_outcome = str(proposal_policy.get("qm_stat_required_review_outcome", "")).strip()
    gr_required_outcome = str(proposal_policy.get("gr_required_outcome", "")).strip()
    em_qft_required_outcome = str(proposal_policy.get("em_qft_required_outcome", "")).strip()

    shared_missing_structure = list(proposal_policy.get("shared_missing_structure", []))
    single_shared_model_class_can_cover = bool(
        proposal_policy.get("single_shared_model_class_can_cover_gr_and_em_qft", False)
    )
    minimum_components = list(proposal_policy.get("minimum_model_class_components", []))
    first_bounded_test_packet = dict(proposal_policy.get("first_bounded_test_packet", {}))
    policy_ready_for_proposal = bool(proposal_policy.get("policy_ready_for_proposal", False))

    preconditions_ok = (
        convergence_outcome == required_convergence_outcome
        and qm_stat_outcome == qm_stat_required_review_outcome
        and gr_outcome == gr_required_outcome
        and em_qft_outcome == em_qft_required_outcome
        and gr_frozen
        and em_qft_frozen
    )

    has_shared_missing_structure = len(shared_missing_structure) > 0
    has_minimum_components = len(minimum_components) > 0
    has_first_bounded_test = all(
        str(first_bounded_test_packet.get(key, "")).strip()
        for key in ("packet_id", "target", "acceptance_gate")
    )

    allowed_outcomes = set(proposal_contract.get("allowed_outcomes", []))
    default_outcome = str(
        proposal_contract.get("default_outcome", "HOLD_AND_DO_NOT_OPEN_MODEL_CLASS_PROGRAM_YET")
    ).strip()

    if not preconditions_ok:
        terminal_outcome = "HOLD_AND_DO_NOT_OPEN_MODEL_CLASS_PROGRAM_YET"
        next_action = "RESTORE_CONVERGENCE_AND_LANE_STATE_PRECONDITIONS"
    elif not policy_ready_for_proposal:
        terminal_outcome = "HIGHER_LEVEL_POLICY_REQUIRED_BEFORE_PROPOSAL"
        next_action = "OPEN_HIGHER_LEVEL_POLICY_ALIGNMENT_LAYER"
    elif (
        single_shared_model_class_can_cover
        and has_shared_missing_structure
        and has_minimum_components
        and has_first_bounded_test
    ):
        terminal_outcome = "SHARED_MODEL_CLASS_PROPOSAL_JUSTIFIED"
        next_action = "OPEN_SHARED_MODEL_CLASS_FIRST_BOUNDED_TEST_PACKET_LAYER"
    elif has_shared_missing_structure:
        terminal_outcome = "SEPARATE_MODEL_CLASS_PROPOSALS_REQUIRED"
        next_action = "OPEN_SEPARATE_GR_AND_EM_QFT_MODEL_CLASS_PROPOSAL_LAYERS"
    else:
        terminal_outcome = "HOLD_AND_DO_NOT_OPEN_MODEL_CLASS_PROGRAM_YET"
        next_action = "REFINE_SHARED_STRUCTURE_EVIDENCE_BEFORE_PROPOSAL"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "convergence_match": convergence_outcome == required_convergence_outcome,
            "qm_stat_parked_match": qm_stat_outcome == qm_stat_required_review_outcome,
            "gr_frozen_match": gr_outcome == gr_required_outcome and gr_frozen,
            "em_qft_frozen_match": em_qft_outcome == em_qft_required_outcome and em_qft_frozen,
            "shared_missing_structure_present": has_shared_missing_structure,
            "minimum_components_declared": has_minimum_components,
            "first_bounded_test_declared": has_first_bounded_test,
            "single_terminal_outcome_rule_declared": str(
                proposal_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_SHARED_MODEL_CLASS_PROPOSAL_OUTCOME",
            "no_loop_rule_declared": str(proposal_contract.get("no_loop_rule", "")).strip()
            == "ONE_SHARED_MODEL_CLASS_PROPOSAL_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "proposal_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "convergence_outcome": convergence_outcome,
                "required_convergence_outcome": required_convergence_outcome,
                "qm_stat_outcome": qm_stat_outcome,
                "qm_stat_required_review_outcome": qm_stat_required_review_outcome,
                "gr_outcome": gr_outcome,
                "gr_required_outcome": gr_required_outcome,
                "gr_frozen": gr_frozen,
                "em_qft_outcome": em_qft_outcome,
                "em_qft_required_outcome": em_qft_required_outcome,
                "em_qft_frozen": em_qft_frozen,
                "single_shared_model_class_can_cover_gr_and_em_qft": single_shared_model_class_can_cover,
                "policy_ready_for_proposal": policy_ready_for_proposal,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "proposal_payload": {
            "shared_missing_structure": shared_missing_structure,
            "minimum_model_class_components": minimum_components,
            "first_bounded_test_packet": first_bounded_test_packet,
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "next_action": next_action,
            "single_layer_only": bool(proposal_policy.get("single_layer_only", True)),
            "single_outcome_only": bool(proposal_policy.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "science_post_multi_lane_structure_convergence_review_report": _ptr(convergence_path),
            "gr_row_001_structural_gap_definition_report": _ptr(gr_path),
            "em_qft_higher_level_structure_review_report": _ptr(em_qft_path),
            "bridge_external_validation_policy_review_report": _ptr(qm_stat_path),
        },
        "non_claim_boundary": "Repository-local shared model-class program proposal report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate shared model-class program proposal report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "shared_model_class_program_proposal_20260412_v0.json",
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
        "shared_model_class_program_proposal_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

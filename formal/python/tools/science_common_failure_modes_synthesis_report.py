from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_COMMON_FAILURE_MODES_SYNTHESIS_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "SCIENCE_COMMON_FAILURE_MODES_SYNTHESIS_20260412_v0.json"
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
    synthesis_policy = dict(declaration.get("synthesis_policy", {}))
    taxonomy_contract = dict(declaration.get("failure_mode_taxonomy_contract", {}))

    shared_path = REPO_ROOT / str(required_inputs.get("shared_model_class_post_refinement_decision_report", "")).strip()
    qft_gr_path = REPO_ROOT / str(required_inputs.get("qft_gr_post_refinement_decision_report", "")).strip()
    gr_path = REPO_ROOT / str(required_inputs.get("gr_row_001_structural_gap_definition_report", "")).strip()
    em_qft_path = REPO_ROOT / str(required_inputs.get("em_qft_higher_level_structure_review_report", "")).strip()
    qm_stat_path = REPO_ROOT / str(required_inputs.get("bridge_external_validation_policy_review_report", "")).strip()
    trend_path = REPO_ROOT / str(required_inputs.get("governance_blocker_trend_window_report", "")).strip()
    closure_map_path = REPO_ROOT / str(required_inputs.get("governance_blocker_closure_map_report", "")).strip()
    em_obligation_path = REPO_ROOT / str(
        required_inputs.get("em_qft_interface_alignment_obligation_declaration_report", "")
    ).strip()
    gr_obligation_path = REPO_ROOT / str(
        required_inputs.get("gr_regime_limit_alignment_obligation_declaration_report", "")
    ).strip()

    shared = _read_json(shared_path)
    qft_gr = _read_json(qft_gr_path)
    gr = _read_json(gr_path)
    em_qft = _read_json(em_qft_path)
    qm_stat = _read_json(qm_stat_path)
    trend = _read_json(trend_path)
    closure_map = _read_json(closure_map_path)
    em_obligation = _read_json(em_obligation_path)
    gr_obligation = _read_json(gr_obligation_path)

    shared_outcome = str(dict(shared.get("summary", {})).get("terminal_outcome", "")).strip()
    qft_gr_outcome = str(dict(qft_gr.get("summary", {})).get("terminal_outcome", "")).strip()
    gr_outcome = str(dict(gr.get("summary", {})).get("terminal_outcome", "")).strip()
    gr_frozen = bool(dict(gr.get("summary", {})).get("row_001_attack_class_cycling_frozen", False))
    em_qft_outcome = str(dict(em_qft.get("summary", {})).get("terminal_outcome", "")).strip()
    em_qft_frozen = bool(dict(em_qft.get("summary", {})).get("em_qft_attack_class_cycling_frozen", False))
    qm_stat_outcome = str(dict(qm_stat.get("summary", {})).get("review_outcome", "")).strip()

    trend_status = str(dict(trend.get("trend_summary", {})).get("movement_status", "")).strip()
    trend_net_delta = int(dict(trend.get("blocker_counts", {})).get("net_delta", 0))
    blocker_rows = int(closure_map.get("rows_total", 0))

    em_obligation_outcome = str(dict(em_obligation.get("summary", {})).get("terminal_outcome", "")).strip()
    em_obligation_type = str(dict(em_obligation.get("summary", {})).get("obligation_type", "")).strip()
    gr_obligation_outcome = str(dict(gr_obligation.get("summary", {})).get("terminal_outcome", "")).strip()
    gr_obligation_type = str(dict(gr_obligation.get("summary", {})).get("obligation_type", "")).strip()

    required_shared_outcome = str(synthesis_policy.get("required_shared_model_class_outcome", "")).strip()
    required_qft_gr_outcome = str(synthesis_policy.get("required_qft_gr_outcome", "")).strip()
    required_gr_outcome = str(synthesis_policy.get("required_gr_outcome", "")).strip()
    required_em_qft_outcome = str(synthesis_policy.get("required_em_qft_outcome", "")).strip()
    required_qm_stat_outcome = str(synthesis_policy.get("required_qm_stat_outcome", "")).strip()
    required_trend_status = str(synthesis_policy.get("required_trend_movement_status", "")).strip()
    required_trend_net_delta = int(synthesis_policy.get("required_trend_net_delta", 0))
    required_em_obligation_outcome = str(synthesis_policy.get("required_em_qft_obligation_outcome", "")).strip()
    required_gr_obligation_outcome = str(synthesis_policy.get("required_gr_obligation_outcome", "")).strip()
    required_obligation_type = str(synthesis_policy.get("required_obligation_type", "")).strip()
    minimum_blocker_rows = int(synthesis_policy.get("minimum_blocker_rows", 1))

    policy_lane_required = bool(synthesis_policy.get("policy_lane_required_for_restart", False))
    architecture_review_required = bool(synthesis_policy.get("architecture_review_required", False))

    preconditions_ok = (
        shared_outcome == required_shared_outcome
        and qft_gr_outcome == required_qft_gr_outcome
        and gr_outcome == required_gr_outcome
        and gr_frozen
        and em_qft_outcome == required_em_qft_outcome
        and em_qft_frozen
        and qm_stat_outcome == required_qm_stat_outcome
        and trend_status == required_trend_status
        and trend_net_delta == required_trend_net_delta
        and blocker_rows >= minimum_blocker_rows
        and em_obligation_outcome == required_em_obligation_outcome
        and gr_obligation_outcome == required_gr_obligation_outcome
        and em_obligation_type == required_obligation_type
        and gr_obligation_type == required_obligation_type
    )

    taxonomy = {
        "comparator_residual_tolerance_gap": shared_outcome == required_shared_outcome and qft_gr_outcome == required_qft_gr_outcome,
        "externally_comparable_to_probe_ready_transition_gap": (
            shared_outcome == required_shared_outcome
            and qft_gr_outcome == required_qft_gr_outcome
            and qm_stat_outcome == required_qm_stat_outcome
        ),
        "bridge_interface_obligation_non_discharge": (
            em_obligation_outcome == required_em_obligation_outcome
            and gr_obligation_outcome == required_gr_obligation_outcome
            and em_qft_outcome == required_em_qft_outcome
            and gr_outcome == required_gr_outcome
        ),
        "regime_translation_gap": gr_outcome == required_gr_outcome and trend_net_delta >= 0,
        "proof_debt_plateau": trend_status == required_trend_status and trend_net_delta == required_trend_net_delta,
    }

    required_taxonomy_keys = list(taxonomy_contract.get("required_taxonomy_keys", []))
    taxonomy_complete = all(key in taxonomy for key in required_taxonomy_keys)

    allowed_outcomes = set(taxonomy_contract.get("allowed_outcomes", []))
    default_outcome = str(
        taxonomy_contract.get("default_outcome", "COMMON_FAILURE_MODES_SYNTHESIZED_AND_LOCKED")
    ).strip()

    if not preconditions_ok or not taxonomy_complete:
        terminal_outcome = "COMMON_FAILURE_MODES_EVIDENCE_INCOMPLETE"
        next_action = "RESTORE_REQUIRED_INPUT_EVIDENCE_AND_RERUN_SYNTHESIS"
    elif architecture_review_required:
        terminal_outcome = "HOLD_PENDING_ARCHITECTURE_REVIEW"
        next_action = "OPEN_ONE_BOUNDED_ARCHITECTURE_REVIEW_LAYER"
    elif policy_lane_required:
        terminal_outcome = "REQUIRES_POLICY_LANE_FOR_PROBE_READINESS_STANDARD"
        next_action = "OPEN_ONE_BOUNDED_POLICY_EVIDENCE_STANDARD_SELECTION_LAYER"
    else:
        terminal_outcome = "COMMON_FAILURE_MODES_SYNTHESIZED_AND_LOCKED"
        next_action = "OPEN_ONE_BOUNDED_RESTART_SELECTION_LAYER"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "shared_model_class_hold_match": shared_outcome == required_shared_outcome,
            "qft_gr_hold_match": qft_gr_outcome == required_qft_gr_outcome,
            "gr_structural_gap_match": gr_outcome == required_gr_outcome and gr_frozen,
            "em_qft_structural_gap_match": em_qft_outcome == required_em_qft_outcome and em_qft_frozen,
            "qm_stat_external_policy_hold_match": qm_stat_outcome == required_qm_stat_outcome,
            "blocker_trend_plateau_match": trend_status == required_trend_status and trend_net_delta == required_trend_net_delta,
            "obligation_signals_match": (
                em_obligation_outcome == required_em_obligation_outcome
                and gr_obligation_outcome == required_gr_obligation_outcome
                and em_obligation_type == required_obligation_type
                and gr_obligation_type == required_obligation_type
            ),
            "taxonomy_complete": taxonomy_complete,
            "single_terminal_outcome_rule_declared": str(
                taxonomy_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_SCIENCE_COMMON_FAILURE_MODES_SYNTHESIS_OUTCOME",
            "no_loop_rule_declared": str(taxonomy_contract.get("no_loop_rule", "")).strip()
            == "ONE_SCIENCE_COMMON_FAILURE_MODES_SYNTHESIS_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "synthesis_preconditions_satisfied": preconditions_ok,
            },
            "inputs": {
                "shared_model_class_outcome": shared_outcome,
                "required_shared_model_class_outcome": required_shared_outcome,
                "qft_gr_outcome": qft_gr_outcome,
                "required_qft_gr_outcome": required_qft_gr_outcome,
                "gr_outcome": gr_outcome,
                "required_gr_outcome": required_gr_outcome,
                "gr_frozen": gr_frozen,
                "em_qft_outcome": em_qft_outcome,
                "required_em_qft_outcome": required_em_qft_outcome,
                "em_qft_frozen": em_qft_frozen,
                "qm_stat_outcome": qm_stat_outcome,
                "required_qm_stat_outcome": required_qm_stat_outcome,
                "trend_movement_status": trend_status,
                "required_trend_movement_status": required_trend_status,
                "trend_net_delta": trend_net_delta,
                "required_trend_net_delta": required_trend_net_delta,
                "blocker_rows": blocker_rows,
                "minimum_blocker_rows": minimum_blocker_rows,
                "em_obligation_outcome": em_obligation_outcome,
                "required_em_obligation_outcome": required_em_obligation_outcome,
                "gr_obligation_outcome": gr_obligation_outcome,
                "required_gr_obligation_outcome": required_gr_obligation_outcome,
                "em_obligation_type": em_obligation_type,
                "gr_obligation_type": gr_obligation_type,
                "required_obligation_type": required_obligation_type,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "common_failure_mode_taxonomy": taxonomy,
        "summary": {
            "terminal_outcome": terminal_outcome,
            "next_action": next_action,
            "recommended_restart_mode": "POLICY_EVIDENCE_STANDARD_FIRST",
            "single_layer_only": bool(synthesis_policy.get("single_layer_only", True)),
            "single_outcome_only": bool(synthesis_policy.get("single_outcome_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "shared_model_class_post_refinement_decision_report": _ptr(shared_path),
            "qft_gr_post_refinement_decision_report": _ptr(qft_gr_path),
            "gr_row_001_structural_gap_definition_report": _ptr(gr_path),
            "em_qft_higher_level_structure_review_report": _ptr(em_qft_path),
            "bridge_external_validation_policy_review_report": _ptr(qm_stat_path),
            "governance_blocker_trend_window_report": _ptr(trend_path),
            "governance_blocker_closure_map_report": _ptr(closure_map_path),
            "em_qft_interface_alignment_obligation_declaration_report": _ptr(em_obligation_path),
            "gr_regime_limit_alignment_obligation_declaration_report": _ptr(gr_obligation_path),
        },
        "non_claim_boundary": "Repository-local cross-lane common-failure-mode synthesis report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate cross-lane common failure modes synthesis report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "science_common_failure_modes_synthesis_20260412_v0.json",
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
        "science_common_failure_modes_synthesis_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SCIENCE_POST_QM_STAT_REBALANCE_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCIENCE_POST_QM_STAT_REBALANCE_20260412_v0.json"
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
    selection_policy = dict(declaration.get("selection_policy", {}))
    contract = dict(declaration.get("selection_contract", {}))

    external_policy_path = REPO_ROOT / str(
        required_inputs.get("bridge_external_validation_policy_review_report", "")
    ).strip()
    admissibility_path = REPO_ROOT / str(
        required_inputs.get("bridge_admissibility_standard_review_report", "")
    ).strip()
    naming_path = REPO_ROOT / str(
        required_inputs.get("bridge_repeatability_check_naming_review_report", "")
    ).strip()

    external_policy = _read_json(external_policy_path)
    admissibility = _read_json(admissibility_path)
    naming = _read_json(naming_path)

    external_policy_outcome = str(dict(external_policy.get("summary", {})).get("review_outcome", "")).strip()
    admissibility_outcome = str(dict(admissibility.get("summary", {})).get("review_outcome", "")).strip()
    naming_outcome = str(dict(naming.get("summary", {})).get("review_outcome", "")).strip()

    required_policy_hold = str(selection_policy.get("qm_stat_bridge_hold_required_outcome", "")).strip()
    required_admissibility_hold = str(
        selection_policy.get("qm_stat_admissibility_hold_required_outcome", "")
    ).strip()
    required_naming_hold = str(selection_policy.get("qm_stat_naming_hold_required_outcome", "")).strip()

    qm_stat_hold_confirmed = (
        external_policy_outcome == required_policy_hold
        and admissibility_outcome == required_admissibility_hold
        and naming_outcome == required_naming_hold
    )

    gr_blocker_moving_ready = bool(selection_policy.get("gr_blocker_moving_ready", False))
    em_qft_first_test_ready = bool(selection_policy.get("em_qft_first_test_ready", False))
    qft_gr_discovery_only_enforced = bool(selection_policy.get("qft_gr_discovery_only_enforced", True))
    require_rescoring_before_activation = bool(
        selection_policy.get("require_rescoring_before_activation", False)
    )

    allowed_outcomes = set(contract.get("allowed_outcomes", []))
    default_outcome = str(contract.get("default_outcome", "HOLD_AND_REQUIRE_RESCORING")).strip()

    if not qm_stat_hold_confirmed or require_rescoring_before_activation:
        selected_outcome = "HOLD_AND_REQUIRE_RESCORING"
        next_action = "RUN_SINGLE_RESCORING_PASS_BEFORE_ANY_NEW_SCIENCE_ACTIVATION"
    elif gr_blocker_moving_ready:
        selected_outcome = "ACTIVATE_GR_BLOCKER_MOVING_TRANCHE"
        next_action = str(selection_policy.get("default_next_action", "")).strip() or (
            "OPEN_SINGLE_GR_BLOCKER_MOVING_TRANCHE_PACKET"
        )
    elif em_qft_first_test_ready:
        selected_outcome = "ACTIVATE_EM_QFT_SEAM_FIRST_TEST"
        next_action = "OPEN_SINGLE_EM_QFT_FIRST_TEST_PACKET"
    elif qft_gr_discovery_only_enforced:
        selected_outcome = "KEEP_QFT_GR_DISCOVERY_ONLY"
        next_action = "KEEP_QFT_GR_IN_DISCOVERY_SCORING_WITHOUT_EXPANSION"
    else:
        selected_outcome = default_outcome
        next_action = "RUN_SINGLE_RESCORING_PASS_BEFORE_ANY_NEW_SCIENCE_ACTIVATION"

    if selected_outcome not in allowed_outcomes:
        selected_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "qm_stat_hold_confirmed": qm_stat_hold_confirmed,
            "gr_blocker_moving_ready": gr_blocker_moving_ready,
            "em_qft_first_test_ready": em_qft_first_test_ready,
            "qft_gr_discovery_only_enforced": qft_gr_discovery_only_enforced,
            "single_terminal_outcome_rule_declared": str(
                contract.get("single_terminal_outcome_rule", "")
            ).strip() == "EXACTLY_ONE_ALLOWED_SCIENCE_REBALANCE_OUTCOME",
            "no_loop_rule_declared": str(contract.get("no_loop_rule", "")).strip()
            == "ONE_POST_QM_STAT_REBALANCE_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": selected_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "hold_to_rebalance_transition_explicit": True,
            },
            "inputs": {
                "external_policy_outcome": external_policy_outcome,
                "admissibility_outcome": admissibility_outcome,
                "naming_outcome": naming_outcome,
                "required_policy_hold": required_policy_hold,
                "required_admissibility_hold": required_admissibility_hold,
                "required_naming_hold": required_naming_hold,
                "gr_blocker_moving_ready": gr_blocker_moving_ready,
                "em_qft_first_test_ready": em_qft_first_test_ready,
                "qft_gr_discovery_only_enforced": qft_gr_discovery_only_enforced,
                "require_rescoring_before_activation": require_rescoring_before_activation,
            },
            "summary": {
                "all_criteria_satisfied": selected_outcome
                in {
                    "ACTIVATE_GR_BLOCKER_MOVING_TRANCHE",
                    "ACTIVATE_EM_QFT_SEAM_FIRST_TEST",
                    "KEEP_QFT_GR_DISCOVERY_ONLY",
                },
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "selected_outcome": selected_outcome,
            "next_action": next_action,
            "qm_stat_bridge_state": external_policy_outcome,
            "qm_stat_admissibility_state": admissibility_outcome,
            "qm_stat_naming_state": naming_outcome,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "bridge_external_validation_policy_review_report": _ptr(external_policy_path),
            "bridge_admissibility_standard_review_report": _ptr(admissibility_path),
            "bridge_repeatability_check_naming_review_report": _ptr(naming_path),
        },
        "non_claim_boundary": "Repository-local post-QM-STAT science rebalancing report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate post-QM-STAT science rebalancing report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "science_post_qm_stat_rebalance_20260412_v0.json",
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
        "science_post_qm_stat_rebalance_report: "
        f"selected_outcome={payload['summary']['selected_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

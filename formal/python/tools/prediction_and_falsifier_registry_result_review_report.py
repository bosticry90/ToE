from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.prediction_and_falsifier_registry_report import (
    REGISTRY_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "PREDICTION_AND_FALSIFIER_REGISTRY_RESULT_REVIEW_20260515_v0"
REVIEW_ID = "PREDICTION_AND_FALSIFIER_REGISTRY_RESULT_REVIEW_v0"
OUTCOME_ID = (
    "PREDICTION_AND_FALSIFIER_REGISTRY_RESULT_REVIEW_ACCEPTS_NONCLAIM_TEST_DESIGN_REGISTRATION_"
    "AND_AUTHORIZES_COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_PREPARATION_ONLY"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"
DEFAULT_REGISTRY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "PREDICTION_AND_FALSIFIER_REGISTRY_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PREDICTION_AND_FALSIFIER_REGISTRY_RESULT_REVIEW_20260515_v0.json"
)

EXPECTED_ROWS = [
    "C6_CP_NLSE_2D_LANE",
    "C7_MT01A_ACOUSTIC_METRIC_LANE",
    "UCFF_SPECTRAL_AUDIT_LINEAGE",
    "BRAGG_DISPERSION_ELIMINATIVE_LANE",
    "RL01_RELATIVISTIC_DISPERSION_LIMIT",
    "RL02_NONRELATIVISTIC_NLSE_LIMIT",
    "GR01_DERIVATION_COMPLETENESS_GATE",
    "BRIDGE_PROGRAM_ORTHOGONALITY_REPORTS",
]

FORBIDDEN_EFFECTS = [
    "prediction_confirmation",
    "prediction_execution",
    "falsifier_execution",
    "falsifier_success_claim",
    "validation_upgrade",
    "recovery_claim",
    "empirical_support_claim",
    "theorem_discharge",
    "blocker_movement",
    "lane_reopen",
    "phase2_authorization",
    "empirical_validation_claim",
    "seam_closure",
    "master_action_promotion",
    "external_truth_claim",
]


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _counts(rows: list[dict[str, Any]], field: str) -> dict[str, int]:
    counts: dict[str, int] = {}
    for row in rows:
        value = str(row.get(field, "missing"))
        counts[value] = counts.get(value, 0) + 1
    return dict(sorted(counts.items()))


def _rows_keep_dependencies_visible(rows: list[dict[str, Any]]) -> bool:
    required_fields = (
        "method_verification_dependency",
        "uq_dependency",
        "robustness_dependency",
        "referent_dependency",
    )
    return all(all(row.get(field) for field in required_fields) for row in rows)


def build_result_review(
    *,
    registry_path: Path = DEFAULT_REGISTRY_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    registry = _read_json(registry_path)
    rows = list(registry.get("registry_rows", []))
    row_ids = [str(row.get("artifact_id")) for row in rows]
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_prediction_and_falsifier_registry": registry.get("registry_id") == REGISTRY_ID,
        "registry_status_nonclaim": registry.get("status") == "ACTIVE_NONLIVE_NONCLAIM",
        "authorization_class_preserved": registry.get("authorization_class")
        == "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS",
        "row_count_exactly_eight": int(registry.get("row_count", -1)) == 8,
        "row_ids_match_full_lineage": row_ids == EXPECTED_ROWS,
        "promotion_allowed_count_zero": int(registry.get("promotion_allowed_count", -1)) == 0,
        "all_promotion_allowed_false": registry.get("all_promotion_allowed_false") is True,
        "validation_upgrade_count_zero": int(registry.get("validation_upgrade_count", -1)) == 0,
        "prediction_execution_claim_count_zero": int(
            registry.get("prediction_execution_claim_count", -1)
        )
        == 0,
        "falsifier_execution_claim_count_zero": int(registry.get("falsifier_execution_claim_count", -1)) == 0,
        "prediction_result_claim_count_zero": int(registry.get("prediction_result_claim_count", -1)) == 0,
        "falsifier_result_claim_count_zero": int(registry.get("falsifier_result_claim_count", -1)) == 0,
        "all_rows_unexecuted": all(row.get("execution_status") == "not_executed_v0" for row in rows),
        "prediction_statuses_unexecuted": all(
            row.get("prediction_status") == "candidate_not_executed_v0" for row in rows
        ),
        "falsifier_statuses_unexecuted": all(
            row.get("falsifier_status") == "defined_not_executed_v0" for row in rows
        ),
        "dependencies_visible": _rows_keep_dependencies_visible(rows),
        "primary_gap_preserved": registry.get("primary_falsifier_gap")
        == "PREDICTION_AND_FALSIFIER_PASS_FAIL_CRITERIA_REGISTERED_BUT_NOT_EXECUTED_V0",
        "registry_scope_nonexecution": registry.get("registry_scope")
        == "REGISTER_TEST_DESIGNS_ONLY_NO_EXECUTION_OR_RESULT_CLAIM",
        "no_numerical_score": registry.get("scoring_policy") == "NO_NUMERICAL_CREDIBILITY_SCORE_IN_V0",
        "forbidden_effects_all_false": all(value is False for value in forbidden_effect_status.values()),
    }

    accepted = all(acceptance_criteria.values())
    if accepted:
        next_packet = "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_v0"
        next_action = "PREPARE_COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_AFTER_PREDICTION_AND_FALSIFIER_REGISTRY_REVIEW"
        outcome_id = OUTCOME_ID
    else:
        next_packet = "BLOCKED_PENDING_PREDICTION_AND_FALSIFIER_REGISTRY_REMEDIATION"
        next_action = "REMEDIATE_PREDICTION_AND_FALSIFIER_REGISTRY_RESULT_REVIEW_FAILURE"
        outcome_id = "PREDICTION_AND_FALSIFIER_REGISTRY_RESULT_REVIEW_BLOCKED"

    return {
        "schema_id": SCHEMA_ID,
        "review_id": REVIEW_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "consumed_registry": {
            "registry_id": registry.get("registry_id"),
            "registry_path": _ptr(registry_path),
            "registry_schema_id": registry.get("schema_id"),
            "registry_preparation_result": registry.get("preparation_result"),
        },
        "source_lineage": {
            "source_model_card_template_result_review": registry.get("consumes_result_review"),
            "source_model_card_template": registry.get("source_model_card_template"),
            "source_referent_registry": registry.get("source_referent_registry"),
            "source_sensitivity_robustness_protocol": registry.get(
                "source_sensitivity_robustness_protocol"
            ),
            "source_regime_recovery_matrix": registry.get("source_regime_recovery_matrix"),
            "source_numerical_method_registry": registry.get("source_numerical_method_registry"),
            "source_vvuq_ledger": registry.get("source_vvuq_ledger"),
            "source_audit": registry.get("source_audit"),
        },
        "acceptance_criteria": acceptance_criteria,
        "accepted": accepted,
        "outcome_id": outcome_id,
        "forbidden_effect_status": forbidden_effect_status,
        "scope_confirmation": {
            "row_count": int(registry.get("row_count", -1)),
            "promotion_allowed_count": int(registry.get("promotion_allowed_count", -1)),
            "validation_upgrade_count": int(registry.get("validation_upgrade_count", -1)),
            "prediction_execution_claim_count": int(
                registry.get("prediction_execution_claim_count", -1)
            ),
            "falsifier_execution_claim_count": int(registry.get("falsifier_execution_claim_count", -1)),
            "prediction_result_claim_count": int(registry.get("prediction_result_claim_count", -1)),
            "falsifier_result_claim_count": int(registry.get("falsifier_result_claim_count", -1)),
            "execution_status_counts": _counts(rows, "execution_status"),
            "prediction_status_counts": _counts(rows, "prediction_status"),
            "falsifier_status_counts": _counts(rows, "falsifier_status"),
            "method_verification_dependency_counts": _counts(rows, "method_verification_dependency"),
            "uq_dependency_counts": _counts(rows, "uq_dependency"),
            "robustness_dependency_counts": _counts(rows, "robustness_dependency"),
            "referent_dependency_counts": _counts(rows, "referent_dependency"),
            "primary_falsifier_gap": registry.get("primary_falsifier_gap"),
            "registry_scope": registry.get("registry_scope"),
        },
        "next_packet": next_packet,
        "next_action": next_action,
        "next_packet_authorization_scope": "PREPARATION_ONLY",
        "roadmap_update_required": True,
        "non_claim_boundary": (
            "Result review accepts nonclaim prediction/falsifier test-design registration only; it authorizes "
            "computational-physics integration closeout preparation only and does not authorize prediction execution, "
            "falsifier execution, prediction confirmation, falsifier success claims, validation upgrade, recovery claim, "
            "empirical support claim, theorem discharge, blocker movement, seam closure, Phase 2 authorization, "
            "master-action promotion, or external-truth claim."
        ),
    }


def write_result_review(
    *,
    registry_path: Path = DEFAULT_REGISTRY_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_result_review(
        registry_path=registry_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the prediction/falsifier registry result review.")
    parser.add_argument("--registry", type=Path, default=DEFAULT_REGISTRY_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    registry_path = ns.registry if ns.registry.is_absolute() else (REPO_ROOT / ns.registry)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_result_review(
        registry_path=registry_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "prediction_and_falsifier_registry_result_review_report: "
        f"accepted={payload['accepted']} next_packet={payload['next_packet']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

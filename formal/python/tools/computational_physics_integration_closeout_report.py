from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_20260515_v0"
CLOSEOUT_ID = "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_v0"
PREPARATION_RESULT = (
    "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_PREPARED_AS_NONCLAIM_CREDIBILITY_INFRASTRUCTURE_"
    "WITH_NO_EXECUTION_OR_PROMOTION"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"
DEFAULT_JSON_OUT = (
    REPO_ROOT / "formal" / "docs" / "release" / "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_20260515_v0.json"
)
DEFAULT_MD_OUT = REPO_ROOT / "formal" / "docs" / "paper" / "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_REPORT_v0.md"

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

PACKET_PATHS = {
    "capability_audit": REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_20260515_v0.json",
    "capability_audit_result_review": REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_RESULT_REVIEW_20260515_v0.json",
    "vvuq_ledger": REPO_ROOT / "formal" / "docs" / "release" / "VVUQ_CREDIBILITY_LEDGER_20260515_v0.json",
    "vvuq_ledger_result_review": REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "VVUQ_CREDIBILITY_LEDGER_RESULT_REVIEW_20260515_v0.json",
    "numerical_method_registry": REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "NUMERICAL_METHOD_VERIFICATION_REGISTRY_20260515_v0.json",
    "numerical_method_registry_result_review": REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "NUMERICAL_METHOD_VERIFICATION_REGISTRY_RESULT_REVIEW_20260515_v0.json",
    "regime_recovery_matrix": REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "REGIME_RECOVERY_MATRIX_20260515_v0.json",
    "regime_recovery_matrix_result_review": REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "REGIME_RECOVERY_MATRIX_RESULT_REVIEW_20260515_v0.json",
    "sensitivity_robustness_protocol": REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SENSITIVITY_ROBUSTNESS_PROTOCOL_20260515_v0.json",
    "sensitivity_robustness_protocol_result_review": REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SENSITIVITY_ROBUSTNESS_PROTOCOL_RESULT_REVIEW_20260515_v0.json",
    "referent_registry": REPO_ROOT / "formal" / "docs" / "release" / "REFERENT_REGISTRY_20260515_v0.json",
    "referent_registry_result_review": REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "REFERENT_REGISTRY_RESULT_REVIEW_20260515_v0.json",
    "simulation_model_card_template": REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SIMULATION_MODEL_CARD_TEMPLATE_20260515_v0.json",
    "simulation_model_card_template_result_review": REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SIMULATION_MODEL_CARD_TEMPLATE_RESULT_REVIEW_20260515_v0.json",
    "prediction_and_falsifier_registry": REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PREDICTION_AND_FALSIFIER_REGISTRY_20260515_v0.json",
    "prediction_and_falsifier_registry_result_review": REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PREDICTION_AND_FALSIFIER_REGISTRY_RESULT_REVIEW_20260515_v0.json",
}

STACK_LAYERS = [
    {
        "layer_order": 1,
        "layer_id": "capability_audit",
        "artifact_key": "capability_audit",
        "result_review_key": "capability_audit_result_review",
        "function": "identifies computational-physics roles",
    },
    {
        "layer_order": 2,
        "layer_id": "vvuq_ledger",
        "artifact_key": "vvuq_ledger",
        "result_review_key": "vvuq_ledger_result_review",
        "function": "records credibility posture and gaps",
    },
    {
        "layer_order": 3,
        "layer_id": "numerical_method_registry",
        "artifact_key": "numerical_method_registry",
        "result_review_key": "numerical_method_registry_result_review",
        "function": "records numerical-method verification debt",
    },
    {
        "layer_order": 4,
        "layer_id": "regime_recovery_matrix",
        "artifact_key": "regime_recovery_matrix",
        "result_review_key": "regime_recovery_matrix_result_review",
        "function": "records known-limit posture",
    },
    {
        "layer_order": 5,
        "layer_id": "sensitivity_robustness_protocol",
        "artifact_key": "sensitivity_robustness_protocol",
        "result_review_key": "sensitivity_robustness_protocol_result_review",
        "function": "defines required perturbation and robustness scans",
    },
    {
        "layer_order": 6,
        "layer_id": "referent_registry",
        "artifact_key": "referent_registry",
        "result_review_key": "referent_registry_result_review",
        "function": "registers allowed comparison targets",
    },
    {
        "layer_order": 7,
        "layer_id": "simulation_model_card_template",
        "artifact_key": "simulation_model_card_template",
        "result_review_key": "simulation_model_card_template_result_review",
        "function": "standardizes future artifact documentation",
    },
    {
        "layer_order": 8,
        "layer_id": "prediction_and_falsifier_registry",
        "artifact_key": "prediction_and_falsifier_registry",
        "result_review_key": "prediction_and_falsifier_registry_result_review",
        "function": "registers future test designs and failure conditions",
    },
]

FORBIDDEN_EFFECTS = [
    "theory_validation",
    "empirical_validation",
    "referent_comparison_execution",
    "robustness_scan_execution",
    "prediction_execution",
    "falsifier_execution",
    "theorem_discharge",
    "blocker_movement",
    "lane_reopen",
    "seam_closure",
    "phase2_authorization",
    "master_action_promotion",
    "simulation_execution",
    "validation_upgrade",
    "claim_promotion",
    "numerical_credibility_scoring",
    "external_truth_claim",
]


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _row_ids(payload: dict[str, Any], row_key: str) -> list[str]:
    return [str(row["artifact_id"]) for row in payload.get(row_key, [])]


def _row_lineage(payloads: dict[str, dict[str, Any]]) -> dict[str, list[str]]:
    return {
        "capability_audit": _row_ids(payloads["capability_audit"], "audit_rows"),
        "vvuq_ledger": _row_ids(payloads["vvuq_ledger"], "ledger_rows"),
        "numerical_method_registry": _row_ids(payloads["numerical_method_registry"], "registry_rows"),
        "regime_recovery_matrix": _row_ids(payloads["regime_recovery_matrix"], "matrix_rows"),
        "sensitivity_robustness_protocol": _row_ids(payloads["sensitivity_robustness_protocol"], "protocol_rows"),
        "referent_registry": _row_ids(payloads["referent_registry"], "referent_rows"),
        "prediction_and_falsifier_registry": _row_ids(
            payloads["prediction_and_falsifier_registry"], "registry_rows"
        ),
    }


def _review_accepted(payloads: dict[str, dict[str, Any]], review_key: str) -> bool:
    return payloads[review_key].get("accepted") is True


def _layer_summary(payloads: dict[str, dict[str, Any]]) -> list[dict[str, Any]]:
    rows = []
    for layer in STACK_LAYERS:
        artifact_key = str(layer["artifact_key"])
        review_key = str(layer["result_review_key"])
        artifact = payloads[artifact_key]
        review = payloads[review_key]
        rows.append(
            {
                "layer_order": layer["layer_order"],
                "layer_id": layer["layer_id"],
                "artifact_path": _ptr(PACKET_PATHS[artifact_key]),
                "artifact_status": artifact.get("status"),
                "result_review_id": review.get("review_id"),
                "result_review_path": _ptr(PACKET_PATHS[review_key]),
                "result_review_accepted": review.get("accepted") is True,
                "function": layer["function"],
            }
        )
    return rows


def _count_sum(payloads: dict[str, dict[str, Any]], keys: list[tuple[str, str]]) -> int:
    total = 0
    for payload_key, field in keys:
        total += int(payloads[payload_key].get(field, 0))
    return total


def build_closeout(
    *,
    packet_paths: dict[str, Path] | None = None,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    paths = PACKET_PATHS if packet_paths is None else packet_paths
    payloads = {key: _read_json(path) for key, path in paths.items()}
    source_review = payloads["prediction_and_falsifier_registry_result_review"]
    lineage = _row_lineage(payloads)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}
    all_reviews_accepted = all(_review_accepted(payloads, str(layer["result_review_key"])) for layer in STACK_LAYERS)
    lineage_preserved = all(ids == EXPECTED_ROWS for ids in lineage.values())

    promotion_allowed_count = _count_sum(
        payloads,
        [
            ("vvuq_ledger", "promotion_allowed_count"),
            ("numerical_method_registry", "promotion_allowed_count"),
            ("regime_recovery_matrix", "promotion_allowed_count"),
            ("sensitivity_robustness_protocol", "promotion_allowed_count"),
            ("referent_registry", "promotion_allowed_count"),
            ("prediction_and_falsifier_registry", "promotion_allowed_count"),
        ],
    )
    validation_upgrade_count = _count_sum(
        payloads,
        [
            ("numerical_method_registry", "validation_upgrade_count"),
            ("regime_recovery_matrix", "validation_upgrade_count"),
            ("sensitivity_robustness_protocol", "validation_upgrade_count"),
            ("referent_registry", "validation_upgrade_count"),
            ("prediction_and_falsifier_registry", "validation_upgrade_count"),
        ],
    )
    execution_claim_count = _count_sum(
        payloads,
        [
            ("sensitivity_robustness_protocol", "scan_execution_claim_count"),
            ("referent_registry", "referent_comparison_execution_claim_count"),
            ("prediction_and_falsifier_registry", "prediction_execution_claim_count"),
            ("prediction_and_falsifier_registry", "falsifier_execution_claim_count"),
            ("prediction_and_falsifier_registry", "prediction_result_claim_count"),
            ("prediction_and_falsifier_registry", "falsifier_result_claim_count"),
        ],
    )
    completion_claim_count = _count_sum(
        payloads,
        [
            ("regime_recovery_matrix", "recovery_completion_claim_count"),
            ("sensitivity_robustness_protocol", "robustness_completion_claim_count"),
            ("referent_registry", "empirical_validation_claim_count"),
            ("simulation_model_card_template", "model_card_instantiation_claim_count"),
        ],
    )
    scoring_policy_preserved = all(
        payloads[key].get("scoring_policy") == "NO_NUMERICAL_CREDIBILITY_SCORE_IN_V0"
        for key in (
            "vvuq_ledger",
            "numerical_method_registry",
            "regime_recovery_matrix",
            "sensitivity_robustness_protocol",
            "referent_registry",
            "prediction_and_falsifier_registry",
        )
    )

    acceptance_criteria = {
        "consumes_prediction_falsifier_result_review": source_review.get("review_id")
        == "PREDICTION_AND_FALSIFIER_REGISTRY_RESULT_REVIEW_v0",
        "source_result_review_accepted": source_review.get("accepted") is True,
        "source_authorizes_closeout_only": source_review.get("next_packet")
        == "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_v0",
        "source_scope_preparation_only": source_review.get("next_packet_authorization_scope") == "PREPARATION_ONLY",
        "all_planned_packets_exist_and_loaded": set(payloads) == set(PACKET_PATHS),
        "all_result_reviews_accepted": all_reviews_accepted,
        "eight_row_lineage_preserved": lineage_preserved,
        "promotion_allowed_count_zero": promotion_allowed_count == 0,
        "validation_upgrade_count_zero": validation_upgrade_count == 0,
        "execution_claim_count_zero": execution_claim_count == 0,
        "completion_claim_count_zero": completion_claim_count == 0,
        "no_numerical_credibility_score": scoring_policy_preserved,
        "forbidden_effects_all_false": all(value is False for value in forbidden_effect_status.values()),
    }

    prepared = all(acceptance_criteria.values())
    return {
        "schema_id": SCHEMA_ID,
        "closeout_id": CLOSEOUT_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "authorization_class": "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS",
        "preparation_result": PREPARATION_RESULT,
        "consumes_result_review": "PREDICTION_AND_FALSIFIER_REGISTRY_RESULT_REVIEW_v0",
        "consumes_result_review_pointer": _ptr(paths["prediction_and_falsifier_registry_result_review"]),
        "closeout_scope": "SUMMARY_ONLY_NO_EXECUTION_OR_PROMOTION",
        "prepared": prepared,
        "acceptance_criteria": acceptance_criteria,
        "stack_layers": _layer_summary(payloads),
        "row_count": len(EXPECTED_ROWS),
        "expected_row_ids": EXPECTED_ROWS,
        "lineage_row_ids": lineage,
        "lineage_preserved": lineage_preserved,
        "all_result_reviews_accepted": all_reviews_accepted,
        "promotion_allowed_count": promotion_allowed_count,
        "validation_upgrade_count": validation_upgrade_count,
        "execution_claim_count": execution_claim_count,
        "completion_claim_count": completion_claim_count,
        "scoring_policy": "NO_NUMERICAL_CREDIBILITY_SCORE_IN_V0",
        "forbidden_effect_status": forbidden_effect_status,
        "final_non_execution_readout": {
            "no_theory_validation": True,
            "no_empirical_validation": True,
            "no_referent_comparison_execution": True,
            "no_robustness_scan_execution": True,
            "no_prediction_execution": True,
            "no_falsifier_execution": True,
            "no_theorem_discharge": True,
            "no_blocker_movement": True,
            "no_lane_reopen": True,
            "no_seam_closure": True,
            "no_phase2_authorization": True,
            "no_master_action_promotion": True,
        },
        "summary": {
            "stack_layer_count": len(STACK_LAYERS),
            "result_review_count": len(STACK_LAYERS),
            "row_count": len(EXPECTED_ROWS),
            "terminal_readout": "NONCLAIM_CREDIBILITY_INFRASTRUCTURE_PREPARED_NO_EXECUTION_OR_PROMOTION",
            "next_recommended_action": "REVIEW_COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_RESULT",
        },
        "next_action": "REVIEW_COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_RESULT",
        "next_packet_authorization_scope": "RESULT_REVIEW_ONLY",
        "roadmap_update_required": True,
        "non_claim_boundary": (
            "Computational-physics integration closeout summarizes prepared credibility infrastructure only. "
            "It records no theory validation, no empirical validation, no referent comparison execution, "
            "no robustness scan execution, no prediction execution, no falsifier execution, no theorem discharge, "
            "no blocker movement, no lane reopen, no seam closure, no Phase 2 authorization, no master-action "
            "promotion, and no external-truth claim."
        ),
    }


def build_markdown_report(closeout: dict[str, Any]) -> str:
    lines = [
        "# Computational Physics Integration Closeout Report v0",
        "",
        "Spec ID:",
        "- `COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_REPORT_v0`",
        "",
        "Preparation result:",
        f"- `{closeout['preparation_result']}`",
        "",
        "Authority binding:",
        f"- `{closeout['authorization_class']}`",
        f"- Consumed result review: `{closeout['consumes_result_review_pointer']}`",
        "- JSON closeout: `formal/docs/release/COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_20260515_v0.json`",
        "- Gate: `formal/python/tests/test_computational_physics_integration_closeout_gate.py`",
        "",
        "Non-claim boundary:",
        f"- {closeout['non_claim_boundary']}",
        "",
        "## Stack Layers",
        "",
        "| Order | Layer | Function | Artifact status | Review accepted |",
        "| --- | --- | --- | --- | --- |",
    ]
    for row in closeout["stack_layers"]:
        lines.append(
            "| `{order}` | `{layer}` | {function} | `{status}` | `{accepted}` |".format(
                order=row["layer_order"],
                layer=row["layer_id"],
                function=row["function"],
                status=row["artifact_status"],
                accepted=str(row["result_review_accepted"]).lower(),
            )
        )

    lines.extend(
        [
            "",
            "## Final Readout",
            "",
            f"- Stack layers: `{closeout['summary']['stack_layer_count']}`",
            f"- Result reviews accepted: `{closeout['all_result_reviews_accepted']}`",
            f"- Eight-row lineage preserved: `{closeout['lineage_preserved']}`",
            f"- Promotion allowed count: `{closeout['promotion_allowed_count']}`",
            f"- Validation upgrade count: `{closeout['validation_upgrade_count']}`",
            f"- Execution claim count: `{closeout['execution_claim_count']}`",
            f"- Completion claim count: `{closeout['completion_claim_count']}`",
            f"- Scoring policy: `{closeout['scoring_policy']}`",
            f"- Next recommended action: `{closeout['summary']['next_recommended_action']}`",
            "",
            "Explicit non-execution confirmations:",
            "- no theory validation",
            "- no empirical validation",
            "- no referent comparison execution",
            "- no robustness scan execution",
            "- no prediction execution",
            "- no falsifier execution",
            "- no theorem discharge",
            "- no blocker movement",
            "- no lane reopen",
            "- no seam closure",
            "- no Phase 2 authorization",
            "- no master-action promotion",
            "",
        ]
    )
    return "\n".join(lines)


def write_closeout(
    *,
    json_out: Path = DEFAULT_JSON_OUT,
    md_out: Path = DEFAULT_MD_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    closeout = build_closeout(captured_at_utc=captured_at_utc)
    json_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.write_text(json.dumps(closeout, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    md_out.write_text(build_markdown_report(closeout), encoding="utf-8")
    return closeout


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the computational-physics integration closeout.")
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON_OUT)
    parser.add_argument("--md-out", type=Path, default=DEFAULT_MD_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    json_out = ns.json_out if ns.json_out.is_absolute() else (REPO_ROOT / ns.json_out)
    md_out = ns.md_out if ns.md_out.is_absolute() else (REPO_ROOT / ns.md_out)
    closeout = write_closeout(
        json_out=json_out,
        md_out=md_out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "computational_physics_integration_closeout_report: "
        f"prepared={closeout['prepared']} layers={closeout['summary']['stack_layer_count']} "
        f"json={_ptr(json_out)} md={_ptr(md_out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

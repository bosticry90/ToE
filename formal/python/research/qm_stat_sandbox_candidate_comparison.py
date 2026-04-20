from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.research import harder_qm_stat_target, qm_stat_sandbox_payload_record


REPO_ROOT = find_repo_root(Path(__file__))

COMPARISON_REPORT_PATH = Path(
    "formal/output/reports/research_mode_qm_stat_sandbox_candidate_comparison_20260419_v0.json"
)


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def build_qm_stat_sandbox_candidate_comparison() -> dict[str, Any]:
    payload_record = qm_stat_sandbox_payload_record.build_qm_stat_sandbox_payload_record()
    harder_target_report = harder_qm_stat_target.build_harder_qm_stat_target_report()
    harder_artifact = dict(harder_target_report["artifact"])
    harder_metrics = dict(harder_artifact["metrics"])
    sandbox_artifact = qm_stat_sandbox_payload_record.build_qm_stat_sandbox_artifact()

    payload_binding = dict(payload_record["target_binding"])
    sandbox_binding = dict(sandbox_artifact["target_binding"])
    harder_binding_ok = harder_target_report["summary"]["row_id"] == payload_binding["row_id"]
    same_target_binding_ok = all(
        [
            payload_binding["row_id"] == sandbox_binding["row_id"],
            payload_binding["target_package_id"] == harder_artifact["live_anchor"]["target_package_id"],
            harder_binding_ok,
        ]
    )
    witness_metric_ok = float(sandbox_artifact["metrics"]["continuity_residual_sup_abs"]) == 0.0
    harder_metric_ok = all(
        [
            float(harder_metrics["continuity_residual_sup_abs_max"]) < 1.0e-6,
            float(harder_metrics["mass_drift_abs_max"]) < 1.0e-6,
            float(harder_metrics["first_moment_transport_gap_abs_max"]) < 1.0e-5,
            float(harder_metrics["second_moment_transport_gap_abs_max"]) < 1.0e-4,
        ]
    )
    support_role_ok = harder_artifact["metadata"]["promotability"] == "NOT_READY"
    comparison_ready = all([same_target_binding_ok, witness_metric_ok, harder_metric_ok, support_role_ok])

    return {
        "schema_id": "RESEARCH_MODE_QM_STAT_SANDBOX_CANDIDATE_COMPARISON_20260419_v0",
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "comparison_scope_v0": "COMPARE_ACCEPTED_QM_STAT_SANDBOX_PAYLOAD_RECORD_AGAINST_ONE_HARDER_LIVE_ROW_LOCAL_TARGET_ONLY",
        "criteria": {
            "same_target_binding": {
                "status_v0": "PASS" if same_target_binding_ok else "FAIL",
                "criterion_v0": "The sandbox payload record and the harder live target must remain attached to the same QM-STAT row-local blocker package.",
            },
            "witness_identity_preserved": {
                "status_v0": "PASS" if witness_metric_ok else "FAIL",
                "criterion_v0": "The sandbox candidate must preserve the exact bounded continuity witness it was promoted from.",
            },
            "harder_target_strength_preserved": {
                "status_v0": "PASS" if harder_metric_ok else "FAIL",
                "criterion_v0": "The harder target must preserve bounded continuity and transport-moment identities at the stricter live row-local surface.",
            },
            "support_role_explicit": {
                "status_v0": "PASS" if support_role_ok else "FAIL",
                "criterion_v0": "The harder live target must remain supporting comparison evidence, not a silent promotion-review substitute.",
            },
        },
        "objective_quality": {
            "criteria": {
                "same_target_binding_ok": same_target_binding_ok,
                "witness_metric_ok": witness_metric_ok,
                "harder_metric_ok": harder_metric_ok,
                "support_role_ok": support_role_ok,
                "all_criteria_pass": comparison_ready,
            },
            "inputs": {
                "payload_artifact_id": payload_record["summary"]["artifact_id"],
                "payload_artifact_pointer": payload_record["summary"]["artifact_pointer"],
                "payload_delta_class": payload_record["metadata_record"]["delta_class"],
                "harder_artifact_id": harder_artifact["metadata"]["artifact_id"],
                "harder_artifact_pointer": harder_artifact["artifact_path"],
                "harder_delta_class": harder_artifact["metadata"]["delta_class"],
                "row_id": payload_binding["row_id"],
                "seam_id": payload_binding["seam_id"],
                "target_package_id": payload_binding["target_package_id"],
            },
            "summary": {
                "comparison_limit_v0": "The harder live target is comparison evidence only. The payload record remains the governed-entry object; the harder target does not become a silent payload substitute.",
            },
        },
        "comparison_record": {
            "payload_candidate": {
                "artifact_id": payload_record["summary"]["artifact_id"],
                "delta_class": payload_record["metadata_record"]["delta_class"],
                "continuity_residual_sup_abs": sandbox_artifact["metrics"]["continuity_residual_sup_abs"],
                "promotion_readiness": payload_record["metadata_record"]["promotion_readiness"],
            },
            "harder_target": {
                "artifact_id": harder_artifact["metadata"]["artifact_id"],
                "delta_class": harder_artifact["metadata"]["delta_class"],
                "continuity_residual_sup_abs_max": harder_metrics["continuity_residual_sup_abs_max"],
                "first_moment_transport_gap_abs_max": harder_metrics["first_moment_transport_gap_abs_max"],
                "second_moment_transport_gap_abs_max": harder_metrics["second_moment_transport_gap_abs_max"],
                "promotability": harder_artifact["metadata"]["promotability"],
            },
            "comparison_disposition_v0": "PAYLOAD_REMAINS_PRIMARY_GOVERNED_ENTRY_OBJECT_HARDER_TARGET_REMAINS_BOUND_SUPPORTING_EVIDENCE",
        },
        "summary": {
            "terminal_outcome": (
                "RESEARCH_MODE_QM_STAT_SANDBOX_CANDIDATE_COMPARISON_ALIGNED"
                if comparison_ready
                else "RESEARCH_MODE_QM_STAT_SANDBOX_CANDIDATE_COMPARISON_EVIDENCE_INCOMPLETE"
            ),
            "row_id": payload_binding["row_id"],
            "seam_id": payload_binding["seam_id"],
            "target_package_id": payload_binding["target_package_id"],
            "comparison_status_v0": (
                "ALIGNED_BOUNDED_v0_NONCLAIM" if comparison_ready else "EVIDENCE_INCOMPLETE_v0_NONCLAIM"
            ),
            "next_action": (
                "KEEP_QM_STAT_PAYLOAD_RECORD_AND_COMPARISON_SURFACE_READY_PENDING_EXPLICIT_GOVERNED_REVIEW_ENTRY"
                if comparison_ready
                else "REPAIR_QM_STAT_PAYLOAD_OR_HARDER_TARGET_INPUTS_AND_RERUN_COMPARISON"
            ),
        },
        "source_bundle": {
            "payload_record": "formal/output/reports/research_mode_qm_stat_sandbox_payload_record_20260419_v0.json",
            "sandbox_artifact": "formal/output/sandbox/qm_stat_transport_witness_sandbox_artifact_20260419_v0.json",
            "harder_target_report": "formal/output/reports/research_mode_harder_qm_stat_target_20260419_v0.json",
            "harder_target_artifact": "formal/output/research/research_qm_stat_transport_moment_stack_probe_20260419_v0.json",
        },
        "non_claim_boundary": "Repository-local comparison surface only; no governed review pass, canonical mutation, or seam closure claim.",
    }


def materialize_qm_stat_sandbox_candidate_comparison(repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    report = build_qm_stat_sandbox_candidate_comparison()
    _write_json(repo_root / COMPARISON_REPORT_PATH, report)
    return report


def main() -> int:
    parser = argparse.ArgumentParser(description="Build or write the QM-STAT sandbox-candidate comparison report.")
    parser.add_argument("--write", action="store_true", help="Write the QM-STAT sandbox-candidate comparison report into the repository output tree.")
    args = parser.parse_args()

    report = materialize_qm_stat_sandbox_candidate_comparison() if args.write else build_qm_stat_sandbox_candidate_comparison()
    print(json.dumps(report["summary"], indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
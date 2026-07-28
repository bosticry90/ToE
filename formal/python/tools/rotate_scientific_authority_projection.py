from __future__ import annotations

import argparse
import hashlib
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import loop_control_registry_integrity as integrity


REPO_ROOT = find_repo_root(Path(__file__))
REGISTRY_PATH = REPO_ROOT / "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"


class ScientificAuthorityRotationError(RuntimeError):
    pass


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rotate(
    *,
    expected_current: str,
    target: str,
    target_kind: str,
    evidence: str,
    report: str,
    outcome: str,
    strict_outcome: str,
    claim_status: str,
    queue_scope: str,
) -> None:
    registry = integrity.load_registry(REGISTRY_PATH)
    state = registry["current_target_state"]
    observed = state["live_next_target"]
    if observed != expected_current:
        raise ScientificAuthorityRotationError(
            f"expected current target {expected_current!r}, observed {observed!r}"
        )
    existing = [
        row for row in registry["workstreams"] if row.get("workstream_id") == target
    ]
    if existing:
        raise ScientificAuthorityRotationError(
            f"target already exists in workstreams: {target}"
        )
    evidence_path = REPO_ROOT / evidence
    report_path = REPO_ROOT / report
    if not evidence_path.is_file() or not report_path.is_file():
        raise ScientificAuthorityRotationError("evidence or report path is missing")
    for row in registry["workstreams"]:
        if row.get("workstream_id") == expected_current:
            row["status"] = "completed"
            row["live_lane"] = "no"
    new_row = {
        "workstream_id": target,
        "status": "active",
        "live_lane": "yes",
        "queue_scope": queue_scope,
        "active_lane": target,
        "authorized_target": target,
        "authorized_next_strict_target": target,
        "selected_next_target": target,
        "selected_next_target_kind": target_kind,
        "authorization_evidence": evidence,
        "report": report,
        "report_path": report,
        "report_sha256": _sha256(report_path),
        "packet_result": outcome,
        "strict_packet_result": strict_outcome,
        "consumed_target": expected_current,
        "consumed_target_kind": "previous_scientific_authority",
        "claim_ceiling_level": 3,
        "claim_label": "B-BOUNDED",
        "claim_status": claim_status,
        "review_accepted": "yes",
        "preserved_descendant_adopted": "no",
        "yukawa_work_authorized": "no",
        "unit_assignment_count": 0,
        "dimension_vector_count": 0,
        "conversion_constant_count": 0,
        "seam_mapping_count": 0,
        "dimensional_closure_claimed": "no",
        "pillar_completion_claimed": "no",
        "seam_admissibility_claimed": "no",
        "physical_calibration_claimed": "no",
        "cross_sector_coupling_validation_claimed": "no",
        "C_k_action_embedding_authorized": "no",
        "ccft_resumed": "no",
        "master_action_promoted": "no",
    }
    registry["workstreams"].append(new_row)
    state.update(
        {
            "live_next_target": target,
            "previous_live_next_target": expected_current,
            "live_next_target_kind": target_kind,
            "live_next_target_evidence": evidence,
            "live_next_target_report": report,
            "live_next_target_outcome": outcome,
            "live_next_target_strict_outcome": strict_outcome,
        }
    )
    registry["ACTIVE_LANE_v0"] = target
    registry["CURRENT_LIVE_NEXT_TARGET_v0"] = target
    repaired = integrity.repair_registry(registry)
    integrity.atomic_write_registry(
        REGISTRY_PATH,
        integrity.canonical_json_bytes(repaired),
    )
    integrity.validate_registry(repaired)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Rotate the canonical scientific projection after an accepted review."
    )
    parser.add_argument("--expected-current", required=True)
    parser.add_argument("--target", required=True)
    parser.add_argument("--target-kind", required=True)
    parser.add_argument("--evidence", required=True)
    parser.add_argument("--report", required=True)
    parser.add_argument("--outcome", required=True)
    parser.add_argument("--strict-outcome", required=True)
    parser.add_argument("--claim-status", required=True)
    parser.add_argument("--queue-scope", required=True)
    args = parser.parse_args()
    try:
        rotate(
            expected_current=args.expected_current,
            target=args.target,
            target_kind=args.target_kind,
            evidence=args.evidence,
            report=args.report,
            outcome=args.outcome,
            strict_outcome=args.strict_outcome,
            claim_status=args.claim_status,
            queue_scope=args.queue_scope,
        )
    except (OSError, KeyError, ValueError, ScientificAuthorityRotationError) as exc:
        print(f"scientific authority rotation failed: {exc}")
        return 1
    print(f"scientific authority rotated to {args.target}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

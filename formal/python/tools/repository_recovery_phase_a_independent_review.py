from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


class PhaseAReviewError(RuntimeError):
    pass


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _canonical(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n").encode(
        "utf-8"
    )


def build_review(custody: Path) -> dict[str, Any]:
    manifest_path = custody / "DIRTY_WORKTREE_CUSTODY_MANIFEST_v0.json"
    manifest = _read(manifest_path)
    commit_ledger = _read(custody / "AUTHORITY_COMMIT_LINEAGE_v0.json")
    transitions = _read(custody / "AUTHORITY_TRANSITION_LEDGER_v0.json")
    artifacts = _read(custody / "POST_REGISTRY_ARTIFACT_CLASSIFICATION_v0.json")
    baseline = _read(custody / "CLEAN_BASELINE_VALIDATION_RESULT_v0.json")
    matrix = _read(custody / "CLEAN_VS_AUDITED_FAILURE_MATRIX_v0.json")
    mutation = _read(
        custody / "CLEAN_BASELINE_POST_VALIDATION_MUTATION_MANIFEST_v0.json"
    )
    sidecar = (custody / "DIRTY_WORKTREE_CUSTODY_MANIFEST_v0.sha256").read_text(
        encoding="ascii"
    ).split()[0]
    object_checks: list[bool] = []
    for row in manifest["entries"]:
        object_rel = row.get("custody_object")
        if object_rel:
            object_path = custody / Path(object_rel)
            object_checks.append(object_path.exists() and _sha(object_path) == row["sha256"])
        if row.get("head_blob_custody_object"):
            object_path = custody / Path(row["head_blob_custody_object"])
            object_checks.append(
                object_path.exists() and _sha(object_path) == row["head_blob_sha256"]
            )
    classification = artifacts["artifacts"]
    checks = {
        "manifest_root_hash_valid": sidecar == _sha(manifest_path),
        "audited_counts_exact": manifest["counts"]
        == {"total": 629, "tracked_dirty": 7, "untracked": 622},
        "original_worktree_unchanged": manifest["original_worktree_unchanged"] is True,
        "all_custody_objects_verified": bool(object_checks) and all(object_checks),
        "commit_lineage_complete": commit_ledger["commit_count"] == 48
        and len(commit_ledger["rows"]) == 48,
        "transition_ledger_nonempty": transitions["transition_count"]
        == len(transitions["rows"])
        and transitions["transition_count"] > 0,
        "v2_not_registry_enrolled": classification["tracked_v2"]["classification"]
        == "TRACKED_BUT_NOT_REGISTRY_ENROLLED"
        and classification["tracked_v2"]["repository_level_acceptance"] is False,
        "scalar_lane_noncurrent": classification["local_scalar_yukawa"]["classification"]
        == "LOCAL_UNTRACKED_EXPLORATORY",
        "maxwell_dirac_not_registry_enrolled": classification[
            "post_registry_maxwell_dirac"
        ]["classification"]
        == "TRACKED_BUT_NOT_REGISTRY_ENROLLED",
        "mirror_conflict_recorded": classification["current_mirrors"]["classification"]
        == "PROVENANCE_INCOMPLETE",
        "baseline_suite_completed": baseline["full_suite_complete"] is True,
        "failure_population_complete": matrix["complete_failure_population"] is True,
        "all_baseline_failures_classified": matrix.get("all_failures_classified")
        is True,
        "baseline_validation_was_read_only": mutation["tracked_dirty_count"] == 0,
        "scientific_posture_preserved": artifacts["scientific_posture"] == "B-BLOCKED"
        and artifacts["scientific_status_changed"] is False,
    }
    if not checks["manifest_root_hash_valid"] or not checks["all_custody_objects_verified"]:
        outcome = "EVIDENCE_BLOCKED_CUSTODY_GAP"
    elif not all(
        checks[key]
        for key in (
            "commit_lineage_complete",
            "transition_ledger_nonempty",
            "v2_not_registry_enrolled",
            "scalar_lane_noncurrent",
            "maxwell_dirac_not_registry_enrolled",
            "mirror_conflict_recorded",
        )
    ):
        outcome = "EVIDENCE_BLOCKED_PROVENANCE_GAP"
    elif (
        not checks["baseline_suite_completed"]
        or not checks["failure_population_complete"]
        or not checks["all_baseline_failures_classified"]
        or not checks["baseline_validation_was_read_only"]
    ):
        outcome = "EVIDENCE_BLOCKED_BASELINE_VALIDATION"
    else:
        outcome = "EVIDENCE_READY_FOR_MAINTENANCE_REPAIR"
    return {
        "schema_id": "REPOSITORY_RECOVERY_PHASE_A_INDEPENDENT_REVIEW_20260719_v0",
        "outcome": outcome,
        "accepted_for_phase_b": outcome == "EVIDENCE_READY_FOR_MAINTENANCE_REPAIR",
        "checks": checks,
        "scientific_execution_authorized": False,
        "scientific_status_changed": False,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--custody", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    review = build_review(args.custody)
    args.out.write_bytes(_canonical(review))
    return 0 if review["accepted_for_phase_b"] else 2


if __name__ == "__main__":
    raise SystemExit(main())

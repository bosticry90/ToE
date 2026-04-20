from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.research import acceptance_review, pilot_pack
from formal.python.research.metadata import ResearchArtifactMetadata, classify_research_artifact


REPO_ROOT = find_repo_root(Path(__file__))

SANDBOX_CANDIDACY_OUTPUT_PATH = Path(
    "formal/output/reports/research_mode_sandbox_candidacy_review_20260419_v0.json"
)


def _ptr(path: Path) -> str:
    return str(path).replace("\\", "/")


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def build_sandbox_candidacy_review() -> dict[str, Any]:
    pack = pilot_pack.build_pilot_pack()
    acceptance = acceptance_review.build_acceptance_review()
    seam = dict(pack["pilots"]["seam"])
    seam_metadata = dict(seam["metadata"])

    candidate_metadata = ResearchArtifactMetadata(
        artifact_id=str(seam_metadata["artifact_id"]),
        research_object=str(seam_metadata["research_object"]),
        research_question=str(seam_metadata["research_question"]),
        test_type=str(seam_metadata["test_type"]),
        output_kind=str(seam_metadata["output_kind"]),
        target_kind=str(seam_metadata["target_kind"]),
        target_binding=str(seam_metadata["target_binding"]),
        delta_class=str(seam_metadata["delta_class"]),
        contradiction_context=str(seam_metadata["contradiction_context"]),
        provenance_family=str(seam_metadata["provenance_family"]),
        nonclaim_boundary=str(seam_metadata["nonclaim_boundary"]),
        promotability="READY_FOR_SANDBOX_REVIEW",
    )
    candidate_class = classify_research_artifact(candidate_metadata)

    sandbox_policy_path = Path("formal/docs/release/SANDBOX_PHYSICS_LANE_EXECUTION_POLICY_20260418_v0.md")
    payload_requirements_path = Path("formal/docs/release/SANDBOX_PROMOTION_PAYLOAD_REQUIREMENTS_20260419_v0.md")
    promotion_lane_path = Path("formal/docs/release/PROMOTION_GOVERNANCE_LANE_POLICY_20260418_v0.md")

    acceptance_ok = (
        acceptance["summary"]["terminal_outcome"] == "RESEARCH_MODE_STEP14_ACCEPTANCE_REVIEW_PASSED_BOUNDED"
        and acceptance["summary"]["step_14_status_v0"] == "COMPLETE_BOUNDED_v0_NONCLAIM"
    )
    direct_math_ok = bool(seam["research_outcome"]["direct_math_artifact_v0"])
    boundary_ok = all(
        [
            not seam["research_outcome"]["canonical_mutation_attempted_v0"],
            int(pack["observability"]["canonical_mutation_attempts"]) == 0,
            int(pack["observability"]["release_gate_truth_changes"]) == 0,
        ]
    )
    contradiction_context_ok = str(candidate_metadata.contradiction_context).strip() not in {"", "NONE"}
    candidate_class_ok = candidate_class == "SANDBOX_CANDIDATE_RESEARCH_ARTIFACT"
    target_binding_ok = candidate_metadata.target_binding == "ROW-SEAM-QM-STAT-001"
    governance_bridge_ok = all(
        [
            (REPO_ROOT / sandbox_policy_path).exists(),
            (REPO_ROOT / payload_requirements_path).exists(),
            (REPO_ROOT / promotion_lane_path).exists(),
        ]
    )
    continuity_identity_ok = all(
        [
            float(seam["metrics"]["continuity_residual_sup_abs"]) == 0.0,
            float(seam["metrics"]["continuity_residual_l1"]) == 0.0,
        ]
    )

    all_criteria_pass = all(
        [
            acceptance_ok,
            direct_math_ok,
            boundary_ok,
            contradiction_context_ok,
            candidate_class_ok,
            target_binding_ok,
            governance_bridge_ok,
            continuity_identity_ok,
        ]
    )

    terminal_outcome = (
        "RESEARCH_MODE_SANDBOX_CANDIDACY_REVIEW_ACCEPTED"
        if all_criteria_pass
        else "RESEARCH_MODE_SANDBOX_CANDIDACY_REVIEW_EVIDENCE_INCOMPLETE"
    )

    return {
        "schema_id": "RESEARCH_MODE_SANDBOX_CANDIDACY_REVIEW_20260419_v0",
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "review_scope_v0": "SELECT_ONE_ACCEPTED_RESEARCH_PILOT_FOR_SANDBOX_CANDIDACY_ONLY",
        "acceptance_precondition_report": acceptance["source_bundle"]["pilot_pack_report"],
        "selected_pilot_key": "seam",
        "criteria": {
            "step14_acceptance_passed": {
                "status_v0": "PASS" if acceptance_ok else "FAIL",
                "criterion_v0": "Step 14 acceptance must pass before any research artifact is advanced to sandbox candidacy.",
            },
            "direct_math_artifact": {
                "status_v0": "PASS" if direct_math_ok else "FAIL",
                "criterion_v0": "The selected research pilot must terminate in a direct mathematical artifact.",
            },
            "boundary_integrity": {
                "status_v0": "PASS" if boundary_ok else "FAIL",
                "criterion_v0": "The selected artifact must preserve the no-canonical-mutation boundary.",
            },
            "candidate_classification": {
                "status_v0": "PASS" if candidate_class_ok else "FAIL",
                "criterion_v0": "The selected artifact must classify as a sandbox candidate under the research metadata schema.",
            },
            "governance_bridge": {
                "status_v0": "PASS" if governance_bridge_ok else "FAIL",
                "criterion_v0": "The selected artifact must point cleanly to the existing sandbox and promotion governance stack.",
            },
        },
        "objective_quality": {
            "criteria": {
                "acceptance_ok": acceptance_ok,
                "direct_math_ok": direct_math_ok,
                "boundary_ok": boundary_ok,
                "candidate_class_ok": candidate_class_ok,
                "governance_bridge_ok": governance_bridge_ok,
                "all_criteria_pass": all_criteria_pass,
            },
            "inputs": {
                "selected_artifact_id": candidate_metadata.artifact_id,
                "selected_artifact_path": seam["artifact_path"],
                "selected_target_binding": candidate_metadata.target_binding,
                "selected_delta_class": candidate_metadata.delta_class,
                "selected_contradiction_context": candidate_metadata.contradiction_context,
                "selected_candidate_class": candidate_class,
                "selected_promotability": candidate_metadata.promotability,
                "sandbox_policy_path": _ptr(sandbox_policy_path),
                "payload_requirements_path": _ptr(payload_requirements_path),
                "promotion_lane_policy_path": _ptr(promotion_lane_path),
            },
            "summary": {
                "selection_basis_v0": "STEP14_ACCEPTED_SEAM_PILOT_WITH_DIRECT_MATH_ARTIFACT_AND_EXPLICIT_QM_STAT_CONTRADICTION_CONTEXT",
                "bridge_limit_v0": "This review accepts sandbox candidacy only; it does not create a sandbox payload record or enter promotion review.",
            },
        },
        "selected_candidate_metadata_record": dict(candidate_metadata.__dict__),
        "summary": {
            "terminal_outcome": terminal_outcome,
            "selected_artifact_id": candidate_metadata.artifact_id,
            "selected_artifact_path": seam["artifact_path"],
            "selected_target_binding": candidate_metadata.target_binding,
            "selected_candidate_class_v0": candidate_class,
            "selected_promotability_v0": candidate_metadata.promotability,
            "sandbox_candidacy_status_v0": (
                "ACCEPTED_BOUNDED_v0_NONCLAIM" if all_criteria_pass else "EVIDENCE_INCOMPLETE_v0_NONCLAIM"
            ),
            "next_action": (
                "AUTHOR_ONE_BOUNDED_SANDBOX_PAYLOAD_RECORD_FOR_QM_STAT_TRANSPORT_WITNESS_ONLY"
                if all_criteria_pass
                else "REPAIR_RESEARCH_SANDBOX_CANDIDACY_INPUTS_AND_RERUN"
            ),
        },
        "source_bundle": {
            "pilot_pack_module": "formal/python/research/pilot_pack.py",
            "pilot_pack_report": pack["report_path"],
            "step14_acceptance_module": "formal/python/research/acceptance_review.py",
            "step14_acceptance_report": "formal/output/reports/research_mode_step14_acceptance_review_20260419_v0.json",
            "sandbox_policy": _ptr(sandbox_policy_path),
            "payload_requirements": _ptr(payload_requirements_path),
            "promotion_lane_policy": _ptr(promotion_lane_path),
        },
        "non_claim_boundary": "Repository-local research-to-sandbox candidacy review only; no sandbox payload emission, promotion review, canonical mutation, or scientific adequacy claim.",
    }


def materialize_sandbox_candidacy_review(repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    review = build_sandbox_candidacy_review()
    _write_json(repo_root / SANDBOX_CANDIDACY_OUTPUT_PATH, review)
    return review


def main() -> int:
    parser = argparse.ArgumentParser(description="Build or write the research-mode sandbox candidacy review.")
    parser.add_argument("--write", action="store_true", help="Write the sandbox candidacy review report into the repository output tree.")
    args = parser.parse_args()

    review = materialize_sandbox_candidacy_review() if args.write else build_sandbox_candidacy_review()
    print(json.dumps(review["summary"], indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
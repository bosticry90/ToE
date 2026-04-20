from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.research import pilot_pack


REPO_ROOT = find_repo_root(Path(__file__))

ACCEPTANCE_OUTPUT_PATH = Path("formal/output/reports/research_mode_step14_acceptance_review_20260419_v0.json")


def _ptr(path: Path) -> str:
    return str(path).replace("\\", "/")


def _write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def build_acceptance_review() -> dict[str, Any]:
    pack = pilot_pack.build_pilot_pack()
    pilots = pack["pilots"]
    pilot_list = list(pilots.values())

    direct_math_artifact_count = int(pack["observability"]["direct_math_artifact_count"])
    release_gate_truth_changes = int(pack["observability"]["release_gate_truth_changes"])
    canonical_mutation_attempts = int(pack["observability"]["canonical_mutation_attempts"])

    artifact_quality_ok = all(
        [
            set(pack["observability"]["target_kinds_covered"]) == {"PILLAR", "SEAM", "MASTER_ACTION"},
            direct_math_artifact_count == 3,
            all(pilot["research_outcome"]["direct_math_artifact_v0"] for pilot in pilot_list),
            pilots["pillar"]["metrics"]["de_bruijn_gap_abs"] == 0.0,
            pilots["seam"]["metrics"]["continuity_residual_sup_abs"] == 0.0,
            pilots["master_action"]["metrics"]["optimized_residual_amplitude_abs"] == 0.0,
        ]
    )

    boundary_integrity_ok = all(
        [
            canonical_mutation_attempts == 0,
            release_gate_truth_changes == 0,
            all(not pilot["research_outcome"]["canonical_mutation_attempted_v0"] for pilot in pilot_list),
            pack["observability"]["boundary_signal_v0"]
            == "ZERO_CANONICAL_MUTATION_ATTEMPTS_AND_PROMOTION_REMAINS_EXTERNAL_TO_RESEARCH_MODE",
        ]
    )

    provenance_families = {pilot["metadata"]["provenance_family"] for pilot in pilot_list}
    shared_runner_path = Path("research_mode_execution.ps1")
    shared_module_path = Path("formal/python/research/pilot_pack.py")
    shared_namespace_path = Path("formal/python/research")

    loop_compression_ok = all(
        [
            artifact_quality_ok,
            boundary_integrity_ok,
            direct_math_artifact_count == len(pilot_list),
            shared_runner_path.exists(),
            shared_module_path.exists(),
            pack["observability"]["throughput_signal_v0"]
            == "THREE_OF_THREE_PILOTS_TERMINATE_IN_DIRECT_MATH_ARTIFACTS",
            pack["summary"]["terminal_outcome"] == "RESEARCH_MODE_PILOT_PACK_MATERIALIZED",
        ]
    )

    repeatability_ok = all(
        [
            len(provenance_families) == 1,
            len(pack["pilot_artifact_paths"]) == 3,
            set(pack["pilot_artifact_paths"].keys()) == {"pillar", "seam", "master_action"},
            shared_runner_path.exists(),
            shared_module_path.exists(),
            shared_namespace_path.exists(),
        ]
    )

    all_criteria_pass = all(
        [
            artifact_quality_ok,
            boundary_integrity_ok,
            loop_compression_ok,
            repeatability_ok,
        ]
    )

    terminal_outcome = (
        "RESEARCH_MODE_STEP14_ACCEPTANCE_REVIEW_PASSED_BOUNDED"
        if all_criteria_pass
        else "RESEARCH_MODE_STEP14_ACCEPTANCE_REVIEW_EVIDENCE_INCOMPLETE"
    )

    return {
        "schema_id": "RESEARCH_MODE_STEP14_ACCEPTANCE_REVIEW_20260419_v0",
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "review_scope_v0": "BOUNDED_ACCEPTANCE_REVIEW_OF_RESEARCH_MODE_PILOT_PACK_ONLY",
        "policy_basis": "formal/docs/release/RESEARCH_MODE_EXECUTION_POLICY_20260419_v0.md",
        "pilot_report_path": pack["report_path"],
        "criteria": {
            "artifact_quality": {
                "status_v0": "PASS" if artifact_quality_ok else "FAIL",
                "criterion_v0": "Each pilot ends in a bounded direct mathematical artifact.",
            },
            "boundary_integrity": {
                "status_v0": "PASS" if boundary_integrity_ok else "FAIL",
                "criterion_v0": "No canonical mutation occurs and promotion remains opt-in.",
            },
            "loop_compression": {
                "status_v0": "PASS_BOUNDED_PROXY" if loop_compression_ok else "FAIL",
                "criterion_v0": "The research lane reaches direct math artifacts through one shared runner and one shared pilot path rather than terminating in governance-only packaging.",
            },
            "repeatability": {
                "status_v0": "PASS_BOUNDED_PROXY" if repeatability_ok else "FAIL",
                "criterion_v0": "The same research-mode execution path can be reused across pillar, seam, and master-action-adjacent targets without bespoke architectural expansion.",
            },
        },
        "objective_quality": {
            "criteria": {
                "artifact_quality_ok": artifact_quality_ok,
                "boundary_integrity_ok": boundary_integrity_ok,
                "loop_compression_ok": loop_compression_ok,
                "repeatability_ok": repeatability_ok,
                "all_criteria_pass": all_criteria_pass,
            },
            "inputs": {
                "pilot_count": len(pilot_list),
                "target_kinds_covered": pack["observability"]["target_kinds_covered"],
                "direct_math_artifact_count": direct_math_artifact_count,
                "canonical_mutation_attempts": canonical_mutation_attempts,
                "release_gate_truth_changes": release_gate_truth_changes,
                "shared_runner_path": _ptr(shared_runner_path),
                "shared_module_path": _ptr(shared_module_path),
                "shared_namespace_path": _ptr(shared_namespace_path),
                "shared_provenance_family": next(iter(provenance_families)),
            },
            "summary": {
                "loop_compression_basis_v0": "BOUNDED_PROXY_SINGLE_SHARED_RUNNER_AND_DIRECT_MATH_TERMINI",
                "repeatability_basis_v0": "BOUNDED_PROXY_SHARED_PROVENANCE_AND_SHARED_EXECUTION_PATH_ACROSS_THREE_TARGET_KINDS",
                "bounded_limit_v0": "This review accepts bounded proxy evidence for loop compression and repeatability, not a historical time-study or longitudinal multi-pack audit.",
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "step_14_status_v0": (
                "COMPLETE_BOUNDED_v0_NONCLAIM" if all_criteria_pass else "EVIDENCE_INCOMPLETE_v0_NONCLAIM"
            ),
            "step_14_disposition_v0": (
                "ACCEPT_ROLLOUT_UNDER_BOUNDED_ACCEPTANCE_REVIEW"
                if all_criteria_pass
                else "RETAIN_PRELIMINARY_SIGNAL_PENDING_MORE_EVIDENCE"
            ),
            "next_action": "REVIEW_PILOT_OUTPUTS_FOR_SANDBOX_CANDIDACY_WITHOUT_CANONICAL_MUTATION",
        },
        "source_bundle": {
            "pilot_pack_module": "formal/python/research/pilot_pack.py",
            "pilot_pack_gate": "formal/python/tests/test_research_mode_pilot_pack_report.py",
            "pilot_pack_report": pack["report_path"],
            "runner": _ptr(shared_runner_path),
        },
        "non_claim_boundary": "Repository-local Step 14 acceptance review only; bounded proxy evidence, no canonical mutation, no scientific adequacy claim.",
    }


def materialize_acceptance_review(repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    review = build_acceptance_review()
    _write_json(repo_root / ACCEPTANCE_OUTPUT_PATH, review)
    return review


def main() -> int:
    parser = argparse.ArgumentParser(description="Build or write the research-mode Step 14 acceptance review.")
    parser.add_argument("--write", action="store_true", help="Write the Step 14 acceptance review report into the repository output tree.")
    args = parser.parse_args()

    review = materialize_acceptance_review() if args.write else build_acceptance_review()
    print(json.dumps(review["summary"], indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
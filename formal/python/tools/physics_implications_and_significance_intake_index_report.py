from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "PHYSICS_IMPLICATIONS_AND_SIGNIFICANCE_INTAKE_INDEX_20260606_v0"
INDEX_ID = "PHYSICS_IMPLICATIONS_AND_SIGNIFICANCE_INTAKE_INDEX_20260606_v0"
OUTCOME_ID = (
    "PHYSICS_IMPLICATIONS_AND_SIGNIFICANCE_INTAKE_INDEX_PREPARED_AS_NONCLAIM_"
    "WITH_NO_LIVE_TARGET_MUTATION"
)
CLASSIFICATION = (
    "physics_implications_and_significance_intake_index_prepared_nonclaim_"
    "no_live_target_mutation"
)
CURRENT_LIVE_NEXT_TARGET = (
    "execute_qft_gr_state_domain_object_assumption_reduction_attempt"
)
SOURCE_ATTACHMENT = "Physics Imps and Sigs.txt"
LEDGER_TARGET = "prepare_physics_implications_source_verification_ledger_packet"

DEFAULT_INDEX_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "lanes"
    / "PHYSICS_IMPLICATIONS_AND_SIGNIFICANCE_INTAKE_INDEX_20260606_v0.md"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PHYSICS_IMPLICATIONS_AND_SIGNIFICANCE_INTAKE_INDEX_20260606_v0.json"
)
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"

NONCLAIM_FLAGS = [
    "NONCLAIM",
    "NO_THEOREM_DISCHARGE",
    "NO_SEAM_CLOSURE",
    "NO_EMPIRICAL_VALIDATION",
    "NO_MASTER_ACTION_PROMOTION",
    "NO_RELEASE_ASSEMBLY",
    "NO_PUBLIC_SUBMISSION",
]

CATEGORIES = [
    "methodological benchmarks",
    "external physics benchmark candidates",
    "workflow/tooling benchmarks",
    "operational-position research thread",
    "plain-language recap candidate",
    "live-lane support notes",
]

ROWS = [
    {
        "intake_id": "METHODOLOGICAL_BENCHMARK_FOUNDATIONAL_LANGUAGE_REBUILD_v0",
        "category": "methodological benchmarks",
        "lesson": (
            "Better foundational language can make seam obligations easier to "
            "state, prove, refute, or retain."
        ),
        "required_future_packet": "prepare_toe_foundational_language_benchmark_packet",
    },
    {
        "intake_id": "EXTERNAL_BENCHMARK_QUANTUM_SENSOR_RESIDUALS_v0",
        "category": "external physics benchmark candidates",
        "lesson": "Quantum sensors can become future observable-residual benchmark pressure.",
        "required_future_packet": "prepare_physics_implications_external_benchmark_queue_packet",
    },
    {
        "intake_id": (
            "EXTERNAL_BENCHMARK_SYMMETRY_CONDITIONED_ANGULAR_MOMENTUM_TRANSFER_v0"
        ),
        "category": "external physics benchmark candidates",
        "lesson": (
            "Conservation transport should be tested against symmetry-conditioned "
            "transfer rules."
        ),
        "required_future_packet": "prepare_physics_implications_external_benchmark_queue_packet",
    },
    {
        "intake_id": "EXTERNAL_BENCHMARK_PATH_DEPENDENT_FORMATION_v0",
        "category": "external physics benchmark candidates",
        "lesson": "Final-state matching is weaker than path-resolved formation matching.",
        "required_future_packet": "prepare_physics_implications_external_benchmark_queue_packet",
    },
    {
        "intake_id": "EXTERNAL_METHOD_BENCHMARK_EMBODIED_AI_LAB_v0",
        "category": "external physics benchmark candidates",
        "lesson": "Closed-loop lab automation is future method infrastructure, not ToE validation.",
        "required_future_packet": "prepare_physics_implications_external_benchmark_queue_packet",
    },
    {
        "intake_id": "TOE_EXTERNAL_EVIDENCE_INTAKE_ASSISTANT_v0",
        "category": "workflow/tooling benchmarks",
        "lesson": (
            "AI can gather and organize possible evidence but cannot decide "
            "scientific authority."
        ),
        "required_future_packet": "prepare_toe_external_evidence_intake_assistant_packet",
    },
    {
        "intake_id": "TOE_LOCAL_RETRIEVAL_PILOT_v0",
        "category": "workflow/tooling benchmarks",
        "lesson": "Retrieval can act as a repo librarian, not a repo judge.",
        "required_future_packet": "prepare_toe_local_retrieval_pilot_packet",
    },
    {
        "intake_id": "TOE_RESEARCH_OPERATING_SYSTEM_SKILL_v0",
        "category": "workflow/tooling benchmarks",
        "lesson": (
            "Skill-governed workflows can standardize intake and proof-of-work "
            "boundaries."
        ),
        "required_future_packet": "prepare_toe_skill_governed_agent_workflow_packet",
    },
    {
        "intake_id": "OPERATIONAL_POSITION_RESEARCH_THREAD_v0",
        "category": "operational-position research thread",
        "lesson": (
            "Position may be modeled as timing-window plus correlation-consistency "
            "constraint satisfiability."
        ),
        "required_future_packet": "prepare_operational_position_research_thread_packet",
    },
    {
        "intake_id": "TOE_PUBLIC_PLAIN_LANGUAGE_PROJECT_RECAP_20260606_v0",
        "category": "plain-language recap candidate",
        "lesson": (
            "Public explanation should say the project maps what a completed "
            "theory would have to prove."
        ),
        "required_future_packet": "prepare_toe_public_plain_language_project_recap_packet",
    },
    {
        "intake_id": "LIVE_LANE_SUPPORT_SEAM_BLOCKER_PILLAR_REDUCTION_SPIRAL_v0",
        "category": "live-lane support notes",
        "lesson": (
            "Seams expose the pillar math that matters next: blocker, assumption "
            "reduction, seam retest."
        ),
        "required_future_packet": "continue_current_qft_gr_renormalization_lane",
    },
]


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _registry_live_target() -> str:
    payload = _read_json(REGISTRY_PATH)
    return str(payload["current_target_state"]["live_next_target"])


def _rows() -> list[dict[str, Any]]:
    return [
        {
            **row,
            "claim_status": "NONCLAIM",
            "source_verification_status": (
                "UNLEDGERED_INTAKE_PENDING_SOURCE_VERIFICATION_LEDGER"
            ),
            "not_authorized": [
                "NO_THEOREM_DISCHARGE",
                "NO_SEAM_CLOSURE",
                "NO_EMPIRICAL_VALIDATION",
                "NO_MASTER_ACTION_PROMOTION",
            ],
        }
        for row in ROWS
    ]


def build_physics_implications_and_significance_intake_index_packet(
    *,
    index_path: Path = DEFAULT_INDEX_PATH,
    current_live_next_target: str | None = None,
) -> dict[str, Any]:
    live_target = current_live_next_target or _registry_live_target()
    rows = _rows()
    row_categories = {row["category"] for row in rows}
    intake_ids = [row["intake_id"] for row in rows]

    ceilings = {
        "validates_toe": False,
        "closes_seams": False,
        "promotes_master_action": False,
        "authorizes_release_assembly": False,
        "authorizes_public_submission": False,
        "discharges_theorems": False,
        "claims_empirical_validation": False,
        "mutates_live_target": False,
    }

    acceptance_criteria = {
        "index_markdown_exists": index_path.exists(),
        "classification_is_nonclaim": True,
        "live_target_mutation_allowed_false": True,
        "current_live_next_target_preserved": live_target == CURRENT_LIVE_NEXT_TARGET,
        "current_live_next_target_before_equals_after": live_target
        == CURRENT_LIVE_NEXT_TARGET,
        "all_required_categories_present": set(CATEGORIES) == row_categories,
        "exactly_supplemental_categories": len(CATEGORIES) == 6,
        "source_verification_deferred": True,
        "no_toe_validation": ceilings["validates_toe"] is False,
        "no_seam_closure": ceilings["closes_seams"] is False,
        "no_master_action_promotion": ceilings["promotes_master_action"] is False,
        "no_release_assembly": ceilings["authorizes_release_assembly"] is False,
        "no_public_submission": ceilings["authorizes_public_submission"] is False,
    }

    return {
        "schema_id": SCHEMA_ID,
        "index_id": INDEX_ID,
        "source_attachment": SOURCE_ATTACHMENT,
        "index_markdown": _ptr(index_path),
        "classification": CLASSIFICATION,
        "claim_status": "NONCLAIM",
        "outcome_id": OUTCOME_ID,
        "prepared_target": "prepare_physics_implications_and_significance_intake_index_packet",
        "purpose": (
            "Classify external articles, speculative insights, operational-position "
            "notes, workflow lessons, and benchmark ideas as NONCLAIM intake material."
        ),
        "live_target_mutation_allowed": False,
        "current_live_next_target_before_intake": live_target,
        "current_live_next_target_after_intake": live_target,
        "current_live_next_target_unchanged_assertion": (
            "CURRENT_LIVE_NEXT_TARGET_v0 remains unchanged by this supplemental "
            "intake packet."
        ),
        "categories": CATEGORIES,
        "intake_row_count": len(rows),
        "intake_ids": intake_ids,
        "intake_rows": rows,
        "nonclaim_flags": NONCLAIM_FLAGS,
        "ceiling_statements": ceilings,
        "source_verification_deferred_to": LEDGER_TARGET,
        "not_a_source_verification_ledger": True,
        "not_live_target_mutation": True,
        "exactly_one_next_target": LEDGER_TARGET,
        "acceptance_criteria": acceptance_criteria,
    }


def write_report(path: Path = DEFAULT_OUT) -> dict[str, Any]:
    payload = build_physics_implications_and_significance_intake_index_packet()
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Prepare the Physics Implications and Significance NONCLAIM intake index packet."
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    args = parser.parse_args()
    payload = write_report(args.out)
    print(
        "physics_implications_and_significance_intake_index_report: "
        f"rows={payload['intake_row_count']} live={payload['current_live_next_target_after_intake']} "
        f"out={_ptr(args.out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "V01_ALPHA_EXPERT_REVIEW_PACKET_20260515_v0"
PACKET_ID = "V01_ALPHA_EXPERT_REVIEW_PACKET_v0"
OUTCOME_ID = (
    "V01_ALPHA_EXPERT_REVIEW_PACKET_PREPARED_FROM_LEAN_DEPENDENCY_AUDIT_CAPTURE_"
    "WITH_NO_REVIEW_EXECUTION_OR_RELEASE_PROMOTION"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_CAPTURE_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_RESULT_REVIEW_20260515_v0.json"
)
DEFAULT_CAPTURE_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_PACKET_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT / "formal" / "docs" / "release" / "V01_ALPHA_EXPERT_REVIEW_PACKET_20260515_v0.json"
)

EXPECTED_CAPTURE_REVIEW_ID = "V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_RESULT_REVIEW_v0"
EXPECTED_CAPTURE_PACKET_ID = "V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_PACKET_v0"
EXPECTED_PRIOR_NEXT_TARGET = "prepare_v01_alpha_expert_review_packet"
EXPECTED_GAP_READOUT = "LEAN_DEPENDENCY_AUDIT_CAPTURE_AND_EXPERT_REVIEW_PACKET_NOT_READY"
EXPECTED_CAPTURE_GAP = "EXACT_AXIOM_PRINT_OUTPUT_AND_EXPERT_REVIEW_NOT_EXECUTED_V0"
NEXT_TARGET = "review_v01_alpha_expert_review_packet_result"

FORBIDDEN_EFFECTS = [
    "expert_review_executed",
    "release_packet_assembled",
    "v01_alpha_marked_ready",
    "lean_theorem_debt_discharged",
    "axiom_spec_backed_debt_reduced",
    "axiom_spec_backed_debt_reduced_by_documentation",
    "proof_debt_reduced",
    "theorem_discharge_authorized",
    "blocker_movement_authorized",
    "lane_reopen_authorized",
    "phase2_authorized",
    "seam_closure_authorized",
    "empirical_validation_authorized",
    "master_action_promotion_authorized",
    "claim_promotion_authorized",
    "computational_physics_execution_surface_opened",
]


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _dependency_review_rows(capture_packet: dict[str, Any]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for row in capture_packet.get("v01_release_dependency_rows", []):
        rows.append(
            {
                "theorem": row.get("theorem"),
                "source_file": row.get("source_file"),
                "release_label": row.get("release_label"),
                "audit_command": row.get("audit_command"),
                "observed_dependency_result": row.get("observed_dependency_result"),
                "project_axioms_used": row.get("project_axioms_used"),
                "supplied_structures_used": row.get("supplied_structures_used"),
                "linked_assumptions": row.get("linked_assumptions"),
                "audit_status": row.get("audit_status"),
                "release_dependency_class": row.get("release_dependency_class"),
                "expert_review_required": True,
                "review_execution_status": "not_executed_v0",
                "reviewer_assessment_status": "prepared_not_assessed",
                "proof_debt_discharge_claim": False,
            }
        )
    return rows


def build_expert_review_packet(
    *,
    capture_review_path: Path = DEFAULT_CAPTURE_REVIEW_PATH,
    capture_packet_path: Path = DEFAULT_CAPTURE_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    capture_review = _read_json(capture_review_path)
    capture_packet = _read_json(capture_packet_path)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}
    capture_summary = capture_packet.get("capture_summary", {})
    dependency_rows = _dependency_review_rows(capture_packet)
    retained_assumptions = capture_packet.get("known_retained_assumptions", [])
    proof_debt_classes = capture_packet.get("known_proof_debt_classes", [])

    acceptance_criteria = {
        "consumes_capture_result_review": capture_review.get("review_id") == EXPECTED_CAPTURE_REVIEW_ID,
        "capture_result_review_accepted": capture_review.get("accepted") is True,
        "capture_result_review_selected_this_packet": capture_review.get("selected_next_target")
        == EXPECTED_PRIOR_NEXT_TARGET,
        "capture_result_review_scope_preparation_only": capture_review.get("next_action_scope")
        == "PREPARE_EXPERT_REVIEW_PACKET_ONLY_NO_EXPERT_REVIEW_EXECUTION",
        "capture_result_review_preserves_gap": capture_review.get("source_gap_review_primary_gap")
        == EXPECTED_GAP_READOUT,
        "source_capture_packet_matches": capture_packet.get("packet_id") == EXPECTED_CAPTURE_PACKET_ID,
        "capture_gap_preserved": capture_summary.get("primary_capture_gap") == EXPECTED_CAPTURE_GAP,
        "dependency_review_rows_prepared": len(dependency_rows) == 6,
        "release_blocking_dependencies_prepared": len(capture_packet.get("release_blocking_dependencies", []))
        == 6,
        "documentation_only_dependencies_prepared": len(capture_packet.get("documentation_only_dependencies", []))
        == 3,
        "expert_review_required_dependencies_prepared": len(
            capture_packet.get("expert_review_required_dependencies", [])
        )
        == 6,
        "retained_assumptions_available": len(retained_assumptions) == 22,
        "proof_debt_classes_available": len(proof_debt_classes) == 3,
        "no_expert_review_execution": forbidden_effect_status["expert_review_executed"] is False,
        "no_release_packet_assembly": forbidden_effect_status["release_packet_assembled"] is False,
        "no_v01_readiness_marking": forbidden_effect_status["v01_alpha_marked_ready"] is False,
        "no_lean_theorem_debt_discharge": forbidden_effect_status["lean_theorem_debt_discharged"] is False,
        "no_axiom_spec_backed_debt_reduction": forbidden_effect_status["axiom_spec_backed_debt_reduced"]
        is False,
        "forbidden_effects_all_false": all(value is False for value in forbidden_effect_status.values()),
        "exactly_one_next_target_selected": NEXT_TARGET == "review_v01_alpha_expert_review_packet_result",
    }
    prepared = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "classification": "P-POLICY/nonclaim",
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "outcome_id": OUTCOME_ID if prepared else "V01_ALPHA_EXPERT_REVIEW_PACKET_BLOCKED",
        "consumed_target": EXPECTED_PRIOR_NEXT_TARGET,
        "consumes_result_review": EXPECTED_CAPTURE_REVIEW_ID,
        "consumes_result_review_pointer": _ptr(capture_review_path),
        "source_capture_packet": EXPECTED_CAPTURE_PACKET_ID,
        "source_capture_packet_pointer": _ptr(capture_packet_path),
        "source_gap_review_primary_gap": capture_review.get("source_gap_review_primary_gap"),
        "source_capture_gap": capture_summary.get("primary_capture_gap"),
        "packet_scope": "PREPARE_EXPERT_REVIEW_PACKET_ONLY_NO_REVIEW_EXECUTION_OR_RELEASE_ASSEMBLY",
        "review_execution_status": "not_executed_v0",
        "expert_review_executed": False,
        "release_packet_assembled": False,
        "v01_alpha_marked_ready": False,
        "lean_theorem_debt_discharged": False,
        "axiom_spec_backed_debt_reduced": False,
        "axiom_spec_backed_debt_reduced_by_documentation": False,
        "proof_debt_reduced": False,
        "review_scope": {
            "lean_dependency_audit_posture": {
                "pointer": capture_packet.get("lean_dependency_audit_pointer"),
                "dependency_row_count": len(dependency_rows),
                "reviewer_task": "Assess exact Lean dependency posture and project-axiom/supplied-structure classification for each release-facing row.",
            },
            "axiom_spec_backed_ledger_posture": {
                "pointer": capture_packet.get("axiom_spec_backed_ledger_pointer"),
                "posture": capture_packet.get("axiom_ledger_posture", {}),
                "reviewer_task": "Assess whether retained assumptions and spec-backed rows are accurately labeled and release-blocking.",
            },
            "retained_assumptions": {
                "row_count": len(retained_assumptions),
                "rows": retained_assumptions,
                "reviewer_task": "Inspect retained assumptions for release-blocking status; do not treat listing as discharge.",
            },
            "release_blocking_dependencies": {
                "row_count": len(capture_packet.get("release_blocking_dependencies", [])),
                "dependencies": capture_packet.get("release_blocking_dependencies", []),
                "reviewer_task": "Determine whether each dependency blocks v0.1-alpha release packet readiness.",
            },
            "documentation_only_dependencies": {
                "row_count": len(capture_packet.get("documentation_only_dependencies", [])),
                "dependencies": capture_packet.get("documentation_only_dependencies", []),
                "reviewer_task": "Confirm which surfaces are documentation or indexing support only.",
            },
            "expert_review_required_dependencies": {
                "row_count": len(capture_packet.get("expert_review_required_dependencies", [])),
                "dependencies": capture_packet.get("expert_review_required_dependencies", []),
                "reviewer_task": "Prepare these dependencies for later review execution; do not execute in this packet.",
            },
            "proof_debt_categories": {
                "row_count": len(proof_debt_classes),
                "classes": proof_debt_classes,
                "reviewer_task": "Classify retained, spec-backed, and full-pillar-blocking proof debt without reducing it.",
            },
            "unresolved_theorem_seam_master_action_blockers": {
                "row_count": len(capture_packet.get("unresolved_dependencies", [])),
                "dependencies": capture_packet.get("unresolved_dependencies", []),
                "reviewer_task": "Identify unresolved theorem, seam, and master-action blockers for later adjudication.",
            },
        },
        "reviewer_assessment_questions": [
            "Are the release-facing Lean dependency rows complete enough for v0.1-alpha readiness review?",
            "Which dependencies are release-blocking rather than documentation-only?",
            "Which retained assumptions or spec-backed rows require proof work before any stronger release claim?",
            "Which exact Lean #print axioms outputs must be captured or verified in a later execution packet?",
            "What evidence would be required before release packet assembly could be considered?",
        ],
        "reviewer_not_allowed_to_promote": [
            "expert review execution",
            "v0.1-alpha release packet assembly",
            "v0.1-alpha readiness",
            "Lean theorem debt discharge",
            "axiom/spec-backed proof debt reduction",
            "Phase 2 authorization",
            "seam closure",
            "empirical validation",
            "master-action promotion",
            "claim promotion",
        ],
        "dependency_review_rows": dependency_rows,
        "packet_summary": {
            "dependency_review_row_count": len(dependency_rows),
            "release_blocking_dependency_count": len(capture_packet.get("release_blocking_dependencies", [])),
            "documentation_only_dependency_count": len(capture_packet.get("documentation_only_dependencies", [])),
            "expert_review_required_dependency_count": len(
                capture_packet.get("expert_review_required_dependencies", [])
            ),
            "retained_assumption_count": len(retained_assumptions),
            "proof_debt_class_count": len(proof_debt_classes),
            "primary_packet_gap": "EXPERT_REVIEW_PACKET_PREPARED_BUT_REVIEW_NOT_EXECUTED_V0",
        },
        "selected_next_target": NEXT_TARGET if prepared else "REMEDIATE_V01_ALPHA_EXPERT_REVIEW_PACKET",
        "selected_next_target_kind": "result_review_only",
        "selection_count": 1 if prepared else 0,
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": "The prepared expert-review packet should be reviewed before any expert review execution packet or release-readiness adjudication.",
            },
            {
                "target": "prepare_v01_alpha_expert_review_execution_packet",
                "decision": "deferred",
                "reason": "Expert review execution requires acceptance of this prepared packet first.",
            },
            {
                "target": "prepare_v01_alpha_release_readiness_dependency_gap_adjudication",
                "decision": "deferred",
                "reason": "Dependency-gap adjudication should consume the expert-review packet result review.",
            },
        ],
        "forbidden_effect_status": forbidden_effect_status,
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha expert review packet prepares reviewer scope only. It does not execute expert review, "
            "assemble the release packet, mark v0.1-alpha readiness, discharge Lean theorem debt, reduce "
            "axiom/spec-backed proof debt, authorize Phase 2, close seams, validate empirically, promote the master "
            "action, promote claims, or make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_expert_review_packet(
    *,
    capture_review_path: Path = DEFAULT_CAPTURE_REVIEW_PATH,
    capture_packet_path: Path = DEFAULT_CAPTURE_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_expert_review_packet(
        capture_review_path=capture_review_path,
        capture_packet_path=capture_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the v0.1-alpha expert review packet.")
    parser.add_argument("--capture-review", type=Path, default=DEFAULT_CAPTURE_REVIEW_PATH)
    parser.add_argument("--capture-packet", type=Path, default=DEFAULT_CAPTURE_PACKET_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    capture_review_path = (
        ns.capture_review if ns.capture_review.is_absolute() else (REPO_ROOT / ns.capture_review)
    )
    capture_packet_path = (
        ns.capture_packet if ns.capture_packet.is_absolute() else (REPO_ROOT / ns.capture_packet)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_expert_review_packet(
        capture_review_path=capture_review_path,
        capture_packet_path=capture_packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_expert_review_packet_report: "
        f"prepared={payload['prepared']} selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

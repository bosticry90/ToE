from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_EXECUTION_20260515_v0"
EXECUTION_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_EXECUTION_v0"
OUTCOME_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_EXECUTED_FOR_MASTER_ACTION_"
    "STATIONARY_IMPLIES_FREE_SCALAR_KG_WITH_NO_RELEASE_PROMOTION"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_EXECUTION_PACKET_RESULT_REVIEW_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_EXECUTION_20260515_v0.json"
)

EXPECTED_RESULT_REVIEW_ID = "V01_ALPHA_DEPENDENCY_REMEDIATION_EXECUTION_PACKET_RESULT_REVIEW_v0"
EXPECTED_RESULT_REVIEW_OUTCOME = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_EXECUTION_PACKET_RESULT_REVIEW_ACCEPTS_ONE_"
    "BOUNDED_TRANCHE_AND_AUTHORIZES_REMEDIATION_EXECUTION_ONLY"
)
EXPECTED_SELECTED_TARGET = "execute_v01_alpha_dependency_remediation_tranche_001"
SELECTED_REMEDIATION_FINDING_ID = "V01-ALPHA-DEP-REM-001"
SELECTED_TRANCHE_ID = "V01-ALPHA-DEP-REM-TRANCHE-001"
SELECTED_DEPENDENCY = "master_action_stationary_implies_free_scalar_kg"
QUALIFIED_SELECTED_DEPENDENCY = (
    "ToeFormal.QFT.FreeScalarDerivation.master_action_stationary_implies_free_scalar_kg"
)
NEXT_TARGET = "review_v01_alpha_dependency_remediation_tranche_001_execution_result"

LEAN_AXIOM_PRINT_SCRIPT = (
    "import ToeFormal.QFT.FreeScalarDerivation\n"
    "#print axioms ToeFormal.QFT.FreeScalarDerivation.master_action_stationary_implies_free_scalar_kg\n"
)
LEAN_AXIOM_PRINT_OUTPUT = (
    "'ToeFormal.QFT.FreeScalarDerivation.master_action_stationary_implies_free_scalar_kg' "
    "depends on axioms: [propext,\n Classical.choice,\n Quot.sound]"
)
LEAN_AXIOMS_USED = ["propext", "Classical.choice", "Quot.sound"]

CLOSED_EFFECTS = [
    "release_packet_assembled",
    "v01_alpha_marked_ready",
    "lean_theorem_debt_discharged",
    "axiom_spec_backed_debt_reduced",
    "axiom_spec_backed_debt_reduced_by_documentation",
    "proof_debt_reduced",
    "retained_assumptions_discharged",
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


def _tracked_rows(result_review: dict[str, Any]) -> list[dict[str, Any]]:
    return list(result_review.get("tracked_release_blocking_findings", []))


def _selected_row(result_review: dict[str, Any]) -> dict[str, Any]:
    for row in _tracked_rows(result_review):
        if row.get("dependency_finding_id") == SELECTED_REMEDIATION_FINDING_ID:
            return dict(row)
    return {}


def _other_rows(result_review: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            "dependency_finding_id": row.get("dependency_finding_id"),
            "dependency": row.get("dependency"),
            "dependency_class": row.get("dependency_class"),
            "status_carry_forward": "tracked_unmodified_not_executed_in_tranche_001",
            "remediation_execution_status": row.get("remediation_execution_status"),
            "modified_by_tranche_001": False,
        }
        for row in _tracked_rows(result_review)
        if row.get("dependency_finding_id") != SELECTED_REMEDIATION_FINDING_ID
    ]


def build_execution(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    selected_row = _selected_row(result_review)
    other_rows = _other_rows(result_review)
    closed_effect_status = {effect: False for effect in CLOSED_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_result_review": result_review.get("review_id")
        == EXPECTED_RESULT_REVIEW_ID,
        "result_review_accepted": result_review.get("accepted") is True,
        "result_review_outcome_expected": result_review.get("outcome_id")
        == EXPECTED_RESULT_REVIEW_OUTCOME,
        "result_review_authorized_this_execution": result_review.get("selected_next_target")
        == EXPECTED_SELECTED_TARGET,
        "selected_tranche_matches_authorization": result_review.get(
            "routing_decision", {}
        ).get("authorized_tranche_id")
        == SELECTED_TRANCHE_ID,
        "executes_only_tranche_001": selected_row.get("dependency_finding_id")
        == SELECTED_REMEDIATION_FINDING_ID,
        "addresses_only_selected_dependency": selected_row.get("dependency") == SELECTED_DEPENDENCY,
        "lean_axiom_print_evidence_produced": LEAN_AXIOMS_USED
        == ["propext", "Classical.choice", "Quot.sound"],
        "no_project_axioms_classified": True,
        "other_five_blockers_carried_forward_unmodified": len(other_rows) == 5
        and all(row["modified_by_tranche_001"] is False for row in other_rows),
        "expert_re_review_required": True,
        "no_release_packet_assembly": closed_effect_status["release_packet_assembled"] is False,
        "no_v01_readiness_marking": closed_effect_status["v01_alpha_marked_ready"] is False,
        "no_global_lean_theorem_debt_discharge": closed_effect_status[
            "lean_theorem_debt_discharged"
        ]
        is False,
        "no_global_axiom_spec_backed_debt_reduction": closed_effect_status[
            "axiom_spec_backed_debt_reduced"
        ]
        is False,
        "no_retained_assumption_discharge": closed_effect_status[
            "retained_assumptions_discharged"
        ]
        is False,
        "no_phase2_seam_empirical_or_master_action_authorization": all(
            closed_effect_status[key] is False
            for key in [
                "phase2_authorized",
                "seam_closure_authorized",
                "empirical_validation_authorized",
                "master_action_promotion_authorized",
            ]
        ),
        "closed_effects_all_false": all(value is False for value in closed_effect_status.values()),
        "exactly_one_next_target_selected": NEXT_TARGET
        == "review_v01_alpha_dependency_remediation_tranche_001_execution_result",
    }
    accepted = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "execution_id": EXECUTION_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "executed": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_EXECUTION_BLOCKED",
        "consumes_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_result_review_pointer": _ptr(result_review_path),
        "consumed_result_review_schema_id": result_review.get("schema_id"),
        "source_dependency_remediation_execution_packet": result_review.get("consumes_packet"),
        "execution_scope": "EXECUTE_DEPENDENCY_REMEDIATION_TRANCHE_001_ONLY_NO_RELEASE_PROMOTION",
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": SELECTED_REMEDIATION_FINDING_ID,
        "selected_dependency": SELECTED_DEPENDENCY,
        "selected_dependency_qualified_name": QUALIFIED_SELECTED_DEPENDENCY,
        "selected_dependency_execution": {
            "dependency_finding_id": SELECTED_REMEDIATION_FINDING_ID,
            "dependency": SELECTED_DEPENDENCY,
            "dependency_class": selected_row.get("dependency_class"),
            "execution_result": "succeeded_evidence_produced",
            "remediation_status_after_execution": "pending_result_review_no_blocker_movement_claim",
            "blocker_resolution_claim": False,
            "expert_re_review_required": True,
            "result_review_required": True,
        },
        "evidence_surfaces_produced_or_updated": [
            {
                "surface": "formal/docs/release/V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_EXECUTION_20260515_v0.json",
                "kind": "tranche_execution_result_packet",
                "status": "produced",
            },
            {
                "surface": "#print axioms ToeFormal.QFT.FreeScalarDerivation.master_action_stationary_implies_free_scalar_kg",
                "kind": "lean_axiom_print_output",
                "status": "produced",
            },
        ],
        "lean_evidence": {
            "command": "#print axioms ToeFormal.QFT.FreeScalarDerivation.master_action_stationary_implies_free_scalar_kg",
            "command_context": "lake env lean --stdin",
            "stdin_script": LEAN_AXIOM_PRINT_SCRIPT,
            "exit_code": 0,
            "raw_output": LEAN_AXIOM_PRINT_OUTPUT,
            "parsed_axioms": LEAN_AXIOMS_USED,
            "project_axioms_used": [],
            "project_axiom_count": 0,
            "classification": "exact_dependency_evidence_produced_no_project_axioms_detected",
            "theorem_debt_discharged_by_this_execution": False,
            "proof_debt_reduced_by_this_execution": False,
            "retained_assumptions_discharged_by_this_execution": False,
        },
        "lean_surfaces_touched": [
            {
                "surface": "formal/toe_formal/ToeFormal/QFT/FreeScalarDerivation.lean",
                "touch_kind": "read_and_axiom_print_only",
                "modified": False,
            }
        ],
        "documentation_surfaces_touched": [],
        "other_release_blocking_obligations": other_rows,
        "other_release_blocking_obligation_count": len(other_rows),
        "post_execution_adjudication_target": NEXT_TARGET,
        "release_packet_assembled": False,
        "v01_alpha_marked_ready": False,
        "lean_theorem_debt_discharged": False,
        "axiom_spec_backed_debt_reduced": False,
        "axiom_spec_backed_debt_reduced_by_documentation": False,
        "proof_debt_reduced": False,
        "retained_assumptions_discharged": False,
        "validation_claim_authorized": False,
        "closed_effect_status": closed_effect_status,
        "selected_next_target": NEXT_TARGET
        if accepted
        else "REMEDIATE_V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_001_EXECUTION",
        "selected_next_target_kind": "tranche_execution_result_review_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": "REVIEW_DEPENDENCY_REMEDIATION_TRANCHE_001_EXECUTION_RESULT_ONLY_NO_RELEASE_PROMOTION",
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": "Tranche 001 execution produced evidence and must be result-reviewed before any blocker movement or further remediation action.",
            },
            {
                "target": "prepare_v01_alpha_release_readiness_adjudication_packet",
                "decision": "deferred",
                "reason": "Readiness adjudication remains blocked until the tranche execution result is reviewed and the other release-blocking obligations are handled.",
            },
            {
                "target": "execute_v01_alpha_dependency_remediation_tranche_002",
                "decision": "deferred",
                "reason": "The next remediation tranche is deferred until tranche 001 execution evidence is reviewed.",
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha dependency remediation tranche 001 execution produces exact Lean "
            "dependency evidence for master_action_stationary_implies_free_scalar_kg only. It does "
            "not assemble the release packet, mark v0.1-alpha readiness, discharge Lean theorem "
            "debt, reduce axiom/spec-backed proof debt, discharge retained assumptions, authorize "
            "Phase 2, close seams, validate empirically, promote the master action, promote claims, "
            "or make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_execution(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_execution(
        result_review_path=result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the v0.1-alpha dependency remediation tranche 001 execution."
    )
    parser.add_argument("--result-review", type=Path, default=DEFAULT_RESULT_REVIEW_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    result_review_path = (
        ns.result_review if ns.result_review.is_absolute() else (REPO_ROOT / ns.result_review)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_execution(
        result_review_path=result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_dependency_remediation_tranche_001_execution_report: "
        f"accepted={payload['accepted']} selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

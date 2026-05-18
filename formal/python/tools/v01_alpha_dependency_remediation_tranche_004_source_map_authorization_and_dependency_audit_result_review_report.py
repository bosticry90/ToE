from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_AND_"
    "DEPENDENCY_AUDIT_RESULT_REVIEW_20260515_v0"
)
REVIEW_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_AND_"
    "DEPENDENCY_AUDIT_RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_AUDIT_RESULT_REVIEW_ACCEPTS_REAL_"
    "SOURCE_MAP_AUTHORIZATION_BLOCKER_AND_AUTHORIZES_REMEDIATION_PLANNING_ONLY"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_AUDIT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_AND_DEPENDENCY_AUDIT_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_AND_DEPENDENCY_AUDIT_RESULT_REVIEW_20260515_v0.json"
)

EXPECTED_AUDIT_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_AND_"
    "DEPENDENCY_AUDIT_v0"
)
EXPECTED_AUDIT_OUTCOME = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_AND_"
    "DEPENDENCY_AUDIT_EXECUTED_WITH_NO_RELEASE_PROMOTION"
)
EXPECTED_AUDIT_SELECTED_TARGET = (
    "review_v01_alpha_dependency_remediation_tranche_004_source_map_authorization_and_"
    "dependency_audit_result"
)
TRANCHE_001_STATUS = "documented_dependency_nonblocking"
TRANCHE_002_STATUS = "documented_dependency_nonblocking"
TRANCHE_003_STATUS = "documented_dependency_nonblocking"
SELECTED_TRANCHE_ID = "V01-ALPHA-DEP-REM-TRANCHE-004"
SELECTED_FINDING_ID = "V01-ALPHA-DEP-REM-004"
SELECTED_DEPENDENCY = (
    "qft_gr_source_map_eligibility_ladder_summary_source_map_not_authorized_v0"
)
SELECTED_DEPENDENCY_CLASS = "blocked_bridge_authorization_dependency"
REQUIRED_REMEDIATION_TYPE = "source_map_authorization_and_dependency_adjudication"
SOURCE_MAP_AUTHORIZATION_STATUS = "full_source_map_semantic_closure_not_authorized"
SOURCE_MAP_NOT_AUTHORIZED_REASON = (
    "obligation_ladder_constructed_witness_chain_absent_source_map_closure_not_authorized"
)
SOURCE_MAP_AUTHORIZATION_BLOCKER_CLASSIFICATION = (
    "real_blocking_source_map_authorization_dependency_pending_result_review"
)
RESULT_REVIEW_CLASSIFICATION = (
    "real_source_map_authorization_blocker_accepted_pending_remediation_planning"
)
LEAN_AXIOMS_USED: list[str] = []
PROJECT_AXIOMS_USED: list[str] = []
NEXT_TARGET = (
    "prepare_v01_alpha_dependency_remediation_tranche_004_source_map_authorization_"
    "remediation_packet"
)

FORBIDDEN_EFFECTS = [
    "remediation_execution_authorized",
    "remediation_executed",
    "broader_remediation_executed",
    "documentation_prepared",
    "policy_adjudication_executed",
    "expert_re_review_executed",
    "blocker_movement_registered",
    "blocker_movement_authorized",
    "blocker_fully_remediated",
    "release_packet_assembled",
    "v01_alpha_marked_ready",
    "lean_theorem_debt_discharged",
    "axiom_spec_backed_debt_reduced",
    "axiom_spec_backed_debt_reduced_by_documentation",
    "proof_debt_reduced",
    "retained_assumptions_discharged",
    "theorem_discharge_authorized",
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


def _source_map_posture(audit: dict[str, Any]) -> dict[str, Any]:
    return dict(audit.get("source_map_authorization_posture", {}))


def _lean_posture(audit: dict[str, Any]) -> dict[str, Any]:
    return dict(audit.get("lean_dependency_posture", {}))


def _policy_assessment(audit: dict[str, Any]) -> dict[str, Any]:
    return dict(audit.get("policy_or_documentation_issue_assessment", {}))


def _release_blockers(audit: dict[str, Any]) -> list[dict[str, Any]]:
    return list(audit.get("release_blocking_obligations_carry_forward", []))


def _other_blockers(audit: dict[str, Any]) -> list[dict[str, Any]]:
    return list(audit.get("other_release_blocking_obligations", []))


def _selected_obligation(rows: list[dict[str, Any]]) -> dict[str, Any]:
    for row in rows:
        if row.get("dependency_finding_id") == SELECTED_FINDING_ID:
            return dict(row)
    return {}


def _release_blockers_tracked(rows: list[dict[str, Any]]) -> bool:
    return (
        len(rows) == 3
        and [row.get("dependency_finding_id") for row in rows]
        == [
            "V01-ALPHA-DEP-REM-004",
            "V01-ALPHA-DEP-REM-005",
            "V01-ALPHA-DEP-REM-006",
        ]
        and all(row.get("modified_by_tranche_003") is False for row in rows)
        and all(
            row.get("status_carry_forward") == "tracked_unmodified_not_audited_in_tranche_003"
            for row in rows
        )
    )


def _other_blockers_unmodified(rows: list[dict[str, Any]]) -> bool:
    return (
        len(rows) == 2
        and [row.get("dependency_finding_id") for row in rows]
        == ["V01-ALPHA-DEP-REM-005", "V01-ALPHA-DEP-REM-006"]
        and all(row.get("modified_by_tranche_004") is False for row in rows)
        and all(
            row.get("status_carry_forward") == "tracked_unmodified_not_audited_in_tranche_004"
            for row in rows
        )
    )


def build_result_review(
    *,
    audit_path: Path = DEFAULT_AUDIT_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    audit = _read_json(audit_path)
    source_map = _source_map_posture(audit)
    lean = _lean_posture(audit)
    assessment = _policy_assessment(audit)
    release_blockers = _release_blockers(audit)
    other_blockers = _other_blockers(audit)
    selected_obligation = _selected_obligation(release_blockers)
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_audit": audit.get("audit_id") == EXPECTED_AUDIT_ID,
        "audit_accepted": audit.get("accepted") is True,
        "audit_executed": audit.get("executed") is True,
        "audit_outcome_expected": audit.get("outcome_id") == EXPECTED_AUDIT_OUTCOME,
        "audit_selected_this_review": audit.get("selected_next_target")
        == EXPECTED_AUDIT_SELECTED_TARGET,
        "tranche_004_only_reviewed_target": audit.get("selected_tranche_id")
        == SELECTED_TRANCHE_ID
        and audit.get("selected_remediation_finding_id") == SELECTED_FINDING_ID
        and audit.get("selected_dependency") == SELECTED_DEPENDENCY,
        "selected_dependency_expected": selected_obligation.get("dependency")
        == SELECTED_DEPENDENCY
        and selected_obligation.get("dependency_class") == SELECTED_DEPENDENCY_CLASS,
        "required_remediation_type_preserved": audit.get("required_remediation_type")
        == REQUIRED_REMEDIATION_TYPE,
        "source_map_posture_exact": source_map.get("authorization_status")
        == SOURCE_MAP_AUTHORIZATION_STATUS
        and source_map.get("full_source_map_semantic_closure_authorized") is False
        and source_map.get("source_map_not_authorized") is True
        and source_map.get("not_authorized_reason") == SOURCE_MAP_NOT_AUTHORIZED_REASON,
        "source_map_evidence_preserved": source_map.get("missing_witness_count") == 10
        and source_map.get("supplied_only_layer_count") == 9
        and source_map.get("retained_blocker_id")
        == "PHASE1-BLOCKER-QFTGR-SOURCE-MAP-WITNESS-CHAIN-RETAINED",
        "lean_audit_no_axioms_preserved": lean.get("parsed_axioms") == LEAN_AXIOMS_USED
        and lean.get("exact_axioms_or_dependencies_used") == LEAN_AXIOMS_USED
        and lean.get("standard_lean_axiom_count") == 0
        and lean.get("depends_on_no_axioms") is True,
        "project_axioms_empty": lean.get("project_axioms_used") == PROJECT_AXIOMS_USED
        and lean.get("project_axiom_count") == 0
        and lean.get("project_local_axioms_present") is False,
        "audit_claims_no_debt_discharge": lean.get(
            "theorem_debt_discharged_by_this_audit"
        )
        is False
        and lean.get("proof_debt_reduced_by_this_audit") is False
        and lean.get("retained_assumptions_discharged_by_this_audit") is False,
        "classification_preserved": assessment.get("classification")
        == SOURCE_MAP_AUTHORIZATION_BLOCKER_CLASSIFICATION
        and assessment.get("source_map_authorization_blocker_retained") is True
        and assessment.get("documentation_only_resolution_supported_by_audit") is False,
        "result_review_classification_expected": RESULT_REVIEW_CLASSIFICATION
        == "real_source_map_authorization_blocker_accepted_pending_remediation_planning",
        "tranche_001_documented_nonblocking_preserved": audit.get("tranche_001_status")
        == TRANCHE_001_STATUS,
        "tranche_002_documented_nonblocking_preserved": audit.get("tranche_002_status")
        == TRANCHE_002_STATUS,
        "tranche_003_documented_nonblocking_preserved": audit.get("tranche_003_status")
        == TRANCHE_003_STATUS,
        "release_blockers_remain_tracked": _release_blockers_tracked(release_blockers),
        "other_blockers_unmodified": _other_blockers_unmodified(other_blockers),
        "no_blocker_movement": audit.get("blocker_movement_registered") is False
        and audit.get("blocker_movement_authorized") is False
        and forbidden_effect_status["blocker_movement_registered"] is False
        and forbidden_effect_status["blocker_movement_authorized"] is False,
        "no_release_packet_assembly": forbidden_effect_status["release_packet_assembled"]
        is False,
        "no_v01_readiness_marking": forbidden_effect_status["v01_alpha_marked_ready"]
        is False,
        "no_theorem_or_proof_debt_discharge": forbidden_effect_status[
            "lean_theorem_debt_discharged"
        ]
        is False
        and forbidden_effect_status["proof_debt_reduced"] is False
        and forbidden_effect_status["axiom_spec_backed_debt_reduced"] is False,
        "no_retained_assumption_discharge": forbidden_effect_status[
            "retained_assumptions_discharged"
        ]
        is False,
        "no_phase2_seam_empirical_or_master_action_authorization": all(
            forbidden_effect_status[key] is False
            for key in [
                "phase2_authorized",
                "seam_closure_authorized",
                "empirical_validation_authorized",
                "master_action_promotion_authorized",
            ]
        ),
        "forbidden_effects_all_false": all(
            value is False for value in forbidden_effect_status.values()
        ),
        "exactly_one_next_target_selected": NEXT_TARGET
        == "prepare_v01_alpha_dependency_remediation_tranche_004_source_map_authorization_remediation_packet",
    }
    accepted = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "review_id": REVIEW_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_AND_"
            "DEPENDENCY_AUDIT_RESULT_REVIEW_BLOCKED"
        ),
        "consumes_audit": EXPECTED_AUDIT_ID,
        "consumes_audit_pointer": _ptr(audit_path),
        "consumed_audit_schema_id": audit.get("schema_id"),
        "source_execution_packet_result_review": audit.get(
            "consumes_tranche_004_execution_packet_result_review"
        ),
        "review_scope": (
            "REVIEW_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_AND_DEPENDENCY_AUDIT_RESULT_ONLY_"
            "NO_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
        ),
        "tranche_001_status": TRANCHE_001_STATUS,
        "tranche_002_status": TRANCHE_002_STATUS,
        "tranche_003_status": TRANCHE_003_STATUS,
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": SELECTED_FINDING_ID,
        "selected_dependency": SELECTED_DEPENDENCY,
        "selected_dependency_class": SELECTED_DEPENDENCY_CLASS,
        "required_remediation_type": REQUIRED_REMEDIATION_TYPE,
        "selected_release_blocking_obligation": selected_obligation,
        "source_map_authorization_posture": source_map,
        "accepted_source_map_authorization_posture": {
            "authorization_status": source_map.get("authorization_status"),
            "not_authorized_reason": source_map.get("not_authorized_reason"),
            "full_source_map_semantic_closure_authorized": source_map.get(
                "full_source_map_semantic_closure_authorized"
            ),
            "source_map_not_authorized": source_map.get("source_map_not_authorized"),
            "retained_blocker_id": source_map.get("retained_blocker_id"),
            "missing_witness_count": source_map.get("missing_witness_count"),
            "supplied_only_layer_count": source_map.get("supplied_only_layer_count"),
        },
        "accepted_lean_dependency_posture": {
            "lean_target": lean.get("lean_target"),
            "lean_source": lean.get("lean_source"),
            "command": lean.get("command"),
            "command_context": lean.get("command_context"),
            "exit_code": lean.get("exit_code"),
            "raw_output": lean.get("raw_output"),
            "parsed_axioms": lean.get("parsed_axioms"),
            "exact_axioms_or_dependencies_used": lean.get(
                "exact_axioms_or_dependencies_used"
            ),
            "standard_lean_axiom_count": lean.get("standard_lean_axiom_count"),
            "project_axioms_used": lean.get("project_axioms_used"),
            "project_axiom_count": lean.get("project_axiom_count"),
            "project_local_axioms_present": lean.get("project_local_axioms_present"),
            "depends_on_no_axioms": lean.get("depends_on_no_axioms"),
            "classification": lean.get("classification"),
        },
        "preserved_audit_classification": assessment.get("classification"),
        "tranche_004_audit_result_review_classification": RESULT_REVIEW_CLASSIFICATION,
        "classification_options_considered": [
            {
                "classification": "audit_evidence_accepted_pending_release_policy_adjudication",
                "decision": "rejected",
                "reason": "The primary blocker is not standard Lean axiom policy; source-map closure remains unauthorized.",
            },
            {
                "classification": "source_map_authorization_blocker_retained_pending_remediation",
                "decision": "accepted_as_input_posture",
                "reason": "The audit preserves the retained blocker and missing witness-chain reason.",
            },
            {
                "classification": RESULT_REVIEW_CLASSIFICATION,
                "decision": "selected",
                "reason": "The next bounded action is source-map authorization remediation planning only.",
            },
        ],
        "review_accepts_real_source_map_authorization_blocker": accepted,
        "lean_dependency_audit_clean": True,
        "project_axioms_used": PROJECT_AXIOMS_USED,
        "source_map_authorization_remediation_packet_preparation_authorized": accepted,
        "release_policy_documentation_path_authorized": False,
        "release_policy_adjudication_packet_preparation_authorized": False,
        "documentation_packet_preparation_authorized": False,
        "expert_re_review_execution_authorized": False,
        "tranche_004_release_blocker_status": (
            "still_blocking_pending_source_map_authorization_remediation_packet_preparation"
        ),
        "release_readiness_blocked_by_tranche_004_source_map_authorization": True,
        "blocker_movement_authorized": False,
        "blocker_movement_registered": False,
        "blocker_fully_remediated": False,
        "remediation_execution_authorized": False,
        "remediation_executed": False,
        "broader_remediation_executed": False,
        "documentation_prepared": False,
        "policy_adjudication_executed": False,
        "expert_re_review_executed": False,
        "release_blocking_obligations_carry_forward": release_blockers,
        "release_blocking_obligation_count": len(release_blockers),
        "other_release_blocking_obligations": other_blockers,
        "other_release_blocking_obligation_count": len(other_blockers),
        "release_packet_assembled": False,
        "v01_alpha_marked_ready": False,
        "lean_theorem_debt_discharged": False,
        "axiom_spec_backed_debt_reduced": False,
        "axiom_spec_backed_debt_reduced_by_documentation": False,
        "proof_debt_reduced": False,
        "retained_assumptions_discharged": False,
        "validation_claim_authorized": False,
        "forbidden_effect_status": forbidden_effect_status,
        "selected_next_target": NEXT_TARGET
        if accepted
        else (
            "REMEDIATE_V01_ALPHA_DEPENDENCY_REMEDIATION_TRANCHE_004_SOURCE_MAP_"
            "AUTHORIZATION_AND_DEPENDENCY_AUDIT_RESULT_REVIEW"
        ),
        "selected_next_target_kind": (
            "tranche_004_source_map_authorization_remediation_packet_preparation_only"
        ),
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_TRANCHE_004_SOURCE_MAP_AUTHORIZATION_REMEDIATION_PACKET_ONLY_"
            "NO_REMEDIATION_EXECUTION_BLOCKER_MOVEMENT_OR_RELEASE_PROMOTION"
        ),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": (
                    "The audit result review accepts a real source-map authorization blocker "
                    "and must prepare the evidence/remediation plan before any further action."
                ),
            },
            {
                "target": (
                    "prepare_v01_alpha_dependency_remediation_tranche_004_release_policy_"
                    "adjudication_packet"
                ),
                "decision": "deferred",
                "reason": "The simple release-policy documentation route is not appropriate before source-map remediation planning.",
            },
            {
                "target": "prepare_v01_alpha_release_readiness_adjudication_packet",
                "decision": "deferred",
                "reason": "Release-readiness adjudication remains blocked by retained source-map authorization and other tracked obligations.",
            },
        ],
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha dependency remediation tranche 004 source-map authorization and "
            "dependency audit result review accepts that the Lean dependency audit is clean "
            "and that project_axioms_used is empty, while preserving full_source_map_semantic_"
            "closure_not_authorized as a real retained blocker caused by the absent witness "
            "chain. It authorizes only source-map authorization remediation packet preparation. "
            "It does not prepare documentation, decide policy, execute remediation, move any "
            "blocker, assemble the release packet, mark v0.1-alpha readiness, discharge "
            "theorem/proof debt, discharge retained assumptions, authorize Phase 2, close "
            "seams, validate empirically, promote the master action, promote claims, or make "
            "an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_result_review(
    *,
    audit_path: Path = DEFAULT_AUDIT_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_result_review(audit_path=audit_path, captured_at_utc=captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha dependency remediation tranche 004 source-map "
            "authorization and dependency audit result review."
        )
    )
    parser.add_argument("--audit", type=Path, default=DEFAULT_AUDIT_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    audit_path = ns.audit if ns.audit.is_absolute() else (REPO_ROOT / ns.audit)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_result_review(
        audit_path=audit_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_dependency_remediation_tranche_004_source_map_authorization_and_dependency_audit_result_review_report: "
        f"accepted={payload['accepted']} classification={payload['tranche_004_audit_result_review_classification']} "
        f"selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_release_hold_packet_due_to_retained_tranche_004_source_map_blocker_result_review_report import (
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT as DEFAULT_RESULT_REVIEW_PATH,
    FORBIDDEN_EFFECTS as RESULT_REVIEW_FORBIDDEN_EFFECTS,
    NEXT_TARGET as EXPECTED_RESULT_REVIEW_SELECTED_TARGET,
    OUTCOME_ID as EXPECTED_RESULT_REVIEW_OUTCOME,
    REVIEW_ID as EXPECTED_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_RESULT_REVIEW_SCHEMA_ID,
    TRANCHE_004_FUTURE_ROUTE,
    TRANCHE_001_STATUS,
    TRANCHE_002_STATUS,
    TRANCHE_003_STATUS,
    TRANCHE_004_CURRENT_BLOCKER,
    TRANCHE_004_DEPENDENCY,
    TRANCHE_004_FINDING_ID,
    TRANCHE_004_RETAINED_REASON,
    TRANCHE_004_STATUS,
    TRANCHE_005_DEPENDENCY,
    TRANCHE_005_STATUS,
    TRANCHE_006_DEPENDENCY,
    TRANCHE_006_DEPENDENCY_CLASS,
    TRANCHE_006_FINDING_ID,
    TRANCHE_006_STATUS,
)
from formal.python.tools.v01_alpha_retained_tranche_004_release_readiness_adjudication_report import (
    RELEASE_READINESS_DECISION,
    SELECTED_TRANCHE_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "V01_ALPHA_POST_HOLD_ROUTING_PACKET_DUE_TO_RETAINED_TRANCHE_004_20260522_v0"
PACKET_ID = "V01_ALPHA_POST_HOLD_ROUTING_PACKET_DUE_TO_RETAINED_TRANCHE_004_v0"
OUTCOME_ID = (
    "V01_ALPHA_POST_HOLD_ROUTING_PACKET_PREPARED_DUE_TO_RETAINED_TRANCHE_004_"
    "WITH_NO_RELEASE_PROMOTION"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_POST_HOLD_ROUTING_PACKET_DUE_TO_RETAINED_TRANCHE_004_20260522_v0.json"
)

NEXT_TARGET = "prepare_v01_alpha_retained_tranche_004_future_remediation_program"
RELEASE_HOLD_SUMMARY_TARGET = "prepare_release_hold_summary_and_pause_v01_alpha_assembly"
MAIN_PHYSICS_SELECTION_TARGET = "return_to_main_physics_target_selection_after_release_hold"
SOURCE_MAP_SANDBOX_TARGET = "prepare_source_map_witness_chain_research_or_sandbox_packet"
ASSEMBLE_RELEASE_PACKET_TARGET = "assemble_v01_alpha_release_packet"

ROUTING_QUESTION = (
    "Given that simple dependency remediation is exhausted but tranche 004 remains "
    "retained/release-blocking, what is the next bounded route?"
)

FORBIDDEN_EFFECTS = sorted(
    set(RESULT_REVIEW_FORBIDDEN_EFFECTS)
    | {
        "future_remediation_program_prepared",
        "main_physics_target_selection_returned",
        "release_hold_summary_prepared",
        "source_map_witness_chain_research_packet_prepared",
    }
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _retained_tranche_004(result_review: dict[str, Any]) -> dict[str, Any]:
    return dict(result_review.get("retained_tranche_004_carry_forward", {}))


def _documented_rows(result_review: dict[str, Any]) -> list[dict[str, Any]]:
    return list(result_review.get("documented_dependency_nonblocking_tranches", []))


def build_routing_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    retained_tranche_004 = _retained_tranche_004(result_review)
    documented_rows = _documented_rows(result_review)
    result_review_forbidden = dict(result_review.get("forbidden_effect_status", {}))
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    routing_options = [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "This route preserves the release hold while defining the future evidence, "
                "authorization, and failure conditions for the retained source-map blocker."
            ),
        },
        {
            "target": RELEASE_HOLD_SUMMARY_TARGET,
            "decision": "deferred",
            "reason": (
                "A hold-summary pause packet remains available after the future remediation "
                "program is scoped or explicitly rejected."
            ),
        },
        {
            "target": MAIN_PHYSICS_SELECTION_TARGET,
            "decision": "deferred",
            "reason": (
                "Returning to broader physics target selection is deferred until tranche 004 "
                "future-remediation obligations are made explicit."
            ),
        },
        {
            "target": SOURCE_MAP_SANDBOX_TARGET,
            "decision": "deferred",
            "reason": (
                "A witness-chain research/sandbox packet is lower-level work and should be "
                "authorized, if at all, by the retained-tranche-004 remediation program."
            ),
        },
        {
            "target": ASSEMBLE_RELEASE_PACKET_TARGET,
            "decision": "not_authorized",
            "reason": (
                "Release assembly remains blocked because tranche 004 remains retained and "
                "source-map closure is not authorized."
            ),
        },
    ]

    acceptance_criteria = {
        "consumes_expected_result_review": result_review.get("review_id")
        == EXPECTED_RESULT_REVIEW_ID,
        "result_review_schema_expected": result_review.get("schema_id")
        == EXPECTED_RESULT_REVIEW_SCHEMA_ID,
        "result_review_accepted": result_review.get("accepted") is True,
        "result_review_outcome_expected": result_review.get("outcome_id")
        == EXPECTED_RESULT_REVIEW_OUTCOME,
        "result_review_selected_this_packet": result_review.get("selected_next_target")
        == EXPECTED_RESULT_REVIEW_SELECTED_TARGET,
        "release_readiness_hold_preserved": result_review.get(
            "release_readiness_decision_status"
        )
        == RELEASE_READINESS_DECISION
        and result_review.get("release_readiness_held") is True
        and result_review.get("release_readiness_still_blocked") is True
        and result_review.get("release_readiness_blocked_by_tranche_004") is True,
        "tranche_001_documented_nonblocking_preserved": result_review.get(
            "tranche_001_status"
        )
        == TRANCHE_001_STATUS,
        "tranche_002_documented_nonblocking_preserved": result_review.get(
            "tranche_002_status"
        )
        == TRANCHE_002_STATUS,
        "tranche_003_documented_nonblocking_preserved": result_review.get(
            "tranche_003_status"
        )
        == TRANCHE_003_STATUS,
        "tranche_005_documented_nonblocking_preserved": result_review.get(
            "tranche_005_status"
        )
        == TRANCHE_005_STATUS
        and result_review.get("tranche_005_dependency") == TRANCHE_005_DEPENDENCY,
        "tranche_006_documented_nonblocking_preserved": result_review.get(
            "tranche_006_status"
        )
        == TRANCHE_006_STATUS
        and result_review.get("tranche_006_dependency") == TRANCHE_006_DEPENDENCY
        and result_review.get("tranche_006_dependency_class") == TRANCHE_006_DEPENDENCY_CLASS
        and result_review.get("tranche_006_dependency_finding_id")
        == TRANCHE_006_FINDING_ID,
        "documented_dependency_queue_count_expected": result_review.get(
            "documented_dependency_nonblocking_tranche_count"
        )
        == 5
        and [row.get("finding_id") for row in documented_rows]
        == [
            "V01-ALPHA-DEP-REM-001",
            "V01-ALPHA-DEP-REM-002",
            "V01-ALPHA-DEP-REM-003",
            "V01-ALPHA-DEP-REM-005",
            "V01-ALPHA-DEP-REM-006",
        ],
        "tranche_004_retained_blocker_preserved": result_review.get(
            "tranche_004_status"
        )
        == TRANCHE_004_STATUS
        and retained_tranche_004.get("status") == TRANCHE_004_STATUS
        and retained_tranche_004.get("dependency_finding_id") == TRANCHE_004_FINDING_ID
        and retained_tranche_004.get("dependency") == TRANCHE_004_DEPENDENCY
        and retained_tranche_004.get("current_blocker") == TRANCHE_004_CURRENT_BLOCKER
        and retained_tranche_004.get("retained_blocker_reason")
        == TRANCHE_004_RETAINED_REASON,
        "simple_dependency_remediation_queue_exhausted": result_review.get(
            "simple_dependency_remediation_queue_exhausted"
        )
        is True
        and result_review.get("dependency_remediation_queue_exhausted") is True,
        "release_packet_not_assembled": result_review.get("release_packet_assembled")
        is False
        and result_review.get("release_assembly_authorized") is False,
        "readiness_not_marked": result_review.get("v01_alpha_marked_ready") is False
        and result_review.get("readiness_marking_authorized") is False,
        "no_theorem_or_proof_debt_discharge": result_review.get(
            "lean_theorem_debt_discharged"
        )
        is False
        and result_review.get("proof_debt_reduced") is False
        and result_review.get("axiom_spec_backed_debt_reduced") is False,
        "no_source_map_or_qft_gr_seam_closure": result_review.get(
            "source_map_closure_claimed"
        )
        is False
        and result_review.get("source_map_closure_achieved") is False
        and result_review.get("qft_gr_seam_closure_claimed") is False
        and result_review.get("qft_gr_seam_closed") is False,
        "no_phase2_empirical_or_master_action_promotion": all(
            result_review.get(key, result_review_forbidden.get(key)) is False
            for key in [
                "phase2_authorized",
                "empirical_validation_authorized",
                "master_action_promotion_authorized",
            ]
        ),
        "future_route_preserved": result_review.get("required_future_route_for_tranche_004")
        == TRANCHE_004_FUTURE_ROUTE,
        "routing_question_prepared_only": ROUTING_QUESTION.startswith("Given that"),
        "selected_future_remediation_program": NEXT_TARGET
        == "prepare_v01_alpha_retained_tranche_004_future_remediation_program",
        "routing_options_include_expected_candidates": [
            row["target"] for row in routing_options
        ]
        == [
            NEXT_TARGET,
            RELEASE_HOLD_SUMMARY_TARGET,
            MAIN_PHYSICS_SELECTION_TARGET,
            SOURCE_MAP_SANDBOX_TARGET,
            ASSEMBLE_RELEASE_PACKET_TARGET,
        ],
        "forbidden_effects_all_false": all(
            value is False for value in forbidden_effect_status.values()
        ),
        "exactly_one_next_target_selected": sum(
            1 for row in routing_options if row["decision"] == "selected"
        )
        == 1,
    }
    accepted = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "V01_ALPHA_POST_HOLD_ROUTING_PACKET_DUE_TO_RETAINED_TRANCHE_004_BLOCKED",
        "consumes_result_review": EXPECTED_RESULT_REVIEW_ID,
        "consumes_result_review_pointer": _ptr(result_review_path),
        "consumed_result_review_schema_id": result_review.get("schema_id"),
        "packet_scope": (
            "PREPARE_POST_HOLD_ROUTING_PACKET_DUE_TO_RETAINED_TRANCHE_004_ONLY_"
            "NO_RELEASE_ASSEMBLY_READINESS_MARKING_OR_PROMOTION"
        ),
        "routing_question": ROUTING_QUESTION,
        "routing_packet_prepared": accepted,
        "routing_decision_made": accepted,
        "selected_route_id": "retained_tranche_004_future_remediation_program",
        "selected_tranche_id": SELECTED_TRANCHE_ID,
        "selected_remediation_finding_id": TRANCHE_004_FINDING_ID,
        "selected_dependency": TRANCHE_004_DEPENDENCY,
        "selected_dependency_class": "blocked_bridge_authorization_dependency",
        "tranche_001_status": TRANCHE_001_STATUS,
        "tranche_002_status": TRANCHE_002_STATUS,
        "tranche_003_status": TRANCHE_003_STATUS,
        "tranche_004_status": TRANCHE_004_STATUS,
        "tranche_005_status": TRANCHE_005_STATUS,
        "tranche_005_dependency": TRANCHE_005_DEPENDENCY,
        "tranche_006_status": TRANCHE_006_STATUS,
        "tranche_006_dependency": TRANCHE_006_DEPENDENCY,
        "tranche_006_dependency_class": TRANCHE_006_DEPENDENCY_CLASS,
        "tranche_006_dependency_finding_id": TRANCHE_006_FINDING_ID,
        "documented_dependency_nonblocking_tranches": documented_rows,
        "documented_dependency_nonblocking_tranche_count": len(documented_rows),
        "dependency_remediation_queue_exhausted": True,
        "simple_dependency_remediation_queue_exhausted": True,
        "retained_tranche_004_carry_forward": retained_tranche_004,
        "retained_release_blocking_obligations": result_review.get(
            "retained_release_blocking_obligations", []
        ),
        "retained_release_blocking_obligation_count": result_review.get(
            "retained_release_blocking_obligation_count"
        ),
        "release_readiness_decision_status": RELEASE_READINESS_DECISION,
        "release_readiness_held": True,
        "release_readiness_still_blocked": True,
        "release_readiness_blocked_by_tranche_004": True,
        "release_readiness_proceed_authorized": False,
        "post_hold_routing_packet_prepared": accepted,
        "future_remediation_program_authorized_for_preparation": accepted,
        "future_remediation_program_prepared": False,
        "release_hold_summary_prepared": False,
        "main_physics_target_selection_returned": False,
        "source_map_witness_chain_research_packet_prepared": False,
        "release_hold_registered": False,
        "release_assembly_authorized": False,
        "release_packet_assembled": False,
        "readiness_marking_authorized": False,
        "v01_alpha_marked_ready": False,
        "source_map_closure_achieved": False,
        "source_map_closure_claimed": False,
        "qft_gr_seam_closed": False,
        "qft_gr_seam_closure_claimed": False,
        "phase2_authorized": False,
        "empirical_validation_authorized": False,
        "master_action_promotion_authorized": False,
        "tranche_004_future_route_required": result_review.get(
            "tranche_004_future_route_required"
        ),
        "required_future_route_for_tranche_004": TRANCHE_004_FUTURE_ROUTE,
        "tranche_004_moved_to_documented_dependency_nonblocking": False,
        "tranche_004_status_downgraded": False,
        "tranche_004_retained_blocker_discharged": False,
        "lean_theorem_debt_discharged": False,
        "axiom_spec_backed_debt_reduced": False,
        "axiom_spec_backed_debt_reduced_by_documentation": False,
        "proof_debt_reduced": False,
        "retained_assumptions_discharged": False,
        "validation_claim_authorized": False,
        "forbidden_effect_status": forbidden_effect_status,
        "routing_options": routing_options,
        "selected_next_target": NEXT_TARGET
        if accepted
        else "REMEDIATE_V01_ALPHA_POST_HOLD_ROUTING_PACKET_DUE_TO_RETAINED_TRANCHE_004",
        "selected_next_target_kind": "retained_tranche_004_future_remediation_program_preparation_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_RETAINED_TRANCHE_004_FUTURE_REMEDIATION_PROGRAM_ONLY_"
            "NO_RELEASE_ASSEMBLY_READINESS_MARKING_OR_PROMOTION"
        ),
        "candidate_next_targets": routing_options,
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The post-hold routing packet chooses only the next control route after the "
            "v0.1-alpha release hold. It selects future remediation-program preparation "
            "for retained tranche 004 and does not prepare that program, assemble release, "
            "mark readiness, downgrade tranche 004, discharge theorem/proof debt or "
            "retained assumptions, claim source-map or QFT-GR seam closure, authorize "
            "Phase 2, validate empirically, promote the master action, or make an "
            "external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_routing_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_routing_packet(
        result_review_path=result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha post-hold routing packet due to retained tranche 004."
        )
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
    payload = write_routing_packet(
        result_review_path=result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_post_hold_routing_packet_due_to_retained_tranche_004_report: "
        f"accepted={payload['accepted']} route={payload['selected_route_id']} "
        f"selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

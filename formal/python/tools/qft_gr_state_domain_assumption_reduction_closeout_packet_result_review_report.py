from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_covariant_conservation_assumption_reduction_packet_report import (
    DEFAULT_OUT as DEFAULT_FAMILY_MAP_PATH,
)
from formal.python.tools.qft_gr_state_domain_assumption_reduction_closeout_packet_report import (
    BLOCKER,
    CLOSEOUT_CLASSIFICATION as EXPECTED_PACKET_CLASSIFICATION,
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT as DEFAULT_PACKET_PATH,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as EXPECTED_PACKET_OUTCOME,
    PACKET_ID as EXPECTED_PACKET_ID,
    SCHEMA_ID as EXPECTED_PACKET_SCHEMA_ID,
    SELECTED_ASSUMPTION_FAMILY,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "QFT_GR_STATE_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_"
    "RESULT_REVIEW_20260608_v0"
)
REVIEW_ID = "QFT_GR_STATE_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_v0"
OUTCOME_ID = (
    "QFT_GR_STATE_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_"
    "ACCEPTS_STATE_DOMAIN_FAMILY_CLOSEOUT_AND_AUTHORIZES_NEXT_ASSUMPTION_"
    "FAMILY_SELECTION_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_state_domain_assumption_reduction_closeout_packet_result_review_"
    "accepts_state_domain_family_closeout_and_authorizes_next_assumption_"
    "family_selection_only"
)
NEXT_ASSUMPTION_FAMILY = "mathematical_regularity_assumptions"
NEXT_TARGET = "prepare_qft_gr_mathematical_regularity_assumption_reduction_packet"
NEXT_TARGET_KIND = "qft_gr_mathematical_regularity_assumption_reduction_packet_preparation"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_STATE_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_"
        "RESULT_REVIEW_20260608_v0.json"
    )
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _accepted_rows() -> list[str]:
    return [
        "SD-ASSUMP-001-state_domain_object",
        "SD-ASSUMP-002-state_admissibility_boundary",
        "SD-ASSUMP-003-state_expectation_compatibility",
    ]


def _expected_assumption_classes() -> list[str]:
    return [
        "mathematical_regularity_assumptions",
        "renormalization_assumptions",
        "operator_domain_assumptions",
        "state_domain_assumptions",
        "geometric_Bianchi_assumptions",
        "physical_source_admissibility_assumptions",
    ]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "Operator-domain, renormalization, and state-domain assumption "
                "families are now accepted at row-reduction closeout level for "
                "this lane. The repo-authoritative six-family map still marks "
                "mathematical regularity as candidate-reducible, while Bianchi "
                "and physical source-admissibility remain not reducible in the "
                "current lane."
            ),
        },
        {
            "target": "prepare_qft_gr_bianchi_compatibility_assumption_reduction_packet",
            "decision": "not_authorized_current_lane",
            "reason": (
                "Geometric/Bianchi assumptions are present in the six-family "
                "map, but that map marks them not reducible in the current lane."
            ),
        },
        {
            "target": "prepare_qft_gr_physical_source_admissibility_assumption_reduction_packet",
            "decision": "not_authorized_current_lane",
            "reason": (
                "Physical source-admissibility assumptions are present in the "
                "six-family map, but that map marks them not reducible in the "
                "current lane."
            ),
        },
        {
            "target": "construct_qft_gr_conservation_proof_object",
            "decision": "not_authorized",
            "reason": (
                "State-domain closeout result review does not construct or "
                "authorize a conservation proof object."
            ),
        },
        {
            "target": "construct_qft_gr_conservation_witness",
            "decision": "not_authorized",
            "reason": "No conservation witness is constructed or authorized.",
        },
        {
            "target": "claim_qft_gr_state_admissibility",
            "decision": "not_authorized",
            "reason": (
                "Accepted state-domain rows remain bounded row reductions and "
                "do not imply state admissibility."
            ),
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": (
                "Accepted state-domain rows do not imply stress-energy source "
                "admissibility."
            ),
        },
        {
            "target": "claim_qft_gr_bianchi_compatibility",
            "decision": "not_authorized",
            "reason": (
                "Accepted state-domain rows do not imply Bianchi compatibility."
            ),
        },
        {
            "target": "derive_semiclassical_einstein_equation",
            "decision": "not_authorized",
            "reason": "The semiclassical Einstein equation is not derived here.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "QFT-GR seam closure remains explicitly unclaimed.",
        },
        {
            "target": "authorize_release_assembly_or_public_submission",
            "decision": "not_authorized",
            "reason": "Release assembly and public submission remain unauthorized.",
        },
    ]


def build_qft_gr_state_domain_assumption_reduction_closeout_packet_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    family_map_path: Path = DEFAULT_FAMILY_MAP_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    family_map = _read_json(family_map_path)
    candidate_next_targets = _candidate_next_targets()
    accepted_rows = _accepted_rows()
    expected_classes = _expected_assumption_classes()
    candidate_reducible = family_map.get("candidate_reducible_assumption_classes", [])
    not_reducible = family_map.get("not_reducible_in_current_lane_classes", [])
    completed_families = [
        "operator_domain_assumptions",
        "renormalization_assumptions",
        "state_domain_assumptions",
    ]

    acceptance_criteria = {
        "consumes_expected_closeout_packet": packet.get("schema_id")
        == EXPECTED_PACKET_SCHEMA_ID
        and packet.get("packet_id") == EXPECTED_PACKET_ID,
        "packet_outcome_expected": packet.get("outcome_id")
        == EXPECTED_PACKET_OUTCOME,
        "packet_classification_expected": packet.get("closeout_classification")
        == EXPECTED_PACKET_CLASSIFICATION,
        "packet_selected_this_review": packet.get("selected_next_target")
        == CONSUMED_TARGET,
        "packet_specific_selected_target_preserved": packet.get(
            "state_domain_assumption_reduction_closeout_packet_selected_next_target"
        )
        == packet.get("selected_next_target")
        == CONSUMED_TARGET,
        "packet_and_result_review_selected_targets_split": NEXT_TARGET
        != CONSUMED_TARGET,
        "packet_is_prepared_and_accepted": packet.get("prepared") is True
        and packet.get("accepted") is True,
        "all_three_state_domain_rows_accepted": packet.get(
            "accepted_state_domain_assumption_rows"
        )
        == accepted_rows
        and packet.get("accepted_state_domain_assumption_row_count") == 3,
        "no_remaining_state_domain_row": packet.get(
            "no_remaining_state_domain_assumption_row_in_current_inventory"
        )
        is True
        and packet.get("state_domain_assumption_reduction_row_inventory_exhausted")
        is True
        and packet.get("next_state_domain_assumption_row") is None,
        "state_domain_family_closed_only_for_this_lane": packet.get(
            "state_domain_assumptions_reduced_for_this_lane"
        )
        is True
        and packet.get("state_domain_assumption_reduction_family_reduced") is True,
        "broader_conservation_blocker_preserved": packet.get("blocker") == BLOCKER
        and packet.get("conservation_blocker_remains") is True,
        "six_family_map_present": family_map.get("assumption_classes")
        == expected_classes
        and family_map.get("assumption_class_count") == 6,
        "mathematical_regularity_is_next_reducible_family": NEXT_ASSUMPTION_FAMILY
        in candidate_reducible,
        "completed_families_are_not_reselected": (
            SELECTED_ASSUMPTION_FAMILY == "state_domain_assumptions"
            and SELECTED_ASSUMPTION_FAMILY in completed_families
            and NEXT_ASSUMPTION_FAMILY not in completed_families
        ),
        "nonselected_family_posture_preserved": (
            "geometric_Bianchi_assumptions" in not_reducible
            and "physical_source_admissibility_assumptions" in not_reducible
        ),
        "packet_does_not_discharge_assumptions": packet.get(
            "assumption_discharge_claimed"
        )
        is False
        and packet.get("assumptions_discharged_by_closeout") is False,
        "no_state_admissibility": packet.get("state_admissibility_claimed")
        is False
        and packet.get("state_admissibility_discharged") is False,
        "no_source_admissibility": packet.get("source_admissibility_claimed")
        is False
        and packet.get("stress_energy_source_admissibility_claimed") is False,
        "no_conservation_proof": packet.get("conservation_proved") is False
        and packet.get("actual_conservation_claimed") is False,
        "no_conservation_proof_object": packet.get(
            "conservation_proof_object_constructed"
        )
        is False
        and packet.get("proof_object_constructed") is False,
        "no_conservation_witness": packet.get("conservation_witness_constructed")
        is False,
        "no_bianchi_compatibility": packet.get("Bianchi_compatibility_claimed")
        is False,
        "no_semiclassical_einstein_derivation": packet.get(
            "semiclassical_einstein_equation_derived"
        )
        is False,
        "no_qft_gr_seam_closure": packet.get("qft_gr_seam_closed") is False,
        "no_empirical_validation": packet.get("empirical_validation_claimed")
        is False,
        "no_master_action_promotion": packet.get("master_action_promoted") is False
        and packet.get("master_action_promotion_authorized") is False,
        "no_release_or_public_submission": packet.get("release_assembly_authorized")
        is False
        and packet.get("release_packet_assembled") is False
        and packet.get("public_submission_authorized") is False,
        "exactly_one_next_target_selected": sum(
            1 for row in candidate_next_targets if row["decision"] == "selected"
        )
        == 1
        and candidate_next_targets[0]["target"] == NEXT_TARGET,
    }
    accepted = all(acceptance_criteria.values())
    selected_result_review_next_target = (
        NEXT_TARGET
        if accepted
        else (
            "REMEDIATE_QFT_GR_STATE_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_"
            "PACKET_RESULT_REVIEW"
        )
    )

    return {
        "schema_id": SCHEMA_ID,
        "review_id": REVIEW_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "review_decision": "accepted" if accepted else "rejected",
        "outcome_id": OUTCOME_ID
        if accepted
        else (
            "QFT_GR_STATE_DOMAIN_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_"
            "RESULT_REVIEW_REJECTS_OR_REQUIRES_REMEDIATION"
        ),
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION
        if accepted
        else (
            "qft_gr_state_domain_assumption_reduction_closeout_packet_"
            "result_review_rejects_or_requires_remediation"
        ),
        "result_review_classification_count": 1 if accepted else 0,
        "consumes_qft_gr_state_domain_assumption_reduction_closeout_packet": (
            EXPECTED_PACKET_ID
        ),
        "consumes_qft_gr_state_domain_assumption_reduction_closeout_packet_pointer": _ptr(
            packet_path
        ),
        "consumed_target": CONSUMED_TARGET,
        "packet_selected_next_target": CONSUMED_TARGET,
        "result_review_selected_next_target": selected_result_review_next_target,
        "state_domain_assumption_reduction_closeout_packet_selected_next_target": (
            CONSUMED_TARGET
        ),
        "state_domain_assumption_reduction_closeout_packet_result_review_selected_next_target": (
            selected_result_review_next_target
        ),
        "packet_result_review_selected_target_split_preserved": (
            accepted and selected_result_review_next_target != CONSUMED_TARGET
        ),
        "consumed_packet_schema_id": packet.get("schema_id"),
        "consumed_packet_outcome_id": packet.get("outcome_id"),
        "consumed_packet_classification": packet.get("closeout_classification"),
        "repo_authoritative_assumption_family_map": _ptr(family_map_path),
        "assumption_classes": expected_classes,
        "assumption_class_count": 6,
        "candidate_reducible_assumption_classes": candidate_reducible,
        "not_reducible_in_current_lane_classes": not_reducible,
        "completed_assumption_families_for_this_lane": completed_families,
        "completed_assumption_family_count": len(completed_families),
        "blocker": BLOCKER,
        "selected_blocker": BLOCKER,
        "blocker_remains": BLOCKER,
        "conservation_blocker_remains": True,
        "broader_blocker_resolution_required": True,
        "selected_assumption_family": SELECTED_ASSUMPTION_FAMILY,
        "closed_assumption_family": SELECTED_ASSUMPTION_FAMILY,
        "primary_assumption_reduction_family": SELECTED_ASSUMPTION_FAMILY,
        "accepted_state_domain_assumption_rows": accepted_rows,
        "accepted_state_domain_assumption_row_count": 3,
        "state_domain_assumptions_closed_for_this_lane": accepted,
        "state_domain_assumptions_reduced_for_this_lane": accepted,
        "state_domain_assumption_reduction_family_reduced": accepted,
        "state_domain_assumption_reduction_closeout_packet_reviewed": accepted,
        "state_domain_assumption_reduction_closeout_accepted": accepted,
        "state_domain_assumption_reduction_closeout_rejected": not accepted,
        "state_domain_assumption_reduction_closeout_scope": (
            "state_domain_assumption_family_closed_for_this_lane_only"
        ),
        "state_domain_assumption_reduction_row_inventory_exhausted": accepted,
        "no_remaining_state_domain_assumption_row_in_current_inventory": accepted,
        "next_state_domain_assumption_row": None,
        "assumption_family_selection_authorized": accepted,
        "next_assumption_family": NEXT_ASSUMPTION_FAMILY,
        "next_assumption_family_selection_only": accepted,
        "mathematical_regularity_assumption_reduction_packet_authorized": accepted,
        "geometric_Bianchi_assumption_reduction_packet_not_authorized_current_lane": True,
        "physical_source_admissibility_assumption_reduction_packet_not_authorized_current_lane": True,
        "state_admissibility_claimed": False,
        "state_admissibility_discharged": False,
        "source_admissibility_claimed": False,
        "stress_energy_source_admissibility_claimed": False,
        "conservation_proved": False,
        "actual_conservation_claimed": False,
        "covariant_conservation_statement_proved": False,
        "proof_object_constructed": False,
        "conservation_proof_object_constructed": False,
        "conservation_witness_constructed": False,
        "Bianchi_compatibility_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "qft_gr_seam_closed": False,
        "qft_gr_source_map_closure_claimed": False,
        "empirical_validation_claimed": False,
        "scientific_validation_claimed": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "release_assembly_authorized": False,
        "release_packet_assembled": False,
        "public_submission_authorized": False,
        "publication_authorized": False,
        "assumption_discharge_claimed": False,
        "assumptions_discharged_by_closeout_review": False,
        "assumptions_reduced_or_discharged_by_closeout_review": False,
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": selected_result_review_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selected_route": (
            "qft_gr_mathematical_regularity_assumption_reduction_packet_"
            "preparation_after_state_domain_family_closeout_review"
        ),
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_QFT_GR_MATHEMATICAL_REGULARITY_ASSUMPTION_REDUCTION_"
            "PACKET_ONLY_NO_CONSERVATION_WITNESS_OR_QFT_GR_SEAM_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This result review accepts only the state-domain assumption row "
            "closeout for this assumption-reduction lane and authorizes "
            "selection of the next assumption family. It preserves blocker "
            "insufficient_assumptions_for_conservation and does not claim "
            "state admissibility, claim source admissibility, prove "
            "conservation, construct a conservation proof object or witness, "
            "claim Bianchi compatibility, derive the semiclassical Einstein "
            "equation, close QFT-GR, validate empirically, promote the master "
            "action, assemble release, or authorize public submission."
        ),
    }


def write_qft_gr_state_domain_assumption_reduction_closeout_packet_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    family_map_path: Path = DEFAULT_FAMILY_MAP_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_state_domain_assumption_reduction_closeout_packet_result_review(
        packet_path=packet_path,
        family_map_path=family_map_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR state-domain assumption-reduction closeout "
            "packet result review."
        )
    )
    parser.add_argument("--packet", type=Path, default=DEFAULT_PACKET_PATH)
    parser.add_argument("--family-map", type=Path, default=DEFAULT_FAMILY_MAP_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    packet_path = ns.packet if ns.packet.is_absolute() else (REPO_ROOT / ns.packet)
    family_map_path = (
        ns.family_map if ns.family_map.is_absolute() else (REPO_ROOT / ns.family_map)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_state_domain_assumption_reduction_closeout_packet_result_review(
        packet_path=packet_path,
        family_map_path=family_map_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_state_domain_assumption_reduction_closeout_packet_result_review_report: "
        f"accepted={payload['accepted']} next_family={payload['next_assumption_family']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

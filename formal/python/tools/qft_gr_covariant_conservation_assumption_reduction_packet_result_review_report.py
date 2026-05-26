from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_covariant_conservation_assumption_reduction_packet_report import (
    DEFAULT_OUT as DEFAULT_PACKET_PATH,
    NEXT_TARGET as EXPECTED_REVIEW_TARGET,
    OUTCOME_ID as EXPECTED_PACKET_OUTCOME,
    PACKET_CLASSIFICATION as EXPECTED_PACKET_CLASSIFICATION,
    PACKET_ID as EXPECTED_PACKET_ID,
    SCHEMA_ID as EXPECTED_PACKET_SCHEMA_ID,
)
from formal.python.tools.qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet_result_review_report import (
    PRIMARY_BLOCKER,
)
from formal.python.tools.qft_gr_covariant_conservation_statement_witness_packet_report import (
    DEFAULT_CAPTURED_AT_UTC,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "QFT_GR_COVARIANT_CONSERVATION_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_"
    "20260525_v0"
)
REVIEW_ID = "QFT_GR_COVARIANT_CONSERVATION_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_v0"
OUTCOME_ID = (
    "QFT_GR_COVARIANT_CONSERVATION_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_"
    "ACCEPTS_ASSUMPTION_FAMILY_CLASSIFICATION_AND_AUTHORIZES_PRIMARY_ASSUMPTION_"
    "REDUCTION_TARGET_SELECTION_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_covariant_conservation_assumption_reduction_packet_result_review_accepts_"
    "assumption_family_classification_and_authorizes_primary_assumption_reduction_"
    "target_selection_only"
)
CONSUMED_TARGET = EXPECTED_REVIEW_TARGET
PRIMARY_ASSUMPTION_REDUCTION_TARGET = (
    "prepare_qft_gr_operator_domain_assumption_reduction_packet"
)
NEXT_TARGET = PRIMARY_ASSUMPTION_REDUCTION_TARGET

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_COVARIANT_CONSERVATION_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_20260525_v0.json"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


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
            "reason": "The prior missing covariant-derivative/operator-domain blocker makes operator-domain assumption reduction the coherent first target.",
        },
        {
            "target": "prepare_qft_gr_state_domain_assumption_reduction_packet",
            "decision": "deferred",
            "reason": "State-domain reduction remains plausible after operator-domain assumptions are reviewed.",
        },
        {
            "target": "prepare_qft_gr_renormalization_assumption_reduction_packet",
            "decision": "deferred",
            "reason": "Renormalization reduction remains downstream of the primary operator-domain target.",
        },
        {
            "target": "prepare_qft_gr_bianchi_compatibility_assumption_reduction_packet",
            "decision": "deferred",
            "reason": "Bianchi compatibility is downstream and not selected as the first reduction target.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "Reviewing assumption classification does not close QFT-GR.",
        },
    ]


def build_qft_gr_covariant_conservation_assumption_reduction_packet_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    candidate_next_targets = _candidate_next_targets()
    expected_classes = _expected_assumption_classes()
    acceptance_criteria = {
        "consumes_expected_packet": packet.get("packet_id") == EXPECTED_PACKET_ID,
        "packet_schema_expected": packet.get("schema_id") == EXPECTED_PACKET_SCHEMA_ID,
        "packet_outcome_expected": packet.get("outcome_id") == EXPECTED_PACKET_OUTCOME,
        "packet_classification_expected": packet.get("packet_classification")
        == EXPECTED_PACKET_CLASSIFICATION,
        "packet_selected_this_review": packet.get("selected_next_target")
        == CONSUMED_TARGET,
        "preserves_insufficient_assumptions_blocker": packet.get("selected_blocker")
        == PRIMARY_BLOCKER
        and packet.get("blocker") == PRIMARY_BLOCKER,
        "all_six_assumption_families_present": packet.get("assumption_classes")
        == expected_classes
        and packet.get("assumption_class_count") == 6,
        "no_assumption_reduced_or_discharged": packet.get(
            "reduces_or_discharges_assumptions_by_preparation"
        )
        is False,
        "no_proof_object_constructed": packet.get("proof_object_constructed")
        is False
        and packet.get("conservation_proof_object_constructed") is False,
        "no_conservation_witness_constructed": packet.get(
            "conservation_witness_constructed"
        )
        is False,
        "no_source_or_bianchi_claim": packet.get(
            "stress_energy_source_admissibility_claimed"
        )
        is False
        and packet.get("Bianchi_compatibility_claimed") is False,
        "no_einstein_or_qft_gr_closure": packet.get(
            "semiclassical_einstein_equation_derived"
        )
        is False
        and packet.get("qft_gr_seam_closed") is False,
        "no_empirical_master_release_or_public_submission": packet.get(
            "empirical_validation_claimed"
        )
        is False
        and packet.get("master_action_promoted") is False
        and packet.get("release_assembly_authorized") is False
        and packet.get("public_submission_authorized") is False,
        "exactly_one_next_target_selected": sum(
            1 for row in candidate_next_targets if row["decision"] == "selected"
        )
        == 1
        and candidate_next_targets[0]["target"] == NEXT_TARGET,
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
        else "QFT_GR_COVARIANT_CONSERVATION_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_BLOCKED",
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION,
        "result_review_classification_count": 1 if accepted else 0,
        "consumes_qft_gr_covariant_conservation_assumption_reduction_packet": EXPECTED_PACKET_ID,
        "consumes_qft_gr_covariant_conservation_assumption_reduction_packet_pointer": _ptr(
            packet_path
        ),
        "consumed_packet_outcome_id": packet.get("outcome_id"),
        "consumed_packet_classification": packet.get("packet_classification"),
        "blocker": PRIMARY_BLOCKER,
        "selected_blocker": PRIMARY_BLOCKER,
        "assumption_family_classification_accepted": accepted,
        "assumption_classes": expected_classes,
        "assumption_class_count": len(expected_classes),
        "primary_assumption_reduction_family": "operator_domain_assumptions",
        "primary_assumption_reduction_target": NEXT_TARGET,
        "assumptions_reduced_or_discharged_by_review": False,
        "proof_object_constructed": False,
        "conservation_proof_object_constructed": False,
        "conservation_witness_constructed": False,
        "stress_energy_source_admissibility_claimed": False,
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
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": NEXT_TARGET
        if accepted
        else "REMEDIATE_QFT_GR_COVARIANT_CONSERVATION_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW",
        "selected_next_target_kind": (
            "qft_gr_operator_domain_assumption_reduction_packet_preparation"
        ),
        "selected_route": (
            "qft_gr_operator_domain_assumption_reduction_packet_preparation_after_assumption_family_classification_review"
        ),
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_QFT_GR_OPERATOR_DOMAIN_ASSUMPTION_REDUCTION_PACKET_ONLY_"
            "NO_ASSUMPTION_DISCHARGE_OR_QFT_GR_SEAM_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This result review accepts only the six-family assumption "
            "classification and selects the primary operator-domain assumption "
            "reduction target. It does not reduce or discharge assumptions, "
            "construct a proof object or conservation witness, claim source "
            "admissibility or Bianchi compatibility, derive the semiclassical "
            "Einstein equation, close QFT-GR, validate empirically, promote the "
            "master action, assemble release, or authorize public submission."
        ),
    }


def write_qft_gr_covariant_conservation_assumption_reduction_packet_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_covariant_conservation_assumption_reduction_packet_result_review(
        packet_path=packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QFT-GR covariant conservation assumption-reduction packet result review."
    )
    parser.add_argument("--packet", type=Path, default=DEFAULT_PACKET_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    packet_path = ns.packet if ns.packet.is_absolute() else (REPO_ROOT / ns.packet)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_covariant_conservation_assumption_reduction_packet_result_review(
        packet_path=packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_covariant_conservation_assumption_reduction_packet_result_review_report: "
        f"accepted={payload['accepted']} primary={payload['primary_assumption_reduction_family']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

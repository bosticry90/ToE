from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet_result_review_report import (
    DEFAULT_OUT as DEFAULT_RESULT_REVIEW_PATH,
    NEXT_TARGET as EXPECTED_PACKET_TARGET,
    OUTCOME_ID as EXPECTED_RESULT_REVIEW_OUTCOME,
    PRIMARY_BLOCKER,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_RESULT_REVIEW_SCHEMA_ID,
)
from formal.python.tools.qft_gr_covariant_conservation_statement_witness_packet_report import (
    DEFAULT_CAPTURED_AT_UTC,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QFT_GR_COVARIANT_CONSERVATION_ASSUMPTION_REDUCTION_PACKET_20260525_v0"
PACKET_ID = "QFT_GR_COVARIANT_CONSERVATION_ASSUMPTION_REDUCTION_PACKET_v0"
OUTCOME_ID = (
    "QFT_GR_COVARIANT_CONSERVATION_ASSUMPTION_REDUCTION_PACKET_PREPARED_WITH_"
    "NO_CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
)
PACKET_CLASSIFICATION = (
    "qft_gr_covariant_conservation_assumption_reduction_packet_prepared_"
    "insufficient_assumptions_classified_no_conservation_witness_or_seam_closure"
)
CONSUMED_TARGET = EXPECTED_PACKET_TARGET
NEXT_TARGET = "review_qft_gr_covariant_conservation_assumption_reduction_packet_result"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_COVARIANT_CONSERVATION_ASSUMPTION_REDUCTION_PACKET_20260525_v0.json"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _assumption_rows() -> list[dict[str, Any]]:
    return [
        {
            "assumption_class": "mathematical_regularity_assumptions",
            "required": True,
            "supplied": "partial",
            "derivable": False,
            "missing": True,
            "too_strong": "unknown",
            "candidate_reducible": True,
            "not_reducible_in_current_lane": False,
            "blocking_role": "regularity needed for derivative exchange and weak/strong conservation comparison is not yet pinned.",
        },
        {
            "assumption_class": "renormalization_assumptions",
            "required": True,
            "supplied": "partial",
            "derivable": False,
            "missing": True,
            "too_strong": "unknown",
            "candidate_reducible": True,
            "not_reducible_in_current_lane": False,
            "blocking_role": "renormalized expectation compatibility with the covariant derivative remains unproved.",
        },
        {
            "assumption_class": "operator_domain_assumptions",
            "required": True,
            "supplied": "prepared_at_domain_statement_level",
            "derivable": False,
            "missing": True,
            "too_strong": "possibly",
            "candidate_reducible": True,
            "not_reducible_in_current_lane": False,
            "blocking_role": "prepared operator-domain structure does not yet provide the conservation proof object.",
        },
        {
            "assumption_class": "state_domain_assumptions",
            "required": True,
            "supplied": "partial",
            "derivable": False,
            "missing": True,
            "too_strong": "unknown",
            "candidate_reducible": True,
            "not_reducible_in_current_lane": False,
            "blocking_role": "state-domain stability under the derivative and expectation operations remains unavailable.",
        },
        {
            "assumption_class": "geometric_Bianchi_assumptions",
            "required": True,
            "supplied": "boundary_only",
            "derivable": False,
            "missing": True,
            "too_strong": "possibly",
            "candidate_reducible": False,
            "not_reducible_in_current_lane": True,
            "blocking_role": "Bianchi compatibility is downstream and cannot be claimed by conservation assumption reduction alone.",
        },
        {
            "assumption_class": "physical_source_admissibility_assumptions",
            "required": True,
            "supplied": "boundary_only",
            "derivable": False,
            "missing": True,
            "too_strong": "unknown",
            "candidate_reducible": False,
            "not_reducible_in_current_lane": True,
            "blocking_role": "source admissibility remains conditional until conservation and Bianchi dependencies are separately supported.",
        },
    ]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": "The assumption-reduction packet must be reviewed before selecting a narrow reduction target.",
        },
        {
            "target": "prepare_qft_gr_operator_domain_assumption_reduction_packet",
            "decision": "deferred",
            "reason": "Operator-domain reduction is plausible but not selected until this packet is reviewed.",
        },
        {
            "target": "prepare_qft_gr_state_domain_assumption_reduction_packet",
            "decision": "deferred",
            "reason": "State-domain reduction is plausible but not selected until this packet is reviewed.",
        },
        {
            "target": "execute_qft_gr_covariant_conservation_proof_object_attempt",
            "decision": "deferred",
            "reason": "A proof-object attempt remains blocked until assumption reduction is reviewed.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "Assumption-reduction packet preparation does not close QFT-GR.",
        },
    ]


def build_qft_gr_covariant_conservation_assumption_reduction_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    result_review = _read_json(result_review_path)
    assumption_rows = _assumption_rows()
    candidate_next_targets = _candidate_next_targets()
    assumption_classes = [row["assumption_class"] for row in assumption_rows]
    acceptance_criteria = {
        "consumes_expected_result_review": result_review.get("schema_id")
        == EXPECTED_RESULT_REVIEW_SCHEMA_ID,
        "result_review_outcome_expected": result_review.get("outcome_id")
        == EXPECTED_RESULT_REVIEW_OUTCOME,
        "result_review_classification_expected": result_review.get(
            "result_review_classification"
        )
        == EXPECTED_RESULT_REVIEW_CLASSIFICATION,
        "result_review_authorized_this_packet": result_review.get(
            "selected_next_target"
        )
        == CONSUMED_TARGET,
        "preserves_insufficient_assumptions_blocker": result_review.get(
            "selected_blocker"
        )
        == PRIMARY_BLOCKER,
        "six_assumption_classes_classified": assumption_classes
        == [
            "mathematical_regularity_assumptions",
            "renormalization_assumptions",
            "operator_domain_assumptions",
            "state_domain_assumptions",
            "geometric_Bianchi_assumptions",
            "physical_source_admissibility_assumptions",
        ],
        "does_not_reduce_or_discharge_assumptions": True,
        "does_not_construct_proof_object": result_review.get("proof_object_constructed")
        is False
        and result_review.get("conservation_proof_object_constructed") is False,
        "does_not_construct_conservation_witness": result_review.get(
            "conservation_witness_constructed"
        )
        is False,
        "does_not_claim_source_or_bianchi": result_review.get(
            "stress_energy_source_admissibility_claimed"
        )
        is False
        and result_review.get("Bianchi_compatibility_claimed") is False,
        "does_not_close_or_validate": result_review.get("qft_gr_seam_closed")
        is False
        and result_review.get("empirical_validation_claimed") is False,
        "no_release_or_public_submission": result_review.get(
            "release_assembly_authorized"
        )
        is False
        and result_review.get("public_submission_authorized") is False,
        "exactly_one_next_target_selected": sum(
            1 for row in candidate_next_targets if row["decision"] == "selected"
        )
        == 1
        and candidate_next_targets[0]["target"] == NEXT_TARGET,
    }
    prepared = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "accepted": prepared,
        "outcome_id": OUTCOME_ID
        if prepared
        else "QFT_GR_COVARIANT_CONSERVATION_ASSUMPTION_REDUCTION_PACKET_BLOCKED",
        "packet_classification": PACKET_CLASSIFICATION,
        "packet_classification_count": 1 if prepared else 0,
        "consumes_qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet_result_review": EXPECTED_RESULT_REVIEW_SCHEMA_ID,
        "consumes_qft_gr_covariant_conservation_proof_object_obstruction_refinement_packet_result_review_pointer": _ptr(
            result_review_path
        ),
        "consumed_result_review_id": EXPECTED_RESULT_REVIEW_ID,
        "consumed_result_review_outcome_id": result_review.get("outcome_id"),
        "consumed_result_review_classification": result_review.get(
            "result_review_classification"
        ),
        "blocker": PRIMARY_BLOCKER,
        "selected_blocker": PRIMARY_BLOCKER,
        "assumption_reduction_analysis_prepared": prepared,
        "assumption_classes": assumption_classes,
        "assumption_class_count": len(assumption_classes),
        "assumption_status_vocabulary": [
            "required",
            "supplied",
            "derivable",
            "missing",
            "too_strong",
            "candidate_reducible",
            "not_reducible_in_current_lane",
        ],
        "assumption_rows": assumption_rows,
        "candidate_reducible_assumption_classes": [
            row["assumption_class"]
            for row in assumption_rows
            if row["candidate_reducible"] is True
        ],
        "not_reducible_in_current_lane_classes": [
            row["assumption_class"]
            for row in assumption_rows
            if row["not_reducible_in_current_lane"] is True
        ],
        "reduces_or_discharges_assumptions_by_preparation": False,
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
        if prepared
        else "REMEDIATE_QFT_GR_COVARIANT_CONSERVATION_ASSUMPTION_REDUCTION_PACKET",
        "selected_next_target_kind": (
            "qft_gr_covariant_conservation_assumption_reduction_packet_result_review"
        ),
        "selected_route": (
            "qft_gr_covariant_conservation_assumption_reduction_packet_result_review_after_packet_preparation"
        ),
        "selection_count": 1 if prepared else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_COVARIANT_CONSERVATION_ASSUMPTION_REDUCTION_PACKET_"
            "RESULT_ONLY_NO_ASSUMPTION_DISCHARGE_OR_QFT_GR_SEAM_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet prepares assumption-reduction analysis only. It "
            "classifies assumptions blocking the conservation proof object and "
            "does not reduce or discharge assumptions, construct a proof object "
            "or conservation witness, claim source admissibility or Bianchi "
            "compatibility, derive the semiclassical Einstein equation, close "
            "QFT-GR, validate empirically, promote the master action, assemble "
            "release, or authorize public submission."
        ),
    }


def write_qft_gr_covariant_conservation_assumption_reduction_packet(
    *,
    result_review_path: Path = DEFAULT_RESULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_covariant_conservation_assumption_reduction_packet(
        result_review_path=result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QFT-GR covariant conservation assumption-reduction packet."
    )
    parser.add_argument("--result-review", type=Path, default=DEFAULT_RESULT_REVIEW_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    result_review_path = (
        ns.result_review
        if ns.result_review.is_absolute()
        else (REPO_ROOT / ns.result_review)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_covariant_conservation_assumption_reduction_packet(
        result_review_path=result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_covariant_conservation_assumption_reduction_packet_report: "
        f"prepared={payload['prepared']} classes={payload['assumption_class_count']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

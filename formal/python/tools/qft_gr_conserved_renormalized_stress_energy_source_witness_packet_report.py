from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_result_review_report import (
    DEFAULT_OUT as DEFAULT_CONTROL_REVIEW_PATH,
    NEXT_TARGET as EXPECTED_PACKET_TARGET,
    OUTCOME_ID as EXPECTED_CONTROL_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_CONTROL_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_CONTROL_REVIEW_ID,
    SCHEMA_ID as EXPECTED_CONTROL_REVIEW_SCHEMA_ID,
)
from formal.python.tools.v01_alpha_retained_tranche_004_future_remediation_program_report import (
    DEFAULT_CAPTURED_AT_UTC,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QFT_GR_CONSERVED_RENORMALIZED_STRESS_ENERGY_SOURCE_WITNESS_PACKET_20260525_v0"
PACKET_ID = "QFT_GR_CONSERVED_RENORMALIZED_STRESS_ENERGY_SOURCE_WITNESS_PACKET_v0"
OUTCOME_ID = (
    "QFT_GR_CONSERVED_RENORMALIZED_STRESS_ENERGY_SOURCE_WITNESS_PACKET_"
    "PREPARED_WITH_NO_SEAM_CLOSURE_OR_EMPIRICAL_VALIDATION"
)
PACKET_CLASSIFICATION = (
    "qft_gr_conserved_renormalized_stress_energy_source_witness_packet_"
    "prepared_no_witness_claim_no_seam_closure_or_empirical_validation"
)
CONSUMED_TARGET = "prepare_qft_gr_conserved_renormalized_stress_energy_source_witness_packet"
NEXT_TARGET = "review_qft_gr_conserved_renormalized_stress_energy_source_witness_packet_result"
EXECUTION_TARGET = "execute_qft_gr_conserved_renormalized_stress_energy_source_witness_attempt"

SCIENTIFIC_QUESTION = (
    "Can the repo construct or refute a bounded witness that a renormalized "
    "QFT stress-energy expectation is finite, meaningful, conserved, "
    "Bianchi-compatible, and admissible as a GR source?"
)

EXECUTION_CLASSIFICATIONS = [
    "qft_gr_conserved_renormalized_source_witness_constructed_pending_result_review",
    "qft_gr_conserved_renormalized_source_witness_obstruction_identified_requires_refinement",
    "qft_gr_conserved_renormalized_source_witness_inconclusive_requires_assumption_reduction",
]

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_CONSERVED_RENORMALIZED_STRESS_ENERGY_SOURCE_WITNESS_PACKET_20260525_v0.json"
)

REQUIRED_LEAN_SURFACES = [
    "ToeFormal.Bridges.QFT_GR_StressEnergyOperatorDomainSemantics",
    "ToeFormal.Bridges.QFT_GR_StateExpectationFunctionalSemantics",
    "ToeFormal.Bridges.QFT_GR_RenormalizedExpectationValueSemantics",
    "ToeFormal.Bridges.QFT_GR_ClassicalSourceAdmissibilitySemantics",
    "ToeFormal.Bridges.QFT_GR_CovariantConservationObligationSemantics",
    "ToeFormal.Bridges.QFT_GR_BianchiCompatibilityObligationSemantics",
    "ToeFormal.Bridges.QFT_GR_EinsteinCouplingObligationSemantics",
    "ToeFormal.Bridges.QFT_GR_WeakCurvatureSourceIdentificationObligationSemantics",
    "ToeFormal.Bridges.QFT_GR_PoissonRecoveryObligationSemantics",
    "ToeFormal.Bridges.QFT_GR_SourceMapEligibilityLadderSummary",
]

FORBIDDEN_CLAIMS = [
    "criticizability_readiness_treated_as_scientific_evidence",
    "witness_constructed",
    "conserved_renormalized_stress_energy_source_exists",
    "semiclassical_einstein_equation_derived",
    "qft_gr_seam_closed",
    "qft_gr_source_map_closure_claimed",
    "empirical_validation_claimed",
    "master_action_promoted",
    "release_assembly_authorized",
    "public_submission_authorized",
]


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": "The prepared witness packet must be result-reviewed before any witness attempt.",
        },
        {
            "target": EXECUTION_TARGET,
            "decision": "deferred",
            "reason": "Execution requires a later packet result review.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "Packet preparation does not close the QFT-GR seam.",
        },
        {
            "target": "assemble_v01_alpha_release_packet",
            "decision": "not_authorized",
            "reason": "Release assembly remains outside Track 2 packet preparation.",
        },
        {
            "target": "authorize_public_submission",
            "decision": "not_authorized",
            "reason": "Public submission is not authorized by this scientific packet.",
        },
    ]


def build_qft_gr_conserved_renormalized_stress_energy_source_witness_packet(
    *,
    control_review_path: Path = DEFAULT_CONTROL_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    control_review = _read_json(control_review_path)
    candidate_next_targets = _candidate_next_targets()
    forbidden_claim_status = {claim: False for claim in FORBIDDEN_CLAIMS}

    required_math_assumptions = [
        "well-defined operator-domain semantics for stress-energy candidates",
        "renormalization prescription sufficient to define a finite expectation value",
        "state expectation functional with domain/regularity conditions stated",
        "distributional or tensorial equality notion for conservation and Bianchi compatibility",
        "weak-curvature or Poisson recovery comparison map stated before use",
    ]
    required_physics_assumptions = [
        "state class adequate for renormalized stress-energy expectation semantics",
        "renormalized stress-energy candidate is meaningful before source admissibility is tested",
        "covariant conservation is required before GR source admissibility",
        "Bianchi compatibility is required before Einstein-coupling interpretation",
        "weak-curvature or Poisson recovery is a boundary check, not a closure claim",
    ]

    packet_fields = {
        "stress_energy_object": (
            "candidate renormalized QFT stress-energy expectation object "
            "<T_mu_nu>_ren, not yet constructed as a witness"
        ),
        "renormalization_scope": (
            "bounded repo-local renormalization semantics sufficient to test finiteness "
            "and meaningfulness, without claiming scheme validity"
        ),
        "state_expectation_scope": (
            "state expectation functional scope over admissible candidate states, with "
            "domain and regularity assumptions explicit"
        ),
        "finiteness_condition": (
            "the candidate expectation must be finite in the declared renormalized scope"
        ),
        "conservation_condition": (
            "the candidate source must satisfy the declared covariant-conservation obligation"
        ),
        "classical_source_admissibility_condition": (
            "the candidate expectation must be admissible as a classical GR source before coupling"
        ),
        "Bianchi_compatibility_condition": (
            "the candidate source must be compatible with the Bianchi identity boundary"
        ),
        "Einstein_coupling_boundary": (
            "Einstein coupling may be tested only as a bounded compatibility boundary; "
            "the packet does not derive G_mu_nu = kappa <T_mu_nu>_ren"
        ),
        "weak_curvature_or_Poisson_recovery_boundary": (
            "weak-curvature or Poisson recovery may be used only as a boundary check, "
            "not as empirical validation or seam closure"
        ),
        "failure_or_obstruction_mode": (
            "if any finiteness, meaningfulness, conservation, Bianchi, admissibility, "
            "coupling, or recovery condition is missing/refuted/inconclusive, the later "
            "attempt must classify the result as obstruction or inconclusive refinement"
        ),
        "required_Lean_surfaces": REQUIRED_LEAN_SURFACES,
        "required_math_assumptions": required_math_assumptions,
        "required_physics_assumptions": required_physics_assumptions,
        "claim_ceiling": (
            "packet_preparation_only_no_witness_construction_no_qft_gr_closure_no_"
            "empirical_validation_no_master_action_promotion"
        ),
        "forbidden_claims": FORBIDDEN_CLAIMS,
        "post_packet_review_target": NEXT_TARGET,
    }

    acceptance_criteria = {
        "consumes_expected_control_review": control_review.get("review_id")
        == EXPECTED_CONTROL_REVIEW_ID,
        "control_review_schema_expected": control_review.get("schema_id")
        == EXPECTED_CONTROL_REVIEW_SCHEMA_ID,
        "control_review_outcome_expected": control_review.get("outcome_id")
        == EXPECTED_CONTROL_REVIEW_OUTCOME,
        "control_review_classification_expected": control_review.get(
            "result_review_classification"
        )
        == EXPECTED_CONTROL_REVIEW_CLASSIFICATION,
        "control_review_selected_this_packet": control_review.get("selected_next_target")
        == CONSUMED_TARGET
        and EXPECTED_PACKET_TARGET == CONSUMED_TARGET,
        "control_review_used_as_clearance_only": control_review.get(
            "criticizability_readiness_eligibility_accepted"
        )
        is True
        and control_review.get("track2_selection_kind")
        == "qft_gr_witness_packet_preparation_only"
        and control_review.get("track2_scientific_evidence_claimed_from_track1") is False,
        "packet_asks_exact_scientific_question": SCIENTIFIC_QUESTION
        == (
            "Can the repo construct or refute a bounded witness that a renormalized "
            "QFT stress-energy expectation is finite, meaningful, conserved, "
            "Bianchi-compatible, and admissible as a GR source?"
        ),
        "required_fields_present": set(packet_fields)
        == {
            "stress_energy_object",
            "renormalization_scope",
            "state_expectation_scope",
            "finiteness_condition",
            "conservation_condition",
            "classical_source_admissibility_condition",
            "Bianchi_compatibility_condition",
            "Einstein_coupling_boundary",
            "weak_curvature_or_Poisson_recovery_boundary",
            "failure_or_obstruction_mode",
            "required_Lean_surfaces",
            "required_math_assumptions",
            "required_physics_assumptions",
            "claim_ceiling",
            "forbidden_claims",
            "post_packet_review_target",
        },
        "packet_preparation_only": control_review.get(
            "qft_gr_witness_packet_preparation_authorized"
        )
        is True
        and control_review.get("qft_gr_witness_packet_prepared") is False,
        "does_not_construct_or_claim_witness": all(
            forbidden_claim_status[key] is False
            for key in [
                "witness_constructed",
                "conserved_renormalized_stress_energy_source_exists",
            ]
        ),
        "does_not_derive_einstein_equation_or_close_qft_gr": all(
            forbidden_claim_status[key] is False
            for key in [
                "semiclassical_einstein_equation_derived",
                "qft_gr_seam_closed",
                "qft_gr_source_map_closure_claimed",
            ]
        ),
        "no_empirical_master_release_or_public_submission": all(
            forbidden_claim_status[key] is False
            for key in [
                "empirical_validation_claimed",
                "master_action_promoted",
                "release_assembly_authorized",
                "public_submission_authorized",
            ]
        ),
        "exactly_one_next_target_selected": sum(
            1 for row in candidate_next_targets if row["decision"] == "selected"
        )
        == 1
        and candidate_next_targets[0]["target"] == NEXT_TARGET,
        "allowed_execution_classifications_deferred": len(EXECUTION_CLASSIFICATIONS) == 3,
        "forbidden_claims_all_false": all(
            value is False for value in forbidden_claim_status.values()
        ),
    }
    accepted = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID if accepted else "QFT_GR_CONSERVED_RENORMALIZED_STRESS_ENERGY_SOURCE_WITNESS_PACKET_BLOCKED",
        "packet_classification": PACKET_CLASSIFICATION,
        "packet_classification_count": 1 if accepted else 0,
        "consumes_criticizability_readiness_result_review": EXPECTED_CONTROL_REVIEW_ID,
        "consumes_criticizability_readiness_result_review_pointer": _ptr(
            control_review_path
        ),
        "consumed_control_review_outcome_id": control_review.get("outcome_id"),
        "consumed_control_review_classification": control_review.get(
            "result_review_classification"
        ),
        "control_lane_clearance_only": True,
        "criticizability_readiness_treated_as_scientific_evidence": False,
        "scientific_question": SCIENTIFIC_QUESTION,
        "packet_scope": (
            "PREPARE_QFT_GR_CONSERVED_RENORMALIZED_STRESS_ENERGY_SOURCE_WITNESS_"
            "PACKET_ONLY_NO_WITNESS_CONSTRUCTION_OR_CLOSURE"
        ),
        **packet_fields,
        "execution_classification_options": EXECUTION_CLASSIFICATIONS,
        "execution_classification_selected": None,
        "witness_packet_prepared": accepted,
        "witness_constructed": False,
        "conserved_renormalized_stress_energy_source_exists_claimed": False,
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
        "forbidden_claim_status": forbidden_claim_status,
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": NEXT_TARGET if accepted else "REMEDIATE_QFT_GR_CONSERVED_RENORMALIZED_STRESS_ENERGY_SOURCE_WITNESS_PACKET",
        "selected_next_target_kind": "qft_gr_witness_packet_result_review_only",
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_CONSERVED_RENORMALIZED_STRESS_ENERGY_SOURCE_WITNESS_"
            "PACKET_RESULT_ONLY_NO_WITNESS_EXECUTION_OR_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet prepares the QFT-GR conserved renormalized stress-energy "
            "source witness question only. It does not construct the witness, claim "
            "a conserved renormalized stress-energy source exists, derive the "
            "semiclassical Einstein equation, close the QFT-GR seam, claim empirical "
            "validation, promote the master action, or authorize release assembly or "
            "public submission."
        ),
        "roadmap_update_required": True,
    }


def write_qft_gr_conserved_renormalized_stress_energy_source_witness_packet(
    *,
    control_review_path: Path = DEFAULT_CONTROL_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_conserved_renormalized_stress_energy_source_witness_packet(
        control_review_path=control_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QFT-GR conserved renormalized stress-energy source witness packet."
    )
    parser.add_argument("--control-review", type=Path, default=DEFAULT_CONTROL_REVIEW_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    control_review_path = (
        ns.control_review
        if ns.control_review.is_absolute()
        else (REPO_ROOT / ns.control_review)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_conserved_renormalized_stress_energy_source_witness_packet(
        control_review_path=control_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_conserved_renormalized_stress_energy_source_witness_packet_report: "
        f"accepted={payload['accepted']} next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

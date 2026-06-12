from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_minimal_working_model_candidate_analysis_result_review_report import (
    DEFAULT_OUT as DEFAULT_CANDIDATE_ANALYSIS_RESULT_REVIEW_PATH,
    NEXT_TARGET as EXPECTED_CONSUMED_TARGET,
    OUTCOME_ID as EXPECTED_RESULT_REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION as EXPECTED_RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID as EXPECTED_RESULT_REVIEW_ID,
    SCHEMA_ID as EXPECTED_RESULT_REVIEW_SCHEMA_ID,
    TOY_SOURCE_STATUS,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-12T00:00:00Z"
SCHEMA_ID = "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_TEST_PACKET_20260612_v0"
PACKET_ID = "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_TEST_PACKET_v0"
OUTCOME_ID = (
    "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_TEST_PACKET_PREPARED_WITH_NO_"
    "CONSERVATION_PROOF_OR_SOURCE_ADMISSIBILITY"
)
PACKET_CLASSIFICATION = (
    "qft_gr_minimal_working_model_conservation_test_packet_prepared_pending_result_review"
)
CONSUMED_TARGET = EXPECTED_CONSUMED_TARGET
NEXT_TARGET = "review_qft_gr_minimal_working_model_conservation_test_packet_result"
NEXT_TARGET_KIND = "qft_gr_minimal_working_model_conservation_test_packet_result_review"
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_TEST_PACKET_20260612_v0.json"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _selected_targets(rows: list[dict[str, str]]) -> list[str]:
    return [row["target"] for row in rows if row.get("decision") == "selected"]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The conservation-test packet must be reviewed before any "
                "test execution, countermodel packet, scope-refinement packet, "
                "or conservation/source-admissibility claim is authorized."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": "This conservation-test packet preparation target is consumed here.",
        },
        {
            "target": "execute_qft_gr_minimal_working_model_conservation_test",
            "decision": "not_authorized_before_packet_result_review",
            "reason": "This packet defines the test only; it does not execute the test.",
        },
        {
            "target": "prepare_qft_gr_minimal_working_model_countermodel_packet",
            "decision": "not_authorized_before_test_result",
            "reason": "Countermodel routing depends on a later executed test result.",
        },
        {
            "target": "prepare_qft_gr_minimal_working_model_scope_refinement_packet",
            "decision": "not_authorized_before_test_result",
            "reason": "Scope refinement routing depends on a later executed test result.",
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "The toy source remains a candidate only.",
        },
        {
            "target": "prove_qft_gr_conservation",
            "decision": "not_authorized",
            "reason": "The packet prepares a test and does not prove conservation.",
        },
        {
            "target": "construct_qft_gr_conservation_witness",
            "decision": "not_authorized",
            "reason": "No conservation witness is constructed by packet preparation.",
        },
        {
            "target": "claim_qft_gr_bianchi_compatibility",
            "decision": "not_authorized",
            "reason": "Bianchi compatibility remains downstream and unclaimed.",
        },
        {
            "target": "derive_semiclassical_einstein_equation",
            "decision": "not_authorized",
            "reason": "The semiclassical Einstein equation is not derived here.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "QFT-GR closure remains outside this packet.",
        },
        {
            "target": "authorize_empirical_validation_or_public_submission",
            "decision": "not_authorized",
            "reason": "Empirical validation and public submission are not authorized.",
        },
    ]


def _conservation_sense() -> dict[str, Any]:
    return {
        "sense_id": "weak_distributional_covariant_conservation_for_toy_candidate",
        "sense_being_tested": (
            "Weak covariant conservation of the toy stress-energy-like "
            "candidate against an admitted test-vector domain on the fixed "
            "controlled background."
        ),
        "statement_template": (
            "For every admitted compactly supported test vector field X in "
            "the test domain, the weak pairing of div_g(T_candidate) with X "
            "vanishes; otherwise record the first explicit obstruction."
        ),
        "fixed_background_only": True,
        "strong_pointwise_conservation_claimed": False,
        "global_conservation_claimed": False,
        "test_executed": False,
    }


def _weak_vs_strong_scope() -> dict[str, Any]:
    return {
        "weak_scope": (
            "distributional or weak divergence vanishing under the supplied "
            "pairing, domain, and regularity assumptions"
        ),
        "strong_scope": (
            "pointwise classical covariant divergence vanishing for an "
            "admissible stress-energy source"
        ),
        "scope_decision": "weak_scope_only_for_this_packet",
        "strong_conservation_tested": False,
        "strong_conservation_claimed": False,
        "weak_conservation_claimed": False,
    }


def _test_object_and_domain(review: dict[str, Any]) -> dict[str, Any]:
    status_map = review.get("candidate_status_map", {})
    return {
        "test_object_id": "QFT_GR_MINIMAL_WORKING_MODEL_TOY_SOURCE_CANDIDATE_v0",
        "test_object_status": review.get("toy_source_candidate_status"),
        "test_object_role": "stress_energy_like_candidate_only",
        "background": "fixed controlled background; backreaction excluded",
        "test_domain": {
            "test_vectors": (
                "admitted compactly supported smooth vector-field test objects "
                "or their packet-level formal surrogate"
            ),
            "pairing_domain_status": status_map.get("pairing", {}).get("status"),
            "domain_status": status_map.get("domain", {}).get("status"),
            "source_domain_membership_claimed": False,
            "admissible_source_domain_established": False,
        },
    }


def _pass_fail_inconclusive_criteria() -> dict[str, Any]:
    return {
        "pass": [
            (
                "every packet-admitted weak pairing is defined under the "
                "supplied domain and regularity assumptions"
            ),
            (
                "every packet-admitted weak divergence pairing evaluates to "
                "zero without adding an unrecorded assumption"
            ),
            "no obstruction row is triggered by the packet's test matrix",
        ],
        "fail": [
            "a packet-admitted weak divergence pairing is explicitly nonzero",
            "the required distributional pairing is undefined for the toy candidate",
            "a required limit/interchange or derivative-exchange step is blocked",
        ],
        "inconclusive": [
            "the test cannot decide zero versus nonzero under supplied assumptions",
            (
                "the test requires a stronger domain, pairing, or regularity "
                "assumption than the packet is allowed to add"
            ),
            "the weak and strong conservation scopes cannot be separated cleanly",
        ],
    }


def build_qft_gr_minimal_working_model_conservation_test_packet(
    *,
    candidate_analysis_result_review_path: Path = (
        DEFAULT_CANDIDATE_ANALYSIS_RESULT_REVIEW_PATH
    ),
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(candidate_analysis_result_review_path)
    status_map = review.get("candidate_status_map", {})
    regularity_assumptions = status_map.get("regularity", {}).get(
        "imported_regularities", []
    )
    candidate_next_targets = _candidate_next_targets()
    conservation_sense = _conservation_sense()
    weak_vs_strong_scope = _weak_vs_strong_scope()
    test_object_and_domain = _test_object_and_domain(review)
    supplied_assumptions = [
        *review.get("what_remains_supplied", []),
        "candidate-analysis result review authorization for bounded conservation-test packet preparation",
    ]
    pass_fail_inconclusive_criteria = _pass_fail_inconclusive_criteria()
    why_passing_does_not_imply_source_admissibility = [
        (
            "Weak divergence vanishing against the packet test domain is only "
            "one source-admissibility component."
        ),
        (
            "The packet does not establish full source-domain membership, "
            "Bianchi compatibility, or coupling to the semiclassical Einstein "
            "equation."
        ),
        (
            "The tested object remains a toy stress-energy-like candidate and "
            "is not promoted to an admissible physical source."
        ),
    ]
    why_failing_routes_to_countermodel_or_scope_refinement = [
        (
            "An explicit nonzero weak pairing or undefined pairing supplies a "
            "countermodel route for the toy candidate."
        ),
        (
            "A blocked domain, pairing, or regularity step routes to bounded "
            "scope refinement rather than source-admissibility promotion."
        ),
        (
            "Any failure remains local to the bounded toy candidate unless a "
            "later reviewed artifact authorizes a broader conclusion."
        ),
    ]

    acceptance_criteria = {
        "consumes_expected_candidate_analysis_result_review_artifact": review.get(
            "schema_id"
        )
        == EXPECTED_RESULT_REVIEW_SCHEMA_ID,
        "candidate_analysis_result_review_outcome_expected": review.get(
            "outcome_id"
        )
        == EXPECTED_RESULT_REVIEW_OUTCOME,
        "candidate_analysis_result_review_classification_expected": review.get(
            "result_review_classification"
        )
        == EXPECTED_RESULT_REVIEW_CLASSIFICATION,
        "candidate_analysis_result_review_selected_this_packet": review.get(
            "selected_next_target"
        )
        == CONSUMED_TARGET,
        "bounded_packet_authorized_by_review": review.get(
            "bounded_conservation_test_packet_authorized"
        )
        is True
        and review.get("conservation_test_packet_prepared_by_review") is False,
        "toy_source_remains_candidate_only": review.get("toy_source_candidate_status")
        == TOY_SOURCE_STATUS
        and review.get("toy_source_candidate_remains_candidate_only") is True,
        "defines_conservation_sense": bool(
            conservation_sense.get("sense_being_tested")
        ),
        "defines_weak_vs_strong_scope": weak_vs_strong_scope.get("scope_decision")
        == "weak_scope_only_for_this_packet",
        "defines_test_object_and_domain": test_object_and_domain.get(
            "test_object_status"
        )
        == TOY_SOURCE_STATUS,
        "records_supplied_assumptions": len(supplied_assumptions) >= 6,
        "records_inherited_regularity_assumptions": set(regularity_assumptions)
        >= {
            "MR-ASSUMP-001-derivative_exchange_regular_boundary",
            "MR-ASSUMP-002-weak_strong_conservation_comparison_scope",
            "MR-ASSUMP-003-distributional_pairing_regular_domain",
            "MR-ASSUMP-004-limit_interchange_regularization_boundary",
        },
        "defines_pass_fail_inconclusive": set(pass_fail_inconclusive_criteria)
        == {"pass", "fail", "inconclusive"},
        "records_pass_not_source_admissibility": len(
            why_passing_does_not_imply_source_admissibility
        )
        >= 3,
        "records_failure_routing": len(
            why_failing_routes_to_countermodel_or_scope_refinement
        )
        >= 3,
        "no_conservation_test_execution": conservation_sense.get("test_executed")
        is False,
        "no_source_admissibility_claim": review.get("source_admissibility_claimed")
        is False
        and review.get("stress_energy_source_admissibility_claimed") is False,
        "no_conservation_claim_or_witness": review.get("conservation_claimed")
        is False
        and review.get("conservation_proved") is False
        and review.get("conservation_proof_object_constructed") is False
        and review.get("conservation_witness_constructed") is False,
        "no_bianchi_or_semiclassical_einstein": review.get(
            "Bianchi_compatibility_claimed"
        )
        is False
        and review.get("semiclassical_einstein_equation_derived") is False,
        "no_qft_gr_closure": review.get("qft_gr_seam_closed") is False
        and review.get("qft_gr_source_map_closure_claimed") is False,
        "exactly_one_next_target_selected": _selected_targets(candidate_next_targets)
        == [NEXT_TARGET],
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_TEST_PACKET"
    )

    return {
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "packet_prepared": accepted,
        "packet_preparation_only": True,
        "outcome_id": OUTCOME_ID
        if accepted
        else "QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_TEST_PACKET_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION
        if accepted
        else "qft_gr_minimal_working_model_conservation_test_packet_requires_remediation",
        "packet_classification_count": 1 if accepted else 0,
        "consumed_target": CONSUMED_TARGET,
        "consumes_qft_gr_minimal_working_model_candidate_analysis_result_review": (
            EXPECTED_RESULT_REVIEW_ID
        ),
        "consumes_qft_gr_minimal_working_model_candidate_analysis_result_review_pointer": _ptr(
            candidate_analysis_result_review_path
        ),
        "consumed_candidate_analysis_result_review_schema_id": review.get("schema_id"),
        "consumed_candidate_analysis_result_review_outcome_id": review.get(
            "outcome_id"
        ),
        "consumed_candidate_analysis_result_review_classification": review.get(
            "result_review_classification"
        ),
        "toy_source_candidate_status": review.get("toy_source_candidate_status"),
        "toy_source_candidate_remains_candidate_only": True,
        "toy_source_promoted_to_admissible_source": False,
        "conservation_sense_being_tested": conservation_sense,
        "weak_vs_strong_conservation_scope": weak_vs_strong_scope,
        "test_object_and_test_domain": test_object_and_domain,
        "supplied_assumptions": supplied_assumptions,
        "regularity_assumptions_inherited_from_mr_rows": regularity_assumptions,
        "pass_fail_inconclusive_criteria": pass_fail_inconclusive_criteria,
        "why_passing_does_not_imply_source_admissibility": (
            why_passing_does_not_imply_source_admissibility
        ),
        "why_failing_routes_to_countermodel_or_scope_refinement": (
            why_failing_routes_to_countermodel_or_scope_refinement
        ),
        "conservation_test_executed": False,
        "conservation_test_result_claimed": False,
        "conservation_test_packet_result_reviewed": False,
        "countermodel_packet_prepared": False,
        "scope_refinement_packet_prepared": False,
        "source_admissibility_claimed": False,
        "stress_energy_source_admissibility_claimed": False,
        "physical_source_claimed": False,
        "conservation_claimed": False,
        "conservation_proved": False,
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
        "aggregate_lean_timeout_caveat_preserved": review.get(
            "aggregate_lean_timeout_caveat_preserved"
        )
        is True,
        "validation_caveat": review.get("validation_caveat"),
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selection_count": 1 if accepted else 0,
        "selected_next_target_count": 1 if accepted else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_MINIMAL_WORKING_MODEL_CONSERVATION_TEST_PACKET_"
            "RESULT_ONLY_NO_TEST_EXECUTION_SOURCE_ADMISSIBILITY_CONSERVATION_"
            "PROOF_WITNESS_BIANCHI_SEMICLASSICAL_EINSTEIN_QFT_GR_CLOSURE_"
            "EMPIRICAL_VALIDATION_OR_PUBLIC_SUBMISSION"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet prepares a bounded weak-conservation test for the toy "
            "source candidate only. It does not execute the test and preserves "
            "no source admissibility, no conservation claim, no conservation "
            "proof object, no conservation witness, no Bianchi compatibility, "
            "no semiclassical Einstein equation, no QFT-GR closure, no "
            "empirical validation, no public submission, and no master-action "
            "promotion."
        ),
    }


def write_qft_gr_minimal_working_model_conservation_test_packet(
    *,
    candidate_analysis_result_review_path: Path = (
        DEFAULT_CANDIDATE_ANALYSIS_RESULT_REVIEW_PATH
    ),
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_minimal_working_model_conservation_test_packet(
        candidate_analysis_result_review_path=candidate_analysis_result_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR minimal working model conservation-test packet."
        )
    )
    parser.add_argument(
        "--result-review",
        type=Path,
        default=DEFAULT_CANDIDATE_ANALYSIS_RESULT_REVIEW_PATH,
    )
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
    payload = write_qft_gr_minimal_working_model_conservation_test_packet(
        candidate_analysis_result_review_path=result_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "qft_gr_minimal_working_model_conservation_test_packet_report: "
        f"accepted={payload['accepted']} next={payload['selected_next_target']} "
        f"out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

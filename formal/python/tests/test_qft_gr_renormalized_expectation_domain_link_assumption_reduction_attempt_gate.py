from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_operator_domain_assumption_reduction_packet_report import (
    PRIMARY_ASSUMPTION_FAMILY,
)
from formal.python.tools.qft_gr_renormalized_expectation_domain_link_assumption_reduction_attempt_report import (
    ATTEMPT_ID,
    DEFAULT_OUT,
    NEXT_TARGET,
    OUTCOME_ID,
    RENORMALIZED_EXPECTATION_DOMAIN_LINK_CONTRACT_ID,
    RESULT_CLASSIFICATION,
    SCHEMA_ID,
    build_qft_gr_renormalized_expectation_domain_link_assumption_reduction_attempt,
)
from formal.python.tools.qft_gr_renormalized_expectation_domain_link_assumption_reduction_packet_report import (
    OPERATOR_DOMAIN_LINK_CONDITION,
    PRIOR_ACCEPTED_ROW001,
    PRIOR_ACCEPTED_ROW002,
    PRIOR_ACCEPTED_ROW003,
    RENORMALIZED_EXPECTATION_OBJECT,
    SELECTED_ROW_ID,
)
from formal.python.tools.qft_gr_renormalized_expectation_domain_link_assumption_reduction_packet_result_review_report import (
    AUTHORIZED_ATTEMPT_RESULT_CLASSIFICATIONS,
    DEFAULT_CAPTURED_AT_UTC,
    DEFAULT_OUT as REVIEW_PATH,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as REVIEW_OUTCOME,
    RESULT_REVIEW_CLASSIFICATION,
    REVIEW_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
LEAN_ATTEMPT_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Bridges"
    / "QFT_GR_RenormalizedExpectationDomainLinkAssumptionReductionAttempt.lean"
)
TOOL_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "tools"
    / "qft_gr_renormalized_expectation_domain_link_assumption_reduction_attempt_report.py"
)
SURFACES_PATH = REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md"
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
V01_INDEX_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"
)
FRONTIER_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CrossPillarClosureFrontier.lean"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_qft_gr_renormalized_expectation_domain_link_assumption_reduction_attempt_files_exist() -> None:
    assert REVIEW_PATH.exists()
    assert DEFAULT_OUT.exists()
    assert TOOL_PATH.exists()
    assert LEAN_ATTEMPT_PATH.exists()


def test_qft_gr_renormalized_expectation_domain_link_assumption_reduction_attempt_consumes_review() -> None:
    attempt = _json(DEFAULT_OUT)
    review = _json(REVIEW_PATH)
    assert attempt["schema_id"] == SCHEMA_ID
    assert attempt["attempt_id"] == ATTEMPT_ID
    assert attempt["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert attempt["executed"] is True
    assert attempt["outcome_id"] == OUTCOME_ID
    assert (
        attempt[
            "consumes_qft_gr_renormalized_expectation_domain_link_assumption_reduction_packet_result_review"
        ]
        == REVIEW_ID
    )
    assert review["outcome_id"] == REVIEW_OUTCOME
    assert review["result_review_classification"] == RESULT_REVIEW_CLASSIFICATION
    assert review["selected_next_target"] == CONSUMED_TARGET


def test_qft_gr_renormalized_expectation_domain_link_assumption_reduction_attempt_records_one_classification() -> None:
    attempt = _json(DEFAULT_OUT)
    assert attempt["result_classification"] == RESULT_CLASSIFICATION
    assert attempt["classification_options"] == AUTHORIZED_ATTEMPT_RESULT_CLASSIFICATIONS
    assert [row["classification"] for row in attempt["classification_rows"]] == (
        AUTHORIZED_ATTEMPT_RESULT_CLASSIFICATIONS
    )
    assert attempt["result_classification_count"] == 1
    assert sum(1 for row in attempt["classification_rows"] if row["selected"]) == 1
    assert (
        attempt[
            "renormalized_expectation_domain_link_assumption_reduced_pending_result_review"
        ]
        is True
    )
    assert (
        attempt[
            "renormalized_expectation_domain_link_assumption_obstruction_identified"
        ]
        is False
    )
    assert (
        attempt["renormalized_expectation_domain_link_assumption_inconclusive"]
        is False
    )


def test_qft_gr_renormalized_expectation_domain_link_assumption_reduction_attempt_reduces_selected_row_only() -> None:
    attempt = _json(DEFAULT_OUT)
    contract = attempt["renormalized_expectation_domain_link_reduction_contract"]
    assert attempt["blocker"] == "insufficient_assumptions_for_conservation"
    assert attempt["selected_blocker"] == "insufficient_assumptions_for_conservation"
    assert attempt["current_family"] == PRIMARY_ASSUMPTION_FAMILY
    assert attempt["selected_assumption_family"] == PRIMARY_ASSUMPTION_FAMILY
    assert attempt["primary_assumption_reduction_family"] == PRIMARY_ASSUMPTION_FAMILY
    assert attempt["prior_accepted_operator_domain_assumption_rows"] == [
        PRIOR_ACCEPTED_ROW001,
        PRIOR_ACCEPTED_ROW002,
        PRIOR_ACCEPTED_ROW003,
    ]
    assert attempt["selected_operator_domain_assumption_row"] == SELECTED_ROW_ID
    assert contract["contract_id"] == RENORMALIZED_EXPECTATION_DOMAIN_LINK_CONTRACT_ID
    assert contract["assumption_id"] == SELECTED_ROW_ID
    assert contract["assumption_family"] == PRIMARY_ASSUMPTION_FAMILY
    assert contract["renormalized_expectation_object"] == RENORMALIZED_EXPECTATION_OBJECT
    assert contract["operator_domain_link_condition"] == OPERATOR_DOMAIN_LINK_CONDITION
    assert len(attempt["execution_findings"]) == 4


def test_qft_gr_renormalized_expectation_domain_link_assumption_reduction_attempt_preserves_nonclaims() -> None:
    attempt = _json(DEFAULT_OUT)
    assert attempt["renormalized_expectation_domain_link_assumption_discharged"] is False
    assert (
        attempt[
            "renormalized_expectation_domain_link_claimed_as_operator_domain_closed"
        ]
        is False
    )
    assert attempt["renormalization_compatibility_with_conservation_claimed"] is False
    assert attempt["source_admissibility_claimed"] is False
    assert attempt["stress_energy_source_admissibility_claimed"] is False
    assert attempt["assumption_discharge_claimed"] is False
    assert attempt["assumptions_reduced_or_discharged_by_implication"] is False
    assert attempt["proof_object_constructed"] is False
    assert attempt["conservation_proof_object_constructed"] is False
    assert attempt["conservation_witness_constructed"] is False
    assert attempt["Bianchi_compatibility_claimed"] is False
    assert attempt["semiclassical_einstein_equation_derived"] is False
    assert attempt["qft_gr_seam_closed"] is False
    assert attempt["empirical_validation_claimed"] is False
    assert attempt["master_action_promoted"] is False
    assert attempt["release_assembly_authorized"] is False
    assert attempt["public_submission_authorized"] is False


def test_qft_gr_renormalized_expectation_domain_link_assumption_reduction_attempt_selects_one_review_target() -> None:
    attempt = _json(DEFAULT_OUT)
    assert attempt["selected_next_target"] == NEXT_TARGET
    assert attempt["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in attempt["candidate_next_targets"]} == {
        NEXT_TARGET: "selected",
        "prepare_qft_gr_source_admissibility_assumption_reduction_packet": "not_authorized",
        "execute_qft_gr_covariant_conservation_proof_object_attempt": "not_authorized",
        "close_qft_gr_seam": "not_authorized",
        "authorize_public_submission": "not_authorized",
    }


def test_qft_gr_renormalized_expectation_domain_link_assumption_reduction_attempt_deterministic_and_pinned() -> None:
    attempt = _json(DEFAULT_OUT)
    generated = (
        build_qft_gr_renormalized_expectation_domain_link_assumption_reduction_attempt(
            review_path=REVIEW_PATH,
            captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
        )
    )
    assert attempt == generated
    for key, value in attempt["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    joined = "\n".join(
        _read(path)
        for path in [
            TOOL_PATH,
            SURFACES_PATH,
            REGISTRY_PATH,
            ROADMAP_PATH,
            LEAN_ATTEMPT_PATH,
            V01_INDEX_PATH,
            FRONTIER_PATH,
        ]
    )
    for token in [
        ATTEMPT_ID,
        OUTCOME_ID,
        RESULT_CLASSIFICATION,
        RENORMALIZED_EXPECTATION_DOMAIN_LINK_CONTRACT_ID,
        NEXT_TARGET,
    ]:
        assert token in joined

from __future__ import annotations

from formal.python.tools import (
    pillar_seam_unit_mapping_ledger_blocker_response_route_selection_v2_result_review as review,
)


def test_v2_review_report_is_accepted_and_current() -> None:
    report = review.load_json(review.REVIEW_REPORT_PATH)
    assert report["accepted"] is True
    assert report["verdict"] == "ACCEPT"
    assert report["failed_decision_ids"] == []
    assert report["passed_decision_count"] == report["decision_count"] == 16
    assert report["selected_next_target"] == review.ACCEPTED_NEXT_TARGET


def test_v2_review_recomputes_authority_routes_and_eligibility() -> None:
    packet = review.load_json(review.PACKET_PATH)
    manifest = review.load_json(review.MANIFEST_PATH)
    preparation_report = review.load_json(review.PREPARATION_REPORT_PATH)
    ledger = review.load_json(review.LEDGER_PATH)
    audit = review.independent_packet_audit(packet, manifest, preparation_report, ledger)
    assert audit["all_checks_passed"] is True
    assert audit["authority_mismatches"] == []
    assert audit["locator_failures"] == []
    assert audit["eligibility_failures"] == []
    assert audit["route_failures"] == []


def test_v2_review_binds_immutable_preparation_and_prompt() -> None:
    custody = review.preparation_custody()
    assert custody["passed"] is True
    assert all(custody["working_hash_comparisons"].values())
    assert all(custody["commit_hash_comparisons"].values())
    packet = review.load_json(review.PACKET_PATH)
    prompt = packet["prompt_protection"]
    assert prompt == {
        "excluded_from_scientific_inputs": True,
        "excluded_from_staging_pathspecs": True,
        "frozen_commit": review._frozen_commit(),
        "git_blob_oid": review._git_blob_oid(
            review.PROMPT_RELATIVE_PATH,
            review._frozen_commit(),
        ),
        "identity_type": "GIT_BLOB_SHA256",
        "path": review.PROMPT_RELATIVE_PATH,
        "pre_tranche_sha256": review.sha256_bytes(
            review._git_blob_bytes(
                review.PROMPT_RELATIVE_PATH,
                review._frozen_commit(),
            )
        ),
        "sha256": review.sha256_bytes(
            review._git_blob_bytes(
                review.PROMPT_RELATIVE_PATH,
                review._frozen_commit(),
            )
        ),
    }
    assert review._identity_matches(prompt)


def test_v2_review_independence_and_detached_regenerations_are_recorded() -> None:
    report = review.load_json(review.REVIEW_REPORT_PATH)
    independence = report["reviewer_independence"]
    assert independence["imports_preparation_generator"] is False
    assert independence["shares_role_assignment_logic"] is False
    assert independence["shares_eligibility_implementation"] is False
    assert independence["shares_route_selection_implementation"] is False
    assert independence["shares_mutation_constructors"] is False
    regeneration = report["isolated_regeneration"]
    assert regeneration["passed"] is True
    assert regeneration["run_count"] == 2
    assert regeneration["cross_run_byte_identity"] is True
    assert all(item["clean_detached_start"] for item in regeneration["runs"])

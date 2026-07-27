from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools import (
    eotwash_2020_yukawa_primary_evidence_custody_acquisition_result_review_v0
    as review,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / review.REPORT_RELATIVE_PATH


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def _reproduction() -> dict[str, object]:
    return _report()["independent_reproduction"]


def test_review_regenerates_and_freezes_execution_and_raw_custody() -> None:
    assert review.artifact_bytes() == REPORT_PATH.read_bytes()
    report = _report()
    assert report["target"] == review.TARGET
    assert report["verdict"] == review.VERDICT
    assert report["principal_review_outcome"] == review.PRINCIPAL_OUTCOME
    assert report["selected_next_target"] == review.SELECTED_NEXT_TARGET
    assert {
        row["relative_path"]: row["sha256"]
        for row in report["authority"]["frozen_execution_artifacts"]
    } == review.EXECUTION_HASHES
    assert len(report["authority"]["verified_raw_custody_objects"]) == 13


def test_all_twenty_one_review_gates_pass() -> None:
    gates = _report()["review_gates"]
    assert gates["gate_count"] == gates["pass_count"] == 21
    assert gates["failure_count"] == 0
    assert all(row["status"] == "PASS" for row in gates["rows"])


def test_attempt_limits_and_unused_attempt_are_reproduced() -> None:
    row = _reproduction()["retrieval_limits"]
    assert row["attempt_numbers"] == list(range(1, 8))
    assert row["attempt_count"] == 7
    assert row["attempt_cap"] == 8
    assert row["remaining_attempts"] == 1
    assert row["maximum_same_url_count"] == 2
    assert row["manual_sessions"] == 1
    assert row["authenticated_mirrors"] == 0
    assert row["contact_executed"] is False
    assert row["passed"] is True


def test_source_priority_and_tier_exhaustion_are_transparent() -> None:
    row = _reproduction()["source_order_and_exhaustion"]
    assert row["first_two_attempts_are_official_supplement"] is True
    assert row["official_article_surface_reached_before_lower_tiers"] is True
    assert row["late_tier_two_chorus_check_disclosed"] is True
    assert "NONMATERIAL" in row["late_check_classification"]
    assert row["tier_count"] == row["tiers_exhausted"] == 5
    assert row["tier_five_authenticated_mirror_identified"] is False
    assert row["distinct_authorized_eighth_source_identified"] is False


def test_aps_supplement_status_is_exact_and_contents_are_not_inferred() -> None:
    row = _reproduction()["aps_supplement"]
    assert row["identified"] is True
    assert row["official_source_confirmed"] is True
    assert row["content_acquired"] is False
    assert row["ordinary_get_status_403"] is True
    assert row["ordinary_get_challenge"] is True
    assert row["chorus_get_status_403"] is True
    assert row["browser_subscription_required"] is True
    assert row["authentication_used"] is False
    assert row["download_after_notice"] is False
    assert row["contents_inferred"] is False


def test_arxiv_archive_cites_but_does_not_contain_supplement() -> None:
    row = _reproduction()["arxiv_archive"]
    assert row["member_count"] == 11
    assert row["tex_member_present"] is True
    assert row["supplement_member_present"] is False
    assert row["article_reports_95_by_3"] is True
    assert row["article_cites_external_supplement"] is True
    assert row["passed"] is True


def test_institutional_sources_are_supporting_only() -> None:
    sources = _reproduction()["institutional_sources"]
    dissertation = _reproduction()["dissertation_visual_and_text_review"]
    assert sources["eotwash_page_links_arxiv"] is True
    assert sources["eotwash_page_mentions_supplement"] is False
    assert sources["researchworks_title_present"] is True
    assert sources["researchworks_bitstream_id_present"] is True
    assert sources["researchworks_cc_by_present"] is True
    assert dissertation["supporting_institutional_methods_evidence"] is True
    assert dissertation["primary_release_package"] is False


def test_dissertation_reinspection_reproduces_exact_partial_content() -> None:
    row = _reproduction()["dissertation_visual_and_text_review"]
    assert row["pdf_page_count"] == 169
    assert row["unique_science_run_rows"] == 95
    assert row["torque_harmonic_columns"] == ["N120", "N18", "N54"]
    assert row["pointwise_errors_printed"] is True
    assert row["five_profiled_nuisances"] == [
        "x0", "y0", "s0", "epsilon", "gamma"
    ]
    assert row["published_limit_rule_present"] is True


def test_all_six_components_remain_partial_and_none_complete() -> None:
    row = _reproduction()["component_review"]
    assert row["item_count"] == 6
    assert row["verified_partial_count"] == 6
    assert row["complete_count"] == 0
    assert all(item["complete"] is False for item in row["rows"])
    assert row["forward_model_status"] == "NOT_EXECUTABLE"
    assert row["statistical_status"] == "NOT_EXECUTABLE"
    assert row["passed"] is True


def test_accepted_claim_is_custody_only() -> None:
    claim = _report()["accepted_bounded_claim"]
    assert claim["contact_required"] is True
    assert claim["evidence_components"] == "0_OF_6_COMPLETE_6_OF_6_PARTIAL"
    assert claim["evidence_nonexistence_claim"] is False
    assert claim["experiment_irreproducibility_claim"] is False
    assert claim["scalar_allowance_or_exclusion_claim"] is False


def test_no_contact_fit_bound_or_adoption_is_authorized() -> None:
    scope = _report()["scope"]
    assert scope["independent_result_review_executed"] is True
    assert scope["bounded_acquisition_result_accepted"] is True
    assert scope["scientific_response_selection_authorized"] is True
    for key, value in scope.items():
        if key not in {
            "independent_result_review_executed",
            "bounded_acquisition_result_accepted",
            "scientific_response_selection_authorized",
        }:
            assert value is False, key


def test_post_custody_sources_do_not_create_completeness() -> None:
    rows = _report()["post_custody_source_checks"]
    assert len(rows) == 4
    assert all(row["role"] for row in rows)
    assert _reproduction()["component_review"]["complete_count"] == 0


def test_human_review_records_scope_order_and_stop() -> None:
    text = (REPO_ROOT / review.HUMAN_REVIEW_RELATIVE_PATH).read_text(
        encoding="utf-8"
    )
    for token in (
        review.VERDICT,
        "21 / 21 GATES PASSED",
        "NONMATERIAL",
        "95 unique science-run rows",
        "0 / 6",
        "NOT EXECUTABLE",
        review.SELECTED_NEXT_TARGET,
    ):
        assert token in text

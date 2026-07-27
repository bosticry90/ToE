from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import (
    eotwash_2020_yukawa_primary_evidence_custody_acquisition_v0 as execution,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / execution.REPORT_RELATIVE_PATH


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def _inventory() -> dict[str, dict[str, object]]:
    return {
        row["item_id"]: row
        for row in _report()["required_evidence_inventory"]["rows"]
    }


def test_execution_regenerates_exactly_and_freezes_authority_and_acquired_objects() -> None:
    assert execution.artifact_bytes() == REPORT_PATH.read_bytes()
    before_review = {
        path: _sha256(REPO_ROOT / path) for path in execution.REVIEW_HASHES
    }
    before_objects = {
        path: _sha256(REPO_ROOT / path) for path in execution.ACQUIRED_OBJECT_HASHES
    }
    assert before_review == execution.REVIEW_HASHES
    assert before_objects == execution.ACQUIRED_OBJECT_HASHES


def test_exact_single_authorized_acquisition_is_consumed() -> None:
    report = _report()
    assert report["target"] == execution.TARGET
    assert report["authority"]["authorized_execution_count"] == 1
    assert report["authority"]["consumed_execution_count"] == 1
    assert report["status"] == "PENDING_INDEPENDENT_ACQUISITION_RESULT_REVIEW"


def test_principal_outcome_requires_contact_but_does_not_execute_contact() -> None:
    report = _report()
    assert report["principal_outcome"] == "AUTHORS_OR_CUSTODIAN_CONTACT_REQUIRED"
    assert report["scope"]["author_or_custodian_contact_executed"] is False
    assert report["selected_next_target"] == execution.SELECTED_NEXT_TARGET
    assert report["selected_next_target_kind"] == (
        "INDEPENDENT_ACQUISITION_RESULT_REVIEW_ONLY"
    )


def test_seven_attempts_obey_all_retrieval_limits_and_stop_early() -> None:
    attempts = _report()["retrieval_attempts"]
    assert attempts["attempt_count"] == 7
    assert attempts["maximum_attempt_count"] == 8
    assert attempts["remaining_attempt_count"] == 1
    assert attempts["maximum_attempts_per_url"] == 2
    assert attempts["manual_sessions_consumed"] == 1
    assert attempts["authenticated_mirrors_used"] == 0
    urls = [row["source_location"] for row in attempts["rows"]]
    assert max(urls.count(url) for url in set(urls)) == 2


def test_each_attempt_has_the_mandatory_custody_fields() -> None:
    mandatory = {
        "source_location",
        "acquisition_method",
        "acquisition_timestamp",
        "original_filename",
        "file_type",
        "file_size",
        "sha256",
        "publisher_or_custodian_identity",
        "license_or_access_conditions",
        "content_description",
        "ingestion_result",
        "completeness_status",
    }
    for row in _report()["retrieval_attempts"]["rows"]:
        assert mandatory <= row.keys()
        assert row["acquisition_timestamp"]["started_utc"]
        assert row["acquisition_timestamp"]["finished_utc"]


def test_official_supplement_was_identified_but_not_acquired() -> None:
    report = _report()
    assert report["custody_summary"]["primary_supplement_acquired"] is False
    assert report["custody_summary"]["primary_supplement_ingested"] is False
    first = report["retrieval_attempts"]["rows"][0]
    second = report["retrieval_attempts"]["rows"][1]
    assert first["access_result"] == "HTTP_403_CLOUDFLARE_CHALLENGE"
    assert second["access_result"] == (
        "APS_ARTICLE_REACHED_SUPPLEMENT_SUBSCRIPTION_REQUIRED"
    )
    assert second["sha256"] is None


def test_arxiv_source_archive_contains_article_source_not_supplement() -> None:
    third = _report()["retrieval_attempts"]["rows"][2]
    assert third["custody_state"] == "VERIFIED"
    assert third["ingestion_result"] == "TAR_GZIP_OPENED_11_MEMBERS_PARSED"
    assert third["completeness_status"] == (
        "VERIFIED_ARTICLE_SOURCE_NOT_SUPPLEMENT"
    )


def test_dissertation_is_verified_supporting_evidence_only() -> None:
    report = _report()
    summary = report["custody_summary"]
    assert summary["supporting_dissertation_acquired"] is True
    assert summary["supporting_dissertation_page_count"] == 169
    assert summary["supporting_dissertation_license"] == "CC_BY"
    assert summary[
        "supporting_dissertation_cannot_replace_primary_numerical_evidence"
    ] is True
    dissertation = report["retrieval_attempts"]["rows"][5]
    assert "95 runs x three torques" in dissertation["content_description"]
    assert dissertation["custody_state"] == "VERIFIED"


def test_all_six_inventory_items_are_partial_and_zero_are_complete() -> None:
    inventory = _report()["required_evidence_inventory"]
    assert inventory["item_count"] == 6
    assert inventory["verified_partial_item_count"] == 6
    assert inventory["complete_item_count"] == 0
    assert all(row["complete"] is False for row in inventory["rows"])


def test_observation_table_does_not_silently_complete_primary_contract() -> None:
    observation = _inventory()["OBSERVATION_TORQUE_VECTOR"]
    assert observation["status"] == (
        "VERIFIED_SUPPORTING_EXACT_TABLE_NOT_COMPLETE_AS_PRIMARY"
    )
    assert "95 run identifiers" in observation["present"]
    assert "primary supplement" in observation["missing"]


def test_configuration_covariance_and_nuisance_contracts_remain_incomplete() -> None:
    rows = _inventory()
    assert "per-run x and y" in rows["DISPLACEMENT_AND_CONFIGURATION_METADATA"]["missing"]
    assert "correlated-systematic" in rows["UNCERTAINTY_AND_COVARIANCE_MODEL"]["missing"]
    assert "executable entry points" in rows["FIVE_NUISANCE_PRIOR_CONTRACTS"]["missing"]


def test_forward_model_and_boundary_coverage_remain_non_executable() -> None:
    report = _report()
    forward = report["forward_model_sufficiency"]
    statistical = report["statistical_sufficiency"]
    assert forward["status"] == "NOT_EXECUTABLE"
    assert not any(
        forward[key]
        for key in (
            "published_Newtonian_prediction_reproducible_without_guessing",
            "three_harmonics_at_all_95_settings_computable",
            "all_five_nuisance_effects_executable",
            "fixed_strength_Yukawa_arbitrary_lambda_computable",
            "complete_residual_vector_constructible",
        )
    )
    assert statistical["status"] == "NOT_EXECUTABLE"
    assert statistical["boundary_coverage_calibrated"] is False


def test_no_empirical_or_theory_claim_lane_was_opened() -> None:
    scope = _report()["scope"]
    for key in (
        "access_control_circumvention_executed",
        "author_or_custodian_contact_executed",
        "synthetic_forecast_executed",
        "published_constraint_reinterpreted",
        "likelihood_executed",
        "numerical_bound_computed",
        "lambda0_selected",
        "alpha_selected",
        "scalar_branch_adopted",
        "native_gravitational_principle_identified",
        "gravitational_action_selected",
        "frame_dragging_resumed",
    ):
        assert scope[key] is False


def test_all_execution_controls_pass() -> None:
    controls = _report()["execution_controls"]
    assert controls["control_count"] == 12
    assert controls["pass_count"] == 12
    assert controls["failure_count"] == 0
    assert all(row["status"] == "PASSED" for row in controls["rows"])

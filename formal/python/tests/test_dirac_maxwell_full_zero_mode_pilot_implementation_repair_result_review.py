from __future__ import annotations

from formal.python.tools import dirac_maxwell_full_zero_mode_pilot_implementation_repair_result_review as review


def test_repair_review_artifact_is_current() -> None:
    report = review.build_review_report()
    assert review.REVIEW_REPORT_PATH.read_bytes() == review.canonical_json_bytes(report)


def test_preparation_custody_and_independent_identity_audit_pass() -> None:
    report = review.build_review_report()
    assert report["preparation_custody"]["passed"] is True
    audit = report["independent_identity_audit"]
    assert audit["records_match_independent_recomputation"] is True
    assert audit["run_record_ids_unique"] is True
    assert audit["all_ids_role_qualified"] is True
    assert len(audit["duplicate_legacy_run_ids"]) == 2
    assert len(audit["shared_execution_ids_across_distinct_roles"]) == 2


def test_all_decisions_accept_only_pilot_v1() -> None:
    report = review.build_review_report()
    assert report["accepted"] is True
    assert report["verdict"] == "ACCEPT"
    assert report["passed_decision_count"] == report["decision_count"] == 13
    assert report["failed_decision_ids"] == []
    assert report["selected_next_target"] == review.ACCEPTED_TARGET
    rotation = report["authority_rotation"]
    assert rotation["run_identity_repair_accepted"] is True
    assert rotation["non_authoritative_pilot_v1_authorized"] is True
    assert rotation["pilot_v0_engineering_evidence_accepted"] is False
    assert rotation["canonical_parameter_freeze_authorized"] is False
    assert rotation["canonical_execution_authorized"] is False


def test_prompt_is_preserved() -> None:
    assert review.sha256_path(review.REPO_ROOT / review.PROMPT_RELATIVE_PATH) == review.PROMPT_SHA256

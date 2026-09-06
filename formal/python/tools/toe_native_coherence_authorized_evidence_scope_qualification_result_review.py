from __future__ import annotations

from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    REPO_ROOT,
    read_json,
    sha256_path,
    write_or_check,
)


CAPTURED_AT_UTC = "2026-07-30T00:00:00Z"
CALC_PATH = REPO_ROOT / (
    "formal/output/"
    "CALC-TOE-NATIVE-COHERENCE-AUTHORIZED-EVIDENCE-SCOPE-"
    "QUALIFICATION-v0.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "TOE_NATIVE_COHERENCE_AUTHORIZED_EVIDENCE_SCOPE_QUALIFICATION_"
    "RESULT_REVIEW_20260730_v0.json"
)


def build() -> dict:
    calc = read_json(CALC_PATH)
    evidence_ok = all(
        (REPO_ROOT / item["path"]).is_file()
        and sha256_path(REPO_ROOT / item["path"]) == item["sha256"]
        for item in calc["evidence"].values()
    )
    scope = calc["scope_qualification"]
    closed = calc["preserved_closed_result"]
    custody = calc["custody_controls"]
    checks = {
        "evidence_hashes_recompute": evidence_ok,
        "authorized_source_count_is_13": (
            calc["source_scope_facts"]["stage_1_distinct_authorized_source_count"]
            == 13
        ),
        "archive_index_records_more_than_authorized_set": (
            calc["source_scope_facts"]["archive_indexed_file_count"] > 13
        ),
        "archive_census_is_not_claimed": (
            scope["archive_wide_ccft_evidence_census"] == "NOT_PERFORMED"
            and scope["repository_wide_evidence_sufficiency"] == "NOT_TESTED"
        ),
        "precise_scope_wording_is_present": (
            scope["precise_status_statement"]
            == (
                "The coherence claims contained in the authorized canonical "
                "evidence set were insufficiently defined for operational "
                "representation. Potentially relevant historical archive "
                "material was outside scope and remains unadjudicated."
            )
        ),
        "closed_scientific_outcome_is_unchanged": (
            closed["program_result"]
            == "EXISTING_COHERENCE_CLAIMS_INSUFFICIENTLY_DEFINED"
            and closed["operational_result"]
            == "COHERENCE_CLAIM_INSUFFICIENTLY_OPERATIONAL"
            and closed["terminal_outcome_changed"] is False
        ),
        "closed_program_is_not_reopened": (
            closed["program_reopened"] is False
            and custody["new_scientific_stage_consumed"] is False
        ),
        "archive_material_is_not_adopted": (
            custody["archive_files_modified"] is False
            and custody["archive_material_promoted"] is False
        ),
        "future_coherence_is_not_ruled_out": (
            scope["future_coherence_representation_ruled_out"] is False
        ),
        "no_automatic_successor_is_selected": (
            custody["automatic_successor_selected"] is False
        ),
    }
    failed = sorted(name for name, passed in checks.items() if not passed)
    return {
        "schema_id": (
            "toe.native_coherence.authorized_evidence_scope_qualification_review.v0"
        ),
        "artifact_id": (
            "TOE_NATIVE_COHERENCE_AUTHORIZED_EVIDENCE_SCOPE_QUALIFICATION_"
            "RESULT_REVIEW_20260730_v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "reviewed_result": {
            "path": CALC_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(CALC_PATH),
        },
        "checks": checks,
        "failed_checks": failed,
        "accepted": not failed,
        "scientific_result_changed": False,
        "scientific_program_reopened": False,
        "archive_evidence_adopted": False,
        "verdict": (
            "ACCEPT_SCOPE_QUALIFICATION_CLOSED_RESULT_UNCHANGED"
            if not failed
            else "REJECT_SCOPE_QUALIFICATION_REVIEW_FAILED"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build,
        description="coherence scope qualification result review",
    )


if __name__ == "__main__":
    raise SystemExit(main())

from __future__ import annotations

from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    REPO_ROOT,
    QuadraticHyperbolicityError,
    read_json,
    sha256_path,
    write_or_check,
)


CAPTURED_AT_UTC = "2026-07-30T00:00:00Z"
EXECUTION_TARGET = (
    "record_toe_native_coherence_authorized_evidence_scope_qualification_v0"
)
OUTCOME = "COHERENCE_CLOSEOUT_SCOPE_QUALIFIED_WITHOUT_SCIENTIFIC_REOPENING"
STRICT_OUTCOME = (
    "AUTHORIZED_13_SOURCE_EVIDENCE_INSUFFICIENT_ARCHIVE_WIDE_EVIDENCE_"
    "UNADJUDICATED_ORIGINAL_CLOSEOUT_AND_TERMINAL_OUTCOME_UNCHANGED"
)

STAGE_1_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "TOE_NATIVE_CONTROLLED_COHERENCE_CLAIM_INVENTORY_RESULT_20260729_v0.json"
)
STAGE_2_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "TOE_NATIVE_COHERENCE_OPERATIONAL_DEFINITION_RESULT_20260729_v0.json"
)
CLOSEOUT_PATH = REPO_ROOT / (
    "formal/output/"
    "CALC-TOE-NATIVE-COHERENCE-ONTOLOGY-AND-REPRESENTATION-V0-"
    "BOUNDED-CLOSEOUT-v0.json"
)
CLOSEOUT_REVIEW_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "TOE_NATIVE_COHERENCE_ONTOLOGY_AND_REPRESENTATION_V0_"
    "BOUNDED_CLOSEOUT_REVIEW_20260730_v0.json"
)
MANIFEST_PATH = REPO_ROOT / (
    "formal/docs/release/bounded_program_manifests/"
    "TOE_NATIVE_COHERENCE_ONTOLOGY_AND_REPRESENTATION_V0_MANIFEST_v1.json"
)
ARCHIVE_INDEX_PATH = REPO_ROOT / "formal/output/archive_intake_index.json"
ARCHIVE_RANKING_PATH = REPO_ROOT / "formal/output/archive_candidate_ranking.json"
CCFT_DOSSIER_PATH = REPO_ROOT / (
    "formal/quarantine/dossiers/"
    "DOSSIER_0007_archive_docs_monograph_ccft_monograph_md.md"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/output/"
    "CALC-TOE-NATIVE-COHERENCE-AUTHORIZED-EVIDENCE-SCOPE-"
    "QUALIFICATION-v0.json"
)

EVIDENCE_PATHS = {
    "stage_1_claim_inventory": STAGE_1_PATH,
    "stage_2_operational_test": STAGE_2_PATH,
    "terminal_closeout": CLOSEOUT_PATH,
    "terminal_closeout_review": CLOSEOUT_REVIEW_PATH,
    "closed_program_manifest": MANIFEST_PATH,
    "archive_intake_index": ARCHIVE_INDEX_PATH,
    "archive_candidate_ranking": ARCHIVE_RANKING_PATH,
    "ccft_archive_quarantine_dossier": CCFT_DOSSIER_PATH,
}


def build() -> dict:
    stage_1 = read_json(STAGE_1_PATH)
    stage_2 = read_json(STAGE_2_PATH)
    closeout = read_json(CLOSEOUT_PATH)
    archive_index = read_json(ARCHIVE_INDEX_PATH)
    if not isinstance(archive_index.get("files"), list):
        raise QuadraticHyperbolicityError("archive intake index lacks files array")
    sources = stage_1.get("source_bound_claim_inventory")
    claims = stage_1.get("claim_inventory")
    if not isinstance(sources, list) or not isinstance(claims, list):
        raise QuadraticHyperbolicityError(
            "Stage 1 result lacks source or claim inventory"
        )
    authorized_sources = sorted(
        {
            source["path"]
            for source in sources
            if isinstance(source, dict) and "path" in source
        }
    )
    if (
        len(claims) != 13
        or len(sources) != 13
        or len(authorized_sources) != 13
    ):
        raise QuadraticHyperbolicityError(
            "expected exactly 13 source-bound claims and authorized sources"
        )
    if (
        closeout.get("scientific_results", {}).get("program_result")
        != "EXISTING_COHERENCE_CLAIMS_INSUFFICIENTLY_DEFINED"
    ):
        raise QuadraticHyperbolicityError("closed program result changed")
    if (
        stage_2.get("terminal_outcome")
        != "EXISTING_COHERENCE_CLAIMS_INSUFFICIENTLY_DEFINED"
    ):
        raise QuadraticHyperbolicityError("Stage 2 terminal outcome changed")

    evidence = {
        key: {
            "path": path.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(path),
        }
        for key, path in EVIDENCE_PATHS.items()
    }
    return {
        "schema_id": "toe.native_coherence.authorized_evidence_scope_qualification.v0",
        "artifact_id": (
            "CALC-TOE-NATIVE-COHERENCE-AUTHORIZED-EVIDENCE-SCOPE-"
            "QUALIFICATION-v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "execution_target": EXECUTION_TARGET,
        "native_hypothesis_tested": "NONE_GOVERNANCE_OR_CUSTODY_ONLY",
        "native_relevance": {
            "kind": "SCIENTIFIC_CUSTODY_SCOPE_QUALIFICATION",
            "statement": (
                "Qualifies the evidentiary reach of a closed native-coherence "
                "program without changing its result."
            ),
        },
        "evidence": evidence,
        "source_scope_facts": {
            "stage_1_claim_count": len(claims),
            "stage_1_source_record_count": len(sources),
            "stage_1_distinct_authorized_source_count": len(authorized_sources),
            "stage_1_authorized_sources": authorized_sources,
            "archive_indexed_file_count": len(archive_index["files"]),
            "archive_material_was_in_stage_1_authority": False,
            "archive_wide_ccft_evidence_census_performed": False,
            "repository_wide_native_hypothesis_census_performed": False,
            "ccft_monograph_was_available_only_through_a_canonical_dossier": True,
        },
        "scope_qualification": {
            "precise_status_statement": (
                "The coherence claims contained in the authorized canonical "
                "evidence set were insufficiently defined for operational "
                "representation. Potentially relevant historical archive "
                "material was outside scope and remains unadjudicated."
            ),
            "authorized_evidence_sufficiency": "FAILED",
            "repository_wide_evidence_sufficiency": "NOT_TESTED",
            "ccft_operational_representability": (
                "BLOCKED_ON_AUTHORIZED_EVIDENCE"
            ),
            "archive_wide_ccft_evidence_census": "NOT_PERFORMED",
            "every_repository_coherence_claim_exhausted": False,
            "future_coherence_representation_ruled_out": False,
            "archive_contains_operational_definition": "UNKNOWN_NOT_TESTED",
        },
        "preserved_closed_result": {
            "program_id": (
                "TOE_NATIVE_COHERENCE_ONTOLOGY_AND_REPRESENTATION_V0"
            ),
            "program_result": (
                "EXISTING_COHERENCE_CLAIMS_INSUFFICIENTLY_DEFINED"
            ),
            "operational_result": (
                "COHERENCE_CLAIM_INSUFFICIENTLY_OPERATIONAL"
            ),
            "representation_status": "NOT_REACHED",
            "calculation_status": "NOT_REACHED",
            "native_model_status": "NOT_CONSTRUCTED",
            "program_reopened": False,
            "original_artifacts_rewritten": False,
            "terminal_outcome_changed": False,
        },
        "scientific_boundary": {
            "established": [
                (
                    "The authorized 13-source evidence set was insufficient "
                    "for operational representation."
                )
            ],
            "not_established": [
                "the entire repository lacks an operational definition",
                "the archive contains an operational definition",
                "CCFT is false",
                "coherence cannot be physical",
                "a future coherence representation is impossible",
            ],
        },
        "custody_controls": {
            "non_destructive_addendum": True,
            "closed_program_event_chain_unchanged": True,
            "closed_program_manifest_unchanged": True,
            "archive_files_modified": False,
            "archive_material_promoted": False,
            "new_scientific_stage_consumed": False,
            "automatic_successor_selected": False,
        },
        "terminal_outcome": OUTCOME,
        "strict_terminal_outcome": STRICT_OUTCOME,
        "verdict": (
            "ACCEPT_FORWARD_ONLY_SCOPE_QUALIFICATION_PRESERVE_CLOSED_RESULT"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build,
        description="coherence authorized-evidence scope qualification",
    )


if __name__ == "__main__":
    raise SystemExit(main())

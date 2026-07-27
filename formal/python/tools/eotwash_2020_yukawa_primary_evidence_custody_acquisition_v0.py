from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "EOTWASH_2020_YUKAWA_PRIMARY_EVIDENCE_CUSTODY_ACQUISITION_"
    "20260718_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/"
    "EOTWASH_2020_YUKAWA_PRIMARY_EVIDENCE_CUSTODY_ACQUISITION_"
    "20260718_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_eotwash_2020_yukawa_primary_evidence_custody_acquisition_v0.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "Eotwash2020YukawaPrimaryEvidenceCustodyAcquisitionV0.lean"
)
REVIEW_RELATIVE_PATH = (
    "formal/docs/release/"
    "EOTWASH_2020_YUKAWA_PRIMARY_EVIDENCE_CUSTODY_ACQUISITION_PACKET_"
    "REVIEW_20260718_v0.json"
)

TARGET = "execute_eotwash_2020_yukawa_primary_evidence_custody_acquisition_v0"
VERDICT = (
    "PRIMARY_EVIDENCE_ACQUISITION_PARTIAL_CONTACT_REQUIRED_"
    "PENDING_INDEPENDENT_REVIEW"
)
PRINCIPAL_OUTCOME = "AUTHORS_OR_CUSTODIAN_CONTACT_REQUIRED"
SELECTED_NEXT_TARGET = (
    "review_eotwash_2020_yukawa_primary_evidence_custody_acquisition_v0_result"
)
SELECTED_NEXT_TARGET_KIND = "INDEPENDENT_ACQUISITION_RESULT_REVIEW_ONLY"

REVIEW_HASHES = {
    "formal/docs/lanes/EOTWASH_2020_YUKAWA_PRIMARY_EVIDENCE_CUSTODY_ACQUISITION_PACKET_REVIEW_20260718_v0.md":
        "5056b7d67f1319c6771c5ed97179c163c5d57fee85f8a75b0ad703f3085aa050",
    REVIEW_RELATIVE_PATH:
        "2600e7a4b0c118168ef8af2950560d2a94b28e0207ce3de336c81503f49d2a1d",
    "formal/python/tools/eotwash_2020_yukawa_primary_evidence_custody_acquisition_packet_review_v0.py":
        "23a65ccb077d96b0091e7c01e7f42e40cdcc6c9b82adf65c4996ec30e2ad8da5",
    "formal/python/tests/test_eotwash_2020_yukawa_primary_evidence_custody_acquisition_packet_review_v0.py":
        "084cfa3501c18aaa7fa46048d218c37109eaff6f534e162ddc71e7a5961214d6",
    "formal/toe_formal/ToeFormal/Derivation/Eotwash2020YukawaPrimaryEvidenceCustodyAcquisitionPacketReviewV0.lean":
        "171536eb366391e78f2f136b0206e449dcf83c7cb6bf72e6abe0bf45bfe15ac4",
}

ACQUIRED_OBJECT_HASHES = {
    "formal/data/eotwash_2020_primary_evidence_acquisition_v0/attempt_01_aps_official_supplement/error_response.html":
        "b15dec15f1c4ee65b6089d7497906df46ed140883aa1fefa3547390f5b696bba",
    "formal/data/eotwash_2020_primary_evidence_acquisition_v0/attempt_01_aps_official_supplement/response_headers.txt":
        "371cd576e9979fe8fc1b584ba07c7f671ccf6deb04975150690ee852cab1dc25",
    "formal/data/eotwash_2020_primary_evidence_acquisition_v0/attempt_02_aps_official_manual_browser/attempt_record.json":
        "5337ec6cbce9b1a7942eee967301260d3de49681dd5a4529305e05ccb795b9ce",
    "formal/data/eotwash_2020_primary_evidence_acquisition_v0/attempt_03_arxiv_source_archive/arXiv-2002.11761v1.tar.gz":
        "114bac164ab553858a310a569b5a165cc3a97b03285dc880288c5ecbf3284952",
    "formal/data/eotwash_2020_primary_evidence_acquisition_v0/attempt_03_arxiv_source_archive/response_headers.txt":
        "641f173aa4cbb54745b63383ab1d48b3e84cb33444b8921fcf7161f07d38711d",
    "formal/data/eotwash_2020_primary_evidence_acquisition_v0/attempt_04_eotwash_official_archive_index/eotwash_homepage.html":
        "172596b169fd2ab62fea48bd3e10650f1b7453a6911172abc62caa3537bbf4aa",
    "formal/data/eotwash_2020_primary_evidence_acquisition_v0/attempt_04_eotwash_official_archive_index/response_headers.txt":
        "7dba4a8938c14f8dd772ef2fbe82f86a5942e75c7721ba66f3f15a30073acae7",
    "formal/data/eotwash_2020_primary_evidence_acquisition_v0/attempt_05_uw_researchworks_item/researchworks_item.html":
        "521bdbac4ed0959805200a2c269c3671592b01d78160d58dbb1874cc88855af1",
    "formal/data/eotwash_2020_primary_evidence_acquisition_v0/attempt_05_uw_researchworks_item/response_headers.txt":
        "7b64407c96f702d0f2ab1f21f5f381677fb09c68f17324f45364a2ea6ea45224",
    "formal/data/eotwash_2020_primary_evidence_acquisition_v0/attempt_06_uw_dissertation_bitstream/A_Fourier-Bessel_Test_of_the_Gravitational_Inverse-Square_Law.pdf":
        "00d13a466e4f8c14c3f6067d49d90fd0c49a89e72a8cf93f3a79c18d6aef924a",
    "formal/data/eotwash_2020_primary_evidence_acquisition_v0/attempt_06_uw_dissertation_bitstream/response_headers.txt":
        "864d367087c3f80069c413c0ae7da611d7df4d0a2333060339721cb89a377279",
    "formal/data/eotwash_2020_primary_evidence_acquisition_v0/attempt_07_aps_chorus_accepted_manuscript/error_response.html":
        "df1065eb3c6f41a6a09a401cc96e241f4b52c76931d8cdec2fe561cda185c1bf",
    "formal/data/eotwash_2020_primary_evidence_acquisition_v0/attempt_07_aps_chorus_accepted_manuscript/response_headers.txt":
        "55973a87b60b64bece924dfcd14e1d2094d4933271b78caacafcec15c0a6b572",
}


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {relative_path}")
    return value


def _validate_authority() -> tuple[list[dict[str, str]], dict[str, Any]]:
    rows: list[dict[str, str]] = []
    for relative_path, expected in REVIEW_HASHES.items():
        observed = _sha256(REPO_ROOT / relative_path)
        if observed != expected:
            raise ValueError(f"acquisition authority drift: {relative_path}")
        rows.append({"relative_path": relative_path, "sha256": observed})
    review = _load_json(REVIEW_RELATIVE_PATH)
    if review.get("verdict") != (
        "ACCEPTED_PRIMARY_EVIDENCE_ACQUISITION_CONTRACT_READY_FOR_ONE_BOUNDED_EXECUTION"
    ):
        raise ValueError("acquisition packet review was not accepted")
    if review.get("selected_next_target") != TARGET:
        raise ValueError("packet review did not authorize this acquisition")
    if review["authorized_acquisition"].get("execution_count") != 1:
        raise ValueError("acquisition authority is not exactly one execution")
    return rows, review


def _validate_acquired_objects() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for relative_path, expected in ACQUIRED_OBJECT_HASHES.items():
        path = REPO_ROOT / relative_path
        observed = _sha256(path)
        if observed != expected:
            raise ValueError(f"acquired object custody drift: {relative_path}")
        rows.append({
            "relative_path": relative_path,
            "sha256": observed,
            "size_bytes": path.stat().st_size,
        })
    return rows


def _attempts() -> list[dict[str, Any]]:
    return [
        {
            "attempt_number": 1,
            "source_tier": 1,
            "source_location": "https://link.aps.org/supplemental/10.1103/PhysRevLett.124.101101",
            "acquisition_method": "ordinary unauthenticated curl GET with redirects",
            "acquisition_timestamp": {
                "started_utc": "2026-07-19T00:20:04.5664287Z",
                "finished_utc": "2026-07-19T00:20:05.0765858Z",
            },
            "access_result": "HTTP_403_CLOUDFLARE_CHALLENGE",
            "original_filename": "error_response.html",
            "file_type": "text/html error response",
            "file_size": 5532,
            "sha256": "b15dec15f1c4ee65b6089d7497906df46ed140883aa1fefa3547390f5b696bba",
            "publisher_or_custodian_identity": "American Physical Society",
            "license_or_access_conditions": "supplement bytes not reached; no challenge bypass attempted",
            "content_description": "Cloudflare access-challenge response, not scientific evidence",
            "ingestion_result": "OPENED_AS_HTML_ACCESS_ERROR",
            "completeness_status": "NOT_EVIDENCE",
            "custody_state": "INGESTED_ACCESS_FAILURE",
            "required_component_mapping": [],
        },
        {
            "attempt_number": 2,
            "source_tier": 1,
            "source_location": "https://link.aps.org/supplemental/10.1103/PhysRevLett.124.101101",
            "acquisition_method": "single authorized manual in-app browser session",
            "acquisition_timestamp": {
                "started_utc": "2026-07-19T00:22:13.438Z",
                "finished_utc": "2026-07-19T00:22:18.355Z",
            },
            "access_result": "APS_ARTICLE_REACHED_SUPPLEMENT_SUBSCRIPTION_REQUIRED",
            "original_filename": None,
            "file_type": None,
            "file_size": 0,
            "sha256": None,
            "publisher_or_custodian_identity": "American Physical Society",
            "license_or_access_conditions": "subscription required; no sign-in or access-control action taken",
            "content_description": "official APS section marks supplemental material data-auth-required=true",
            "ingestion_result": "VISIBLE_PAGE_INSPECTED_NO_SUPPLEMENT_BYTES",
            "completeness_status": "IDENTIFIED_NOT_ACQUIRED",
            "custody_state": "IDENTIFIED",
            "required_component_mapping": [],
        },
        {
            "attempt_number": 3,
            "source_tier": 3,
            "source_location": "https://arxiv.org/e-print/2002.11761",
            "acquisition_method": "ordinary unauthenticated curl GET with redirects",
            "acquisition_timestamp": {
                "started_utc": "2026-07-19T00:23:15.6697565Z",
                "finished_utc": "2026-07-19T00:23:16.3954790Z",
            },
            "access_result": "HTTP_200",
            "original_filename": "arXiv-2002.11761v1.tar.gz",
            "file_type": "application/gzip",
            "file_size": 530474,
            "sha256": "114bac164ab553858a310a569b5a165cc3a97b03285dc880288c5ecbf3284952",
            "publisher_or_custodian_identity": "arXiv author-submitted public archive",
            "license_or_access_conditions": "public arXiv distribution; no supplement reuse license inferred",
            "content_description": "article TeX and ten PDF figures; no cited supplemental numerical file or code",
            "ingestion_result": "TAR_GZIP_OPENED_11_MEMBERS_PARSED",
            "completeness_status": "VERIFIED_ARTICLE_SOURCE_NOT_SUPPLEMENT",
            "custody_state": "VERIFIED",
            "required_component_mapping": [
                "UNCERTAINTY_AND_COVARIANCE_MODEL_PARTIAL_METHODS",
                "FIVE_NUISANCE_PRIOR_CONTRACTS_PARTIAL_METHODS",
                "EXTENDED_SOURCE_TORQUE_FORWARD_MODEL_PARTIAL_METHODS",
                "BOUNDARY_COVERAGE_PROCEDURE_PARTIAL_METHODS",
            ],
        },
        {
            "attempt_number": 4,
            "source_tier": 3,
            "source_location": "https://www.npl.washington.edu/eotwash/",
            "acquisition_method": "ordinary unauthenticated curl GET",
            "acquisition_timestamp": {
                "started_utc": "2026-07-19T00:24:05.7089841Z",
                "finished_utc": "2026-07-19T00:24:06.8243292Z",
            },
            "access_result": "HTTP_200",
            "original_filename": "eotwash_homepage.html",
            "file_type": "text/html",
            "file_size": 26691,
            "sha256": "172596b169fd2ab62fea48bd3e10650f1b7453a6911172abc62caa3537bbf4aa",
            "publisher_or_custodian_identity": "Eot-Wash Group, University of Washington",
            "license_or_access_conditions": "public institutional page; site copyright retained",
            "content_description": "official publication index links the 2020 paper only to arXiv; no data, code, or supplement link",
            "ingestion_result": "HTML_OPENED_AND_PUBLICATION_LINKS_VERIFIED",
            "completeness_status": "VERIFIED_INDEX_ONLY",
            "custody_state": "VERIFIED",
            "required_component_mapping": [],
        },
        {
            "attempt_number": 5,
            "source_tier": 4,
            "source_location": "https://digital.lib.washington.edu/researchworks/items/971237d1-100a-41ae-9027-d1bbce8cf315/full",
            "acquisition_method": "ordinary unauthenticated curl GET",
            "acquisition_timestamp": {
                "started_utc": "2026-07-19T00:24:19.9940289Z",
                "finished_utc": "2026-07-19T00:24:23.9428798Z",
            },
            "access_result": "HTTP_200",
            "original_filename": "researchworks_item.html",
            "file_type": "text/html",
            "file_size": 451122,
            "sha256": "521bdbac4ed0959805200a2c269c3671592b01d78160d58dbb1874cc88855af1",
            "publisher_or_custodian_identity": "University of Washington ResearchWorks",
            "license_or_access_conditions": "public repository metadata; item records CC BY",
            "content_description": "institutional dissertation record and exact public bitstream identifier",
            "ingestion_result": "HTML_OPENED_METADATA_AND_BITSTREAM_ID_PARSED",
            "completeness_status": "VERIFIED_SUPPORTING_RECORD_ONLY",
            "custody_state": "VERIFIED",
            "required_component_mapping": [],
        },
        {
            "attempt_number": 6,
            "source_tier": 4,
            "source_location": "https://digital.lib.washington.edu/bitstreams/6013936a-da00-42b7-ba0a-4dff0cb05bf8/download",
            "acquisition_method": "ordinary unauthenticated repository bitstream download",
            "acquisition_timestamp": {
                "started_utc": "2026-07-19T00:24:59.2977165Z",
                "finished_utc": "2026-07-19T00:25:07.9556536Z",
            },
            "access_result": "HTTP_200",
            "original_filename": "Lee_washington_0250E_21241.pdf",
            "file_type": "application/pdf",
            "file_size": 17382930,
            "sha256": "00d13a466e4f8c14c3f6067d49d90fd0c49a89e72a8cf93f3a79c18d6aef924a",
            "publisher_or_custodian_identity": "University of Washington ResearchWorks",
            "license_or_access_conditions": "CC BY stated by repository item",
            "content_description": "J. G. Lee dissertation, 169 PDF pages; Appendix A prints 95 runs x three torques with pointwise uncertainties; chapters describe fit and apparatus",
            "ingestion_result": "PDF_OPENED_TEXT_EXTRACTED_AND_RELEVANT_PAGES_VISUALLY_VERIFIED",
            "completeness_status": "VERIFIED_SUPPORTING_PARTIAL_NOT_PRIMARY_NUMERICAL_SUBSTITUTE",
            "custody_state": "VERIFIED",
            "required_component_mapping": [
                "OBSERVATION_TORQUE_VECTOR_SUPPORTING_EXACT_TABLE",
                "DISPLACEMENT_AND_CONFIGURATION_METADATA_PARTIAL_SEPARATION_ONLY",
                "UNCERTAINTY_AND_COVARIANCE_MODEL_PARTIAL",
                "FIVE_NUISANCE_PRIOR_CONTRACTS_PARTIAL",
                "EXTENDED_SOURCE_TORQUE_FORWARD_MODEL_PARTIAL_METHODS",
                "BOUNDARY_COVERAGE_PROCEDURE_PARTIAL_PUBLISHED_RULE",
            ],
        },
        {
            "attempt_number": 7,
            "source_tier": 2,
            "source_location": "https://link.aps.org/accepted/10.1103/PhysRevLett.124.101101",
            "acquisition_method": "ordinary unauthenticated curl GET with redirects",
            "acquisition_timestamp": {
                "started_utc": "2026-07-19T00:26:45.7566962Z",
                "finished_utc": "2026-07-19T00:26:46.2322875Z",
            },
            "access_result": "HTTP_403_CLOUDFLARE_CHALLENGE",
            "original_filename": "error_response.html",
            "file_type": "text/html error response",
            "file_size": 5520,
            "sha256": "df1065eb3c6f41a6a09a401cc96e241f4b52c76931d8cdec2fe561cda185c1bf",
            "publisher_or_custodian_identity": "American Physical Society CHORUS route",
            "license_or_access_conditions": "accepted manuscript bytes not reached; no challenge bypass attempted",
            "content_description": "Cloudflare access-challenge response, not scientific evidence",
            "ingestion_result": "OPENED_AS_HTML_ACCESS_ERROR",
            "completeness_status": "NOT_EVIDENCE",
            "custody_state": "INGESTED_ACCESS_FAILURE",
            "required_component_mapping": [],
        },
    ]


def _inventory_rows() -> list[dict[str, Any]]:
    return [
        {
            "item_id": "OBSERVATION_TORQUE_VECTOR",
            "status": "VERIFIED_SUPPORTING_EXACT_TABLE_NOT_COMPLETE_AS_PRIMARY",
            "complete": False,
            "present": "95 run identifiers, separation, N120, N18, N54, units, and pointwise errors in dissertation Appendix A",
            "missing": "authorized primary supplement custody and complete primary row/configuration contract",
        },
        {
            "item_id": "DISPLACEMENT_AND_CONFIGURATION_METADATA",
            "status": "VERIFIED_SUPPORTING_PARTIAL",
            "complete": False,
            "present": "run identifier and scalar separation s with uncertainty",
            "missing": "per-run x and y, detector/attractor configuration identifiers, full alignment/phase metadata, exact primary ordering and cuts",
        },
        {
            "item_id": "UNCERTAINTY_AND_COVARIANCE_MODEL",
            "status": "VERIFIED_SUPPORTING_PARTIAL",
            "complete": False,
            "present": "pointwise torque and separation errors plus printed chi-square denominator",
            "missing": "primary correlated-systematic contract, block/covariance declaration, conditioning rules, and exact likelihood ordering",
        },
        {
            "item_id": "FIVE_NUISANCE_PRIOR_CONTRACTS",
            "status": "VERIFIED_SUPPORTING_PARTIAL",
            "complete": False,
            "present": "x0, y0, s0, overcut epsilon, and gamma identities, central values, widths, Gaussian penalties, and profiling description",
            "missing": "primary declared cross-covariance/independence, bounds, and executable entry points into the exact forward model",
        },
        {
            "item_id": "EXTENDED_SOURCE_TORQUE_FORWARD_MODEL",
            "status": "VERIFIED_SUPPORTING_METHODS_ONLY",
            "complete": False,
            "present": "Fourier-Bessel analytic framework, geometry descriptions, corrections, calibration discussion, and model equation",
            "missing": "torque tables or executable code, exact density geometry inputs, all correction tables, and 95-setting prediction path",
        },
        {
            "item_id": "BOUNDARY_COVERAGE_PROCEDURE",
            "status": "VERIFIED_SUPPORTING_PUBLISHED_RULE_ONLY",
            "complete": False,
            "present": "printed Delta-chi-square threshold and Gaussian integral construction used for published limits",
            "missing": "lambda-to-zero boundary calibration, pseudoexperiment/critical-value procedure, interpolation and reproducibility policy",
        },
    ]


def _controls(value: dict[str, Any]) -> dict[str, Any]:
    attempts = value["retrieval_attempts"]["rows"]
    inventory = value["required_evidence_inventory"]["rows"]
    scope = value["scope"]
    url_counts: dict[str, int] = {}
    for row in attempts:
        url_counts[row["source_location"]] = url_counts.get(row["source_location"], 0) + 1
    checks = [
        ("C1_EXACT_SINGLE_AUTHORITY_CONSUMED", value["authority"]["consumed_execution_count"] == 1),
        ("C2_RETRIEVAL_ATTEMPT_LIMIT", len(attempts) == 7 and len(attempts) <= 8),
        ("C3_PER_URL_ATTEMPT_LIMIT", max(url_counts.values()) <= 2),
        ("C4_SINGLE_MANUAL_SESSION_LIMIT", value["retrieval_attempts"]["manual_sessions_consumed"] == 1),
        ("C5_AUTHENTICATED_MIRROR_LIMIT", value["retrieval_attempts"]["authenticated_mirrors_used"] <= 2),
        ("C6_NO_ACCESS_CONTROL_CIRCUMVENTION", scope["access_control_circumvention_executed"] is False),
        ("C7_NO_AUTHOR_CONTACT", scope["author_or_custodian_contact_executed"] is False),
        ("C8_PRIMARY_SUPPLEMENT_NOT_MISCLASSIFIED", value["custody_summary"]["primary_supplement_acquired"] is False),
        ("C9_ZERO_COMPLETE_ITEMS", sum(row["complete"] for row in inventory) == 0),
        ("C10_NO_LIKELIHOOD_OR_BOUND", scope["likelihood_executed"] is False and scope["numerical_bound_computed"] is False),
        ("C11_NO_THEORY_ADOPTION", all(scope[key] is False for key in ("alpha_selected", "scalar_branch_adopted", "native_gravitational_principle_identified", "gravitational_action_selected"))),
        ("C12_ROTATE_ONLY_TO_RESULT_REVIEW", value["selected_next_target"] == SELECTED_NEXT_TARGET),
    ]
    return {
        "control_count": len(checks),
        "pass_count": sum(passed for _, passed in checks),
        "failure_count": sum(not passed for _, passed in checks),
        "rows": [
            {"control_id": control_id, "status": "PASSED" if passed else "FAILED"}
            for control_id, passed in checks
        ],
    }


def build_execution() -> dict[str, Any]:
    authority_rows, review = _validate_authority()
    acquired_rows = _validate_acquired_objects()
    for relative_path in (HUMAN_RELATIVE_PATH, TEST_RELATIVE_PATH, LEAN_RELATIVE_PATH):
        if not (REPO_ROOT / relative_path).is_file():
            raise ValueError(f"execution companion missing: {relative_path}")
    attempts = _attempts()
    inventory = _inventory_rows()
    value: dict[str, Any] = {
        "schema_id": "toe.eotwash_2020_yukawa_primary_evidence_custody_acquisition.execution.v0",
        "packet_id": "EOTWASH_2020_YUKAWA_PRIMARY_EVIDENCE_CUSTODY_ACQUISITION_20260718_v0",
        "captured_at_utc": "2026-07-19T00:27:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "principal_outcome": PRINCIPAL_OUTCOME,
        "subordinate_outcomes": [
            "SUPPLEMENT_IDENTIFIED_BUT_NOT_INGESTIBLE_WITHOUT_SUBSCRIPTION",
            "SUPPORTING_ARXIV_SOURCE_ACQUIRED_NO_SUPPLEMENT_INCLUDED",
            "SUPPORTING_DISSERTATION_ACQUIRED_AND_INGESTED",
            "OBSERVATION_VECTOR_VERIFIED_SUPPORTING_NOT_PRIMARY_COMPLETE",
            "DISPLACEMENT_AND_CONFIGURATION_METADATA_INCOMPLETE",
            "UNCERTAINTY_AND_COVARIANCE_CONTRACT_INCOMPLETE",
            "FIVE_NUISANCE_CONTRACTS_INCOMPLETE_FOR_EXECUTION",
            "EXTENDED_SOURCE_FORWARD_MODEL_INCOMPLETE",
            "BOUNDARY_COVERAGE_PROCEDURE_INCOMPLETE",
            "PRIMARY_EVIDENCE_NOT_OBTAINABLE_WITHIN_BOUNDED_NONCONTACT_ROUTE",
        ],
        "status": "PENDING_INDEPENDENT_ACQUISITION_RESULT_REVIEW",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "authorized_execution_count": 1,
            "consumed_execution_count": 1,
            "consumed_review_verdict": review["verdict"],
            "frozen_review_artifact_count": len(authority_rows),
            "frozen_review_artifacts": authority_rows,
        },
        "retrieval_attempts": {
            "attempt_count": len(attempts),
            "maximum_attempt_count": 8,
            "remaining_attempt_count": 1,
            "maximum_attempts_per_url": 2,
            "authenticated_mirrors_used": 0,
            "maximum_authenticated_mirrors": 2,
            "manual_sessions_consumed": 1,
            "maximum_manual_sessions": 1,
            "stop_basis": "FIVE_NONCONTACT_SOURCE_TIERS_EXHAUSTED_AND_CONTACT_REQUIRED_TERMINAL_OUTCOME_REACHED",
            "rows": attempts,
        },
        "source_tier_audit": {
            "noncontact_tier_count": 5,
            "tiers_exhausted": 5,
            "rows": [
                {"tier": 1, "status": "EXHAUSTED_TWO_ATTEMPTS_ACCESS_LIMITED", "finding": "official supplemental route requires subscription"},
                {"tier": 2, "status": "EXHAUSTED", "finding": "official article/CHORUS routes yielded metadata or access challenge, not supplement"},
                {"tier": 3, "status": "EXHAUSTED", "finding": "official Eot-Wash page points to arXiv; arXiv source has article and figures only"},
                {"tier": 4, "status": "EXHAUSTED_SUPPORTING_ONLY", "finding": "ResearchWorks dissertation is rich supporting evidence but contract forbids primary substitution"},
                {"tier": 5, "status": "NO_CONCRETE_AUTHENTICATED_MIRROR_IDENTIFIED", "finding": "focused provenance search found no verified publisher/lab mirror containing the supplement"},
            ],
        },
        "acquired_object_custody": {
            "hashed_object_count": len(acquired_rows),
            "rows": acquired_rows,
        },
        "custody_summary": {
            "network_payload_count": 6,
            "authenticated_scientific_or_repository_object_count": 4,
            "retained_access_error_response_count": 2,
            "browser_access_record_count": 1,
            "primary_supplement_acquired": False,
            "primary_supplement_ingested": False,
            "primary_evidence_contract_complete": False,
            "supporting_dissertation_acquired": True,
            "supporting_dissertation_page_count": 169,
            "supporting_dissertation_license": "CC_BY",
            "supporting_dissertation_cannot_replace_primary_numerical_evidence": True,
        },
        "required_evidence_inventory": {
            "item_count": len(inventory),
            "verified_partial_item_count": 6,
            "complete_item_count": sum(row["complete"] for row in inventory),
            "rows": inventory,
        },
        "forward_model_sufficiency": {
            "published_Newtonian_prediction_reproducible_without_guessing": False,
            "three_harmonics_at_all_95_settings_computable": False,
            "all_five_nuisance_effects_executable": False,
            "fixed_strength_Yukawa_arbitrary_lambda_computable": False,
            "exact_observation_ordering_complete": False,
            "complete_residual_vector_constructible": False,
            "status": "NOT_EXECUTABLE",
        },
        "statistical_sufficiency": {
            "exact_likelihood_specifiable_without_guessing": False,
            "baseline_fit_reproducible": False,
            "nuisance_profiling_reproducible": False,
            "boundary_coverage_calibrated": False,
            "published_standard_physics_result_reproduced": False,
            "status": "NOT_EXECUTABLE",
        },
        "scope": {
            "acquisition_execution_completed": True,
            "access_control_circumvention_executed": False,
            "author_or_custodian_contact_executed": False,
            "synthetic_forecast_executed": False,
            "published_constraint_reinterpreted": False,
            "likelihood_executed": False,
            "numerical_bound_computed": False,
            "lambda0_selected": False,
            "alpha_selected": False,
            "scalar_branch_adopted": False,
            "native_gravitational_principle_identified": False,
            "gravitational_action_selected": False,
            "frame_dragging_resumed": False,
            "independent_result_review_required": True,
        },
        "current_posture": {
            "acquisition": "COMPLETED_ONCE_PENDING_INDEPENDENT_REVIEW",
            "retrieval_attempts_consumed": "7_OF_8",
            "manual_session_consumed": "1_OF_1",
            "evidence_components_complete": "0_OF_6",
            "primary_supplement": "IDENTIFIED_NOT_ACQUIRED_SUBSCRIPTION_REQUIRED",
            "supporting_dissertation": "ACQUIRED_INGESTED_VERIFIED_PARTIAL",
            "author_contact": "NOT_EXECUTED_SEPARATE_AUTHORITY_REQUIRED",
            "likelihood": "NOT_EXECUTED",
            "numerical_scalar_range_or_alpha_bound": "NONE",
            "next_authority": SELECTED_NEXT_TARGET,
        },
        "claim_ceiling": (
            "One bounded non-contact acquisition execution found the official APS "
            "supplement but could not acquire it without subscription, acquired and "
            "verified the public arXiv article-source bundle, the official Eot-Wash "
            "publication index, the UW ResearchWorks record, and J. G. Lee's CC BY "
            "dissertation. The dissertation contains a supporting 95-run by three-"
            "harmonic torque table and substantial fit-method detail, but the accepted "
            "contract does not allow it to replace the missing primary supplement, "
            "complete configuration/covariance contract, executable torque model, or "
            "boundary-coverage procedure. Zero of six primary evidence items are "
            "complete. No likelihood, forecast, published-limit reinterpretation, "
            "scalar-range or alpha bound, branch adoption, gravitational principle, "
            "or gravitational action is computed or selected."
        ),
    }
    controls = _controls(value)
    if controls["failure_count"]:
        failures = [row["control_id"] for row in controls["rows"] if row["status"] == "FAILED"]
        raise ValueError(f"acquisition execution controls failed: {failures}")
    value["execution_controls"] = controls
    return value


def artifact_bytes() -> bytes:
    return (
        json.dumps(build_execution(), indent=2, sort_keys=True, ensure_ascii=True) + "\n"
    ).encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    path = REPO_ROOT / REPORT_RELATIVE_PATH
    raw = artifact_bytes()
    if args.check:
        if not path.is_file() or path.read_bytes() != raw:
            raise SystemExit("Eot-Wash acquisition execution artifact is stale or missing")
        report = json.loads(raw)
        print(json.dumps({
            "attempts": report["retrieval_attempts"]["attempt_count"],
            "complete_items": report["required_evidence_inventory"]["complete_item_count"],
            "controls": report["execution_controls"]["pass_count"],
            "outcome": report["principal_outcome"],
            "status": "CHECKED",
        }, sort_keys=True))
        return 0
    path.write_bytes(raw)
    print(path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

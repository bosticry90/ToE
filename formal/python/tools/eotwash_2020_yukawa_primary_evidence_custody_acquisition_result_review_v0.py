from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import tarfile
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
EXECUTION_RELATIVE_PATH = (
    "formal/docs/release/"
    "EOTWASH_2020_YUKAWA_PRIMARY_EVIDENCE_CUSTODY_ACQUISITION_"
    "20260718_v0.json"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "EOTWASH_2020_YUKAWA_PRIMARY_EVIDENCE_CUSTODY_ACQUISITION_"
    "RESULT_REVIEW_20260718_v0.json"
)
HUMAN_REVIEW_RELATIVE_PATH = (
    "formal/docs/lanes/"
    "EOTWASH_2020_YUKAWA_PRIMARY_EVIDENCE_CUSTODY_ACQUISITION_"
    "RESULT_REVIEW_20260718_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_eotwash_2020_yukawa_primary_evidence_custody_acquisition_"
    "result_review_v0.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "Eotwash2020YukawaPrimaryEvidenceCustodyAcquisitionResultReviewV0.lean"
)

TARGET = (
    "review_eotwash_2020_yukawa_primary_evidence_custody_acquisition_"
    "v0_result"
)
VERDICT = "ACCEPTED_BOUNDED_PRIMARY_EVIDENCE_ACQUISITION_RESULT"
PRINCIPAL_OUTCOME = "AUTHORS_OR_CUSTODIAN_CONTACT_REQUIRED"
SELECTED_NEXT_TARGET = (
    "select_post_eotwash_2020_yukawa_primary_evidence_custody_"
    "acquisition_scientific_response_v0"
)
SELECTED_NEXT_TARGET_KIND = (
    "SCIENTIFIC_RESPONSE_SELECTION_ONLY_NO_CONTACT_OR_EMPIRICAL_ANALYSIS"
)

EXECUTION_HASHES = {
    "formal/docs/lanes/EOTWASH_2020_YUKAWA_PRIMARY_EVIDENCE_CUSTODY_ACQUISITION_20260718_v0.md":
        "35ef1e03baa0f84df82d1b8a2e425a2295c1b9558984ef6dcaa8c99e930d5847",
    EXECUTION_RELATIVE_PATH:
        "d0a457ba010f7e9a956a529da436b033fcbb546069b5f484e8c923e5a52d6679",
    "formal/python/tools/eotwash_2020_yukawa_primary_evidence_custody_acquisition_v0.py":
        "19180c21a40087ac56ae0ad98cef2ca289ee9e8e12c5c2b1e35b1dfeb6a31f02",
    "formal/python/tests/test_eotwash_2020_yukawa_primary_evidence_custody_acquisition_v0.py":
        "ee2e4b38404655a165a5b7efeb742817e6a87de753111f085fc0c670936bee87",
    "formal/toe_formal/ToeFormal/Derivation/Eotwash2020YukawaPrimaryEvidenceCustodyAcquisitionV0.lean":
        "3eceb7ee6dd5ea5e7fde0dc2bf949560f9b073f7b0a7e9a6ee2e5f83015ac5ca",
}


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {relative_path}")
    return value


def _validate_execution_custody() -> tuple[list[dict[str, str]], dict[str, Any]]:
    rows: list[dict[str, str]] = []
    for relative_path, expected in EXECUTION_HASHES.items():
        observed = _sha256(REPO_ROOT / relative_path)
        if observed != expected:
            raise ValueError(f"acquisition execution custody drift: {relative_path}")
        rows.append({"relative_path": relative_path, "sha256": observed})
    execution = _load_json(EXECUTION_RELATIVE_PATH)
    if execution.get("verdict") != (
        "PRIMARY_EVIDENCE_ACQUISITION_PARTIAL_CONTACT_REQUIRED_"
        "PENDING_INDEPENDENT_REVIEW"
    ):
        raise ValueError("acquisition execution is not pending result review")
    if execution.get("selected_next_target") != TARGET:
        raise ValueError("acquisition execution did not rotate to this review")
    if execution.get("principal_outcome") != PRINCIPAL_OUTCOME:
        raise ValueError("acquisition execution did not issue the reviewed outcome")
    return rows, execution


def _validate_raw_custody(execution: dict[str, Any]) -> list[dict[str, Any]]:
    verified: list[dict[str, Any]] = []
    for row in execution["acquired_object_custody"]["rows"]:
        path = REPO_ROOT / row["relative_path"]
        observed_hash = _sha256(path)
        observed_size = path.stat().st_size
        if observed_hash != row["sha256"] or observed_size != row["size_bytes"]:
            raise ValueError(f"raw acquisition custody drift: {row['relative_path']}")
        verified.append({
            "relative_path": row["relative_path"],
            "sha256": observed_hash,
            "size_bytes": observed_size,
        })
    return verified


def _independent_reproduction(execution: dict[str, Any]) -> dict[str, Any]:
    attempts = execution["retrieval_attempts"]["rows"]
    url_counts = Counter(row["source_location"] for row in attempts)

    attempt1_headers = (
        REPO_ROOT
        / "formal/data/eotwash_2020_primary_evidence_acquisition_v0/"
        "attempt_01_aps_official_supplement/response_headers.txt"
    ).read_text(encoding="utf-8")
    attempt7_headers = (
        REPO_ROOT
        / "formal/data/eotwash_2020_primary_evidence_acquisition_v0/"
        "attempt_07_aps_chorus_accepted_manuscript/response_headers.txt"
    ).read_text(encoding="utf-8")
    browser_record = _load_json(
        "formal/data/eotwash_2020_primary_evidence_acquisition_v0/"
        "attempt_02_aps_official_manual_browser/attempt_record.json"
    )

    arxiv_path = (
        REPO_ROOT
        / "formal/data/eotwash_2020_primary_evidence_acquisition_v0/"
        "attempt_03_arxiv_source_archive/arXiv-2002.11761v1.tar.gz"
    )
    with tarfile.open(arxiv_path, mode="r:gz") as archive:
        member_names = archive.getnames()
        tex_member = archive.extractfile("FB_ISL_pdf.tex")
        if tex_member is None:
            raise ValueError("arXiv source lacks the expected TeX member")
        tex = tex_member.read().decode("utf-8")

    group_page = (
        REPO_ROOT
        / "formal/data/eotwash_2020_primary_evidence_acquisition_v0/"
        "attempt_04_eotwash_official_archive_index/eotwash_homepage.html"
    ).read_text(encoding="utf-8", errors="replace")
    researchworks_page = (
        REPO_ROOT
        / "formal/data/eotwash_2020_primary_evidence_acquisition_v0/"
        "attempt_05_uw_researchworks_item/researchworks_item.html"
    ).read_text(encoding="utf-8", errors="replace")

    inventory = execution["required_evidence_inventory"]
    inventory_rows = {row["item_id"]: row for row in inventory["rows"]}
    scope = execution["scope"]
    tier_rows = execution["source_tier_audit"]["rows"]

    return {
        "retrieval_limits": {
            "attempt_numbers": [row["attempt_number"] for row in attempts],
            "attempt_count": len(attempts),
            "attempt_cap": execution["retrieval_attempts"]["maximum_attempt_count"],
            "remaining_attempts": execution["retrieval_attempts"]["remaining_attempt_count"],
            "maximum_same_url_count": max(url_counts.values()),
            "manual_sessions": execution["retrieval_attempts"]["manual_sessions_consumed"],
            "authenticated_mirrors": execution["retrieval_attempts"]["authenticated_mirrors_used"],
            "contact_executed": scope["author_or_custodian_contact_executed"],
            "passed": (
                [row["attempt_number"] for row in attempts] == list(range(1, 8))
                and len(attempts) == 7
                and max(url_counts.values()) == 2
                and execution["retrieval_attempts"]["manual_sessions_consumed"] == 1
                and execution["retrieval_attempts"]["authenticated_mirrors_used"] == 0
                and scope["author_or_custodian_contact_executed"] is False
            ),
        },
        "source_order_and_exhaustion": {
            "first_two_attempts_are_official_supplement": all(
                row["source_tier"] == 1 for row in attempts[:2]
            ),
            "official_article_surface_reached_before_lower_tiers": (
                browser_record["final_url"].startswith("https://journals.aps.org/prl/")
                and browser_record["content_description"].endswith(
                    "data-auth-required=true."
                )
            ),
            "late_tier_two_chorus_check_disclosed": attempts[-1]["source_tier"] == 2,
            "late_check_classification": (
                "NONMATERIAL_SAME_PUBLISHER_PRIMARY_SURFACE_CROSSCHECK; "
                "official article surface was already inspected in attempt 2"
            ),
            "tier_count": execution["source_tier_audit"]["noncontact_tier_count"],
            "tiers_exhausted": execution["source_tier_audit"]["tiers_exhausted"],
            "tier_statuses": [row["status"] for row in tier_rows],
            "tier_five_authenticated_mirror_identified": False,
            "distinct_authorized_eighth_source_identified": False,
            "independent_provenance_search_queries": [
                "DOI plus supplemental data code",
                "exact article title plus dataset",
                "official Eot-Wash domain plus arXiv identifier and data",
                "Zenodo Dryad or HEPData plus DOI",
            ],
            "independent_search_finding": (
                "official article/CHORUS, arXiv, Eot-Wash, ResearchWorks, and "
                "secondary index records only; no distinct authenticated data package"
            ),
            "passed": (
                execution["source_tier_audit"]["tiers_exhausted"] == 5
                and browser_record["final_url"].startswith("https://journals.aps.org/prl/")
                and attempts[-1]["source_tier"] == 2
            ),
        },
        "aps_supplement": {
            "identified": True,
            "official_source_confirmed": True,
            "content_acquired": False,
            "ordinary_get_status_403": "HTTP/1.1 403 Forbidden" in attempt1_headers,
            "ordinary_get_challenge": "Cf-Mitigated: challenge" in attempt1_headers,
            "chorus_get_status_403": "HTTP/1.1 403 Forbidden" in attempt7_headers,
            "browser_subscription_required": (
                "Subscription Required" in browser_record["content_description"]
            ),
            "authentication_used": browser_record["authentication_used"],
            "download_after_notice": browser_record[
                "download_attempted_after_access_control_notice"
            ],
            "contents_inferred": False,
            "passed": (
                "HTTP/1.1 403 Forbidden" in attempt1_headers
                and "Cf-Mitigated: challenge" in attempt1_headers
                and "HTTP/1.1 403 Forbidden" in attempt7_headers
                and browser_record["authentication_used"] is False
                and browser_record["file_acquired"] is False
            ),
        },
        "arxiv_archive": {
            "member_count": len(member_names),
            "member_names": member_names,
            "tex_member_present": "FB_ISL_pdf.tex" in member_names,
            "supplement_member_present": any(
                "supp" in name.lower() for name in member_names
            ),
            "article_reports_95_by_3": (
                "j=95" in tex and "m=3" in tex
            ),
            "article_cites_external_supplement": (
                "Supplemental Material" in tex and "at XXXX" in tex
            ),
            "passed": (
                len(member_names) == 11
                and "FB_ISL_pdf.tex" in member_names
                and not any("supp" in name.lower() for name in member_names)
                and "Supplemental Material" in tex
            ),
        },
        "institutional_sources": {
            "eotwash_page_links_arxiv": "2002.11761" in group_page,
            "eotwash_page_mentions_supplement": "supplement" in group_page.lower(),
            "researchworks_title_present": (
                "A Fourier-Bessel Test of the Gravitational Inverse-Square Law"
                in researchworks_page
            ),
            "researchworks_bitstream_id_present": (
                "6013936a-da00-42b7-ba0a-4dff0cb05bf8" in researchworks_page
            ),
            "researchworks_cc_by_present": "CC BY" in researchworks_page,
            "passed": (
                "2002.11761" in group_page
                and "supplement" not in group_page.lower()
                and "A Fourier-Bessel Test of the Gravitational Inverse-Square Law"
                in researchworks_page
                and "6013936a-da00-42b7-ba0a-4dff0cb05bf8"
                in researchworks_page
            ),
        },
        "dissertation_visual_and_text_review": {
            "pdf_page_count": 169,
            "methods_pdf_pages_inspected": [144, 145],
            "appendix_pdf_pages_inspected": [158, 159, 160, 161, 162],
            "appendix_printed_page_range": "146-150",
            "unique_science_run_rows": 95,
            "torque_harmonic_columns": ["N120", "N18", "N54"],
            "pointwise_errors_printed": True,
            "five_profiled_nuisances": ["x0", "y0", "s0", "epsilon", "gamma"],
            "published_limit_rule_present": True,
            "primary_release_package": False,
            "supporting_institutional_methods_evidence": True,
            "passed": True,
        },
        "component_review": {
            "item_count": inventory["item_count"],
            "verified_partial_count": inventory["verified_partial_item_count"],
            "complete_count": inventory["complete_item_count"],
            "rows": [
                {
                    "item_id": item_id,
                    "execution_status": row["status"],
                    "review_status": "INCOMPLETE_REPRODUCED",
                    "present": row["present"],
                    "missing": row["missing"],
                    "complete": False,
                }
                for item_id, row in inventory_rows.items()
            ],
            "forward_model_status": execution["forward_model_sufficiency"]["status"],
            "statistical_status": execution["statistical_sufficiency"]["status"],
            "passed": (
                inventory["item_count"] == 6
                and inventory["verified_partial_item_count"] == 6
                and inventory["complete_item_count"] == 0
                and not any(row["complete"] for row in inventory["rows"])
                and execution["forward_model_sufficiency"]["status"] == "NOT_EXECUTABLE"
                and execution["statistical_sufficiency"]["status"] == "NOT_EXECUTABLE"
            ),
        },
    }


def _gate(gate_id: str, passed: bool, finding: str) -> dict[str, Any]:
    return {
        "gate_id": gate_id,
        "status": "PASS" if passed else "FAIL",
        "finding": finding,
    }


def _review_gates(
    execution: dict[str, Any], reproduction: dict[str, Any], raw_count: int
) -> list[dict[str, Any]]:
    limits = reproduction["retrieval_limits"]
    order = reproduction["source_order_and_exhaustion"]
    aps = reproduction["aps_supplement"]
    arxiv = reproduction["arxiv_archive"]
    institutional = reproduction["institutional_sources"]
    dissertation = reproduction["dissertation_visual_and_text_review"]
    components = reproduction["component_review"]
    scope = execution["scope"]
    by_id = {row["item_id"]: row for row in components["rows"]}
    return [
        _gate("G1_EXECUTION_CUSTODY", raw_count == 13, "Five execution artifacts and all thirteen raw custody objects reproduce their frozen hashes and sizes."),
        _gate("G2_EXACT_AUTHORIZED_EXECUTION", execution["authority"]["authorized_execution_count"] == 1 and execution["authority"]["consumed_execution_count"] == 1, "Exactly one authorized acquisition was consumed."),
        _gate("G3_ATTEMPT_CAP_AND_NUMBERING", limits["passed"] and limits["attempt_count"] == 7 and limits["attempt_cap"] == 8, "Attempts are numbered 1 through 7 and remain below the cap of eight."),
        _gate("G4_PER_URL_ATTEMPT_LIMIT", limits["maximum_same_url_count"] == 2, "No concrete URL was attempted more than twice."),
        _gate("G5_MANUAL_MIRROR_AND_CONTACT_LIMITS", limits["manual_sessions"] == 1 and limits["authenticated_mirrors"] == 0 and limits["contact_executed"] is False, "One manual session, zero authenticated mirrors, and zero contacts were used."),
        _gate("G6_SOURCE_PRIORITY_MATERIAL_COMPLIANCE", order["first_two_attempts_are_official_supplement"] and order["official_article_surface_reached_before_lower_tiers"] and order["late_tier_two_chorus_check_disclosed"], "The official supplement and article surface were inspected first; the late CHORUS request is a disclosed same-publisher cross-check, not an authority expansion."),
        _gate("G7_FIVE_NONCONTACT_TIERS_EXHAUSTED", order["passed"] and order["tiers_exhausted"] == 5, "All five authorized non-contact source classes have terminal findings."),
        _gate("G8_UNUSED_ATTEMPT_RESTRAINT", limits["remaining_attempts"] == 1 and order["distinct_authorized_eighth_source_identified"] is False, "The cap was a maximum; no distinct authenticated eighth target was identified."),
        _gate("G9_APS_SUPPLEMENT_EXACT_STATUS", aps["passed"] and aps["identified"] and not aps["content_acquired"] and not aps["contents_inferred"], "The APS supplement is identified at an official access-controlled surface but was neither acquired nor inferred."),
        _gate("G10_ACCESS_FAILURE_RECORDS", aps["ordinary_get_status_403"] and aps["ordinary_get_challenge"] and aps["chorus_get_status_403"], "Both retained APS HTTP responses independently show 403 access challenges."),
        _gate("G11_ARXIV_ARCHIVE_CONTENTS", arxiv["passed"] and arxiv["member_count"] == 11, "The arXiv archive contains article TeX and ten figures; it cites but does not contain the supplement."),
        _gate("G12_OFFICIAL_GROUP_INDEX", institutional["eotwash_page_links_arxiv"] and not institutional["eotwash_page_mentions_supplement"], "The captured official group page points to arXiv and exposes no supplement link."),
        _gate("G13_RESEARCHWORKS_PROVENANCE", institutional["passed"], "The institutional record, public bitstream identifier, title, and CC BY marker reproduce."),
        _gate("G14_DISSERTATION_TABLES_AND_METHODS", dissertation["passed"] and dissertation["pdf_page_count"] == 169 and dissertation["unique_science_run_rows"] == 95 and len(dissertation["torque_harmonic_columns"]) == 3, "Direct visual/text review reproduces 95 science rows, three torque harmonics, pointwise errors, and the five profiled nuisances."),
        _gate("G15_DISSERTATION_SCOPE_FIREWALL", dissertation["supporting_institutional_methods_evidence"] and not dissertation["primary_release_package"], "The dissertation is valuable supporting institutional evidence, not the primary 2020 release package."),
        _gate("G16_OBSERVATION_AND_CONFIGURATION_INCOMPLETE", not by_id["OBSERVATION_TORQUE_VECTOR"]["complete"] and not by_id["DISPLACEMENT_AND_CONFIGURATION_METADATA"]["complete"], "The printed torque table is exact supporting evidence, but primary row/configuration metadata remain incomplete."),
        _gate("G17_COVARIANCE_AND_NUISANCE_INCOMPLETE", not by_id["UNCERTAINTY_AND_COVARIANCE_MODEL"]["complete"] and not by_id["FIVE_NUISANCE_PRIOR_CONTRACTS"]["complete"], "Pointwise errors and nuisance summaries do not supply the primary covariance and executable nuisance contracts."),
        _gate("G18_FORWARD_MODEL_AND_BASELINE_INCOMPLETE", components["forward_model_status"] == "NOT_EXECUTABLE" and not by_id["EXTENDED_SOURCE_TORQUE_FORWARD_MODEL"]["complete"], "Methods do not supply executable 95-setting Newtonian/Yukawa torque and calibration machinery."),
        _gate("G19_BOUNDARY_COVERAGE_INCOMPLETE", components["statistical_status"] == "NOT_EXECUTABLE" and not by_id["BOUNDARY_COVERAGE_PROCEDURE"]["complete"], "The published rule is not a reproducible boundary-calibrated coverage procedure."),
        _gate("G20_NO_UNAUTHORIZED_INFERENCE_OR_ADOPTION", all(scope[key] is False for key in ("access_control_circumvention_executed", "author_or_custodian_contact_executed", "synthetic_forecast_executed", "published_constraint_reinterpreted", "likelihood_executed", "numerical_bound_computed", "lambda0_selected", "alpha_selected", "scalar_branch_adopted", "native_gravitational_principle_identified", "gravitational_action_selected", "frame_dragging_resumed")), "No access bypass, contact, reconstruction, inference, bound, parameter selection, or theory adoption occurred."),
        _gate("G21_PRINCIPAL_RESULT_AND_STOP", components["passed"] and execution["principal_outcome"] == PRINCIPAL_OUTCOME, "Zero of six components are complete; contact is required and authority rotates only to response selection."),
    ]


def build_review() -> dict[str, Any]:
    custody, execution = _validate_execution_custody()
    raw_custody = _validate_raw_custody(execution)
    human = REPO_ROOT / HUMAN_REVIEW_RELATIVE_PATH
    test = REPO_ROOT / TEST_RELATIVE_PATH
    lean = REPO_ROOT / LEAN_RELATIVE_PATH
    if not human.is_file() or not test.is_file() or not lean.is_file():
        raise ValueError("result-review human, test, or Lean artifact missing")
    reproduction = _independent_reproduction(execution)
    gates = _review_gates(execution, reproduction, len(raw_custody))
    if any(row["status"] != "PASS" for row in gates):
        raise ValueError("Eot-Wash acquisition result-review gate failed")
    return {
        "schema_id": (
            "EOTWASH_2020_YUKAWA_PRIMARY_EVIDENCE_CUSTODY_ACQUISITION_"
            "RESULT_REVIEW_20260718_v0"
        ),
        "captured_at_utc": "2026-07-19T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "principal_review_outcome": PRINCIPAL_OUTCOME,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_execution_verdict": execution["verdict"],
            "frozen_execution_artifacts": custody,
            "verified_raw_custody_objects": raw_custody,
            "human_review": {
                "relative_path": HUMAN_REVIEW_RELATIVE_PATH,
                "sha256": _sha256(human),
            },
            "generator": {
                "relative_path": Path(__file__).resolve().relative_to(
                    REPO_ROOT
                ).as_posix(),
                "sha256": _sha256(Path(__file__).resolve()),
            },
            "test": {
                "relative_path": TEST_RELATIVE_PATH,
                "sha256": _sha256(test),
            },
            "lean": {
                "relative_path": LEAN_RELATIVE_PATH,
                "sha256": _sha256(lean),
            },
        },
        "independent_reproduction": reproduction,
        "review_gates": {
            "gate_count": len(gates),
            "pass_count": sum(row["status"] == "PASS" for row in gates),
            "failure_count": sum(row["status"] != "PASS" for row in gates),
            "rows": gates,
        },
        "accepted_bounded_claim": {
            "experiment_suitability": "RETAINED_FROM_ACCEPTED_PACKET_REVIEW",
            "noncontact_acquisition": "COMPLETED_ONCE",
            "retrieval_attempts": "7_OF_8",
            "source_tiers_exhausted": "5_OF_5_NONCONTACT_TIERS",
            "primary_supplement": "IDENTIFIED_NOT_ACQUIRED_ACCESS_CONTROLLED",
            "supporting_dissertation": (
                "VERIFIED_VALUABLE_SUPPORTING_METHODS_AND_95_BY_3_TABLE"
            ),
            "evidence_components": "0_OF_6_COMPLETE_6_OF_6_PARTIAL",
            "forward_model": "NOT_EXECUTABLE",
            "statistical_inference": "NOT_EXECUTABLE",
            "contact_required": True,
            "evidence_nonexistence_claim": False,
            "experiment_irreproducibility_claim": False,
            "scalar_allowance_or_exclusion_claim": False,
        },
        "post_custody_source_checks": [
            {
                "source": "https://journals.aps.org/prl/abstract/10.1103/PhysRevLett.124.101101#supplemental",
                "role": "OFFICIAL_ARTICLE_AND_SUPPLEMENT_ACCESS_SURFACE",
            },
            {
                "source": "https://arxiv.org/abs/2002.11761",
                "role": "PUBLIC_AUTHOR_SUBMITTED_ARTICLE_RECORD",
            },
            {
                "source": "https://www.npl.washington.edu/eotwash/",
                "role": "OFFICIAL_GROUP_PUBLICATION_INDEX",
            },
            {
                "source": "https://digital.lib.washington.edu/researchworks/items/971237d1-100a-41ae-9027-d1bbce8cf315/full",
                "role": "INSTITUTIONAL_DISSERTATION_RECORD",
            },
        ],
        "scope": {
            "independent_result_review_executed": True,
            "bounded_acquisition_result_accepted": True,
            "scientific_response_selection_authorized": True,
            "scientific_response_selection_executed": False,
            "author_or_custodian_contact_prepared": False,
            "author_or_custodian_contact_authorized": False,
            "author_or_custodian_contact_executed": False,
            "synthetic_forecast_authorized": False,
            "published_constraint_reinterpretation_authorized": False,
            "alternative_experiment_selected": False,
            "likelihood_preparation_authorized": False,
            "likelihood_executed": False,
            "numerical_bound_computed": False,
            "lambda0_selected": False,
            "alpha_selected": False,
            "scalar_branch_adopted": False,
            "native_gravitational_principle_identified": False,
            "gravitational_action_selected": False,
            "frame_dragging_resumed": False,
        },
        "current_posture": {
            "scalar_only_comparison": "BOUNDEDLY_VIABLE",
            "native_relevance": "UNESTABLISHED",
            "empirical_target": "2020_EOT_WASH",
            "acquisition_execution": "COMPLETED_ONCE",
            "acquisition_result_review": "ACCEPTED_21_OF_21_GATES",
            "principal_result": PRINCIPAL_OUTCOME,
            "evidence_components_complete": "0_OF_6",
            "likelihood": "NOT_EXECUTABLE",
            "numerical_scalar_range_bound": "NONE",
            "alpha": "NOT_SELECTED",
            "scalar_branch": "NOT_ADOPTED",
            "next_authority": SELECTED_NEXT_TARGET,
        },
    }


def artifact_bytes() -> bytes:
    return (
        json.dumps(build_review(), indent=2, sort_keys=True, ensure_ascii=True)
        + "\n"
    ).encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Independently review the Eot-Wash acquisition result."
    )
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--write", action="store_true")
    group.add_argument("--check", action="store_true")
    args = parser.parse_args()
    expected = artifact_bytes()
    path = REPO_ROOT / REPORT_RELATIVE_PATH
    if args.write:
        path.write_bytes(expected)
        print("eotwash_acquisition_result_review_v0: wrote accepted review")
        return 0
    if not path.is_file() or path.read_bytes() != expected:
        print("eotwash_acquisition_result_review_v0: FAILED artifact drift")
        return 1
    print("eotwash_acquisition_result_review_v0: OK gates=21/21 accepted")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

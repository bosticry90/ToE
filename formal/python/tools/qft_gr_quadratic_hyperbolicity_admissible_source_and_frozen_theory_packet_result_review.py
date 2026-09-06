from __future__ import annotations

import hashlib
import subprocess

from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    CAPTURED_AT_UTC,
    REPO_ROOT,
    read_json,
    sha256_path,
    write_or_check,
)


PACKET_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_HYPERBOLICITY_ADMISSIBLE_SOURCE_AND_"
    "FROZEN_THEORY_PACKET_20260728_v0.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_HYPERBOLICITY_ADMISSIBLE_SOURCE_AND_"
    "FROZEN_THEORY_PACKET_RESULT_REVIEW_20260728_v0.json"
)
EXPECTED_CURRENT_TARGET = (
    "prepare_qft_gr_quadratic_hyperbolicity_admissible_source_"
    "and_frozen_theory_packet_v0"
)
EXPECTED_NEXT_TARGET = "derive_qft_gr_quadratic_physical_spin2_principal_block_v0"
EXPECTED_BLOB = "4351a53e0a582f5ccdd23d6aa80ee5372bda9e6f"
EXPECTED_BLOB_SIZE = 5818
EXPECTED_BLOB_SHA256 = (
    "2a3a3af211ab2c82ceb72e0c8505d3558954d1e14a5d187180b59250b637fb16"
)


def _independent_blob_identity() -> tuple[int, str]:
    blob = subprocess.run(
        ["git", "cat-file", "blob", EXPECTED_BLOB],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
    ).stdout
    return len(blob), hashlib.sha256(blob).hexdigest()


def build_review() -> dict:
    packet = read_json(PACKET_PATH)
    sources = {row["source_id"]: row for row in packet["admissible_primary_sources"]}
    blob_size, blob_sha256 = _independent_blob_identity()
    domains = packet["frozen_theory"]["coefficient_domains"]
    checks = {
        "packet_target_matches_authority": (
            packet["preparation_target"] == EXPECTED_CURRENT_TARGET
        ),
        "bounded_replay_record_is_bound": (
            packet["consumed_selection_review"]["selected_route"]
            == "BOUNDED_RECONCILIATION_OR_REPLAY"
            and len(packet["consumed_selection_review"]["sha256"]) == 64
        ),
        "current_no_go_source_is_primary": (
            sources["ARXIV_2607_11879_V1"]["role"]
            == "PRIMARY_CURRENT_PHYSICAL_PRINCIPAL_BLOCK_REFERENCE"
        ),
        "older_results_are_bounded_comparators": (
            sources["ARXIV_1811_07869_V4"]["role"]
            == "HISTORICAL_SMOOTH_EXISTENCE_COMPARATOR"
            and "Proposition 9 continuous-dependence statement"
            in sources["ARXIV_1811_07869_V4"]["claim_boundary"]
            and sources["NOAKES_1983_JMP_24_1846"]["role"]
            == "HISTORICAL_HARMONIC_REDUCTION_COMPARATOR"
        ),
        "regularized_formulation_is_excluded_comparator": (
            sources["ARXIV_2407_08775_V1"]["role"]
            == "EXCLUDED_REGULARIZED_FORMULATION_COMPARATOR"
        ),
        "preserved_candidate_is_byte_bound_and_not_adopted": (
            packet["preserved_candidate_input"]["git_blob_oid"] == EXPECTED_BLOB
            and packet["preserved_candidate_input"]["byte_size"] == blob_size
            == EXPECTED_BLOB_SIZE
            and packet["preserved_candidate_input"]["sha256"] == blob_sha256
            == EXPECTED_BLOB_SHA256
            and packet["preserved_candidate_input"][
                "scientific_authority_conferred"
            ]
            is False
        ),
        "coefficient_strata_are_separated": (
            domains["G_principal"] == ["beta != 0", "3 alpha + beta != 0"]
            and domains["G_Stelle"]
            == ["beta != 0", "3 alpha + beta != 0", "c_R != 0"]
            and domains["spin2_obstruction_minimal_domain"] == ["beta != 0"]
        ),
        "coefficient_mapping_tracks_spin2_beta": (
            packet["frozen_theory"][
                "coefficient_mapping_to_arxiv_2607_11879"
            ]["paper_alpha0"].startswith("ToE beta")
        ),
        "vacuum_phase_a_is_frozen": (
            packet["source_scope"]["phase_a"] == "VACUUM"
            and packet["phase_a_authorized_calculation"]["target"]
            == EXPECTED_NEXT_TARGET
        ),
        "phase_b_c_and_sources_are_not_yet_authorized": (
            "Nonlinear auxiliary/harmonic formulation execution."
            in packet["not_yet_authorized"]
            and "Adapted derivative-loss energy estimate execution."
            in packet["not_yet_authorized"]
            and "Source extension." in packet["not_yet_authorized"]
        ),
        "prohibitions_preserve_unregularized_problem": (
            "No perturbative order reduction presented as the frozen theory."
            in packet["prohibitions"]
            and "No fiducial massive mode used to claim unregularized hyperbolicity."
            in packet["prohibitions"]
            and "No Yukawa execution or rerun." in packet["prohibitions"]
        ),
    }
    failed = [name for name, passed in checks.items() if not passed]
    accepted = not failed
    return {
        "schema_id": (
            "QFT_GR_QUADRATIC_HYPERBOLICITY_ADMISSIBLE_SOURCE_AND_"
            "FROZEN_THEORY_PACKET_RESULT_REVIEW_20260728_v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "review_target": (
            "review_qft_gr_quadratic_hyperbolicity_admissible_source_"
            "and_frozen_theory_packet_v0_result"
        ),
        "reviewed_packet": {
            "path": PACKET_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(PACKET_PATH),
        },
        "checks": checks,
        "failed_checks": failed,
        "accepted": accepted,
        "reviewer_independence": {
            "imports_packet_generator": False,
            "recomputes_preserved_blob_hash": True,
            "rechecks_source_roles_and_claim_boundaries": True,
            "rechecks_domains_and_coefficient_mapping": True,
        },
        "authority_rotation": {
            "physical_principal_block_execution_authorized": accepted,
            "auxiliary_harmonic_formulation_execution_authorized": False,
            "adapted_norm_estimate_execution_authorized": False,
            "source_extension_authorized": False,
            "preserved_descendant_adoption_authorized": False,
            "yukawa_work_authorized": False,
        },
        "selected_next_target": (
            EXPECTED_NEXT_TARGET
            if accepted
            else "prepare_qft_gr_quadratic_hyperbolicity_source_packet_correction_v0"
        ),
        "verdict": (
            "ACCEPT_FROZEN_VACUUM_THEORY_AUTHORIZE_PHASE_A_ONLY"
            if accepted
            else "B_BLOCKED_FROZEN_THEORY_PACKET_REQUIRES_CORRECTION"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_review,
        description=(
            "quadratic hyperbolicity admissible-source and frozen-theory "
            "packet result review"
        ),
    )


if __name__ == "__main__":
    raise SystemExit(main())

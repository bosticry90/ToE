from __future__ import annotations

from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    REPO_ROOT,
    QuadraticHyperbolicityError,
    read_json,
    sha256_path,
    write_or_check,
)


CAPTURED_AT_UTC = "2026-07-29T00:00:00Z"
RESULT_PATH = REPO_ROOT / (
    "formal/output/CALC-TOE-NATIVE-COHERENCE-REPRESENTATION-v0.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "TOE_NATIVE_COHERENCE_REPRESENTATION_V0_RESULT_REVIEW_20260729_v0.json"
)


def build_review() -> dict:
    result = read_json(RESULT_PATH)
    representation = result["representation_assessment"]
    chi = result["chi_semantics"]
    phi = result["phi_semantics"]
    boundary = result["claim_boundary"]
    checks = {
        "open_event_bound": (
            result["attempt_sequence_number"] == 1
            and len(result["open_event_hash"]) == 64
        ),
        "all_evidence_checks_pass": all(result["evidence_checks"].values()),
        "candidate_layer_not_promoted": (
            representation["real_scalar_crosswalk_found"] is False
            and representation["relativistic_covariant_crosswalk_found"] is False
        ),
        "amplitude_surrogate_not_manufactured": (
            representation["bounded_amplitude_surrogate_possible_in_principle"]
            is True
            and representation[
                "bounded_amplitude_surrogate_authorized_by_preserved_result"
            ]
            is False
        ),
        "chi_semantics_unresolved": (
            chi["chi_symmetry_status"] == "BLOCKED_COHERENCE_Z2_UNJUSTIFIED"
        ),
        "phi_Z2_unjustified": (
            phi["phi_symmetry_status"]
            == "BLOCKED_TEST_MATTER_SYMMETRY_UNJUSTIFIED"
        ),
        "no_action_or_portal_authorized": (
            boundary["native_action_selected"] is False
            and boundary["portal_interaction_authorized"] is False
            and boundary["stage_2_authorized"] is False
        ),
        "failed_closed_without_CCFT_rejection": (
            result["terminal_result"] == "BLOCKED"
            and result["terminal_outcome"]
            == "BLOCKED_CCFT_TO_CONTINUUM_MAP_UNRESOLVED"
            and boundary["ccft_validated"] is False
        ),
        "v0_discriminator_closes_negative": (
            result["v0_discriminator_result"]
            == "NO_UNIQUE_TOE_DISCRIMINATOR_V0"
        ),
    }
    failed = sorted(name for name, passed in checks.items() if not passed)
    if failed:
        raise QuadraticHyperbolicityError(
            f"native coherence representation review failed: {failed}"
        )
    return {
        "schema_id": (
            "TOE_NATIVE_COHERENCE_REPRESENTATION_V0_RESULT_REVIEW_20260729_v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "reviewed_result": {
            "path": RESULT_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(RESULT_PATH),
        },
        "checks": checks,
        "failed_checks": failed,
        "accepted": True,
        "terminal_result": "BLOCKED",
        "terminal_outcome": "BLOCKED_CCFT_TO_CONTINUUM_MAP_UNRESOLVED",
        "representation_outcome": "BLOCKED_CCFT_TO_CONTINUUM_MAP_UNRESOLVED",
        "phi_symmetry_status": "BLOCKED_TEST_MATTER_SYMMETRY_UNJUSTIFIED",
        "chi_symmetry_status": "BLOCKED_COHERENCE_Z2_UNJUSTIFIED",
        "program_v0_closes": True,
        "stage_2_authorized": False,
        "repair_authorized": False,
        "v0_discriminator_result": "NO_UNIQUE_TOE_DISCRIMINATOR_V0",
        "mandatory_exit_target": (
            "close_toe_native_surrogate_v0_after_bounded_result_v0"
        ),
        "verdict": (
            "ACCEPT_BLOCKED_CCFT_TO_CONTINUUM_MAP_UNRESOLVED_CLOSE_NATIVE_"
            "SURROGATE_V0_WITH_NO_UNIQUE_DISCRIMINATOR"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_review,
        description="ToE native coherence representation result review",
    )


if __name__ == "__main__":
    raise SystemExit(main())

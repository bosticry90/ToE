from __future__ import annotations

from formal.python.tools.bounded_program_governance import (
    NATIVE_PROGRAM_ID,
    PROGRAMS_KEY,
)
from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    REPO_ROOT,
    QuadraticHyperbolicityError,
    read_json,
    sha256_path,
    write_or_check,
)


CAPTURED_AT_UTC = "2026-07-29T00:00:00Z"
EXECUTION_TARGET = "select_toe_native_coherence_representation_v0"
OPEN_EVENT_HASH = (
    "dc3749545909da0f587e0931632d472ec518eb1cb2e2652b0fcd1a3cbf6e4429"
)
REGISTRY_PATH = REPO_ROOT / "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"
OUTPUT_PATH = REPO_ROOT / (
    "formal/output/CALC-TOE-NATIVE-COHERENCE-REPRESENTATION-v0.json"
)

EVIDENCE_PATHS = {
    "candidate_layer_review": REPO_ROOT
    / "formal/toe_formal/ToeFormal/Derivation/"
    "CoherenceAdmissibilityBridgeRoadmapRebaseResultReview.lean",
    "object_crosswalk": REPO_ROOT
    / "formal/toe_formal/ToeFormal/Derivation/CCFTToTOEObjectCrosswalkPacket.lean",
    "action_program_review": REPO_ROOT
    / "formal/toe_formal/ToeFormal/Derivation/"
    "CCFTFullVariationalActionProgramPacketResultReview.lean",
    "provisional_scalar_sector": REPO_ROOT
    / "formal/toe_formal/ToeFormal/Derivation/"
    "QFTGRToeMatterSectorCandidateSelectionPacket.lean",
    "phi_policy": REPO_ROOT
    / "formal/toe_formal/ToeFormal/Derivation/"
    "ToeNativePhiSignatureDomainAndPotentialPolicyPacket.lean",
    "archived_ccft_dossier": REPO_ROOT
    / "formal/quarantine/dossiers/"
    "DOSSIER_0007_archive_docs_monograph_ccft_monograph_md.md",
    "historical_complex_field_description": REPO_ROOT
    / "formal/proving docs/Part I - Conceptual Foundations.md",
}


def build_calculation() -> dict:
    registry = read_json(REGISTRY_PATH)
    projection = registry["current_projection_v0"]
    program = registry[PROGRAMS_KEY][NATIVE_PROGRAM_ID]
    if projection["current_target"] not in {
        EXECUTION_TARGET,
        "close_toe_native_surrogate_v0_after_bounded_result_v0",
    }:
        raise QuadraticHyperbolicityError(
            "native coherence representation stage is not authoritative"
        )
    if projection["current_target"] == EXECUTION_TARGET and not (
        program["state"] == "OPEN"
        and program["open_attempt_number"] == 1
        and program["attempted_stage_ids"] == ["COHERENCE_REPRESENTATION"]
        and program["event_chain_tip_hash"] == OPEN_EVENT_HASH
    ):
        raise QuadraticHyperbolicityError(
            "native coherence representation producer lacks its OPEN event"
        )

    evidence_text = {
        name: path.read_text(encoding="utf-8")
        for name, path in EVIDENCE_PATHS.items()
    }
    checks = {
        "ccft_is_only_candidate_mesoscopic_layer": (
            "CANDIDATE_MESOSCOPIC_LINKAGE_LAYER"
            in evidence_text["candidate_layer_review"]
            and "def ccftValidated : Bool := false"
            in evidence_text["candidate_layer_review"]
        ),
        "object_crosswalk_is_mapping_only": (
            "OBJECT_SURFACE_MAPPING_ONLY_NO_CCFT_VALIDATION"
            in evidence_text["object_crosswalk"]
            and "def ccftValidated : Bool := false"
            in evidence_text["object_crosswalk"]
        ),
        "ccft_action_remains_pre_derivation": (
            "ACCEPTS_PRE_DERIVATION_PLAN_NO_CK_VARIATION_OR_CCFT_VALIDATION"
            in evidence_text["action_program_review"]
            and "def actionEmbeddingClaimed : Bool := false"
            in evidence_text["action_program_review"]
        ),
        "historical_ccft_field_is_complex": (
            "primary complex coherence field"
            in evidence_text["historical_complex_field_description"].lower()
            and "amplitude" in evidence_text["historical_complex_field_description"].lower()
            and "phase gradient"
            in evidence_text["historical_complex_field_description"].lower()
        ),
        "archived_ccft_source_is_unaccepted_candidate": (
            "Classification: doc_claim_candidate"
            in evidence_text["archived_ccft_dossier"]
            and "Accepted / Rejected / Reference-only: TBD"
            in evidence_text["archived_ccft_dossier"]
        ),
        "real_scalar_is_only_provisional_test_sector": (
            "provisional_real_scalar_field_test_sector_v0"
            in evidence_text["provisional_scalar_sector"]
            and "def toeNativeMatterSectorDefined : Bool := false"
            in evidence_text["provisional_scalar_sector"]
        ),
        "phi_potential_is_not_even_or_derived": (
            "V : R^{|I_phi|} -> R is assumed smooth and bounded below"
            in evidence_text["phi_policy"]
            and "its functional form is not ToE-derived"
            in evidence_text["phi_policy"]
            and "Z2" not in evidence_text["phi_policy"]
            and "Z_2" not in evidence_text["phi_policy"]
        ),
    }
    if not all(checks.values()):
        failed = sorted(name for name, passed in checks.items() if not passed)
        raise QuadraticHyperbolicityError(
            f"coherence representation evidence audit failed: {failed}"
        )

    evidence = {
        name: {
            "path": path.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(path),
        }
        for name, path in EVIDENCE_PATHS.items()
    }
    return {
        "schema_id": "CALC_TOE_NATIVE_COHERENCE_REPRESENTATION_v0",
        "calculation_id": "CALC-TOE-NATIVE-COHERENCE-REPRESENTATION-v0",
        "captured_at_utc": CAPTURED_AT_UTC,
        "execution_target": EXECUTION_TARGET,
        "program_id": NATIVE_PROGRAM_ID,
        "semantic_stage_id": "COHERENCE_REPRESENTATION",
        "attempt_sequence_number": 1,
        "open_event_hash": OPEN_EVENT_HASH,
        "evidence": evidence,
        "evidence_checks": checks,
        "representation_assessment": {
            "preserved_native_claim": (
                "CCFT is retained only as a candidate mesoscopic coherence "
                "linkage layer."
            ),
            "historical_candidate_structure": (
                "The archived candidate uses a complex primary field whose "
                "amplitude and phase gradient carry distinct density and "
                "transport meanings."
            ),
            "real_scalar_crosswalk_found": False,
            "relativistic_covariant_crosswalk_found": False,
            "faithful_value_sign_zero_gradient_map_found": False,
            "bounded_amplitude_surrogate_possible_in_principle": True,
            "bounded_amplitude_surrogate_authorized_by_preserved_result": False,
            "representation_outcome": "BLOCKED_CCFT_TO_CONTINUUM_MAP_UNRESOLVED",
            "reason": (
                "A real amplitude surrogate is conceivable, but the accepted "
                "repository surfaces provide only candidate/mapping-level CCFT "
                "records. They do not derive or authorize a relativistic real "
                "scalar map, and the historical complex field assigns independent "
                "meaning to amplitude and phase gradient."
            ),
        },
        "chi_semantics": {
            "value": "UNRESOLVED_REAL_SCALAR_TO_COHERENCE_MAP",
            "sign": "UNRESOLVED; complex-field amplitude is nonnegative while a real scalar is signed",
            "zero": "UNRESOLVED; cannot canonically equate zero scalar with absence of coherence",
            "gradient": "UNRESOLVED; historical transport meaning belongs to the complex phase gradient",
            "chi_symmetry_status": "BLOCKED_COHERENCE_Z2_UNJUSTIFIED",
        },
        "phi_semantics": {
            "sector_class": "PROVISIONAL_REAL_SCALAR_TEST_MATTER_SECTOR",
            "phi_symmetry_status": "BLOCKED_TEST_MATTER_SYMMETRY_UNJUSTIFIED",
            "reason": (
                "The preserved scalar policy admits a generic smooth bounded-"
                "below potential and does not select an even potential or an "
                "independent phi-to-minus-phi symmetry."
            ),
        },
        "claim_boundary": {
            "real_scalar_surrogate_accepted": False,
            "real_scalar_representation_derived": False,
            "ccft_validated": False,
            "native_action_selected": False,
            "portal_interaction_authorized": False,
            "stage_2_authorized": False,
            "full_toe_unification_claimed": False,
        },
        "terminal_result": "BLOCKED",
        "terminal_outcome": "BLOCKED_CCFT_TO_CONTINUUM_MAP_UNRESOLVED",
        "mandatory_exit_target": (
            "close_toe_native_surrogate_v0_after_bounded_result_v0"
        ),
        "v0_discriminator_result": "NO_UNIQUE_TOE_DISCRIMINATOR_V0",
        "verdict": (
            "NATIVE_SURROGATE_V0_BLOCKED_AT_COHERENCE_REPRESENTATION_"
            "NO_REPAIR_OR_STAGE_2_AUTHORIZED"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_calculation,
        description="ToE native coherence representation adjudication",
    )


if __name__ == "__main__":
    raise SystemExit(main())

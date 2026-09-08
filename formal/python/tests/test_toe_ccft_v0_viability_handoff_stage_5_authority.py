from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
RELEASE = ROOT / "formal/docs/release"
AUTHORITY = RELEASE / "TOE_CCFT_V0_INTERNAL_VIABILITY_AND_DISTINCTIVENESS_HANDOFF_STAGE_5_OPEN_AUTHORITY_v0.json"
REVIEW = RELEASE / "TOE_CCFT_V0_INTERNAL_VIABILITY_AND_DISTINCTIVENESS_HANDOFF_STAGE_5_OPEN_AUTHORITY_REVIEW_v0.json"
MANIFEST = RELEASE / "bounded_program_manifests/TOE_CCFT_V0_THEORY_CONSTRUCTION_AND_THEOREM_DISCOVERY_V0_MANIFEST_v1.json"


def read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_authority_binds_manifest_stage_five() -> None:
    authority = read(AUTHORITY)
    stage = read(MANIFEST)["stages"][4]
    assert authority["authorized_stage"]["stage_number"] == 5
    assert authority["authorized_stage"]["canonical_scope_hash"] == stage["canonical_scope_hash"]
    assert authority["authorized_stage"]["canonical_target"] == stage["canonical_target"]
    assert authority["canonical_terminal_outcomes"] == stage["mandatory_terminal_outcomes"]
    assert authority["required_outputs"] == stage["canonical_scope"]["required_outputs"]


def test_stage_four_result_is_bound_without_mutation() -> None:
    authority = read(AUTHORITY)
    binding = authority["frozen_stage_4_result_binding"]
    assert binding["gauge_equivalence"] == "PROVED"
    assert binding["unit_background_dispersion"] == "PROVED"
    assert binding["zero_background_dispersion"] == "PROVED"
    assert binding["known_model_equivalence"] == "ESTABLISHED_FOR_THE_FROZEN_V0_EQUATION"
    assert binding["CP_FREQ_001"] == "HISTORICAL_CONTEXT_INSUFFICIENT"
    assert binding["CP_FREQ_002"] == "VALID_SPECIAL_LIMITS"
    assert binding["model_mutation_authorized"] is False
    assert binding["packet_mutation_authorized"] is False


def test_exact_assessment_surfaces_are_authorized() -> None:
    authority = read(AUTHORITY)
    assert [row["surface_id"] for row in authority["authorized_assessment_surfaces"]] == [
        "MATHEMATICAL_VIABILITY",
        "GENERIC_MODEL_EQUIVALENCE",
        "C_FINITE_APPROXIMATION",
        "C_IDENTIFIABILITY",
        "C_COMPLEXITY",
        "FUTURE_ROLE_AND_HANDOFF",
    ]
    limits = authority["scientific_limits"]
    assert limits["maximum_frozen_models_assessed"] == 1
    for key in [
        "frozen_model_mutation_authorized",
        "frozen_packet_mutation_authorized",
        "new_theorem_packet_or_proof_expansion_authorized",
        "new_postulate_or_CCFT_v1_construction_authorized",
        "external_assumption_import_without_exact_alignment_authorized",
        "archive_recovery_reopening_authorized",
        "physical_bearer_units_scale_preparation_or_measurement_assignment_authorized",
        "matter_gravity_seam_or_master_action_work_authorized",
        "empirical_promotion_authorized",
        "automatic_successor_authorization",
    ]:
        assert limits[key] is False


def test_authority_contains_no_stage_five_result() -> None:
    output = read(AUTHORITY)["scientific_output_at_authority"]
    for key in [
        "mathematical_viability_status",
        "numerical_reproducibility_status",
        "C_FINITE_APPROXIMATION",
        "C_IDENTIFIABILITY",
        "C_COMPLEXITY",
        "generic_model_equivalence_audit",
    ]:
        assert output[key] == "UNADJUDICATED"
    assert output["future_role"] == "NONE_SELECTED"
    assert output["successor_program"] == "NONE_AUTHORIZED"
    assert output["physical_interpretation"] == "NONE"
    assert output["empirical_claim"] == "NONE"


def test_evidence_and_review_reproduce() -> None:
    authority = read(AUTHORITY)
    assert all(sha(ROOT / row["path"]) == row["sha256"] for row in authority["evidence_bindings"])
    review = read(REVIEW)
    assert review["authority_sha256"] == sha(AUTHORITY)
    assert review["accepted"] is True
    assert all(review["checks"].values())
    assert review["stage_5_authorized"] is True
    assert review["stage_5_open_event_created"] is False
    assert review["successor_program_authorized"] is False

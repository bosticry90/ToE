from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
RELEASE = ROOT / "formal/docs/release"
AUTHORITY = RELEASE / "TOE_CCFT_V0_PRIMARY_THEOREM_ATTACK_EXECUTION_STAGE_4_OPEN_AUTHORITY_v0.json"
REVIEW = RELEASE / "TOE_CCFT_V0_PRIMARY_THEOREM_ATTACK_EXECUTION_STAGE_4_OPEN_AUTHORITY_REVIEW_v0.json"
MANIFEST = RELEASE / "bounded_program_manifests/TOE_CCFT_V0_THEORY_CONSTRUCTION_AND_THEOREM_DISCOVERY_V0_MANIFEST_v1.json"
PACKET = RELEASE / "TOE_CCFT_V0_PRIMARY_THEOREM_PACKET_PREPARATION_RESULT_v0.json"


def read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_authority_binds_manifest_stage_four() -> None:
    authority = read(AUTHORITY)
    stage = read(MANIFEST)["stages"][3]
    assert authority["authorized_stage"]["stage_number"] == 4
    assert authority["authorized_stage"]["canonical_scope_hash"] == stage["canonical_scope_hash"]
    assert authority["authorized_stage"]["canonical_target"] == stage["canonical_target"]
    assert authority["canonical_terminal_outcomes"] == stage["mandatory_terminal_outcomes"]


def test_frozen_packet_and_model_are_bound_without_mutation() -> None:
    authority = read(AUTHORITY)
    packet = read(PACKET)
    binding = authority["frozen_packet_binding"]
    summary = packet["packet_freeze_summary"]
    assert binding["packet_id"] == packet["frozen_primary_theorem_packet"]["packet_id"]
    assert binding["linked_claim_count"] == packet["frozen_primary_theorem_packet"]["compound_claim_count"] == 4
    assert binding["formal_proposition_count"] == summary["formal_proposition_count"] == 4
    assert binding["formal_negation_count"] == summary["formal_negation_count"] == 4
    assert binding["packet_mutation_authorized"] is False
    assert authority["frozen_model_binding"]["model_mutation_authorized"] is False


def test_exact_execution_lanes_are_authorized_without_scope_expansion() -> None:
    authority = read(AUTHORITY)
    limits = authority["scientific_limits"]
    assert authority["authorized_attack_lanes"]["independent_lanes"] == [
        "PROVE",
        "DISPROVE",
        "CONSTRUCT",
        "FIND_COUNTEREXAMPLE",
    ]
    for key in [
        "proof_execution_authorized",
        "disproof_execution_authorized",
        "construction_execution_authorized",
        "counterexample_execution_authorized",
        "symbolic_contract_execution_authorized",
        "numerical_contract_execution_authorized",
        "Lean_formalization_authorized_where_faithful_and_feasible",
    ]:
        assert limits[key] is True
    for key in [
        "frozen_model_mutation_authorized",
        "frozen_packet_mutation_authorized",
        "new_postulate_authorized",
        "archive_recovery_reopening_authorized",
        "norm_energy_well_posedness_stability_or_novelty_theorem_expansion_authorized",
        "physical_interpretation_or_promotion_authorized",
        "matter_gravity_seam_or_master_action_work_authorized",
        "automatic_successor_authorization",
        "stage_5_authorized",
    ]:
        assert limits[key] is False


def test_authority_contains_no_mathematical_result() -> None:
    output = read(AUTHORITY)["scientific_output_at_authority"]
    assert output["theorems_proved"] == 0
    assert output["claims_refuted"] == 0
    assert output["counterexamples_found"] == 0
    assert output["symbolic_results"] == 0
    assert output["numerical_results"] == 0
    assert output["Lean_theorem_proofs"] == 0
    assert output["gauge_equivalence_result"] == "UNADJUDICATED"
    assert output["historical_formula_classification"] == "UNADJUDICATED"


def test_evidence_and_review_reproduce() -> None:
    authority = read(AUTHORITY)
    assert all(sha(ROOT / row["path"]) == row["sha256"] for row in authority["evidence_bindings"])
    review = read(REVIEW)
    assert review["authority_sha256"] == sha(AUTHORITY)
    assert review["accepted"] is True
    assert all(review["checks"].values())
    assert review["stage_4_authorized"] is True
    assert review["stage_5_authorized"] is False

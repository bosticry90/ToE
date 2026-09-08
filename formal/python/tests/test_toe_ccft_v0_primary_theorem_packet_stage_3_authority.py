from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
RELEASE = ROOT / "formal/docs/release"
AUTHORITY = RELEASE / "TOE_CCFT_V0_PRIMARY_THEOREM_PACKET_PREPARATION_STAGE_3_OPEN_AUTHORITY_v0.json"
REVIEW = RELEASE / "TOE_CCFT_V0_PRIMARY_THEOREM_PACKET_PREPARATION_STAGE_3_OPEN_AUTHORITY_REVIEW_v0.json"
MANIFEST = RELEASE / "bounded_program_manifests/TOE_CCFT_V0_THEORY_CONSTRUCTION_AND_THEOREM_DISCOVERY_V0_MANIFEST_v1.json"
MODEL = RELEASE / "TOE_CCFT_V0_MODEL_CONTRACT_COMPLETION_AND_FREEZE_RESULT_v0.json"


def read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_authority_binds_manifest_stage_three() -> None:
    authority = read(AUTHORITY)
    stage = read(MANIFEST)["stages"][2]
    assert authority["authorized_stage"]["canonical_scope_hash"] == stage["canonical_scope_hash"]
    assert authority["authorized_stage"]["canonical_target"] == stage["canonical_target"]
    assert authority["canonical_terminal_outcomes"] == stage["mandatory_terminal_outcomes"]
    assert authority["scientific_limits"]["maximum_primary_theorem_packets"] == 1


def test_frozen_model_is_bound_without_mutation() -> None:
    authority = read(AUTHORITY)
    model = read(MODEL)
    binding = authority["frozen_model_binding"]
    assert binding["model_id"] == model["immutable_model_contract"]["model_id"]
    assert binding["governing_equation"] == model["immutable_model_contract"]["dynamics"]["equation"]
    assert binding["new_postulate_count"] == model["postulate_budget"]["used"] == 5
    assert binding["model_mutation_authorized"] is False


def test_one_compound_packet_has_four_unadjudicated_claims() -> None:
    authority = read(AUTHORITY)
    refinement = authority["primary_packet_refinement"]
    assert refinement["packet_count"] == 1
    assert refinement["compound_claim_count"] == 4
    assert len(authority["authorized_claim_obligations"]) == 4
    assert all("NOT_" in row["epistemic_status"] or "NO_" in row["epistemic_status"] for row in authority["authorized_claim_obligations"])
    output = authority["scientific_output_at_authority"]
    assert output["primary_theorem_packets_frozen"] == 0
    assert output["theorems_proved"] == 0
    assert output["gauge_equivalence_result"] == "NONE"
    assert output["historical_formula_classification"] == "NONE"


def test_execution_and_physical_promotion_remain_prohibited() -> None:
    limits = read(AUTHORITY)["scientific_limits"]
    prohibited = [key for key in limits if key.endswith("_authorized") and key != "maximum_primary_theorem_packets"]
    assert prohibited
    assert all(limits[key] is False for key in prohibited)
    assert limits["stage_4_authorized"] is False


def test_evidence_and_review_reproduce() -> None:
    authority = read(AUTHORITY)
    assert all(sha(ROOT / row["path"]) == row["sha256"] for row in authority["evidence_bindings"])
    review = read(REVIEW)
    assert review["authority_sha256"] == sha(AUTHORITY)
    assert review["accepted"] is True
    assert all(review["checks"].values())
    assert review["stage_4_authorized"] is False

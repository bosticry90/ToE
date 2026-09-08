from __future__ import annotations

import hashlib
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
RELEASE = ROOT / "formal" / "docs" / "release"
AUTHORITY = RELEASE / "TOE_GRAVITATIONAL_ACTION_FAMILY_ELIGIBILITY_HANDOFF_STAGE_5_OPEN_AUTHORITY_v0.json"
REVIEW = RELEASE / "TOE_GRAVITATIONAL_ACTION_FAMILY_ELIGIBILITY_HANDOFF_STAGE_5_OPEN_AUTHORITY_REVIEW_v0.json"


def read(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_authority_binds_exact_stage_five_manifest_scope() -> None:
    authority = read(AUTHORITY)
    assert authority["authorized_stage"] == {
        "canonical_scope_hash": "aec6355853132543dff1bf7c4aa90e65718ab1b192d56340efc9d5d584bd6dd8",
        "canonical_target": "select_toe_gravitational_action_family_eligibility_handoff_v0",
        "semantic_stage_id": "CANDIDATE_ACTION_FAMILY_ELIGIBILITY_HANDOFF",
        "stage_number": 5,
    }
    assert len(authority["family_ids"]) == len(set(authority["family_ids"])) == 7


def test_source_bindings_reproduce() -> None:
    for binding in read(AUTHORITY)["evidence_bindings"]:
        assert digest(ROOT / binding["path"]) == binding["sha256"]


def test_authority_freezes_eligibility_and_route_vocabularies() -> None:
    authority = read(AUTHORITY)
    assert len(authority["eligibility_classification_vocabulary"]) == 8
    assert authority["post_eligibility_route_vocabulary"] == [
        "DERIVE_POSITIVE_NATIVE_GRAVITATIONAL_PRINCIPLE",
        "PREPARE_BOUNDED_NEW_ACTION_POSTULATE",
        "USE_EINSTEIN_HILBERT_AS_PROVISIONAL_BASELINE",
        "DEFER_NATIVE_GRAVITY_PENDING_REQUIRED_INPUTS",
        "NO_GRAVITATIONAL_ACTION_SELECTION_ROUTE_READY",
    ]
    assert all(authority["eligibility_contract"].values())


def test_authority_prohibits_action_selection_and_automatic_successor() -> None:
    prohibited = " ".join(read(AUTHORITY)["prohibited_work"])
    for phrase in (
        "invent derive or adopt a native gravitational principle",
        "invent construct vary or adopt a gravitational action",
        "select Einstein-Hilbert as native gravity",
        "promote quadratic gravity",
        "perform a gravitational calculation",
        "successor program automatically",
    ):
        assert phrase in prohibited


def test_review_accepts_authority_without_scientific_output() -> None:
    review = read(REVIEW)
    assert review["accepted"] is True
    assert all(review["checks"].values())
    assert review["scientific_output_at_authority_checkpoint"] == {
        "eligibility_classifications_made": 0,
        "gravitational_actions_selected": 0,
        "native_gravitational_principles_selected": 0,
        "post_eligibility_routes_selected": 0,
        "successor_programs_authorized": 0,
    }

from __future__ import annotations

import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
DOC_PATH = REPO_ROOT / "formal" / "docs" / "release" / "TOE_PLAIN_LANGUAGE_SCIENTIFIC_STATUS_BOUNDARY_SUMMARY_v0.md"
JSON_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "TOE_PLAIN_LANGUAGE_SCIENTIFIC_STATUS_BOUNDARY_SUMMARY_20260525_v0.json"
)


def _load_doc() -> str:
    return DOC_PATH.read_text(encoding="utf-8")


def _load_packet() -> dict:
    return json.loads(JSON_PATH.read_text(encoding="utf-8"))


def test_plain_language_status_boundary_artifacts_exist() -> None:
    assert DOC_PATH.exists()
    assert JSON_PATH.exists()


def test_plain_language_status_boundary_preserves_core_nonclaims() -> None:
    text = _load_doc()

    required = [
        "The project has not proven a completed Theory of Everything, and the repo's own controls prevent that interpretation.",
        "The project has not discovered or confirmed new physics yet.",
        "The novel part is architectural, not yet physical.",
        "QFT-GR seam closure is not claimed.",
        "green Lean build != completed physical theory",
        "green Lean build != empirical validation",
    ]

    for phrase in required:
        assert phrase in text


def test_plain_language_status_boundary_is_time_indexed_not_live_control() -> None:
    text = _load_doc()
    packet = _load_packet()

    assert "930e9b14 Review dependency remediation closeout after tranche 004 movement" in text
    assert "Any newer source-map registration" in text
    assert "must be read from the current authoritative surfaces" in text

    policy = packet["current_status_reuse_policy"]
    assert policy["not_live_control_plane"] is True
    assert policy["does_not_change_current_live_target"] is True
    assert policy["newer_status_must_be_read_from_current_authoritative_surfaces"] is True
    assert "formal/docs/release/CURRENT_AUTHORITATIVE_SURFACES_v0.md" in policy["required_current_surfaces"]
    assert "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json" in policy["required_current_surfaces"]


def test_plain_language_status_boundary_forbidden_claims_are_false() -> None:
    packet = _load_packet()
    boundary = packet["public_claim_boundary"]

    forbidden = [
        "completed_toe_claimed",
        "new_confirmed_physics_claimed",
        "empirical_validation_claimed",
        "qft_gr_seam_closure_claimed",
        "pillar_completion_claimed",
        "release_readiness_marked",
        "release_assembly_authorized",
        "theorem_or_proof_debt_discharged",
        "phase2_authorized",
        "publication_authorized",
        "master_action_promoted",
        "canonical_toe_status_claimed",
        "external_truth_claimed",
    ]

    for key in forbidden:
        assert boundary[key] is False


def test_plain_language_status_boundary_allows_only_architectural_novelty() -> None:
    packet = _load_packet()
    allowed = packet["positive_claims_allowed"]

    assert allowed["known_physics_organization"] is True
    assert allowed["formal_governance_framework"] is True
    assert allowed["meaning_preserving_bridge_discipline"] is True
    assert allowed["false_closure_prevention"] is True
    assert allowed["architectural_or_methodological_novelty"] is True
    assert allowed["confirmed_physics_novelty"] is False

from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import (
    native_continuum_action_absence_scientific_target_selection_v0 as selection,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / selection.REPORT_RELATIVE_PATH


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_selection_regenerates_exactly_and_deterministically() -> None:
    assert (
        selection.artifact_bytes()
        == selection.artifact_bytes()
        == REPORT_PATH.read_bytes()
    )


def test_selection_preserves_every_frozen_authority_byte() -> None:
    before = {
        path: _sha256(REPO_ROOT / path)
        for path in selection.AUTHORITY_HASHES
    }
    selection.build_selection()
    after = {
        path: _sha256(REPO_ROOT / path)
        for path in selection.AUTHORITY_HASHES
    }
    assert before == after == selection.AUTHORITY_HASHES


def test_selection_consumes_schematic_action_terminal_target() -> None:
    report = _report()
    assert report["target"] == selection.TARGET
    assert report["authority"]["terminal_master_action_status"] == (
        "MASTER_ACTION_REMAINS_SCHEMATIC_ONLY"
    )
    assert report["authority"]["native_executable_continuum_action"] == (
        "NOT_YET_DEFINED"
    )


def test_minimal_native_gravitational_sector_is_selected() -> None:
    report = _report()
    assert report["verdict"] == (
        "SELECTED_MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_SECTOR_PREPARATION"
    )
    assert report["selected_next_target"] == selection.SELECTED_NEXT_TARGET
    assert report["ranking"]["selected_candidate_id"] == (
        "DEFINE_MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_SECTOR"
    )
    assert report["ranking"]["runner_up_candidate_id"] == (
        "NATIVE_DYNAMICAL_CORE_REQUIREMENTS_AND_NO_GO"
    )


def test_scoring_contract_is_bounded_and_complete() -> None:
    policy = _report()["selection_policy"]
    assert policy["criterion_scale"] == "0..5"
    assert sum(policy["weights"].values()) == 20
    assert policy["maximum_weighted_score"] == 100
    assert policy["candidate_count"] == len(selection.CANDIDATES) == 4
    for row in _report()["ranking"]["rows"]:
        assert set(row["scores"]) == set(selection.CRITERIA)
        assert 0 <= row["weighted_score"] <= 100


def test_selection_is_stable_in_all_twenty_four_variants() -> None:
    sensitivity = _report()["sensitivity_analysis"]
    assert sensitivity["variant_count"] == len(sensitivity["rows"]) == 24
    assert sensitivity["selected_candidate_stable_in_all_variants"] is True
    assert sensitivity["minimum_winning_margin"] >= 0
    assert all(
        row["selected_candidate_id"]
        == "DEFINE_MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_SECTOR"
        for row in sensitivity["rows"]
    )


def test_selected_packet_contract_is_minimal_and_gr_specific() -> None:
    obligation = _report()["selected_scientific_obligation"]
    assert obligation["pillar"] == "GR"
    assert obligation["obligation_class"] == (
        "MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_ACTION_CONTRACT_EXISTENCE_OR_BLOCK"
    )
    assert len(obligation["packet_must_freeze"]) == 10
    assert obligation["allowed_outcomes"] == [
        "MINIMAL_NATIVE_GRAVITATIONAL_ACTION_CONTRACT_READY",
        "SUPPLIED_EINSTEIN_HILBERT_SECTOR_ONLY",
        "BLOCKED_NO_NATIVE_GRAVITATIONAL_PRINCIPLE",
        "BLOCKED_MATTER_COUPLING_UNDEFINED",
    ]
    assert "Do not define a successor master action" in obligation["stopping_rule"]


def test_retained_boundaries_do_not_rehabilitate_master_action_or_rep32() -> None:
    boundaries = _report()["retained_boundaries"]
    assert boundaries["historical_master_action_v0"] == (
        "SCHEMATIC_ORGANIZING_SURFACE"
    )
    assert boundaries["successor_master_action"] == "NOT_AUTHORIZED_OR_CREATED"
    assert boundaries["C_k"] == "EXTERNAL_ADMISSIBILITY_AUDIT_ONLY"
    assert boundaries["native_tensor_field_equation"] == "NOT_DERIVED"
    assert boundaries["standard_GR_sandbox"] == "SUPPLIED_COMPARATOR_ONLY"
    assert boundaries["Rep32"] == (
        "SEPARATE_STRUCTURAL_MODEL_WITHOUT_CONTINUUM_AUTHORITY"
    )


def test_selection_authorizes_packet_preparation_only() -> None:
    scope = _report()["scope"]
    assert scope["scientific_target_selection_executed"] is True
    assert scope["packet_preparation_authorized"] is True
    for key, value in scope.items():
        if key not in {
            "scientific_target_selection_executed",
            "packet_preparation_authorized",
        }:
            assert value is False, key


def test_selection_creates_no_action_variation_gr_claim_or_automation() -> None:
    claim = _report()["claim_ceiling"]
    for token in (
        "defines no action",
        "creates no successor master theory",
        "executes no variation",
        "derives no tensor equation",
        "imports no Einstein equation",
        "automation",
    ):
        assert token in claim

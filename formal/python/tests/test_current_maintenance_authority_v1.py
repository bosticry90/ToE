from __future__ import annotations

import json

from formal.python.tools import current_maintenance_authority_v1 as authority


def _authority() -> dict[str, object]:
    value = json.loads(authority.authority_bytes().decode("utf-8"))
    assert isinstance(value, dict)
    return value


def _pointer() -> dict[str, object]:
    value = json.loads(authority.pointer_bytes().decode("utf-8"))
    assert isinstance(value, dict)
    return value


def test_authority_and_pointer_are_current_and_deterministic() -> None:
    authority_data = authority.authority_bytes()
    pointer_data = authority.pointer_bytes(authority_data)
    assert authority_data == authority.authority_bytes()
    assert pointer_data == authority.pointer_bytes(authority_data)
    assert authority_data == authority.AUTHORITY_PATH.read_bytes()
    assert pointer_data == authority.POINTER_PATH.read_bytes()


def test_versioned_authority_preserves_v0_as_history() -> None:
    report = _authority()
    previous = report["previous_maintenance_authority"]
    assert isinstance(previous, dict)
    assert previous["sha256"] == authority.MAINTENANCE_V0_SHA256
    assert previous["status"] == "SUPERSEDED_AS_CURRENT_RETAINED_IMMUTABLE_HISTORY"


def test_current_maintenance_target_is_bounded_integration_execution() -> None:
    report = _authority()
    assert report["current_maintenance_target"] == authority.MAINTENANCE_TARGET
    assert report["required_result_review_target"] == authority.RESULT_REVIEW_TARGET
    assert report["current_maintenance_target_status"] == (
        "AUTHORIZED_BY_INDEPENDENT_MAINTENANCE_PACKET_REVIEW"
    )


def test_scientific_authority_is_exact_and_unrotated() -> None:
    report = _authority()
    scientific = report["scientific_authority"]
    assert isinstance(scientific, dict)
    assert scientific["current_target"] == authority.SCIENTIFIC_TARGET
    assert scientific["target_rotated"] is False


def test_all_scientific_and_rerun_boundaries_remain_closed() -> None:
    report = _authority()
    boundary = report["boundary"]
    assert isinstance(boundary, dict)
    for field in (
        "maintenance_target_inserted_into_scientific_workstreams",
        "scientific_target_displaced",
        "scientific_target_rotated",
        "july_16_19_scientific_chain_adopted",
        "new_physics_authorized",
        "yukawa_execution_or_rerun_authorized",
        "pipe_repair_and_rerun_authorized",
        "preserved_observations_validation_use_authorized",
        "terminal_yukawa_selection_authorized",
        "production_change_authorized",
    ):
        assert boundary[field] is False
    assert boundary["integration_result_review_required"] is True
    assert boundary["post_maintenance_scientific_reconciliation_required"] is True


def test_pointer_resolves_exact_versioned_authority() -> None:
    pointer = _pointer()
    assert pointer["current_authority_path"] == (
        "formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_v1.json"
    )
    assert pointer["current_maintenance_target"] == authority.MAINTENANCE_TARGET
    assert pointer["scientific_target"] == authority.SCIENTIFIC_TARGET

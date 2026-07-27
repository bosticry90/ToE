from __future__ import annotations

import json

from formal.python.tools import (
    july_16_19_repository_integration_and_live_authority_repair_maintenance_packet_v0
    as packet,
)


def _report() -> dict[str, object]:
    value = json.loads(packet.artifact_bytes().decode("utf-8"))
    assert isinstance(value, dict)
    return value


def test_packet_is_current_and_deterministic() -> None:
    expected = packet.artifact_bytes()
    assert expected == packet.artifact_bytes()
    assert expected == packet.REPORT_PATH.read_bytes()


def test_scientific_authority_is_frozen_exactly() -> None:
    report = _report()
    freeze = report["scientific_authority_freeze"]
    assert isinstance(freeze, dict)
    assert freeze["current_target"] == packet.SCIENTIFIC_TARGET
    assert freeze["target_rotated"] is False
    assert freeze["scientific_packet_chain_adopted"] is False
    assert freeze["new_physics_authorized"] is False
    assert freeze["yukawa_rerun_authorized"] is False
    assert freeze["sandbox_pipe_repair_and_rerun_authorized"] is False
    assert freeze["preserved_observations_are_validation_evidence"] is False


def test_external_custody_counts_and_hashes_are_exact() -> None:
    report = _report()
    custody = report["external_custody_attestation"]
    assert isinstance(custody, dict)
    assert custody["manifest_sha256"] == packet.CUSTODY_MANIFEST_SHA256
    assert custody["dirty_extant_archive_sha256"] == packet.CUSTODY_ARCHIVE_SHA256
    assert custody["modified_tracked_count"] == 4
    assert custody["deleted_tracked_count"] == 3
    assert custody["untracked_file_count"] == 622
    assert custody["archived_extant_file_count"] == 626
    assert custody["manifest_row_count"] == 629


def test_packet_selects_independent_review_only() -> None:
    report = _report()
    assert report["status"] == "PREPARED_PENDING_INDEPENDENT_MAINTENANCE_REVIEW"
    assert report["selected_next_target"] == packet.SELECTED_NEXT_TARGET
    basis = report["authority_basis"]
    assert isinstance(basis, dict)
    assert basis["maintenance_target_rotation_executed"] is False
    assert basis["independent_review_required_before_execution"] is True


def test_prohibited_scope_closes_scientific_and_rerun_routes() -> None:
    report = _report()
    prohibited = report["prohibited_scope"]
    assert isinstance(prohibited, list)
    for item in (
        "ROTATE_SCIENTIFIC_AUTHORITY",
        "ADOPT_JULY_16_19_SCIENTIFIC_PACKET_CHAIN",
        "EXECUTE_OR_RERUN_YUKAWA_SANDBOX",
        "REPAIR_PIPE_AND_RERUN_CONSUMED_SANDBOX",
        "PROMOTE_PRESERVED_OBSERVATIONS_TO_VALIDATION_EVIDENCE",
        "SELECT_TERMINAL_YUKAWA_RESPONSE_DURING_MAINTENANCE",
    ):
        assert item in prohibited


def test_status_axes_do_not_conflate_custody_and_adoption() -> None:
    report = _report()
    axes = report["integration_status_axes"]
    assert isinstance(axes, dict)
    assert axes["custody_status"] == "EXTERNAL_BYTES_AND_MANIFEST_PRESERVED"
    assert axes["integration_status"] == "PENDING_INDEPENDENT_MAINTENANCE_REVIEW"
    assert axes["scientific_adoption_status"] == "NOT_ADOPTED"


def test_terminal_selector_remains_conditional() -> None:
    report = _report()
    boundary = report["successor_boundary"]
    assert isinstance(boundary, dict)
    assert boundary["independent_review_may_authorize_integration_execution"] is True
    assert boundary["maintenance_completion_may_rotate_scientific_authority"] is False
    assert boundary["post_maintenance_scientific_reconciliation_required"] is True
    assert boundary["terminal_yukawa_selector_is_conditional_not_precommitted"] is True

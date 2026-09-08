from __future__ import annotations

import json

from formal.python.tools import (
    july_16_19_repository_integration_and_live_authority_repair_maintenance_packet_review_v0
    as review,
)


def _report() -> dict[str, object]:
    value = json.loads(review.artifact_bytes().decode("utf-8"))
    assert isinstance(value, dict)
    return value


def test_review_is_current_and_deterministic() -> None:
    expected = review.artifact_bytes()
    assert expected == review.artifact_bytes()
    assert expected == review.REPORT_PATH.read_bytes()


def test_all_review_gates_pass() -> None:
    report = _report()
    gates = report["review_gates"]
    assert isinstance(gates, dict)
    assert gates["gate_count"] == 20
    assert gates["pass_count"] == 20
    assert gates["failure_count"] == 0


def test_review_authorizes_bounded_integration_only() -> None:
    report = _report()
    authorization = report["authorization"]
    assert isinstance(authorization, dict)
    assert authorization["bounded_integration_execution_authorized"] is True
    assert authorization["versioned_maintenance_authority_successor_authorized"] is True
    assert authorization["integration_result_review_required"] is True
    assert report["selected_next_target"] == review.SELECTED_NEXT_TARGET


def test_review_preserves_scientific_firewall() -> None:
    report = _report()
    firewall = report["scientific_firewall"]
    assert isinstance(firewall, dict)
    assert firewall["canonical_scientific_target"] == review.packet.SCIENTIFIC_TARGET
    for field in (
        "scientific_target_rotation_authorized",
        "scientific_chain_adoption_authorized",
        "new_derivation_authorized",
        "yukawa_execution_or_rerun_authorized",
        "pipe_repair_and_rerun_authorized",
        "preserved_observations_validation_use_authorized",
        "terminal_yukawa_selection_authorized",
        "production_change_authorized",
    ):
        assert firewall[field] is False


def test_review_keeps_post_maintenance_scientific_decision_open() -> None:
    report = _report()
    boundary = report["result_boundary"]
    assert isinstance(boundary, dict)
    assert boundary["integration_execution_must_preserve_scientific_target"] is True
    assert boundary["scientific_adoption_or_replay_decision_is_post_maintenance"] is True
    assert boundary["ordered_adoption_is_not_presumed"] is True
    assert boundary["terminal_selector_may_be_unreachable_after_reconciliation"] is True

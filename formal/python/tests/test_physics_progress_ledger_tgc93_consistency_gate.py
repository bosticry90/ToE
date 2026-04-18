from __future__ import annotations

import pytest

from formal.python.tools.physics_progress_ledger_generate import (
    _validate_tgc93_consistency,
    build_payload,
)


def test_tgc93_consistency_allows_negative_delta_with_authorize() -> None:
    _validate_tgc93_consistency(-1, "AUTHORIZE_SINGLE_SEAM_REENTRY")


def test_tgc93_consistency_allows_nonnegative_delta_with_rework_route() -> None:
    _validate_tgc93_consistency(0, "ROUTE_TO_THEOREM_GAP_REWORK")
    _validate_tgc93_consistency(2, "ROUTE_TO_THEOREM_GAP_REWORK")


def test_tgc93_consistency_rejects_negative_delta_with_rework_route() -> None:
    with pytest.raises(ValueError, match="Contradiction detected"):
        _validate_tgc93_consistency(-1, "ROUTE_TO_THEOREM_GAP_REWORK")


def test_tgc93_consistency_rejects_nonnegative_delta_with_authorize() -> None:
    with pytest.raises(ValueError, match="Contradiction detected"):
        _validate_tgc93_consistency(0, "AUTHORIZE_SINGLE_SEAM_REENTRY")


def test_tgc93_consistency_rejects_unknown_decision_token() -> None:
    with pytest.raises(ValueError, match="Unexpected TGC-93 branch decision token"):
        _validate_tgc93_consistency(0, "UNKNOWN_DECISION_TOKEN")


def test_physics_progress_ledger_emits_consistency_metadata() -> None:
    payload = build_payload(None)
    consistency = payload["evidence_bundle"]["consistency"]
    assert consistency["status"] == "CONSISTENT"
    assert consistency["rule"] == "FAIL_CLOSED_ON_TREND_DELTA_AND_TGC93_ROUTE_CONTRADICTION"
    assert payload["active_routing_decision_source"] == (
        "formal/docs/release/WS_10_TGC_93_BRANCH_DECISION_PACKAGE_20260411_v0.md"
    )
    assert payload["evidence_bundle"]["tgc_tokens"]["active_routing_decision_source"] == (
        "formal/docs/release/WS_10_TGC_93_BRANCH_DECISION_PACKAGE_20260411_v0.md"
    )

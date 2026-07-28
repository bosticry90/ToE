from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


ROOT = find_repo_root(Path(__file__))
HANDOFF_PATH = ROOT / (
    "formal/docs/release/"
    "JULY_16_19_POST_MAINTENANCE_SCIENTIFIC_ADOPTION_OR_"
    "BOUNDED_REPLAY_DECISION_HANDOFF_20260727_v0.json"
)
REVIEW_PATH = ROOT / (
    "formal/docs/release/"
    "JULY_16_19_REPOSITORY_INTEGRATION_AND_LIVE_AUTHORITY_REPAIR_"
    "EXECUTION_RESULT_REVIEW_20260727_v0.json"
)
HANDOFF_SHA256 = (
    "c04d912dfb6185347c3f78130b0c253bc2ed12f97b9ff3881025b6120be34f44"
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _handoff() -> dict:
    value = json.loads(HANDOFF_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_handoff_is_hash_exact_and_consumes_the_exact_result_review() -> None:
    handoff = _handoff()
    assert _sha256(HANDOFF_PATH) == HANDOFF_SHA256
    assert _sha256(REVIEW_PATH) == handoff["consumed_maintenance_result_review"]["sha256"]
    assert handoff["consumed_maintenance_result_review"]["verdict"] == (
        "ACCEPTED_MAINTENANCE_INTEGRATION_COMPLETE_"
        "SCIENTIFIC_RECONCILIATION_PENDING"
    )


def test_handoff_presents_exactly_two_unselected_bounded_routes() -> None:
    handoff = _handoff()
    assert handoff["decision"]["status"] == "PENDING_SEPARATE_SCIENTIFIC_AUTHORITY"
    assert handoff["decision"]["selected_route"] is None
    assert handoff["decision"]["route_count"] == 2
    assert handoff["decision"]["automatic_selection_permitted"] is False
    assert [route["route_id"] for route in handoff["routes"]] == [
        "ORDERED_ADOPTION",
        "BOUNDED_RECONCILIATION_OR_REPLAY",
    ]
    assert all(route["scientific_effect_before_selection"] == "NONE" for route in handoff["routes"])


def test_exact_terminal_selector_is_preserved_but_not_authorized() -> None:
    selector = _handoff()["preserved_conditional_terminal_selector"]
    assert selector["identifier"] == (
        "select_post_scalar_only_yukawa_analytic_sphere_kernel_exploratory_"
        "sandbox_v1_execution_result_review_scientific_response_v0"
    )
    assert selector["currently_authorized"] is False
    assert selector["rename_authorized"] is False
    assert _handoff()["preserved_terminal_recommendation"]["value"] == (
        "DEFER_CURRENT_KERNEL_PATH"
    )
    assert _handoff()["preserved_terminal_recommendation"]["currently_executable"] is False


def test_handoff_preserves_every_scientific_and_rerun_firewall() -> None:
    handoff = _handoff()
    assert handoff["scientific_authority"]["target_rotated_by_this_handoff"] is False
    for value in handoff["firewall"].values():
        assert value is False

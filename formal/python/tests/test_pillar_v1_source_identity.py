from __future__ import annotations

import copy

from formal.python.tools import (
    pillar_seam_unit_mapping_ledger_blocker_response_route_selection_v1 as v1,
)
from formal.python.tools import pillar_v1_source_identity as subject


def test_contract_is_canonical_and_all_three_commit_relative_identities_resolve() -> None:
    contract = subject.load_contract()
    by_role = subject.verify_contract()
    assert contract["identity_count"] == 3
    assert set(by_role) == {
        subject.FROZEN_REVIEW_ROLE,
        subject.CURRENT_SOURCE_ROLE,
        subject.CURRENT_GENERATOR_ROLE,
    }
    assert by_role[subject.FROZEN_REVIEW_ROLE]["temporal_role"] == "HISTORICAL"
    assert by_role[subject.CURRENT_SOURCE_ROLE]["temporal_role"] == "CURRENT"
    assert by_role[subject.CURRENT_GENERATOR_ROLE]["temporal_role"] == "CURRENT"
    assert contract["contract_version"] == "v1"


def test_previous_current_contract_remains_immutable_and_resolvable() -> None:
    previous = subject.load_contract(subject.PREVIOUS_CONTRACT_PATH)
    previous_by_role = subject.verify_contract(
        contract_path=subject.PREVIOUS_CONTRACT_PATH
    )
    assert previous["contract_version"] == "v0"
    assert (
        previous_by_role[subject.CURRENT_GENERATOR_ROLE]["git_blob"]
        != subject.verify_contract()[subject.CURRENT_GENERATOR_ROLE]["git_blob"]
    )


def test_historical_review_pin_is_preserved_without_live_byte_equality() -> None:
    binding = next(
        item
        for item in v1._frozen_inputs()
        if item["artifact_id"] == "ROUTE_SELECTION_RESULT_REVIEW_TOOL_v0"
    )
    by_role = subject.verify_contract()
    assert binding["sha256"] == by_role[subject.FROZEN_REVIEW_ROLE]["sha256"]
    assert binding["sha256"] != by_role[subject.CURRENT_SOURCE_ROLE]["sha256"]
    assert subject.historical_review_binding_matches(binding)


def test_historical_review_pin_corruption_fails_closed() -> None:
    bindings = copy.deepcopy(v1._frozen_inputs())
    binding = next(
        item
        for item in bindings
        if item["artifact_id"] == "ROUTE_SELECTION_RESULT_REVIEW_TOOL_v0"
    )
    binding["sha256"] = "0" * 64
    assert not subject.bindings_match_declared_identities(bindings)


def test_all_v1_mixed_identity_bindings_resolve() -> None:
    assert subject.bindings_match_declared_identities(v1._frozen_inputs())

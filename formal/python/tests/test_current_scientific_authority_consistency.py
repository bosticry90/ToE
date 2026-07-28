from __future__ import annotations

import pytest

from formal.python.tools import current_scientific_authority_consistency as authority


TARGET = (
    "prepare_pillar_seam_unit_mapping_ledger_blocker_response_"
    "route_selection_packet_v2"
)


def test_witness_parser_requires_exact_nonempty_single_values() -> None:
    output = (
        f"{authority.TARGET_PREFIX}{TARGET}\n"
        f"{authority.AUTHORITY_PREFIX}{TARGET}\n"
    )
    assert authority.parse_witness_output(output) == {
        "lean_current_target": TARGET,
        "lean_current_authority": TARGET,
    }
    with pytest.raises(authority.AuthorityConsistencyError, match="missing"):
        authority.parse_witness_output(f"{authority.TARGET_PREFIX}{TARGET}\n")
    with pytest.raises(authority.AuthorityConsistencyError, match="multiple"):
        authority.parse_witness_output(output + f"{authority.TARGET_PREFIX}{TARGET}\n")
    with pytest.raises(authority.AuthorityConsistencyError, match="empty"):
        authority.parse_witness_output(
            f"{authority.TARGET_PREFIX}\n{authority.AUTHORITY_PREFIX}{TARGET}\n"
        )
    with pytest.raises(authority.AuthorityConsistencyError, match="grammar"):
        authority.parse_witness_output(
            f"{authority.TARGET_PREFIX}not valid\n"
            f"{authority.AUTHORITY_PREFIX}{TARGET}\n"
        )


def test_live_registry_and_evaluated_lean_values_agree() -> None:
    report = authority.build_report()
    assert report["status"] == "PASS"
    assert report["registry_target"] == TARGET
    assert report["lean_current_target"] == TARGET
    assert report["lean_current_authority"] == TARGET
    assert report["all_scientific_values_equal"] is True
    assert report["maintenance_target_separate"] is True


def test_mismatched_lean_value_fails_closed() -> None:
    with pytest.raises(authority.AuthorityConsistencyError, match="mismatch"):
        authority.build_report(
            witness={
                "lean_current_target": "select_unrelated_target",
                "lean_current_authority": TARGET,
            }
        )

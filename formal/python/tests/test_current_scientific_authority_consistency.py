from __future__ import annotations

import json

import pytest

from formal.python.tools import current_scientific_authority_consistency as authority


TARGET = (
    "prepare_qft_gr_quadratic_auxiliary_harmonic_adapted_norm_"
    "well_posedness_packet_v0"
)
JULY_19_SELECT_TARGET = (
    "select_post_scalar_only_yukawa_analytic_sphere_kernel_exploratory_"
    "sandbox_v1_execution_result_review_scientific_response_v0"
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
    with pytest.raises(authority.AuthorityConsistencyError, match="unknown"):
        authority.parse_witness_output(
            f"{authority.TARGET_PREFIX}invent_unregistered_transition_v0\n"
            f"{authority.AUTHORITY_PREFIX}{TARGET}\n"
        )


def test_exact_july_19_select_target_parses_to_nonempty_authority() -> None:
    output = (
        f"{authority.TARGET_PREFIX}{JULY_19_SELECT_TARGET}\n"
        f"{authority.AUTHORITY_PREFIX}{JULY_19_SELECT_TARGET}\n"
    )
    assert authority.parse_witness_output(output) == {
        "lean_current_target": JULY_19_SELECT_TARGET,
        "lean_current_authority": JULY_19_SELECT_TARGET,
    }


def test_every_registry_target_verb_is_supported() -> None:
    registry = authority._read_json(authority.REGISTRY_PATH)
    target_fields = {
        "authorized_next_target",
        "current_target",
        "next_target",
        "selected_next_target",
        "target",
    }
    observed: set[str] = set()

    def visit(value: object) -> None:
        if isinstance(value, dict):
            for key, item in value.items():
                if key in target_fields and isinstance(item, str):
                    if authority.TARGET_GRAMMAR.fullmatch(item):
                        observed.add(item.split("_", 1)[0])
                visit(item)
        elif isinstance(value, list):
            for item in value:
                visit(item)

    visit(registry)
    assert observed
    assert observed <= authority.SCIENTIFIC_TARGET_VERBS


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


def test_maintenance_target_cannot_occupy_scientific_field(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path,
) -> None:
    pointer = tmp_path / "maintenance_pointer.json"
    pointer.write_text(
        json.dumps({"current_maintenance_target": TARGET}),
        encoding="utf-8",
    )
    monkeypatch.setattr(authority, "MAINTENANCE_POINTER_PATH", pointer)
    with pytest.raises(
        authority.AuthorityConsistencyError,
        match="maintenance target appears",
    ):
        authority.build_report(
            witness={
                "lean_current_target": TARGET,
                "lean_current_authority": TARGET,
            }
        )

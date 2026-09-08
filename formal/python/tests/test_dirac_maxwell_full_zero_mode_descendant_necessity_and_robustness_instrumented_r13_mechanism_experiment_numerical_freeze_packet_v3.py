from __future__ import annotations

import copy
import json
from functools import lru_cache
from pathlib import Path
from typing import Any

import pytest

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_numerical_freeze_packet_v3
    as freeze,
)


ROOT = find_repo_root(Path(__file__))


@lru_cache(maxsize=1)
def _artifact_bytes() -> dict[str, bytes]:
    return freeze.artifact_bytes()


@lru_cache(maxsize=1)
def _artifacts() -> tuple[
    dict[str, Any],
    dict[str, Any],
    dict[str, Any],
    dict[str, Any],
    dict[str, Any],
]:
    raw = _artifact_bytes()
    return tuple(
        json.loads(raw[path].decode("utf-8"))
        for path in (
            freeze.PACKET_RELATIVE_PATH,
            freeze.RUN_MATRIX_RELATIVE_PATH,
            freeze.IDENTITY_RELATIVE_PATH,
            freeze.MANIFEST_RELATIVE_PATH,
            freeze.REPORT_RELATIVE_PATH,
        )
    )  # type: ignore[return-value]


def test_all_five_v3_artifacts_regenerate_exactly_and_deterministically() -> None:
    first = _artifact_bytes()
    assert set(first) == {
        freeze.PACKET_RELATIVE_PATH,
        freeze.RUN_MATRIX_RELATIVE_PATH,
        freeze.IDENTITY_RELATIVE_PATH,
        freeze.MANIFEST_RELATIVE_PATH,
        freeze.REPORT_RELATIVE_PATH,
    }
    assert all((ROOT / path).read_bytes() == raw for path, raw in first.items())
    assert freeze.artifact_bytes() == first


def test_v3_preserves_every_v2_physical_and_numerical_input() -> None:
    _, matrix, _, _, _ = _artifacts()
    predecessor = json.loads(
        (ROOT / freeze.PREDECESSOR_MATRIX_RELATIVE_PATH).read_text(
            encoding="utf-8"
        )
    )
    assert matrix["record_count"] == predecessor["record_count"] == 6
    assert matrix["expected_run_id_order"] == predecessor["expected_run_id_order"]
    assert matrix["fixed_numerical_settings"] == predecessor["fixed_numerical_settings"]
    for old, new in zip(predecessor["records"], matrix["records"], strict=True):
        assert old["run_id"] == new["run_id"]
        for field in freeze.executor_v3._PHYSICAL_FIELDS:
            assert new[field] == old[field]
        assert new["scientific_input_core"] == old["scientific_input_core"]
        assert new["scientific_input_core_sha256"] == old[
            "scientific_input_core_sha256"
        ]
    assert matrix["supersedes_blocked_predecessor"][
        "scientific_configuration_changed"
    ] is False


def test_all_six_partial_templates_resolve_before_strict_final_validation() -> None:
    packet, matrix, _, _, report = _artifacts()
    audit = packet["metric_configuration_resolution_contract"][
        "preparation_read_only_audit"
    ]
    assert audit["all_passed"] is True
    assert audit["positive_controls"] == audit["expected_positive_controls"]
    assert audit["positive_controls"] == {
        "partial_template_validation_count": 6,
        "role_resolution_count": 6,
        "resolved_block_floors_match_count": 6,
        "strict_final_validation_count": 6,
        "read_only_execution_plan_count": 6,
        "physical_pair_equality_count": 3,
        "unique_complete_execution_identity_count": 6,
        "simulation_entry_count": 0,
        "future_output_root_created": False,
    }
    v0 = freeze.importlib.import_module(
        freeze.executor_custody_v3.V0_IMPLEMENTATION_MODULE
    )
    for record in matrix["records"]:
        partial = record["partial_metric_configuration"]
        overlay = record["role_resolution_overlay"]
        assert freeze.executor_v3.validate_partial_metric_configuration(partial) == []
        resolved = freeze.executor_v3.resolve_frozen_metric_configuration(
            record, partial, overlay
        )
        assert resolved == record["resolved_metric_configuration"]
        assert resolved["metric_configuration"]["block_floors"] == {
            block_id: freeze.executor_v3.GAMMA64
            for block_id in freeze.executor_v3.METRIC_BLOCK_IDS
        }
        v0._validate_metric_configuration(resolved["metric_configuration"])
    assert report["freeze_summary"]["read_only_execution_plan_count"] == 6
    assert not (ROOT / freeze.EXPERIMENT_OUTPUT_ROOT).exists()


def test_all_eight_resolution_mutations_have_exact_diagnostics() -> None:
    packet, _, _, _, _ = _artifacts()
    audit = packet["metric_configuration_resolution_contract"][
        "preparation_read_only_audit"
    ]
    expected = {
        "unresolved_template_not_executable": "UNRESOLVED_TEMPLATE_NOT_EXECUTABLE",
        "missing_role_mapping": "ROLE_RESOLUTION_MISSING_METRIC_BLOCK_FLOORS",
        "missing_block_floors_after_resolution": "ROLE_RESOLUTION_MISSING_METRIC_BLOCK_FLOORS",
        "wrong_block_floors_for_role": "ROLE_RESOLUTION_WRONG_METRIC_BLOCK_FLOORS",
        "caller_supplied_block_floors": "CALLER_SUPPLIED_METRIC_BLOCK_FLOORS_FORBIDDEN",
        "role_overlay_mutation": "ROLE_RESOLUTION_OVERLAY_IDENTITY_MISMATCH",
        "validation_before_resolution": "VALIDATION_BEFORE_ROLE_RESOLUTION_FORBIDDEN",
        "partial_object_to_numerical_executor": "PARTIAL_CONFIGURATION_NUMERICAL_EXECUTION_FORBIDDEN",
    }
    assert audit["negative_control_count"] == len(expected) == 8
    assert {
        item["control_id"]: item["observed_first_diagnostic"]
        for item in audit["negative_controls"]
    } == expected
    assert all(
        item["passed"] and not item["plan_constructed"]
        for item in audit["negative_controls"]
    )


def test_all_v2_identity_and_runtime_repairs_remain_enforced() -> None:
    packet, matrix, identity, _, _ = _artifacts()
    authority = packet["runtime_execution_authority_proposal"][
        "proposed_review_authority"
    ]
    closure = matrix["runtime_source_closure_sha256"]
    complete: dict[str, str] = {}
    resolved: dict[str, str] = {}
    for record in matrix["records"]:
        run_id = record["run_id"]
        complete[run_id] = freeze.executor_v3.complete_execution_identity_sha256(
            record, closure
        )
        resolved[run_id] = freeze.sha256_bytes(
            freeze.canonical_json_bytes(record["resolved_metric_configuration"])
        )
        assert authority["expected_full_record_sha256_by_run_id"][run_id] == (
            freeze.executor_v3.full_record_identity_sha256(record)
        )
    assert len(set(complete.values())) == 6
    assert authority["expected_complete_execution_sha256_by_run_id"] == complete
    assert authority[
        "expected_resolved_metric_configuration_sha256_by_run_id"
    ] == resolved
    assert {
        item["run_id"]: item["resolved_metric_configuration_sha256"]
        for item in identity["outputs"]
    } == resolved
    mutation = packet["run_lookup_and_preflight_contract"][
        "identity_mutation_diagnostic_audit"
    ]
    assert mutation["mutation_count"] == 20
    assert mutation["exact_first_diagnostic_count"] == 20
    assert mutation["all_passed"] is True


def test_eight_runtime_sources_are_bound_by_path_bytes_and_loader() -> None:
    packet, _, _, _, _ = _artifacts()
    source = packet["source_closure_manifest"]
    assert source["binding_count"] == 8
    assert source["closure_sha256"] == freeze.sha256_bytes(
        freeze.canonical_json_bytes(source["runtime_source_closure"])
    )
    loaded = packet["preparation_self_validation"][
        "runtime_loaded_source_identity"
    ]
    assert loaded["all_passed"] is True
    assert loaded["loaded_module_count"] == 8
    assert all(
        item["path_exact"] and item["bytes_exact"] and item["loader_exact"]
        for item in loaded["loaded_modules"]
    )


def test_review_authority_is_complete_and_cannot_be_self_accepted_by_preparation() -> None:
    packet, matrix, _, _, _ = _artifacts()
    proposal = packet["runtime_execution_authority_proposal"]
    authority = copy.deepcopy(proposal["proposed_review_authority"])
    assert authority["execution_authorized"] is False
    assert authority["artifact_bindings"]["freeze_packet"]["sha256"] is None
    assert freeze.executor_v3.strict_validate_matrix(matrix, authority) == []
    accepted = copy.deepcopy(authority)
    accepted["execution_authorized"] = True
    accepted["artifact_bindings"]["freeze_packet"]["sha256"] = (
        freeze.sha256_bytes(_artifact_bytes()[freeze.PACKET_RELATIVE_PATH])
    )
    anchor = {
        "verdict": freeze.executor_custody_v3.EXPECTED_REVIEW_VERDICT,
        freeze.executor_custody_v3.REVIEW_AUTHORITY_FIELD: accepted,
    }
    assert freeze.executor_v3._validate_freeze_anchor(anchor) == []
    anchor_path = ROOT / freeze.executor_custody_v3.REVIEW_ANCHOR_RELATIVE_PATH
    if anchor_path.exists():
        stored_anchor = json.loads(anchor_path.read_text(encoding="utf-8"))
        assert stored_anchor["verdict"] == (
            freeze.executor_custody_v3.EXPECTED_REVIEW_VERDICT
        )
        assert freeze.executor_v3._validate_freeze_anchor(stored_anchor) == []
    else:
        with pytest.raises(
            freeze.executor_v3.RuntimeCustodyError,
            match="accepted v3 review anchor is absent",
        ):
            freeze.executor_v3.preflight_frozen_execution(ROOT)
    assert not (ROOT / freeze.EXPERIMENT_OUTPUT_ROOT).exists()


def test_real_executor_read_only_preflight_builds_exactly_six_plans(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    packet, _, _, _, _ = _artifacts()
    authority = copy.deepcopy(
        packet["runtime_execution_authority_proposal"][
            "proposed_review_authority"
        ]
    )
    authority["execution_authorized"] = True
    authority["artifact_bindings"]["freeze_packet"]["sha256"] = (
        freeze.sha256_bytes(_artifact_bytes()[freeze.PACKET_RELATIVE_PATH])
    )
    anchor_report = {
        "relative_path": freeze.executor_custody_v3.REVIEW_ANCHOR_RELATIVE_PATH,
        "verdict": freeze.executor_custody_v3.EXPECTED_REVIEW_VERDICT,
        "runtime_execution_authority_sha256": freeze.sha256_bytes(
            freeze.canonical_json_bytes(authority)
        ),
        "fixed_path_bytes_loaded": True,
    }
    monkeypatch.setattr(
        freeze.executor_v3,
        "_load_reviewed_authority",
        lambda _repo_root: (copy.deepcopy(authority), copy.deepcopy(anchor_report)),
    )
    v0 = freeze.importlib.import_module(
        freeze.executor_custody_v3.V0_IMPLEMENTATION_MODULE
    )
    for key, value in v0.REQUIRED_EXECUTION_ENVIRONMENT.items():
        monkeypatch.setenv(key, value)
    fixed_anchor = ROOT / freeze.executor_custody_v3.REVIEW_ANCHOR_RELATIVE_PATH
    fixed_anchor_before = fixed_anchor.read_bytes() if fixed_anchor.exists() else None
    report = freeze.executor_v3.preflight_frozen_execution(ROOT)
    assert report["all_passed"] is True
    assert report["read_only_execution_plan_count"] == 6
    assert len(report["read_only_execution_plans"]) == 6
    assert report["simulation_entry_count"] == 0
    assert report["execution_invoked"] is False
    assert report["output_root_absent"] is True
    assert not (ROOT / freeze.EXPERIMENT_OUTPUT_ROOT).exists()
    fixed_anchor_after = fixed_anchor.read_bytes() if fixed_anchor.exists() else None
    assert fixed_anchor_after == fixed_anchor_before


def test_scientific_matrix_and_claim_boundary_remain_unchanged() -> None:
    packet, matrix, identity, manifest, report = _artifacts()
    assert matrix["fixed_numerical_settings"] == {
        "accepted_step_count": 16,
        "checkpoint_count_including_initial": 17,
        "duration": 0.05,
        "grid_size": 16,
        "iteration_cap": 80,
        "time_step": 0.003125,
        "tolerances_by_configuration": {
            "R10_LOOSE_NEIGHBOR": 1e-8,
            "R13_LOOSE": 1e-8,
            "R13_TIGHT": 1e-12,
        },
    }
    assert packet["equation_block_count"] == 8
    assert packet["mechanism_observable_count"] == 14
    assert packet["classifier_freeze"]["support_constant_count"] == 23
    assert packet["freeze_adversarial_control_count"] == 41
    assert identity["role_payload_file_count"] == 12
    assert report["freeze_summary"]["simulation_entry_count"] == 0
    assert manifest["execution_authorized"] is False
    assert packet["verdict"] == "PREPARED_PENDING_INDEPENDENT_REVIEW"
    assert packet["selected_next_target"] == freeze.REVIEW_TARGET
    boundary = packet["authority_boundary"]
    assert boundary[
        "numerical_freeze_v2_blocked_executor_preflight_configuration"
    ] is True
    assert boundary["numerical_freeze_v3_prepared"] is True
    assert boundary["numerical_freeze_v3_independently_accepted"] is False
    assert boundary["experiment_execution_authorized"] is False
    assert boundary["experiment_execution_performed"] is False
    assert boundary["canonical_robustness"] == "NUMERICALLY_BLOCKED"
    assert boundary["root_mechanism"] == "UNRESOLVED"
    assert boundary["materiality"] == "NOT_EVALUATED_NUMERICAL_BLOCK"
    assert not boundary["new_E_REPRO_claim"]

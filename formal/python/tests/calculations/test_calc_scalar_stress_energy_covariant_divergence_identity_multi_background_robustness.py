from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path

import pytest

import formal.python.toe.calculations.calc_scalar_stress_energy_covariant_divergence_identity_multi_background_robustness as calculation
from formal.python.tools import scalar_multi_background_robustness_reports as contract


@pytest.fixture(scope="module")
def preflight() -> dict[str, object]:
    return calculation.preflight_source_family()


@pytest.fixture(scope="module")
def state(preflight) -> dict[str, object]:
    return calculation.reconstruct_source_family(preflight)


@pytest.fixture(scope="module")
def result(state) -> dict[str, object]:
    return calculation.build_result(state=copy.deepcopy(state))


def test_preflight_verifies_exact_guardrail_and_twenty_four_sources(
    preflight,
) -> None:
    assert preflight["preflight_verified"] is True
    assert preflight["guardrail_sha256"] == calculation.GUARDRAIL_SHA256
    assert len(preflight["chains"]) == 4
    artifacts = [
        artifact
        for chain in preflight["chains"]
        for artifact in chain["artifacts"]
    ]
    assert len(artifacts) == 24
    assert len({artifact["path"] for artifact in artifacts}) == 24
    assert all(
        artifact["verified"] is True
        and artifact["actual_sha256"] == artifact["sha256"]
        for artifact in artifacts
    )
    assert [
        chain["contract"]["chain_id"] for chain in preflight["chains"]
    ] == [
        "minkowski_1plus1",
        "conformal_connection_1plus1",
        "de_sitter_1plus1",
        "warped_2plus1",
    ]


def test_chain_specific_adapters_read_actual_result_evidence(preflight) -> None:
    changed = copy.deepcopy(preflight)
    minkowski = changed["chains"][0]["payloads"]["calculation_result"]
    minkowski["threshold_evidence"][
        "minimum_observed_two_finest_convergence_order"
    ] = 1.9
    minkowski["threshold_evidence"][
        "finest_combined_off_shell_relative_error"
    ] = 0.01
    reconstructed = calculation.reconstruct_source_family(changed)
    row = reconstructed["profiles"][0]
    assert row["profile_row_id"] == "minkowski_off_shell"
    assert row["p_min"] == 1.9
    assert row["off_shell_relative_identity_error"] == 0.01


def test_background_rows_preserve_geometry_dimension_and_grid_meaning(
    result,
) -> None:
    rows = {
        row["chain_id"]: row for row in result["background_comparison_rows"]
    }
    assert len(rows) == 4
    assert {row["spacetime_dimension"] for row in rows.values()} == {2, 3}
    assert {row["divergence_component_count"] for row in rows.values()} == {
        2,
        3,
    }
    assert {row["connection_class"] for row in rows.values()} == {
        "zero_connection",
        "nonzero_connection",
    }
    assert {row["curvature_class"] for row in rows.values()} == {
        "zero_curvature",
        "constant_nonzero_curvature",
        "spatially_varying_signed_curvature_with_zero_crossings",
    }
    assert rows["minkowski_1plus1"]["finest_grid_shape"] == [512]
    assert rows["warped_2plus1"]["finest_grid_shape"] == [256, 256]
    assert rows["warped_2plus1"]["grid_meaning"] == "N x N spatial points"
    assert "two_dimensional_einstein_gravity_degenerate" not in rows[
        "warped_2plus1"
    ]


def test_comparable_envelopes_are_exactly_five_actual_profile_rows(
    result,
) -> None:
    metric = result["comparable_metric_contract"]
    assert len(metric["convergence_rows"]) == 5
    assert len(metric["off_shell_relative_error_rows"]) == 5
    assert metric["family_minimum_p_min"] == pytest.approx(
        1.9916550282637009
    )
    assert metric[
        "family_maximum_off_shell_relative_identity_error"
    ] == pytest.approx(0.004010933857743127)
    assert all(
        row["metric_kind"]
        == "within_background_dimensionless_off_shell_relative_identity_error"
        for row in metric["off_shell_relative_error_rows"]
    )
    serialized = calculation.canonical_json_bytes(result)
    assert b"raw_timing" not in serialized
    assert b"performance_ranking" not in serialized


def test_all_thirty_seven_qualified_source_decisions_remain_individual(
    result,
) -> None:
    rows = result["qualified_source_decisions"]
    assert len(rows) == 37
    assert len({row["qualified_gate_id"] for row in rows}) == 37
    assert all(
        row["passed"] is True
        and row["source_all_thresholds_passed"] is True
        for row in rows
    )
    counts: dict[str, int] = {}
    for row in rows:
        counts[row["chain_id"]] = counts.get(row["chain_id"], 0) + 1
    assert counts == {
        "minkowski_1plus1": 4,
        "conformal_connection_1plus1": 6,
        "de_sitter_1plus1": 11,
        "warped_2plus1": 16,
    }


def test_source_local_on_shell_policies_never_form_relative_error_to_zero(
    result,
) -> None:
    rows = result["source_local_on_shell_policy_rows"]
    assert len(rows) == 4
    assert all(
        row["passed"] is True
        and row["relative_error_against_zero_formed"] is False
        and row["policy"]["relative_error_against_zero_allowed"] is False
        for row in rows
    )
    warped = next(row for row in rows if row["chain_id"] == "warped_2plus1")
    assert warped["source_evidence"]["convergence_status"] == (
        "not_applicable_exact_zero"
    )
    assert warped["source_evidence"]["finest_absolute_divergence"] == pytest.approx(
        1.809414347125402e-19
    )


def test_applicability_is_typed_and_never_zero_filled(result) -> None:
    rows = result["applicability_typed_local_check_rows"]
    assert len(rows) == 4
    assert all(row["passed"] is True for row in rows)
    non_applicable = [
        check
        for row in rows
        for check in row["checks"].values()
        if check["status"] in {
            "not_applicable",
            "baseline_not_recovery_test",
        }
    ]
    assert non_applicable
    assert all(check["value"] is None for check in non_applicable)
    applicable = [
        check
        for row in rows
        for check in row["checks"].values()
        if check["status"] == "passed"
    ]
    assert applicable and all(check["value"] is not None for check in applicable)


def test_ten_controls_cover_eight_mechanisms_without_masking(result) -> None:
    controls = result["control_coverage"]
    assert controls["instance_count"] == 10
    assert controls["mechanism_count"] == 8
    assert controls["all_detected"] is True
    assert len(controls["instances"]) == 10
    assert all(row["detected"] is True for row in controls["instances"])
    assert set(controls["mechanism_classes"]) == {
        "off_shell_nonconservation",
        "naive_partial_divergence",
        "inconsistent_connection",
        "curvature_derivative_omission",
        "omitted_tensor_index_connection",
        "omitted_volume_trace_connection",
        "flat_geometry_substitution",
        "incorrect_inverse_metric_factor",
    }
    conformal = next(
        row
        for row in controls["instances"]
        if row["control_instance_id"] == "conformal_naive_partial"
    )
    assert conformal["adjudication_role"] == (
        "source_diagnostic_without_new_threshold"
    )
    assert conformal["source_evidence"][
        "diagnostic_only_not_guardrail_threshold"
    ] is True


def test_all_sixteen_decisions_and_fourteen_isolated_tamper_controls_pass(
    result,
) -> None:
    assert result["synthesis_decision_count"] == 16
    assert list(result["threshold_checks"]) == [
        row["decision_id"] for row in result["synthesis_decisions"]
    ]
    assert all(result["threshold_checks"].values())
    assert result["synthesis_tamper_control_count"] == 14
    assert all(
        row["fresh_deep_copy_used"] is True
        and row["passed"] is True
        and row["observed_failed_decision_id"]
        == row["expected_failed_decision_id"]
        and row["expected_failed_decision_id"]
        in row["observed_failed_decision_ids"]
        for row in result["synthesis_tamper_controls"]
    )
    assert result["all_decisions_passed"] is True
    assert result["all_thresholds_passed"] is True


@pytest.mark.parametrize(
    ("control_id", "expected_decision"),
    [
        (row[0], row[2]) for row in contract.SYNTHESIS_TAMPER_CONTROLS
    ],
)
def test_each_tamper_mutation_fails_its_intended_decision_in_isolation(
    state,
    control_id: str,
    expected_decision: str,
) -> None:
    mutated = copy.deepcopy(state)
    calculation.TAMPER_MUTATORS[control_id](mutated)
    failures = {
        row["decision_id"]
        for row in calculation.evaluate_synthesis_decisions(mutated)
        if row["passed"] is False
    }
    assert expected_decision in failures
    assert state["source_chains"][0]["artifacts"][0]["sha256"] != "0" * 64


def test_success_result_is_candidate_only_and_matches_report_contract(
    result,
) -> None:
    guardrail = calculation.load_guardrail()[0]
    contract.validate_calculation_result(result, guardrail)
    assert result["calculation_status"] == (
        "executed_candidate_e_repro_pending_independent_review"
    )
    assert result["selected_next_target"] == calculation.RESULT_REVIEW_TARGET
    assert result["claim"] == {
        "primary_label": "E-REPRO",
        "claim_status": "candidate_pending_independent_result_review",
        "claim_ceiling_level": 3,
        "claim_scope": guardrail["claim_ceiling"][
            "allowed_after_successful_review"
        ],
        "review_accepted": False,
        "equation_surface_upgraded": False,
    }
    assert result["boundary"] == guardrail["boundary"]
    assert result["result_review"] == {
        "status": "pending",
        "target": calculation.RESULT_REVIEW_TARGET,
    }


def test_result_is_finite_canonical_and_omits_full_upstream_numeric_rows(
    result,
) -> None:
    encoded = calculation.canonical_json_bytes(result)
    assert encoded.endswith(b"\n") and not encoded.endswith(b"\n\n")
    assert not encoded.startswith(b"\xef\xbb\xbf")
    assert b"\r" not in encoded
    decoded = json.loads(encoded)
    assert calculation._all_finite(decoded)
    assert decoded["source_chain_count"] == 4
    assert "profile_time_resolution_rows" not in decoded
    assert "resolution_aggregates" not in decoded
    assert "negative_controls" not in decoded


def test_write_artifacts_is_path_independent_and_manifest_binds_only_frozen_inputs(
    tmp_path,
) -> None:
    first_output = tmp_path / "one" / "result.json"
    first_manifest = tmp_path / "one" / "manifest.json"
    second_output = tmp_path / "two" / "result.json"
    second_manifest = tmp_path / "two" / "manifest.json"
    first_result, first_binding = calculation.write_artifacts(
        output_path=first_output,
        manifest_path=first_manifest,
    )
    second_result, second_binding = calculation.write_artifacts(
        output_path=second_output,
        manifest_path=second_manifest,
    )
    assert first_result == second_result
    assert first_binding == second_binding
    assert first_output.read_bytes() == second_output.read_bytes()
    assert first_manifest.read_bytes() == second_manifest.read_bytes()
    assert first_binding["output_sha256"] == hashlib.sha256(
        first_output.read_bytes()
    ).hexdigest()
    assert len(first_binding["scientific_input_artifacts"]) == 24
    assert first_binding["ambient_repository_state_serialized"] is False
    assert first_binding["execution_commit_hash_serialized"] is False
    serialized = first_manifest.read_text(encoding="utf-8")
    assert str(tmp_path) not in serialized
    assert "current_branch" not in serialized
    assert "worktree" not in serialized
    guardrail = calculation.load_guardrail()[0]
    contract.validate_calculation_manifest(
        first_binding,
        result=first_result,
        guardrail=guardrail,
        output_sha256=calculation.sha256_file(first_output),
        script_sha256=calculation.sha256_file(
            calculation.REPO_ROOT / calculation.SCRIPT_RELATIVE_PATH
        ),
    )


def test_post_preflight_synthesis_failure_preserves_blocked_artifacts(
    state,
    tmp_path,
) -> None:
    blocked_state = copy.deepcopy(state)
    blocked_state["qualified_source_decisions"][0]["passed"] = False
    output = tmp_path / "blocked" / "result.json"
    manifest = tmp_path / "blocked" / "manifest.json"
    blocked, binding = calculation.write_artifacts(
        output_path=output,
        manifest_path=manifest,
        state=blocked_state,
    )
    assert output.is_file() and manifest.is_file()
    assert blocked["all_decisions_passed"] is False
    assert blocked["calculation_status"] == (
        "executed_blocked_evidence_incompatibility"
    )
    assert blocked["claim"]["primary_label"] == "B-BLOCKED"
    assert blocked["selected_next_target"] == calculation.EVIDENCE_FAILURE_TARGET
    assert blocked["result_review"] == {
        "status": "not_created_synthesis_failure",
        "target": None,
    }
    assert binding["claim_label"] == "B-BLOCKED"
    assert binding["result_review_target"] is None
    contract.validate_calculation_result(blocked, blocked_state["guardrail"])


def test_preflight_failure_creates_no_canonical_execution_artifacts(
    monkeypatch,
    tmp_path,
) -> None:
    output = tmp_path / "result.json"
    manifest = tmp_path / "manifest.json"

    def fail_preflight():
        raise calculation.PreflightError(
            "source_artifact_hash_mismatch", "deterministic source mismatch"
        )

    monkeypatch.setattr(calculation, "preflight_source_family", fail_preflight)
    with pytest.raises(calculation.PreflightError):
        calculation.write_artifacts(
            output_path=output,
            manifest_path=manifest,
        )
    assert not output.exists()
    assert not manifest.exists()


def test_main_preflight_failure_writes_diagnostic_only(
    monkeypatch,
    tmp_path,
) -> None:
    output = tmp_path / "canonical-result.json"
    manifest = tmp_path / "canonical-manifest.json"
    diagnostic = tmp_path / "diagnostic.json"

    def fail_write(**kwargs):
        raise calculation.PreflightError(
            "equation_compendium_hash_mismatch", "compendium boundary mismatch"
        )

    monkeypatch.setattr(calculation, "write_artifacts", fail_write)
    exit_code = calculation.main(
        [
            "--output",
            str(output),
            "--manifest",
            str(manifest),
            "--preflight-diagnostic",
            str(diagnostic),
        ]
    )
    assert exit_code == 2
    assert not output.exists() and not manifest.exists()
    payload = calculation.strict_json_load(diagnostic)
    assert payload["status"] == "preflight_evidence_incompatibility"
    assert payload["primary_label"] == "B-BLOCKED"
    assert payload["error_codes"] == ["equation_compendium_hash_mismatch"]
    assert payload["canonical_result_created"] is False
    assert payload["canonical_manifest_created"] is False
    assert payload["canonical_execution_report_created"] is False
    assert payload["selected_next_target"] == calculation.EVIDENCE_FAILURE_TARGET


@pytest.mark.parametrize(
    "raw",
    [
        b'{"a":1,"a":2}\n',
        b'{"value":NaN}\n',
        b'\xef\xbb\xbf{"value":1}\n',
        b'{"value":1}\r\n',
    ],
)
def test_strict_json_loader_rejects_duplicate_nonfinite_bom_and_crlf(
    tmp_path,
    raw: bytes,
) -> None:
    path = tmp_path / "bad.json"
    path.write_bytes(raw)
    with pytest.raises(ValueError):
        calculation.strict_json_load(path)

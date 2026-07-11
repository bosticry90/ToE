from __future__ import annotations

import copy
import json
import math
from pathlib import Path

import pytest

from formal.python.tools.scalar_multi_background_robustness_reports import (
    COMPENDIUM_SHA256,
    CONTROL_MECHANISMS,
    EVIDENCE_FAILURE_TARGET,
    EXECUTION_TARGET,
    FLAT_EQUATION_ID,
    GUARDRAIL_OUTCOME,
    GUARDRAIL_REPORT_PATH,
    PACKET_SCHEMA_ID,
    REPRODUCIBILITY_FAILURE_TARGET,
    REVIEW_TARGET,
    SOURCE_CHAINS,
    UNIT_LEDGER_TARGET,
    build_guardrail_payload,
    guardrail_main,
    report_json_bytes,
    sha256_path,
    validate_bound_sources,
    validate_guardrail_payload,
)


EXPECTED_MECHANISMS = {
    "off_shell_nonconservation",
    "naive_partial_divergence",
    "inconsistent_connection",
    "curvature_derivative_omission",
    "omitted_tensor_index_connection",
    "omitted_volume_trace_connection",
    "flat_geometry_substitution",
    "incorrect_inverse_metric_factor",
}


def _artifact(chain: dict, role: str) -> dict:
    matches = [
        row for row in chain["artifacts"] if row["artifact_role"] == role
    ]
    assert len(matches) == 1
    return matches[0]


def test_guardrail_freezes_closed_family_lifecycle() -> None:
    payload = build_guardrail_payload()
    validate_guardrail_payload(payload)
    assert payload["schema_id"] == PACKET_SCHEMA_ID
    assert payload["captured_at_utc"] == "2026-07-10T00:00:00Z"
    assert payload["status"] == "prepared_authorizes_execution_only"
    assert payload["packet_result"] == GUARDRAIL_OUTCOME
    assert payload["selected_next_target"] == EXECUTION_TARGET
    assert payload["future_review_target"] == REVIEW_TARGET
    assert payload["failure_targets"] == {
        "execution_evidence_incompatibility": EVIDENCE_FAILURE_TARGET,
        "review_reproducibility_mismatch": REPRODUCIBILITY_FAILURE_TARGET,
    }
    classification = payload["synthesis_classification"]
    assert classification["kind"] == "closed_enumerated_family_evidence_synthesis"
    assert classification["new_pde_calculation"] is False
    assert classification["statistical_sample"] is False
    assert classification["implementation_lineage_independent"] is False
    assert classification["arbitrary_background_generalization_allowed"] is False


def test_all_twenty_four_inputs_are_hash_bound_and_link_checked() -> None:
    payload = build_guardrail_payload()
    validate_bound_sources(payload)
    chains = payload["source_chains"]
    artifacts = [row for chain in chains for row in chain["artifacts"]]
    assert len(chains) == 4
    assert len(artifacts) == 24
    assert len({row["path"] for row in artifacts}) == 24
    assert all(len(row["sha256"]) == 64 for row in artifacts)
    assert all(sha256_path(Path(row["path"])) == row["sha256"] for row in artifacts)
    assert {row["artifact_role"] for row in artifacts} == {
        "guardrail",
        "calculation_script",
        "calculation_result",
        "calculation_manifest",
        "execution_report",
        "independent_review",
    }
    assert len(payload["source_review_result_link_contract"]) == 4
    for chain, link in zip(chains, payload["source_review_result_link_contract"]):
        assert link["chain_id"] == chain["chain_id"]
        assert link["result_review_target"] == chain["review_target"]
        assert link["review_consumed_target"] == chain["review_target"]
        assert link["result_sha256"] == _artifact(
            chain, "calculation_result"
        )["sha256"]
        assert link["review_must_bind_result_hash"] is True
        assert link["review_must_accept_level_3_e_repro"] is True


def test_exact_thirty_seven_upstream_gates_are_enumerated_without_masking() -> None:
    payload = build_guardrail_payload()
    contract = payload["upstream_decision_contract"]
    assert contract["per_chain_counts"] == {
        "minkowski_1plus1": 4,
        "conformal_connection_1plus1": 6,
        "de_sitter_1plus1": 11,
        "warped_2plus1": 16,
    }
    assert contract["total_count"] == 37
    assert len(contract["gate_inventory"]) == 37
    assert len({row["qualified_gate_id"] for row in contract["gate_inventory"]}) == 37
    assert all(row["must_pass_individually"] for row in contract["gate_inventory"])
    assert contract["all_must_pass_individually"] is True
    assert contract["averaging_or_masking_forbidden"] is True
    assert sum(len(chain["upstream_gate_ids"]) for chain in payload["source_chains"]) == 37


def test_typed_background_matrix_preserves_source_heterogeneity() -> None:
    payload = build_guardrail_payload()
    chains = payload["source_chains"]
    assert [row["spacetime_dimension"] for row in chains] == [2, 2, 2, 3]
    assert [row["divergence_component_count"] for row in chains] == [2, 2, 2, 3]
    assert [row["grid_schedule"] for row in chains] == [
        [64, 128, 256, 512],
        [64, 128, 256, 512],
        [64, 128, 256, 512],
        [32, 64, 128, 256],
    ]
    assert chains[-1]["grid_meaning"] == "N x N spatial points"
    assert {row["geometry_class"] for row in chains} == {
        "cartesian_flat_trivial_connection",
        "locally_flat_nontrivial_connection",
        "constant_nonzero_curvature_de_sitter",
        "spatially_varying_signed_curvature_warped",
    }
    assert {row["connection_class"] for row in chains} == {
        "zero_connection",
        "nonzero_connection",
    }
    assert {row["curvature_class"] for row in chains} == {
        "zero_curvature",
        "constant_nonzero_curvature",
        "spatially_varying_signed_curvature_with_zero_crossings",
    }
    reproduction = payload["source_local_policy_contract"][
        "fresh_subprocess_review_status"
    ]
    assert reproduction["warped_2plus1"] == "two_fresh_subprocesses_matched"
    assert all(
        reproduction[chain_id] == "not_recorded_in_legacy_review"
        for chain_id in (
            "minkowski_1plus1",
            "conformal_connection_1plus1",
            "de_sitter_1plus1",
        )
    )


def test_profiles_and_only_defensible_numeric_envelopes_are_frozen() -> None:
    payload = build_guardrail_payload()
    metric = payload["comparable_metric_contract"]
    rows = metric["profile_rows"]
    assert len(rows) == 5
    assert {row["profile_row_id"] for row in rows} == {
        "minkowski_off_shell",
        "conformal_off_shell",
        "de_sitter_off_shell",
        "warped_x_off_shell",
        "warped_y_off_shell",
    }
    assert metric["family_minimum_p_min_reference"] == pytest.approx(
        1.9916550282637009
    )
    assert metric["minimum_allowed_family_p_min"] == 1.8
    assert metric["family_maximum_off_shell_relative_error_reference"] == (
        pytest.approx(0.004010933857743127)
    )
    assert metric["maximum_allowed_family_off_shell_relative_error"] == 0.02
    assert metric["use_as_threshold_envelope_not_performance_ranking"] is True
    comparison = payload["comparison_policy"]
    assert len(comparison["family_envelopes_allowed"]) == 2
    assert {
        "absolute_divergence_error",
        "curvature_magnitude",
        "grid_N",
        "connection_component_count",
        "negative_control_ratio_or_discrepancy",
    } <= set(comparison["cross_background_pooling_forbidden"])
    coverage = payload["coverage_contract"]["profile_coverage_by_chain"]
    assert coverage["warped_2plus1"]["off_shell_y"] == "off_shell_y_mode"
    assert all(
        coverage[chain_id]["off_shell_y"] == "not_applicable_no_y_coordinate"
        for chain_id in (
            "minkowski_1plus1",
            "conformal_connection_1plus1",
            "de_sitter_1plus1",
        )
    )


def test_on_shell_applicability_flat_limit_and_controls_are_source_local() -> None:
    payload = build_guardrail_payload()
    local = payload["source_local_policy_contract"]
    assert local["on_shell_relative_error_against_exact_zero_forbidden"] is True
    assert local["zero_fill_for_not_applicable_forbidden"] is True
    assert local["flat_limit_roles"] == {
        "minkowski_1plus1": "cartesian_baseline_not_a_recovery_test",
        "conformal_connection_1plus1": "source_local_flat_limit_recovery_passed",
        "de_sitter_1plus1": "source_local_flat_limit_recovery_passed",
        "warped_2plus1": "source_local_flat_limit_recovery_passed",
    }
    assert all(
        policy["relative_error_against_zero_allowed"] is False
        for policy in local["on_shell_policies"].values()
    )
    applicability = payload["applicability_typed_local_check_ledger"]
    assert len(applicability) == 4
    assert applicability[0]["curvature_route"] == "not_applicable_flat_baseline"
    assert applicability[2]["patch_or_geometry_safety"] == (
        "applicable_reviewed_patch_domain_safety"
    )
    controls = payload["control_contract"]
    assert controls["instance_count"] == 10
    assert controls["mechanism_count"] == 8
    assert set(controls["mechanism_classes"]) == EXPECTED_MECHANISMS
    assert set(CONTROL_MECHANISMS) == EXPECTED_MECHANISMS
    assert controls["conformal_naive_partial_is_diagnostic_without_new_threshold"] is True
    assert controls["combined_status_is_logical_and_only"] is True


def test_equation_family_mapping_preserves_flat_bridge_and_canonical_row() -> None:
    payload = build_guardrail_payload()
    equation = payload["equation_compendium_boundary"]
    assert sha256_path(Path(equation["path"])) == COMPENDIUM_SHA256
    assert equation["flat_specialization_equation_id"] == FLAT_EQUATION_ID
    assert equation["canonical_covariant_equation_status"] == (
        "ACTIVE_CALCULATION_SURFACE_SCOPED_E_REPRO"
    )
    assert equation["canonical_source_cell_must_remain_unchanged"] is True
    assert equation["equation_row_promotion_authorized"] is False
    mappings = [chain["equation_mapping"] for chain in payload["source_chains"]]
    assert mappings[0]["family_role"] == "flat_specialization_bridge"
    assert mappings[0]["source_equation_id"] == FLAT_EQUATION_ID
    assert all(row["canonical_row_replaced"] is False for row in mappings)
    assert all(
        row["source_equation_id"]
        == equation["canonical_covariant_equation_id"]
        for row in mappings[1:]
    )


def test_exact_sixteen_decisions_and_individual_tamper_controls() -> None:
    payload = build_guardrail_payload()
    decisions = payload["frozen_decisions"]
    assert payload["frozen_decision_count"] == 16
    assert [row["decision_number"] for row in decisions] == list(range(1, 17))
    decision_ids = {row["decision_id"] for row in decisions}
    assert len(decision_ids) == 16
    controls = payload["synthesis_tamper_controls"]
    assert payload["synthesis_tamper_control_count"] == len(controls)
    assert len(controls) >= 12
    assert all(row["must_fail_individually"] for row in controls)
    assert all(row["expected_failed_decision_id"] in decision_ids for row in controls)
    assert {
        "review_hash_tamper",
        "result_hash_tamper",
        "swapped_chain_artifacts",
        "inapplicable_zero_fill",
        "on_shell_relative_error_injection",
        "raw_absolute_error_substitution",
        "nonfinite_injection",
        "degeneracy_language_leak",
        "forbidden_claim_promotion",
    } <= {row["control_id"] for row in controls}


def test_level_three_nonclaims_and_unit_ledger_hard_gate() -> None:
    payload = build_guardrail_payload()
    claim = payload["claim_ceiling"]
    boundary = payload["boundary"]
    assert claim["claim_ladder_level"] == 3
    assert claim["candidate_primary_label"] == "E-REPRO"
    assert claim["execution_status"] == "candidate_pending_independent_review_only"
    assert all(value is True for key, value in claim.items() if key.startswith("not_"))
    forbidden_boolean_keys = (
        "new_pde_solve_authorized",
        "gravity_evolution_claimed",
        "einstein_source_compatibility_claimed",
        "bianchi_compatibility_claimed",
        "qft_gr_seam_admissibility_claimed",
        "qft_gr_seam_closure_claimed",
        "scalar_qft_pillar_recovery_claimed",
        "level_4_or_level_5_claimed",
        "quantum_or_renormalized_stress_energy_claimed",
        "ccft_resumed",
        "C_k_dynamics_claimed",
        "C_k_action_embedding_authorized",
        "master_action_promoted",
    )
    assert all(boundary[key] is False for key in forbidden_boolean_keys)
    assert boundary["unit_ledger_target"] == UNIT_LEDGER_TARGET
    assert boundary["unit_ledger_status"] == "queued_non_live_hard_gate"
    assert boundary["unit_ledger_required_before_stronger_claims"] is True
    language = payload["coverage_contract"]["dimension_language_policy"]
    assert language[
        "warped_2plus1_two_dimensional_Einstein_degeneracy_not_applicable"
    ] is True


def test_builder_returns_independent_payload_and_mutations_are_rejected() -> None:
    payload = build_guardrail_payload()
    original_label = SOURCE_CHAINS[0]["label"]
    payload["source_chains"][0]["label"] = "tampered"
    assert SOURCE_CHAINS[0]["label"] == original_label
    assert build_guardrail_payload()["source_chains"][0]["label"] == original_label
    with pytest.raises(ValueError, match="exact frozen contract"):
        validate_guardrail_payload(payload)


@pytest.mark.parametrize(
    "mutation",
    [
        lambda p: p.__setitem__("selected_next_target", "execute_wrong"),
        lambda p: p["failure_targets"].__setitem__(
            "execution_evidence_incompatibility", "relax_thresholds"
        ),
        lambda p: p["source_chains"].pop(),
        lambda p: p["source_chains"][0]["artifacts"][5].__setitem__(
            "sha256", "0" * 64
        ),
        lambda p: p["source_chains"][1]["artifacts"][2].__setitem__(
            "sha256", "0" * 64
        ),
        lambda p: p["upstream_decision_contract"]["gate_inventory"].pop(),
        lambda p: p["comparable_metric_contract"]["profile_rows"][0].__setitem__(
            "p_min", 0.0
        ),
        lambda p: p["comparable_metric_contract"].__setitem__(
            "family_maximum_off_shell_relative_error_reference", 0.5
        ),
        lambda p: p["source_local_policy_contract"].__setitem__(
            "on_shell_relative_error_against_exact_zero_forbidden", False
        ),
        lambda p: p["applicability_typed_local_check_ledger"][0].__setitem__(
            "curvature_route", 0.0
        ),
        lambda p: p["control_contract"]["instances"].pop(),
        lambda p: p["comparison_policy"]["cross_background_pooling_forbidden"].remove(
            "curvature_magnitude"
        ),
        lambda p: p["frozen_decisions"].pop(),
        lambda p: p["claim_ceiling"].__setitem__("claim_ladder_level", 4),
        lambda p: p["boundary"].__setitem__("master_action_promoted", True),
        lambda p: p["coverage_contract"]["dimension_language_policy"].__setitem__(
            "warped_2plus1_two_dimensional_Einstein_degeneracy_not_applicable",
            False,
        ),
    ],
)
def test_contract_mutations_are_rejected(mutation: object) -> None:
    payload = copy.deepcopy(build_guardrail_payload())
    mutation(payload)  # type: ignore[operator]
    with pytest.raises(ValueError):
        validate_guardrail_payload(payload)


def test_bound_source_validator_rejects_hash_tamper_and_artifact_swap() -> None:
    tampered_hash = build_guardrail_payload()
    tampered_hash["source_chains"][0]["artifacts"][5]["sha256"] = "0" * 64
    with pytest.raises(ValueError, match="bound source artifact mismatch"):
        validate_bound_sources(tampered_hash)

    swapped = build_guardrail_payload()
    first_result = _artifact(swapped["source_chains"][0], "calculation_result")
    second_result = _artifact(swapped["source_chains"][1], "calculation_result")
    first_result["path"], second_result["path"] = (
        second_result["path"],
        first_result["path"],
    )
    first_result["sha256"], second_result["sha256"] = (
        second_result["sha256"],
        first_result["sha256"],
    )
    with pytest.raises(ValueError, match="source gate inventory mismatch"):
        validate_bound_sources(swapped)


def test_report_bytes_are_strict_and_release_artifact_is_deterministic() -> None:
    payload = build_guardrail_payload()
    expected = report_json_bytes(payload)
    assert expected.startswith(b"{\n")
    assert expected.endswith(b"\n") and not expected.endswith(b"\n\n")
    assert b"\r" not in expected
    assert not expected.startswith(b"\xef\xbb\xbf")
    assert GUARDRAIL_REPORT_PATH.read_bytes() == expected
    parsed = json.loads(expected)
    assert parsed == payload


def test_cli_writes_exact_bytes_and_stable_summary(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    output = tmp_path / "guardrail.json"
    assert guardrail_main(["--out", str(output)]) == 0
    assert output.read_bytes() == report_json_bytes(build_guardrail_payload())
    summary = json.loads(capsys.readouterr().out)
    assert summary == {
        "artifact_count": 24,
        "chain_count": 4,
        "decision_count": 16,
        "outcome": GUARDRAIL_OUTCOME,
        "selected_next_target": EXECUTION_TARGET,
    }


def test_nonfinite_payload_cannot_be_serialized() -> None:
    payload = build_guardrail_payload()
    payload["comparable_metric_contract"]["profile_rows"][0]["p_min"] = math.inf
    with pytest.raises(ValueError):
        report_json_bytes(payload)

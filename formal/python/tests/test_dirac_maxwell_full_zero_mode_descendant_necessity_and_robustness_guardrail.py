from __future__ import annotations

from formal.python.tools import dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_guardrail as guardrail


def test_guardrail_artifacts_are_current() -> None:
    packet, manifest, report = guardrail.build_artifacts()
    assert guardrail.PACKET_PATH.read_bytes() == guardrail.canonical_json_bytes(packet)
    assert guardrail.MANIFEST_PATH.read_bytes() == guardrail.canonical_json_bytes(manifest)
    assert guardrail.REPORT_PATH.read_bytes() == guardrail.canonical_json_bytes(report)


def test_accepted_fraction_definition_has_an_admitted_counterexample() -> None:
    audit = guardrail.normalization_audit()
    counterexample = audit["counterexample"]
    assert counterexample["phase_label"] == "POSITIVE_PI_OVER_TWO"
    assert counterexample["f_perp_initial"] > 1.0
    assert counterexample["within_declared_fraction_domain"] is False
    assert audit["bounded_fraction_contract_satisfied"] is False
    assert audit["denominator_positive_definite_established"] is False


def test_counterexample_changes_only_the_admitted_phase_axis() -> None:
    audit = guardrail.normalization_audit()
    fixed = audit["fixed_audit_inputs"]
    assert fixed["grid_size"] == 32
    assert fixed["eta_q"] == 0.2
    assert fixed["mu_mass_domain"] == 1.0
    assert fixed["theta_W"] == 0.3
    assert fixed["varied_axis"] == "DELTA_THETA_PSI"
    assert fixed["reduced_sector_phase_applied_to_components"] == [1, 3]
    assert audit["counterexample_uses_only_admitted_axes"] is True


def test_preparation_blocks_instead_of_redefining_or_freezing() -> None:
    packet = guardrail.build_packet()
    assert packet["blocker_code"] == guardrail.BLOCKER_CODE
    assert packet["accepted_design_reopened"] is False
    assert packet["canonical_result_reopened"] is False
    assert all(value is False for key, value in packet["guardrail_completion"].items() if key != "reason")
    assert packet["authority_boundary"]["pilot_authorized"] is False
    assert packet["authority_boundary"]["canonical_robustness_execution_authorized"] is False
    assert packet["selected_next_target"] == guardrail.REVIEW_TARGET


def test_no_normalization_repair_is_selected_automatically() -> None:
    packet = guardrail.build_packet()
    candidates = packet["repair_route_candidates_for_separate_review"]
    assert len(candidates) == 4
    assert not any(item["selected"] for item in candidates)
    assert packet["post_review_blocker_target_if_confirmed"] == guardrail.REPAIR_TARGET


def test_all_mutations_are_independently_diagnosed() -> None:
    packet = guardrail.build_packet()
    controls = packet["mutation_controls"]
    assert len(controls) == 14
    assert all(item["passed"] for item in controls)
    assert all(item["one_intended_premise_changed"] for item in controls)
    assert all(item["no_unrelated_earlier_failure"] for item in controls)
    assert all(item["actual_diagnostics"] == [item["expected_diagnostic"]] for item in controls)


def test_claim_nonpromotion_and_prompt_preservation() -> None:
    packet = guardrail.build_packet()
    boundary = packet["authority_boundary"]
    assert boundary["canonical_result_remains_accepted_E_REPRO"] is True
    assert boundary["pillar_completion_claimed"] is False
    assert boundary["seam_closure_claimed"] is False
    assert boundary["C_k_dynamics_claimed"] is False
    assert boundary["CCFT_validation_claimed"] is False
    assert boundary["master_action_promotion_claimed"] is False
    assert guardrail.sha256_path(guardrail.REPO_ROOT / guardrail.PROMPT_RELATIVE_PATH) == guardrail.PROMPT_SHA256

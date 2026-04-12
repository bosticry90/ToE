from __future__ import annotations

import json
from pathlib import Path

from formal.python.tests._archived_history_sentinel import split_active_and_archived


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
CHECKLIST_PATH = REPO_ROOT / "Canonical Verification Checklist.md"
DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "GOVERNANCE_AUDIT_PACKET_20260410_v0.md"
PACKET_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_audit_packet_20260410_v0.json"
EXEC_PROGRAM_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "TOE_ENFORCED_EXECUTION_PROGRAM_20260411_v0.md"
)
EXEC_PROGRAM_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "toe_enforced_execution_program_20260411_v0.json"
)
RUNTIME_POLICY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "RUNTIME_MEASUREMENT_INTEGRITY_POLICY_20260411_v0.md"
)
RUNTIME_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "runtime_measurement_integrity_20260411_v0.json"
)
PACKET41_POLICY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "PACKET41_SUCCESSOR_DECISION_ENFORCEMENT_20260411_v0.md"
)
PACKET41_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "packet41_successor_decision_enforcement_20260411_v0.json"
)
D_CONSOLIDATION_POLICY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "GOVERNANCE_SINGLE_SOURCE_CONSOLIDATION_POLICY_20260411_v0.md"
)
D_CONSOLIDATION_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "governance_single_source_consolidation_20260411_v0.json"
)
OBS_POLICY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "GOVERNANCE_SCALE_OBSERVABILITY_POLICY_20260411_v0.md"
)
OBS_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "governance_scale_observability_20260411_v0.json"
)
PARITY_POLICY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "GOVERNANCE_CROSS_PLATFORM_PARITY_POLICY_20260411_v0.md"
)
PARITY_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "governance_cross_platform_parity_20260411_v0.json"
)
SCIENCE_BASELINE_POLICY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "SCIENCE_GLOBAL_COMPLETION_BASELINE_20260411_v0.md"
)
SCIENCE_BASELINE_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "science_global_completion_baseline_20260411_v0.json"
)
THEOREM_WAVE_POLICY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "THEOREM_GAP_REDUCTION_WAVE_20260411_v0.md"
)
THEOREM_WAVE_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_reduction_wave_20260411_v0.json"
)
THEOREM_LINKAGE_POLICY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "THEOREM_GAP_EXECUTION_LINKAGE_20260411_v0.md"
)
THEOREM_LINKAGE_REGISTRY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "THEOREM_GAP_TRANCHE_LINKAGE_REGISTRY_20260411_v0.json"
)
THEOREM_LINKAGE_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_execution_linkage_20260411_v0.json"
)
THEOREM_ROW_TREND_POLICY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "THEOREM_GAP_ROW_OUTCOME_TREND_20260411_v0.md"
)
THEOREM_ROW_TREND_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_row_outcome_trend_20260411_v0.json"
)
THEOREM_SINGLE_ROW_POLICY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "THEOREM_GAP_SINGLE_ROW_EXECUTION_20260411_v0.md"
)
THEOREM_SINGLE_ROW_TRANCHE_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "THEOREM_GAP_SINGLE_ROW_EXECUTION_TRANCHE_20260411_v0.json"
)
THEOREM_SINGLE_ROW_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_single_row_execution_20260411_v0.json"
)
THEOREM_QM_REWORK_POLICY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "THEOREM_GAP_QM_REWORK_TRANCHE_20260411_v0.md"
)
THEOREM_QM_REWORK_TRANCHE_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "THEOREM_GAP_QM_REWORK_TRANCHE_20260411_v0.json"
)
THEOREM_QM_REWORK_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_qm_rework_tranche_20260411_v0.json"
)
THEOREM_QM_SUBTARGET_POLICY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "THEOREM_GAP_QM_SUBTARGET_TRANCHE_20260411_v0.md"
)
THEOREM_QM_SUBTARGET_TRANCHE_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "THEOREM_GAP_QM_SUBTARGET_TRANCHE_20260411_v0.json"
)
THEOREM_QM_SUBTARGET_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "theorem_gap_qm_subtarget_tranche_20260411_v0.json"
)
R0_R6_CLOSEOUT_POLICY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "R0_R6_OBJECTIVE_QUALITY_CLOSEOUT_20260411_v0.md"
)
R0_R6_CLOSEOUT_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "r0_r6_objective_quality_closeout_20260411_v0.json"
)
CLOSEOUT_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "toe_enforced_execution_closeout_20260411_v0.json"
)
GOVERNANCE_SUITE_PATH = REPO_ROOT / "governance_suite.ps1"
CI_PATH = REPO_ROOT / ".github" / "workflows" / "ci.yml"

REQUIRED_BLOCKER_CLASSES = {
    "THEOREM_GAP",
    "SEAM_INTEGRATION_GAP",
    "PARITY_DRIFT",
    "GOVERNANCE_GUARDRAIL",
    "EVIDENCE_ALIGNMENT_GAP",
}

REQUIRED_EXECUTION_RISK_CLASSES = {
    "packet41_seam_closure_blocker",
    "runtime_measurement_fidelity_gap",
    "governance_dual_source_drift",
    "governance_scale_operational_mass",
}

REQUIRED_EXECUTION_PHASE_ORDER = [
    "PHASE_A_PROGRAM_LOCK",
    "PHASE_B_RUNTIME_MEASUREMENT_INTEGRITY",
    "PHASE_C_PACKET41_SUCCESSOR_DECISION_ENFORCEMENT",
    "PHASE_D_GOVERNANCE_SINGLE_SOURCE_CONSOLIDATION",
    "PHASE_E_SCALE_OBSERVABILITY_AND_COST_CONTROL",
    "PHASE_F_CROSS_PLATFORM_PARITY",
    "PHASE_G_CLOSEOUT_AND_AUTHORITY_SYNC",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _active_text(path: Path) -> str:
    active, _ = split_active_and_archived(_read(path), path)
    return active


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_governance_audit_packet_files_exist() -> None:
    assert DECLARATION_PATH.exists(), "Missing governance audit packet declaration."
    assert PACKET_PATH.exists(), "Missing governance audit packet JSON."


def test_toe_enforced_execution_program_files_exist() -> None:
    assert EXEC_PROGRAM_DECLARATION_PATH.exists(), "Missing enforced execution program declaration."
    assert EXEC_PROGRAM_REPORT_PATH.exists(), "Missing enforced execution program report JSON."


def test_toe_enforced_execution_program_contract() -> None:
    declaration_text = _read(EXEC_PROGRAM_DECLARATION_PATH)
    report_payload = _json(EXEC_PROGRAM_REPORT_PATH)

    assert "TOE_ENFORCED_EXECUTION_PROGRAM_20260411_v0" in declaration_text
    assert "ACTIVE_NONLIVE_NONCLAIM" in declaration_text
    assert (
        "formal/output/reports/toe_enforced_execution_program_20260411_v0.json"
        in declaration_text
    )
    assert (
        "formal/python/tests/test_governance_audit_packet_gate.py"
        in declaration_text
    )

    assert report_payload.get("schema_id") == "TOE_ENFORCED_EXECUTION_PROGRAM_20260411_v0"
    assert report_payload.get("status") == "ACTIVE_NONLIVE_NONCLAIM"

    risk_classes = set(report_payload.get("critical_risk_classes", []))
    assert risk_classes == REQUIRED_EXECUTION_RISK_CLASSES

    phase_order = report_payload.get("phase_order", [])
    assert phase_order == REQUIRED_EXECUTION_PHASE_ORDER

    gate_requirements = report_payload.get("phase_gate_requirements", {})
    required_gate_flags = {
        "machine_checkable_artifact_required",
        "explicit_pass_fail_required",
        "fail_closed_on_missing_or_contradictory_evidence",
        "runtime_claim_requires_measured_quality",
        "promotion_requires_blocker_state_change_evidence",
        "authority_update_requires_all_phase_gates",
    }
    assert set(gate_requirements.keys()) == required_gate_flags
    assert all(gate_requirements.values()), "All phase-gate enforcement flags must be true."

    required_pointers = report_payload.get("required_pointers", {})
    assert required_pointers.get("declaration_pointer") == (
        "formal/docs/release/TOE_ENFORCED_EXECUTION_PROGRAM_20260411_v0.md"
    )
    assert required_pointers.get("governance_gate_pointer") == (
        "formal/python/tests/test_governance_audit_packet_gate.py"
    )

    summary = report_payload.get("summary", {})
    assert summary.get("program_lock_active") is True
    assert summary.get("next_phase") == "PHASE_B_RUNTIME_MEASUREMENT_INTEGRITY"
    assert summary.get("execution_mode") == "ENFORCE_THEN_ADVANCE"


def test_toe_enforced_execution_phase_reports_and_closeout() -> None:
    for path in [
        RUNTIME_POLICY_PATH,
        RUNTIME_REPORT_PATH,
        PACKET41_POLICY_PATH,
        PACKET41_REPORT_PATH,
        D_CONSOLIDATION_POLICY_PATH,
        D_CONSOLIDATION_REPORT_PATH,
        OBS_POLICY_PATH,
        OBS_REPORT_PATH,
        PARITY_POLICY_PATH,
        PARITY_REPORT_PATH,
        SCIENCE_BASELINE_POLICY_PATH,
        SCIENCE_BASELINE_REPORT_PATH,
        THEOREM_WAVE_POLICY_PATH,
        THEOREM_WAVE_REPORT_PATH,
        THEOREM_LINKAGE_POLICY_PATH,
        THEOREM_LINKAGE_REGISTRY_PATH,
        THEOREM_LINKAGE_REPORT_PATH,
        THEOREM_ROW_TREND_POLICY_PATH,
        THEOREM_ROW_TREND_REPORT_PATH,
        THEOREM_SINGLE_ROW_POLICY_PATH,
        THEOREM_SINGLE_ROW_TRANCHE_PATH,
        THEOREM_SINGLE_ROW_REPORT_PATH,
        THEOREM_QM_REWORK_POLICY_PATH,
        THEOREM_QM_REWORK_TRANCHE_PATH,
        THEOREM_QM_REWORK_REPORT_PATH,
        THEOREM_QM_SUBTARGET_POLICY_PATH,
        THEOREM_QM_SUBTARGET_TRANCHE_PATH,
        THEOREM_QM_SUBTARGET_REPORT_PATH,
        R0_R6_CLOSEOUT_POLICY_PATH,
        R0_R6_CLOSEOUT_REPORT_PATH,
        CLOSEOUT_REPORT_PATH,
    ]:
        assert path.exists(), f"Missing required phase artifact: {path}"

    runtime_payload = _json(RUNTIME_REPORT_PATH)
    assert runtime_payload.get("schema_id") == "RUNTIME_MEASUREMENT_INTEGRITY_20260411_v0"
    assert runtime_payload.get("summary", {}).get("phase_status") == "COMPLETE"
    runtime_objective = runtime_payload.get("objective_quality", {})
    assert runtime_objective.get("summary", {}).get("phase_status") in {"COMPLETE", "INCOMPLETE"}
    assert set(runtime_objective.get("criteria", {}).keys()) == {
        "sample_count_threshold_satisfied",
        "command_hash_stability_satisfied",
        "runtime_key_coverage_satisfied",
        "runtime_drift_threshold_satisfied",
        "runtime_history_pointer_consistency_satisfied",
    }
    runtime_inputs = runtime_objective.get("inputs", {})
    assert runtime_inputs.get("minimum_sample_count_required") == 3
    assert runtime_inputs.get("maximum_runtime_drift_percent_allowed") == 25.0
    assert isinstance(runtime_inputs.get("runtime_history_pointer"), str)

    packet41_payload = _json(PACKET41_REPORT_PATH)
    assert packet41_payload.get("schema_id") == "PACKET41_SUCCESSOR_DECISION_ENFORCEMENT_20260411_v0"
    assert packet41_payload.get("summary", {}).get("phase_status") == "COMPLETE"
    packet41_objective = packet41_payload.get("objective_quality", {})
    assert packet41_objective.get("summary", {}).get("phase_status") in {"COMPLETE", "INCOMPLETE"}
    assert set(packet41_objective.get("criteria", {}).keys()) == {
        "cycle_outcome_transition_evidenced",
        "cycle02_numeric_values_materialized",
        "cycle02_threshold_profile_consistent",
        "hold_alignment_with_review_failure",
        "cycle01_to_cycle02_admissibility_improved",
    }
    packet41_inputs = packet41_objective.get("inputs", {})
    assert packet41_inputs.get("cycle01_outcome") == "HOLD_RETAINED_DUE_TO_MISSING_ADMISSIBLE_NUMERIC_INPUTS_v0"
    assert packet41_inputs.get("cycle02_outcome") == "HOLD_RETAINED_DUE_TO_REVIEW_LAYER_FAILURE_v0"
    assert isinstance(packet41_inputs.get("cycle02_required_value_keys"), list)

    consolidation_payload = _json(D_CONSOLIDATION_REPORT_PATH)
    assert consolidation_payload.get("schema_id") == "GOVERNANCE_SINGLE_SOURCE_CONSOLIDATION_20260411_v0"
    assert consolidation_payload.get("summary", {}).get("phase_status") == "COMPLETE"
    consolidation_objective = consolidation_payload.get("objective_quality", {})
    assert consolidation_objective.get("summary", {}).get("phase_status") in {"COMPLETE", "INCOMPLETE"}
    assert set(consolidation_objective.get("criteria", {}).keys()) == {
        "selector_count_matches_manifest_expected",
        "selector_hash_matches_manifest_expected",
        "manifest_group_equals_selector_output",
        "selector_output_has_no_duplicates",
    }
    consolidation_inputs = consolidation_objective.get("inputs", {})
    assert isinstance(consolidation_inputs.get("observed_count"), int)
    assert isinstance(consolidation_inputs.get("observed_sha256"), str)

    obs_payload = _json(OBS_REPORT_PATH)
    assert obs_payload.get("schema_id") == "GOVERNANCE_SCALE_OBSERVABILITY_20260411_v0"
    assert obs_payload.get("summary", {}).get("phase_status") == "COMPLETE"
    obs_objective = obs_payload.get("objective_quality", {})
    assert obs_objective.get("summary", {}).get("phase_status") in {"COMPLETE", "INCOMPLETE"}
    assert set(obs_objective.get("criteria", {}).keys()) == {
        "runtime_history_multi_sample_satisfied",
        "percentile_metrics_materialized",
        "budget_breach_analysis_materialized",
        "invalidation_telemetry_quality_satisfied",
        "runtime_flake_proxy_within_bound",
    }
    obs_inputs = obs_objective.get("inputs", {})
    assert obs_inputs.get("minimum_history_samples_required") == 3
    assert isinstance(obs_inputs.get("runtime_cv"), dict)
    assert isinstance(obs_inputs.get("budget_breach_analysis"), dict)

    parity_payload = _json(PARITY_REPORT_PATH)
    assert parity_payload.get("schema_id") == "GOVERNANCE_CROSS_PLATFORM_PARITY_20260411_v0"
    assert parity_payload.get("summary", {}).get("phase_status") == "COMPLETE"
    parity_objective = parity_payload.get("objective_quality", {})
    assert parity_objective.get("summary", {}).get("phase_status") in {"COMPLETE", "INCOMPLETE"}
    parity_inputs = parity_objective.get("inputs", {})
    assert parity_inputs.get("minimum_parity_tests_required") == 10
    assert isinstance(parity_inputs.get("parity_scope_count"), int)

    science_baseline_payload = _json(SCIENCE_BASELINE_REPORT_PATH)
    assert science_baseline_payload.get("schema_id") == "SCIENCE_GLOBAL_COMPLETION_BASELINE_20260411_v0"
    assert science_baseline_payload.get("summary", {}).get("phase_status") == "COMPLETE"
    science_objective = science_baseline_payload.get("objective_quality", {})
    assert science_objective.get("summary", {}).get("phase_status") in {"COMPLETE", "INCOMPLETE"}
    assert set(science_objective.get("criteria", {}).keys()) == {
        "ledger_trend_blocker_counts_consistent",
        "theorem_gap_positive",
        "seam_integration_gap_positive",
        "parity_drift_positive",
        "roadmap_release_gate_truth_pinned",
    }
    completion_assessment = science_baseline_payload.get("completion_assessment", {})
    assert completion_assessment.get("governance_objective_complete") is True
    assert completion_assessment.get("science_global_complete") in {True, False}
    assert completion_assessment.get("global_objective_complete") in {True, False}

    theorem_wave_payload = _json(THEOREM_WAVE_REPORT_PATH)
    assert theorem_wave_payload.get("schema_id") == "THEOREM_GAP_REDUCTION_WAVE_20260411_v0"
    assert theorem_wave_payload.get("summary", {}).get("phase_status") == "COMPLETE"
    theorem_objective = theorem_wave_payload.get("objective_quality", {})
    assert theorem_objective.get("summary", {}).get("phase_status") in {"COMPLETE", "INCOMPLETE"}
    assert set(theorem_objective.get("criteria", {}).keys()) == {
        "theorem_gap_count_reduced",
        "theorem_gap_delta_negative",
        "trend_net_delta_negative",
        "ledger_progress_classification_true_progress",
        "theorem_gap_rows_have_artifact_and_gate_coverage",
    }
    theorem_inputs = theorem_objective.get("inputs", {})
    assert isinstance(theorem_inputs.get("theorem_gap_prior"), int)
    assert isinstance(theorem_inputs.get("theorem_gap_current"), int)
    assert isinstance(theorem_inputs.get("theorem_gap_delta"), int)
    assert isinstance(theorem_inputs.get("theorem_gap_row_ids"), list)

    theorem_linkage_registry = _json(THEOREM_LINKAGE_REGISTRY_PATH)
    assert theorem_linkage_registry.get("schema_id") == "THEOREM_GAP_TRANCHE_LINKAGE_REGISTRY_20260411_v0"
    registry_entries = theorem_linkage_registry.get("entries", [])
    assert isinstance(registry_entries, list)
    assert len(registry_entries) >= 1
    for entry in registry_entries:
        assert isinstance(entry.get("tranche_id"), str) and entry["tranche_id"]
        assert isinstance(entry.get("target_row"), str) and entry["target_row"]
        assert entry.get("expected_blocker_state_change") == "NEGATIVE_THEOREM_GAP_DELTA_REQUIRED"
        assert entry.get("success_threshold") == "THEOREM_GAP_DELTA_LT_0"
        assert entry.get("actual_blocker_state_change") in {
            "NEGATIVE_THEOREM_GAP_DELTA_OBSERVED",
            "NO_CHANGE_OBSERVED",
            "POSITIVE_THEOREM_GAP_DELTA_OBSERVED",
        }
        assert entry.get("outcome_status") in {"SUCCESS", "FAILURE", "NO_CHANGE"}
        if entry.get("outcome_status") == "NO_CHANGE":
            assert entry.get("no_change_rework_route") == "ROUTE_TO_THEOREM_GAP_REWORK"
            assert isinstance(entry.get("rework_evidence_pointer"), str) and entry["rework_evidence_pointer"]
        assert isinstance(entry.get("declaration_pointer"), str) and entry["declaration_pointer"]
        assert isinstance(entry.get("evidence_pointer"), str) and entry["evidence_pointer"]

    tranche_ids = [entry.get("tranche_id") for entry in registry_entries]
    assert len(tranche_ids) == len(set(tranche_ids)), "Each tranche must map to exactly one linkage entry."
    assert "R5-QM-REWORK-001" in tranche_ids
    assert "R6-QM-SUBTARGET-001" in tranche_ids

    theorem_linkage_payload = _json(THEOREM_LINKAGE_REPORT_PATH)
    assert theorem_linkage_payload.get("schema_id") == "THEOREM_GAP_EXECUTION_LINKAGE_20260411_v0"
    assert theorem_linkage_payload.get("summary", {}).get("phase_status") == "COMPLETE"
    theorem_linkage_objective = theorem_linkage_payload.get("objective_quality", {})
    assert theorem_linkage_objective.get("summary", {}).get("phase_status") in {"COMPLETE", "INCOMPLETE"}
    assert theorem_linkage_payload.get("criteria", {}).get("single_target_row_per_tranche_enforced") is True
    assert theorem_linkage_payload.get("criteria", {}).get("no_change_requires_rework_route") is True
    assert set(theorem_linkage_objective.get("criteria", {}).keys()) == {
        "at_least_one_tranche_success_recorded",
        "theorem_gap_count_reduced",
        "theorem_gap_delta_negative",
        "trend_net_delta_negative",
        "ledger_progress_classification_true_progress",
    }
    theorem_linkage_inputs = theorem_linkage_objective.get("inputs", {})
    assert isinstance(theorem_linkage_inputs.get("registry_entry_count"), int)
    assert isinstance(theorem_linkage_inputs.get("covered_theorem_gap_rows"), list)
    assert isinstance(theorem_linkage_inputs.get("success_count"), int)
    assert isinstance(theorem_linkage_inputs.get("failure_count"), int)
    assert isinstance(theorem_linkage_inputs.get("no_change_count"), int)

    theorem_row_trend_payload = _json(THEOREM_ROW_TREND_REPORT_PATH)
    assert theorem_row_trend_payload.get("schema_id") == "THEOREM_GAP_ROW_OUTCOME_TREND_20260411_v0"
    assert theorem_row_trend_payload.get("summary", {}).get("phase_status") == "COMPLETE"
    theorem_row_trend_objective = theorem_row_trend_payload.get("objective_quality", {})
    assert theorem_row_trend_objective.get("summary", {}).get("phase_status") in {"COMPLETE", "INCOMPLETE"}
    assert set(theorem_row_trend_objective.get("criteria", {}).keys()) == {
        "at_least_one_row_has_success",
        "stagnation_rows_empty",
        "all_rows_have_activity",
    }
    theorem_row_trend_inputs = theorem_row_trend_objective.get("inputs", {})
    assert isinstance(theorem_row_trend_inputs.get("row_outcome_counts"), dict)
    assert isinstance(theorem_row_trend_inputs.get("stagnation_rows"), list)
    assert isinstance(theorem_row_trend_inputs.get("rows_with_success"), list)

    theorem_single_row_tranche = _json(THEOREM_SINGLE_ROW_TRANCHE_PATH)
    assert theorem_single_row_tranche.get("schema_id") == "THEOREM_GAP_SINGLE_ROW_EXECUTION_TRANCHE_20260411_v0"
    assert theorem_single_row_tranche.get("target_row") == "ROW-PILLAR-QM-001"
    assert theorem_single_row_tranche.get("expected_blocker_state_change") == "NEGATIVE_THEOREM_GAP_DELTA_REQUIRED"
    assert theorem_single_row_tranche.get("success_threshold") == "THEOREM_GAP_DELTA_LT_0_AND_ROW_SUCCESS_COUNT_GT_0"
    assert theorem_single_row_tranche.get("failure_threshold") == "THEOREM_GAP_DELTA_GE_0_OR_ROW_SUCCESS_COUNT_EQ_0"
    assert theorem_single_row_tranche.get("no_change_fail_closed_policy", {}).get("required") is True
    assert theorem_single_row_tranche.get("no_change_fail_closed_policy", {}).get("route_token") == "ROUTE_TO_THEOREM_GAP_REWORK"

    theorem_single_row_payload = _json(THEOREM_SINGLE_ROW_REPORT_PATH)
    assert theorem_single_row_payload.get("schema_id") == "THEOREM_GAP_SINGLE_ROW_EXECUTION_20260411_v0"
    assert theorem_single_row_payload.get("summary", {}).get("phase_status") == "COMPLETE"
    theorem_single_row_objective = theorem_single_row_payload.get("objective_quality", {})
    assert theorem_single_row_objective.get("summary", {}).get("phase_status") in {"COMPLETE", "INCOMPLETE"}
    assert set(theorem_single_row_objective.get("criteria", {}).keys()) == {
        "target_row_success_observed",
        "theorem_gap_delta_negative",
        "target_row_row_success_count_positive",
        "no_change_fail_closed_route_satisfied",
        "ledger_progress_classification_true_progress",
    }
    theorem_single_row_inputs = theorem_single_row_objective.get("inputs", {})
    assert theorem_single_row_inputs.get("target_row") == "ROW-PILLAR-QM-001"
    assert isinstance(theorem_single_row_inputs.get("target_row_success_count"), int)
    assert isinstance(theorem_single_row_inputs.get("theorem_gap_delta"), int)

    theorem_qm_rework_tranche = _json(THEOREM_QM_REWORK_TRANCHE_PATH)
    assert theorem_qm_rework_tranche.get("schema_id") == "THEOREM_GAP_QM_REWORK_TRANCHE_20260411_v0"
    assert theorem_qm_rework_tranche.get("tranche_id") == "R5-QM-REWORK-001"
    assert theorem_qm_rework_tranche.get("target_row") == "ROW-PILLAR-QM-001"
    assert theorem_qm_rework_tranche.get("expected_blocker_state_change") == "NEGATIVE_THEOREM_GAP_DELTA_REQUIRED"

    theorem_qm_rework_payload = _json(THEOREM_QM_REWORK_REPORT_PATH)
    assert theorem_qm_rework_payload.get("schema_id") == "THEOREM_GAP_QM_REWORK_TRANCHE_20260411_v0"
    assert theorem_qm_rework_payload.get("summary", {}).get("phase_status") == "COMPLETE"
    theorem_qm_rework_objective = theorem_qm_rework_payload.get("objective_quality", {})
    assert theorem_qm_rework_objective.get("summary", {}).get("phase_status") in {"COMPLETE", "INCOMPLETE"}
    assert set(theorem_qm_rework_objective.get("criteria", {}).keys()) == {
        "qm_target_row_success_observed",
        "theorem_gap_delta_negative",
        "target_row_success_count_positive",
        "no_change_fail_closed_route_satisfied",
        "ledger_progress_classification_true_progress",
    }
    theorem_qm_rework_inputs = theorem_qm_rework_objective.get("inputs", {})
    assert theorem_qm_rework_inputs.get("tranche_id") == "R5-QM-REWORK-001"
    assert theorem_qm_rework_inputs.get("target_row") == "ROW-PILLAR-QM-001"
    assert isinstance(theorem_qm_rework_inputs.get("target_row_success_count"), int)
    assert isinstance(theorem_qm_rework_inputs.get("theorem_gap_delta"), int)

    theorem_qm_subtarget_tranche = _json(THEOREM_QM_SUBTARGET_TRANCHE_PATH)
    assert theorem_qm_subtarget_tranche.get("schema_id") == "THEOREM_GAP_QM_SUBTARGET_TRANCHE_20260411_v0"
    assert theorem_qm_subtarget_tranche.get("tranche_id") == "R6-QM-SUBTARGET-001"
    assert theorem_qm_subtarget_tranche.get("target_row") == "ROW-PILLAR-QM-001"
    assert theorem_qm_subtarget_tranche.get("sub_problem") == "QM_PACKET04_THRESHOLD_ALIGNMENT_SUBPROBLEM_v0"
    assert theorem_qm_subtarget_tranche.get("measurable_success_criterion") == (
        "THEOREM_GAP_DELTA_NE_0_OR_TARGET_ROW_SUCCESS_COUNT_INCREMENT"
    )
    assert theorem_qm_subtarget_tranche.get("expected_blocker_transition") == (
        "THEOREM_GAP_REDUCED_BY_AT_LEAST_ONE_OR_ROW_SUCCESS_INCREMENTED"
    )
    assert isinstance(theorem_qm_subtarget_tranche.get("failure_diagnosis"), str)
    assert theorem_qm_subtarget_tranche["failure_diagnosis"]

    theorem_qm_subtarget_payload = _json(THEOREM_QM_SUBTARGET_REPORT_PATH)
    assert theorem_qm_subtarget_payload.get("schema_id") == "THEOREM_GAP_QM_SUBTARGET_TRANCHE_20260411_v0"
    assert theorem_qm_subtarget_payload.get("summary", {}).get("phase_status") == "COMPLETE"
    theorem_qm_subtarget_objective = theorem_qm_subtarget_payload.get("objective_quality", {})
    assert theorem_qm_subtarget_objective.get("summary", {}).get("phase_status") in {"COMPLETE", "INCOMPLETE"}
    assert set(theorem_qm_subtarget_objective.get("criteria", {}).keys()) == {
        "qm_subtarget_success_observed",
        "theorem_gap_delta_changed",
        "target_row_success_count_incremented",
        "no_change_fail_closed_route_satisfied",
        "ledger_progress_classification_true_progress",
    }
    theorem_qm_subtarget_inputs = theorem_qm_subtarget_objective.get("inputs", {})
    assert theorem_qm_subtarget_inputs.get("tranche_id") == "R6-QM-SUBTARGET-001"
    assert theorem_qm_subtarget_inputs.get("target_row") == "ROW-PILLAR-QM-001"
    assert isinstance(theorem_qm_subtarget_inputs.get("theorem_gap_delta"), int)
    assert isinstance(theorem_qm_subtarget_inputs.get("target_row_success_count_incremented"), bool)
    assert isinstance(theorem_qm_subtarget_inputs.get("failure_diagnosis"), str)

    r0_r6_closeout_payload = _json(R0_R6_CLOSEOUT_REPORT_PATH)
    assert r0_r6_closeout_payload.get("schema_id") == "R0_R6_OBJECTIVE_QUALITY_CLOSEOUT_20260411_v0"
    assert r0_r6_closeout_payload.get("summary", {}).get("phase_status") == "COMPLETE"
    assert set(r0_r6_closeout_payload.get("criteria", {}).keys()) == {
        "all_r0_r6_reports_present",
        "all_r0_r6_reports_have_objective_surface",
        "all_r0_r6_contract_surfaces_complete",
        "r2_no_change_fail_closed_route_satisfied",
        "r3_row_stagnation_visibility_materialized",
        "r4_single_row_fail_closed_route_satisfied",
        "r5_qm_rework_fail_closed_route_satisfied",
        "r6_qm_subtarget_failure_diagnosis_materialized",
    }
    completion_assessment = r0_r6_closeout_payload.get("completion_assessment", {})
    assert completion_assessment.get("control_stack_objective_complete") is True
    assert completion_assessment.get("scientific_objective_complete") in {True, False}
    assert completion_assessment.get("global_objective_complete") in {True, False}

    closeout_payload = _json(CLOSEOUT_REPORT_PATH)
    assert closeout_payload.get("schema_id") == "TOE_ENFORCED_EXECUTION_CLOSEOUT_20260411_v0"
    assert closeout_payload.get("summary", {}).get("closeout_status") == "COMPLETE"
    assert closeout_payload.get("summary", {}).get("objective_closeout_status") in {"COMPLETE", "INCOMPLETE"}
    phase_completion = closeout_payload.get("phase_completion", {})
    objective_phase_completion = closeout_payload.get("objective_phase_completion", {})
    required_phases = {
        "PHASE_A_PROGRAM_LOCK",
        "PHASE_B_RUNTIME_MEASUREMENT_INTEGRITY",
        "PHASE_C_PACKET41_SUCCESSOR_DECISION_ENFORCEMENT",
        "PHASE_D_GOVERNANCE_SINGLE_SOURCE_CONSOLIDATION",
        "PHASE_E_SCALE_OBSERVABILITY_AND_COST_CONTROL",
        "PHASE_F_CROSS_PLATFORM_PARITY",
        "PHASE_G_CLOSEOUT_AND_AUTHORITY_SYNC",
    }
    assert set(phase_completion.keys()) == required_phases
    assert set(objective_phase_completion.keys()) == required_phases
    assert all(bool(v) for v in phase_completion.values())


def test_phase_d_and_f_enforcement_surfaces_present() -> None:
    suite_text = _read(GOVERNANCE_SUITE_PATH)
    assert "$governanceGateTokenRegistry" not in suite_text
    assert "manifest-authoritative only" in suite_text

    ci_text = _read(CI_PATH)
    assert "python-governance-linux-parity" in ci_text
    assert "runs-on: ubuntu-latest" in ci_text
    assert "governance_manifest_select --manifest formal/docs/release/GOVERNANCE_TEST_MANIFEST_v1.json --group critical_gates" in ci_text
    assert "governance_manifest_select --manifest formal/docs/release/GOVERNANCE_TEST_MANIFEST_v1.json --group integrity_gates" in ci_text


def test_governance_audit_packet_shape() -> None:
    payload = _json(PACKET_PATH)

    assert payload.get("schema_id") == "GOVERNANCE_AUDIT_PACKET_20260410_v0"
    assert payload.get("status") == "ACTIVE_NONLIVE_NONCLAIM"

    dimensions = payload.get("throughput_dimensions", {})
    assert set(dimensions.keys()) == {"artifact_growth", "evidence_growth", "closure_growth"}
    assert dimensions["closure_growth"].get("governance_decision_role") == "PRIMARY_GATE"

    runtime = payload.get("runtime_baselines", {})
    assert runtime.get("declaration_pointer") == "formal/docs/release/GOVERNANCE_RUNTIME_BASELINE_20260410_v0.md"
    assert runtime.get("report_pointer") == "formal/output/reports/governance_runtime_baseline_20260410_v0.json"
    for runtime_key in [
        "governance_suite_seconds_baseline",
        "branch_health_full_pytest_seconds_baseline",
        "checkpoint_ladder_seconds_baseline",
    ]:
        assert isinstance(runtime.get(runtime_key), (int, float))
        assert runtime[runtime_key] > 0
    budget_policy = runtime.get("budget_policy", {})
    for required_key in [
        "governance_warn_seconds",
        "governance_hard_seconds",
        "branch_health_warn_seconds",
        "branch_health_hard_seconds",
    ]:
        assert required_key in budget_policy
        assert isinstance(budget_policy[required_key], (int, float))

    artifact_snapshot = payload.get("artifact_snapshot", {})
    for required_key in [
        "json_files_under_formal_output",
        "json_files_under_formal_output_reports",
        "baseline_checkpoint_count",
    ]:
        assert required_key in artifact_snapshot
        assert isinstance(artifact_snapshot[required_key], int)
        assert artifact_snapshot[required_key] >= 0

    growth = payload.get("artifact_growth_tracking", {})
    assert growth.get("declaration_pointer") == "formal/docs/release/GOVERNANCE_ARTIFACT_GROWTH_BASELINE_20260410_v0.md"
    assert growth.get("baseline_report_pointer") == "formal/output/reports/governance_artifact_growth_baseline_20260410_v0.json"
    assert growth.get("snapshot_report_pointer") == "formal/output/reports/governance_artifact_growth_snapshot_20260410_v0.json"
    for scope in ["baseline_counts", "current_counts", "delta_vs_baseline"]:
        values = growth.get(scope, {})
        assert isinstance(values, dict)
        for key in [
            "json_files_under_formal_output",
            "json_files_under_formal_output_reports",
        ]:
            assert key in values
            assert isinstance(values[key], int)

    lifecycle_policy = payload.get("artifact_lifecycle_policy", {})
    assert lifecycle_policy.get("declaration_pointer") == "formal/docs/release/ARTIFACT_LIFECYCLE_POLICY_20260410_v0.md"
    assert lifecycle_policy.get("policy_pointer") == "formal/docs/release/ARTIFACT_LIFECYCLE_POLICY_20260410_v0.json"
    assert isinstance(lifecycle_policy.get("retention_policy"), dict)
    assert isinstance(lifecycle_policy.get("family_rules_count"), int)
    assert lifecycle_policy.get("family_rules_count") > 0
    assert lifecycle_policy.get("family_rules_missing_archive_destination_count") == 0
    assert isinstance(lifecycle_policy.get("exemption_classes"), list)
    assert len(lifecycle_policy.get("exemption_classes")) > 0

    closure_map = payload.get("closure_map", {})
    blocker_map = closure_map.get("blocker_count_by_class", {})
    assert set(blocker_map.keys()) == REQUIRED_BLOCKER_CLASSES
    rows_by_blocker = closure_map.get("rows_by_blocker_class", {})
    assert sum(rows_by_blocker.values()) == closure_map.get("rows_total")

    unresolved = closure_map.get("unresolved_blocker_classes", [])
    assert isinstance(unresolved, list)
    for item in unresolved:
        assert item in REQUIRED_BLOCKER_CLASSES

    blocker_to_closure = closure_map.get("blocker_to_closure_map", {})
    assert blocker_to_closure.get("declaration_pointer") == "formal/docs/release/GOVERNANCE_BLOCKER_CLOSURE_MAP_20260410_v0.md"
    assert blocker_to_closure.get("report_pointer") == "formal/output/reports/governance_blocker_closure_map_20260410_v0.json"
    assert blocker_to_closure.get("rows_total") == closure_map.get("rows_total")
    assert blocker_to_closure.get("missing_owner_rows") == []
    mappings = blocker_to_closure.get("mappings", [])
    assert isinstance(mappings, list)
    assert len(mappings) == closure_map.get("rows_total")
    for row in mappings:
        assert row.get("blocker_class") in REQUIRED_BLOCKER_CLASSES
        assert isinstance(row.get("row_id"), str) and row["row_id"]
        assert isinstance(row.get("owning_lane"), str) and row["owning_lane"]
        assert isinstance(row.get("required_closure_artifact"), str) and row["required_closure_artifact"]
        assert isinstance(row.get("required_evidence_surface"), str) and row["required_evidence_surface"]
        assert isinstance(row.get("exit_criterion"), str) and row["exit_criterion"]
        assert isinstance(row.get("closure_gate"), str) and row["closure_gate"]

    owner_assignments = closure_map.get("row_owner_assignments", [])
    assert isinstance(owner_assignments, list)
    assert len(owner_assignments) == closure_map.get("rows_total")
    for row in owner_assignments:
        assert isinstance(row.get("row_id"), str) and row["row_id"]
        assert isinstance(row.get("primary_owner"), str) and row["primary_owner"]
        assert isinstance(row.get("secondary_owner"), str) and row["secondary_owner"]
        assert isinstance(row.get("required_evidence_surface"), str) and row["required_evidence_surface"]
        assert isinstance(row.get("exit_criterion"), str) and row["exit_criterion"]

    owner_coverage = closure_map.get("owner_assignment_coverage", {})
    assert owner_coverage.get("mapped_rows") == closure_map.get("rows_total")
    assert owner_coverage.get("missing_rows") == []
    assert owner_coverage.get("coverage_ratio") == 1.0
    assert owner_coverage.get("owner_map_pointer") == (
        "formal/docs/release/GOVERNANCE_AUDIT_PACKET_CLOSURE_OWNER_MAP_20260410_v0.json"
    )

    rubric = payload.get("risk_delta_rubric", {})
    required_axes = rubric.get("required_axes", [])
    assert set(required_axes) == {
        "runtime_budget_delta",
        "artifact_growth_delta",
        "evidence_growth_delta",
        "closure_growth_delta",
    }

    readiness = payload.get("promotion_readiness", {})
    assert readiness.get("declaration_pointer") == "formal/docs/release/GOVERNANCE_PROMOTION_READINESS_SCORE_20260410_v0.md"
    assert readiness.get("report_pointer") == "formal/output/reports/governance_promotion_readiness_score_20260410_v0.json"
    score = readiness.get("readiness_score_0_to_100")
    assert isinstance(score, (int, float))
    assert 0 <= score <= 100
    assert readiness.get("readiness_status") in {"READY", "CONDITIONAL", "WATCH", "BLOCKED"}
    assert readiness.get("status_rule") == "READY>=85; CONDITIONAL>=65; WATCH>=45; else BLOCKED"
    components = readiness.get("components", {})
    assert isinstance(components, dict)
    for key in [
        "owner_coverage_ratio",
        "blocker_map_coverage_ratio",
        "runtime_health_score",
        "artifact_growth_score",
        "blocker_pressure_score",
        "blocker_delta_bonus",
    ]:
        assert key in components
        assert isinstance(components[key], (int, float))

    action_policy = payload.get("promotion_action_policy", {})
    assert action_policy.get("declaration_pointer") == "formal/docs/release/GOVERNANCE_PROMOTION_READINESS_ACTION_20260410_v0.md"
    assert action_policy.get("report_pointer") == "formal/output/reports/governance_promotion_readiness_action_20260410_v0.json"
    readiness_input = action_policy.get("readiness_input", {})
    assert readiness_input.get("status") == readiness.get("readiness_status")
    assert readiness_input.get("status_rule") == readiness.get("status_rule")
    status_rules = action_policy.get("status_action_rules", {})
    assert set(status_rules.keys()) == {"READY", "CONDITIONAL", "WATCH", "BLOCKED"}
    for rule_name, rule in status_rules.items():
        assert isinstance(rule.get("promotion_allowed"), bool), rule_name
        assert isinstance(rule.get("required_owner_signoff"), list), rule_name
        assert isinstance(rule.get("allowed_tranche_classes"), list), rule_name
        assert isinstance(rule.get("exception_required"), bool), rule_name
        assert "required_exception_artifact" in rule
        assert isinstance(rule.get("action_summary"), str) and rule.get("action_summary")

    current_action = action_policy.get("current_action", {})
    assert current_action.get("status") == readiness.get("readiness_status")
    assert isinstance(current_action.get("promotion_allowed"), bool)
    assert isinstance(current_action.get("required_owner_signoff"), list)
    assert isinstance(current_action.get("allowed_tranche_classes"), list)
    assert isinstance(current_action.get("exception_required"), bool)
    assert "required_exception_artifact" in current_action
    assert isinstance(current_action.get("action_summary"), str) and current_action.get("action_summary")

    freshness = payload.get("freshness_validation", {})
    assert freshness.get("declaration_pointer") == "formal/docs/release/GOVERNANCE_FRESHNESS_SNAPSHOT_20260410_v0.md"
    assert freshness.get("report_pointer") == "formal/output/reports/governance_freshness_snapshot_20260410_v0.json"
    policy = freshness.get("policy", {})
    assert isinstance(policy.get("max_age_seconds"), int)
    assert policy.get("max_age_seconds") > 0
    assert policy.get("stale_input_effect") == "READINESS_INVALID_AND_PROMOTION_NOT_ELIGIBLE"
    sources = freshness.get("sources", {})
    assert isinstance(sources, dict)
    assert set(sources.keys()) == {
        "runtime_baseline",
        "artifact_growth_snapshot",
        "blocker_closure_map",
        "promotion_readiness",
        "promotion_action_policy",
    }
    for source_name, source in sources.items():
        assert isinstance(source.get("report_pointer"), str) and source.get("report_pointer"), source_name
        assert isinstance(source.get("captured_at_utc"), str) and source.get("captured_at_utc"), source_name
        assert isinstance(source.get("age_seconds"), int), source_name
        assert source.get("age_seconds") >= 0, source_name
        assert isinstance(source.get("max_age_seconds"), int), source_name
        assert isinstance(source.get("is_fresh"), bool), source_name
    summary = freshness.get("freshness_summary", {})
    assert summary.get("freshness_status") == "FRESH"
    assert summary.get("all_required_inputs_fresh") is True
    assert summary.get("stale_inputs") == []
    assert summary.get("readiness_inputs_valid") is True
    assert summary.get("promotion_eligibility_from_freshness") is True

    trend = payload.get("blocker_trend_window", {})
    assert trend.get("declaration_pointer") == "formal/docs/release/GOVERNANCE_BLOCKER_TREND_WINDOW_20260410_v0.md"
    assert trend.get("report_pointer") == "formal/output/reports/governance_blocker_trend_window_20260410_v0.json"
    window = trend.get("window", {})
    assert isinstance(window, dict)
    assert isinstance(window.get("start"), str) and window.get("start")
    assert isinstance(window.get("end"), str) and window.get("end")
    assert isinstance(trend.get("tranche_id"), str) and trend.get("tranche_id")
    blocker_counts = trend.get("blocker_counts", {})
    assert isinstance(blocker_counts.get("prior"), dict)
    assert isinstance(blocker_counts.get("current"), dict)
    assert isinstance(blocker_counts.get("net_delta"), int)
    trend_summary = trend.get("trend_summary", {})
    assert trend_summary.get("movement_status") in {"DECREASING", "FLAT", "INCREASING"}
    assert trend_summary.get("movement_rule") == "NET_DELTA_LT_0_IS_PROGRESS_NET_DELTA_GE_0_REQUIRES_EXCEPTION"
    exception_requirement = trend.get("exception_requirement", {})
    assert isinstance(exception_requirement.get("exception_required"), bool)
    if blocker_counts.get("net_delta", 0) >= 0:
        assert exception_requirement.get("exception_required") is True
        pointer = exception_requirement.get("exception_artifact_pointer")
        assert isinstance(pointer, str) and pointer
    else:
        assert exception_requirement.get("exception_required") is False

    closeout = payload.get("operational_closeout", {})
    assert closeout.get("declaration_pointer") == "formal/docs/release/GOVERNANCE_OPERATIONAL_REFINEMENT_CLOSEOUT_20260410_v0.md"
    assert closeout.get("report_pointer") == "formal/output/reports/governance_operational_refinement_closeout_20260410_v0.json"
    closeout_rule = closeout.get("closeout_rule", {})
    assert closeout_rule.get("rule_id") == "AUDIT_PACKET_OPERATIONAL_REFINEMENT_CLOSEOUT_v0"
    required_sections = closeout_rule.get("required_packet_sections", [])
    assert isinstance(required_sections, list)
    assert set(required_sections) == {
        "runtime_baselines",
        "artifact_growth_tracking",
        "artifact_lifecycle_policy",
        "closure_map",
        "promotion_readiness",
        "promotion_action_policy",
        "freshness_validation",
        "blocker_trend_window",
    }
    criteria = closeout.get("criteria", {})
    assert isinstance(criteria, dict)
    for key in [
        "required_packet_sections_present",
        "readiness_action_policy_present",
        "freshness_enforcement_present",
        "blocker_trend_enforcement_present",
        "governance_and_checkpoint_green",
        "clean_tree_now",
        "synced_with_origin_main_now",
    ]:
        assert key in criteria
        assert isinstance(criteria[key], bool)
    summary = closeout.get("summary", {})
    assert isinstance(summary.get("all_criteria_satisfied"), bool)
    assert summary.get("closeout_status") in {"COMPLETE", "INCOMPLETE"}
    assert summary.get("next_action") in {"MAINTENANCE_MODE", "CONTINUE_REFINEMENT_OR_FINALIZE_ANCHOR"}


def test_governance_audit_packet_state_and_checklist_tokens_present() -> None:
    state_text = _active_text(STATE_PATH)
    checklist_text = _read(CHECKLIST_PATH)

    state_required = [
        "GOVERNANCE_AUDIT_PACKET_DECLARATION_v0: formal/docs/release/GOVERNANCE_AUDIT_PACKET_20260410_v0.md",
        "GOVERNANCE_AUDIT_PACKET_JSON_v0: formal/output/reports/governance_audit_packet_20260410_v0.json",
        "GOVERNANCE_AUDIT_PACKET_DIMENSION_RULE_v0: SEPARATE_ARTIFACT_GROWTH_EVIDENCE_GROWTH_AND_CLOSURE_GROWTH",
        "GOVERNANCE_AUDIT_PACKET_ARTIFACT_LIFECYCLE_POLICY_DECLARATION_v0: formal/docs/release/ARTIFACT_LIFECYCLE_POLICY_20260410_v0.md",
        "GOVERNANCE_AUDIT_PACKET_ARTIFACT_LIFECYCLE_POLICY_JSON_v0: formal/docs/release/ARTIFACT_LIFECYCLE_POLICY_20260410_v0.json",
        "GOVERNANCE_AUDIT_PACKET_CLOSURE_OWNER_MAP_JSON_v0: formal/docs/release/GOVERNANCE_AUDIT_PACKET_CLOSURE_OWNER_MAP_20260410_v0.json",
        "GOVERNANCE_AUDIT_PACKET_RUNTIME_BASELINE_DECLARATION_v0: formal/docs/release/GOVERNANCE_RUNTIME_BASELINE_20260410_v0.md",
        "GOVERNANCE_AUDIT_PACKET_RUNTIME_BASELINE_JSON_v0: formal/output/reports/governance_runtime_baseline_20260410_v0.json",
        "GOVERNANCE_AUDIT_PACKET_RUNTIME_CAPTURE_TOOL_v0: formal/python/tools/governance_runtime_baseline_capture.py",
        "GOVERNANCE_AUDIT_PACKET_ARTIFACT_GROWTH_DECLARATION_v0: formal/docs/release/GOVERNANCE_ARTIFACT_GROWTH_BASELINE_20260410_v0.md",
        "GOVERNANCE_AUDIT_PACKET_ARTIFACT_GROWTH_BASELINE_JSON_v0: formal/output/reports/governance_artifact_growth_baseline_20260410_v0.json",
        "GOVERNANCE_AUDIT_PACKET_ARTIFACT_GROWTH_SNAPSHOT_JSON_v0: formal/output/reports/governance_artifact_growth_snapshot_20260410_v0.json",
        "GOVERNANCE_AUDIT_PACKET_ARTIFACT_GROWTH_SNAPSHOT_TOOL_v0: formal/python/tools/governance_artifact_growth_snapshot.py",
        "GOVERNANCE_AUDIT_PACKET_BLOCKER_CLOSURE_MAP_DECLARATION_v0: formal/docs/release/GOVERNANCE_BLOCKER_CLOSURE_MAP_20260410_v0.md",
        "GOVERNANCE_AUDIT_PACKET_BLOCKER_CLOSURE_MAP_JSON_v0: formal/output/reports/governance_blocker_closure_map_20260410_v0.json",
        "GOVERNANCE_AUDIT_PACKET_BLOCKER_CLOSURE_MAP_TOOL_v0: formal/python/tools/governance_blocker_closure_map_generate.py",
        "GOVERNANCE_AUDIT_PACKET_PROMOTION_READINESS_DECLARATION_v0: formal/docs/release/GOVERNANCE_PROMOTION_READINESS_SCORE_20260410_v0.md",
        "GOVERNANCE_AUDIT_PACKET_PROMOTION_READINESS_JSON_v0: formal/output/reports/governance_promotion_readiness_score_20260410_v0.json",
        "GOVERNANCE_AUDIT_PACKET_PROMOTION_READINESS_TOOL_v0: formal/python/tools/governance_promotion_readiness_score.py",
        "GOVERNANCE_AUDIT_PACKET_PROMOTION_READINESS_STATUS_RULE_v0: READY_GE_85_CONDITIONAL_GE_65_WATCH_GE_45_ELSE_BLOCKED",
        "GOVERNANCE_AUDIT_PACKET_PROMOTION_ACTION_POLICY_DECLARATION_v0: formal/docs/release/GOVERNANCE_PROMOTION_READINESS_ACTION_20260410_v0.md",
        "GOVERNANCE_AUDIT_PACKET_PROMOTION_ACTION_POLICY_JSON_v0: formal/output/reports/governance_promotion_readiness_action_20260410_v0.json",
        "GOVERNANCE_AUDIT_PACKET_PROMOTION_ACTION_POLICY_TOOL_v0: formal/python/tools/governance_promotion_readiness_action.py",
        "GOVERNANCE_AUDIT_PACKET_PROMOTION_ACTION_POLICY_RULE_v0: BLOCKED_DISALLOWS_PROMOTION_CONDITIONAL_IS_LIMITED_READY_IS_ALLOWED_WATCH_BLOCKED_REQUIRE_EXCEPTION_POINTERS",
        "GOVERNANCE_AUDIT_PACKET_FRESHNESS_DECLARATION_v0: formal/docs/release/GOVERNANCE_FRESHNESS_SNAPSHOT_20260410_v0.md",
        "GOVERNANCE_AUDIT_PACKET_FRESHNESS_JSON_v0: formal/output/reports/governance_freshness_snapshot_20260410_v0.json",
        "GOVERNANCE_AUDIT_PACKET_FRESHNESS_TOOL_v0: formal/python/tools/governance_freshness_snapshot.py",
        "GOVERNANCE_AUDIT_PACKET_FRESHNESS_RULE_v0: STALE_INPUTS_INVALIDATE_READINESS_AND_PROMOTION_ELIGIBILITY",
        "GOVERNANCE_AUDIT_PACKET_BLOCKER_TREND_DECLARATION_v0: formal/docs/release/GOVERNANCE_BLOCKER_TREND_WINDOW_20260410_v0.md",
        "GOVERNANCE_AUDIT_PACKET_BLOCKER_TREND_JSON_v0: formal/output/reports/governance_blocker_trend_window_20260410_v0.json",
        "GOVERNANCE_AUDIT_PACKET_BLOCKER_TREND_TOOL_v0: formal/python/tools/governance_blocker_trend_window.py",
        "GOVERNANCE_AUDIT_PACKET_BLOCKER_TREND_RULE_v0: NET_DELTA_LT_0_IS_PROGRESS_NET_DELTA_GE_0_REQUIRES_EXCEPTION",
        "GOVERNANCE_AUDIT_PACKET_OPERATIONAL_CLOSEOUT_DECLARATION_v0: formal/docs/release/GOVERNANCE_OPERATIONAL_REFINEMENT_CLOSEOUT_20260410_v0.md",
        "GOVERNANCE_AUDIT_PACKET_OPERATIONAL_CLOSEOUT_JSON_v0: formal/output/reports/governance_operational_refinement_closeout_20260410_v0.json",
        "GOVERNANCE_AUDIT_PACKET_OPERATIONAL_CLOSEOUT_TOOL_v0: formal/python/tools/governance_operational_closeout.py",
        "GOVERNANCE_AUDIT_PACKET_OPERATIONAL_CLOSEOUT_RULE_v0: ALL_REQUIRED_CRITERIA_MUST_BE_TRUE_FOR_COMPLETE",
        "GOVERNANCE_AUDIT_PACKET_OWNER_COVERAGE_RULE_v0: EVERY_COMPLETION_ROW_REQUIRES_PRIMARY_AND_SECONDARY_OWNER_ASSIGNMENT",
        "GOVERNANCE_AUDIT_PACKET_GATE_v0: formal/python/tests/test_governance_audit_packet_gate.py",
    ]
    for token in state_required:
        assert token in state_text, f"Missing state token: {token}"

    checklist_required = [
        "Governance audit packet pointer declared? YES / NO",
        "Governance runtime baseline recorded? YES / NO",
        "Branch-health runtime baseline recorded? YES / NO",
        "Artifact/evidence/closure dimensions separated? YES / NO",
        "Artifact lifecycle policy pointer declared? YES / NO",
        "Artifact family retention and archive thresholds pinned? YES / NO",
        "Closure owner map pointer declared? YES / NO",
        "Every closure row has primary and secondary owner? YES / NO",
        "Closure-growth delta recorded? YES / NO",
        "Blocker-to-closure map declaration pointer declared? YES / NO",
        "Blocker-to-closure map report pointer declared? YES / NO",
        "Blocker-to-closure map includes blocker class plus owning row/lane? YES / NO",
        "Blocker-to-closure map includes required closure artifact and exit criterion? YES / NO",
        "Promotion-readiness declaration pointer declared? YES / NO",
        "Promotion-readiness report pointer declared? YES / NO",
        "Promotion-readiness score recorded? YES / NO",
        "Promotion-readiness status recorded? YES / NO",
        "Promotion-readiness status rule applied? YES / NO",
        "Promotion-action policy declaration pointer declared? YES / NO",
        "Promotion-action policy report pointer declared? YES / NO",
        "Promotion-action policy status mapping exhaustive? YES / NO",
        "Promotion-action policy enforced for current readiness status? YES / NO",
        "Freshness snapshot declaration pointer declared? YES / NO",
        "Freshness snapshot report pointer declared? YES / NO",
        "Freshness budgets applied to all required inputs? YES / NO",
        "Stale inputs invalidate readiness and promotion eligibility? YES / NO",
        "Blocker trend window declaration pointer declared? YES / NO",
        "Blocker trend window report pointer declared? YES / NO",
        "Blocker trend movement status recorded? YES / NO",
        "Flat or increasing blocker trend requires exception artifact? YES / NO",
        "Operational closeout declaration pointer declared? YES / NO",
        "Operational closeout report pointer declared? YES / NO",
        "Operational closeout criteria recorded and typed? YES / NO",
        "Operational closeout complete only when all criteria true? YES / NO",
    ]
    for token in checklist_required:
        assert token in checklist_text, f"Missing checklist token: {token}"

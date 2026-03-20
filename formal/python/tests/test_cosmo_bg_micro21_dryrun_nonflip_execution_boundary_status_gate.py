from __future__ import annotations

from cosmo_nonflip_gate_family_helper import CosmoNonflipGateSpec, register_cosmo_nonflip_gate_suite


register_cosmo_nonflip_gate_suite(
    globals(),
    CosmoNonflipGateSpec(
        micro_id="21",
        micro_doc_relative_path="formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_21_DRYRUN_NONFLIP_EXECUTION_BOUNDARY_STATUS_v0.md",
        artifact_relative_path="formal/output/cosmo_bg_micro21_dryrun_nonflip_execution_boundary_status_cycle01_v0.json",
        gate_relative_path="formal/python/tests/test_cosmo_bg_micro21_dryrun_nonflip_execution_boundary_status_gate.py",
        target_required_tokens=(
            "TARGET-COSMO-BG-MICRO-21-DRYRUN-NONFLIP-EXECUTION-BOUNDARY-STATUS-v0",
            "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_21_DRYRUN_NONFLIP_EXECUTION_BOUNDARY_STATUS_v0.md",
            "formal/output/cosmo_bg_micro21_dryrun_nonflip_execution_boundary_status_cycle01_v0.json",
            "formal/python/tests/test_cosmo_bg_micro21_dryrun_nonflip_execution_boundary_status_gate.py",
        ),
        doc_required_tokens=(
            "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_21_DRYRUN_NONFLIP_EXECUTION_BOUNDARY_STATUS_v0",
            "TARGET-COSMO-BG-MICRO-21-DRYRUN-NONFLIP-EXECUTION-BOUNDARY-STATUS-v0",
            "COSMO_BG_MICRO21_DRYRUN_NONFLIP_EXECUTION_BOUNDARY_STATUS_ADJUDICATION: NOT_YET_DISCHARGED",
            "COSMO_BG_MICRO21_SCOPE_BOUNDARY_v0: DRYRUN_NONFLIP_EXECUTION_BOUNDARY_STATUS_ONLY_NONCLAIM",
            "COSMO_BG_MICRO21_PROGRESS_v0: DRYRUN_NONFLIP_EXECUTION_BOUNDARY_STATUS_TOKEN_PINNED",
            "COSMO_BG_MICRO21_DRYRUN_NONFLIP_EXECUTION_BOUNDARY_STATUS_ARTIFACT_v0: cosmo_bg_micro21_dryrun_nonflip_execution_boundary_status_cycle01_v0",
            "COSMO_DRYRUN_NONFLIP_EXECUTION_BOUNDARY_STATUS_POLICY_v0: CYCLE08_09_10_11_12_13_14_15_16_17_18_19_20_DRYRUN_NONFLIP_EXECUTION_BOUNDARY_LOCK_REQUIRED_NO_STATUS_FLIP_NO_COMPARATOR_AUTHORIZATION",
            "dryrun_nonflip_execution_boundary_status_policy: CYCLE08_09_10_11_12_13_14_15_16_17_18_19_20_DRYRUN_NONFLIP_EXECUTION_BOUNDARY_LOCK_REQUIRED_NO_STATUS_FLIP_NO_COMPARATOR_AUTHORIZATION",
            "dryrun_nonflip_execution_boundary_status_gate: formal/python/tests/test_cosmo_bg_micro21_dryrun_nonflip_execution_boundary_status_gate.py",
        ),
        expected_artifact_id="cosmo_bg_micro21_dryrun_nonflip_execution_boundary_status_cycle01_v0",
        expected_cycle="CYCLE-021",
        expected_boundary_statement="DRYRUN_NONFLIP_LANE_ONLY_NO_ADJUDICATION_FLIP_NO_COMPARATOR_AUTHORIZATION",
        matrix_doc_key="dryrun_nonflip_execution_boundary_status_doc",
        matrix_gate_key="dryrun_nonflip_execution_boundary_status_gate",
        matrix_policy_key="dryrun_nonflip_execution_boundary_status_policy",
        matrix_policy_value="CYCLE08_09_10_11_12_13_14_15_16_17_18_19_20_DRYRUN_NONFLIP_EXECUTION_BOUNDARY_LOCK_REQUIRED_NO_STATUS_FLIP_NO_COMPARATOR_AUTHORIZATION",
        state_required_tokens=(
            "COSMO_DRYRUN_NONFLIP_EXECUTION_BOUNDARY_STATUS_POLICY_v0: CYCLE08_09_10_11_12_13_14_15_16_17_18_19_20_DRYRUN_NONFLIP_EXECUTION_BOUNDARY_LOCK_REQUIRED_NO_STATUS_FLIP_NO_COMPARATOR_AUTHORIZATION",
            "formal/python/tests/test_cosmo_bg_micro21_dryrun_nonflip_execution_boundary_status_gate.py",
        ),
        rollup_required_tokens=(
            "dryrun_nonflip_execution_boundary_status_doc",
            "dryrun_nonflip_execution_boundary_status_gate",
            "dryrun_nonflip_execution_boundary_status_policy",
            "COSMO_DRYRUN_NONFLIP_EXECUTION_BOUNDARY_STATUS_POLICY_v0",
        ),
    ),
)
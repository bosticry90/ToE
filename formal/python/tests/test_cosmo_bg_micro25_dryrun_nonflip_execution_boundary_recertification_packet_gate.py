from __future__ import annotations

from cosmo_nonflip_gate_family_helper import CosmoNonflipGateSpec, register_cosmo_nonflip_gate_suite


register_cosmo_nonflip_gate_suite(
    globals(),
    CosmoNonflipGateSpec(
        micro_id="25",
        micro_doc_relative_path="formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_25_DRYRUN_NONFLIP_EXECUTION_BOUNDARY_RECERTIFICATION_PACKET_v0.md",
        artifact_relative_path="formal/output/cosmo_bg_micro25_dryrun_nonflip_execution_boundary_recertification_packet_cycle01_v0.json",
        gate_relative_path="formal/python/tests/test_cosmo_bg_micro25_dryrun_nonflip_execution_boundary_recertification_packet_gate.py",
        target_required_tokens=(
            "TARGET-COSMO-BG-MICRO-25-DRYRUN-NONFLIP-EXECUTION-BOUNDARY-RECERTIFICATION-PACKET-v0",
            "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_25_DRYRUN_NONFLIP_EXECUTION_BOUNDARY_RECERTIFICATION_PACKET_v0.md",
            "formal/output/cosmo_bg_micro25_dryrun_nonflip_execution_boundary_recertification_packet_cycle01_v0.json",
            "formal/python/tests/test_cosmo_bg_micro25_dryrun_nonflip_execution_boundary_recertification_packet_gate.py",
        ),
        doc_required_tokens=(
            "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_25_DRYRUN_NONFLIP_EXECUTION_BOUNDARY_RECERTIFICATION_PACKET_v0",
            "TARGET-COSMO-BG-MICRO-25-DRYRUN-NONFLIP-EXECUTION-BOUNDARY-RECERTIFICATION-PACKET-v0",
            "COSMO_BG_MICRO25_DRYRUN_NONFLIP_EXECUTION_BOUNDARY_RECERTIFICATION_PACKET_ADJUDICATION: NOT_YET_DISCHARGED",
            "COSMO_BG_MICRO25_SCOPE_BOUNDARY_v0: DRYRUN_NONFLIP_EXECUTION_BOUNDARY_RECERTIFICATION_PACKET_ONLY_NONCLAIM",
            "COSMO_BG_MICRO25_PROGRESS_v0: DRYRUN_NONFLIP_EXECUTION_BOUNDARY_RECERTIFICATION_PACKET_TOKEN_PINNED",
            "COSMO_BG_MICRO25_DRYRUN_NONFLIP_EXECUTION_BOUNDARY_RECERTIFICATION_PACKET_ARTIFACT_v0: cosmo_bg_micro25_dryrun_nonflip_execution_boundary_recertification_packet_cycle01_v0",
            "COSMO_DRYRUN_NONFLIP_EXECUTION_BOUNDARY_RECERTIFICATION_PACKET_POLICY_v0: CYCLE08_09_10_11_12_13_14_15_16_17_18_19_20_21_22_23_24_DRYRUN_NONFLIP_EXECUTION_BOUNDARY_RECERTIFICATION_LOCK_REQUIRED_NO_STATUS_FLIP_NO_COMPARATOR_AUTHORIZATION",
            "dryrun_nonflip_execution_boundary_recertification_packet_policy: CYCLE08_09_10_11_12_13_14_15_16_17_18_19_20_21_22_23_24_DRYRUN_NONFLIP_EXECUTION_BOUNDARY_RECERTIFICATION_LOCK_REQUIRED_NO_STATUS_FLIP_NO_COMPARATOR_AUTHORIZATION",
            "dryrun_nonflip_execution_boundary_recertification_packet_gate: formal/python/tests/test_cosmo_bg_micro25_dryrun_nonflip_execution_boundary_recertification_packet_gate.py",
        ),
        expected_artifact_id="cosmo_bg_micro25_dryrun_nonflip_execution_boundary_recertification_packet_cycle01_v0",
        expected_cycle="CYCLE-025",
        expected_boundary_statement="DRYRUN_NONFLIP_LANE_ONLY_EXECUTION_BOUNDARY_RECERTIFICATION_NO_ADJUDICATION_FLIP_NO_COMPARATOR_AUTHORIZATION",
        matrix_doc_key="dryrun_nonflip_execution_boundary_recertification_packet_doc",
        matrix_gate_key="dryrun_nonflip_execution_boundary_recertification_packet_gate",
        matrix_policy_key="dryrun_nonflip_execution_boundary_recertification_packet_policy",
        matrix_policy_value="CYCLE08_09_10_11_12_13_14_15_16_17_18_19_20_21_22_23_24_DRYRUN_NONFLIP_EXECUTION_BOUNDARY_RECERTIFICATION_LOCK_REQUIRED_NO_STATUS_FLIP_NO_COMPARATOR_AUTHORIZATION",
        state_required_tokens=(
            "COSMO_DRYRUN_NONFLIP_EXECUTION_BOUNDARY_RECERTIFICATION_PACKET_POLICY_v0: CYCLE08_09_10_11_12_13_14_15_16_17_18_19_20_21_22_23_24_DRYRUN_NONFLIP_EXECUTION_BOUNDARY_RECERTIFICATION_LOCK_REQUIRED_NO_STATUS_FLIP_NO_COMPARATOR_AUTHORIZATION",
            "formal/python/tests/test_cosmo_bg_micro25_dryrun_nonflip_execution_boundary_recertification_packet_gate.py",
        ),
        rollup_required_tokens=(
            "dryrun_nonflip_execution_boundary_recertification_packet_doc",
            "dryrun_nonflip_execution_boundary_recertification_packet_gate",
            "dryrun_nonflip_execution_boundary_recertification_packet_policy",
            "COSMO_DRYRUN_NONFLIP_EXECUTION_BOUNDARY_RECERTIFICATION_PACKET_POLICY_v0",
        ),
    ),
)

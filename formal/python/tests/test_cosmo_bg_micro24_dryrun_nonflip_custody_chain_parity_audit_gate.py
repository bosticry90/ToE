from __future__ import annotations

from cosmo_nonflip_gate_family_helper import CosmoNonflipGateSpec, register_cosmo_nonflip_gate_suite


register_cosmo_nonflip_gate_suite(
    globals(),
    CosmoNonflipGateSpec(
        micro_id="24",
        micro_doc_relative_path="formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_24_DRYRUN_NONFLIP_CUSTODY_CHAIN_PARITY_AUDIT_v0.md",
        artifact_relative_path="formal/output/cosmo_bg_micro24_dryrun_nonflip_custody_chain_parity_audit_cycle01_v0.json",
        gate_relative_path="formal/python/tests/test_cosmo_bg_micro24_dryrun_nonflip_custody_chain_parity_audit_gate.py",
        target_required_tokens=(
            "TARGET-COSMO-BG-MICRO-24-DRYRUN-NONFLIP-CUSTODY-CHAIN-PARITY-AUDIT-v0",
            "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_24_DRYRUN_NONFLIP_CUSTODY_CHAIN_PARITY_AUDIT_v0.md",
            "formal/output/cosmo_bg_micro24_dryrun_nonflip_custody_chain_parity_audit_cycle01_v0.json",
            "formal/python/tests/test_cosmo_bg_micro24_dryrun_nonflip_custody_chain_parity_audit_gate.py",
        ),
        doc_required_tokens=(
            "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_24_DRYRUN_NONFLIP_CUSTODY_CHAIN_PARITY_AUDIT_v0",
            "TARGET-COSMO-BG-MICRO-24-DRYRUN-NONFLIP-CUSTODY-CHAIN-PARITY-AUDIT-v0",
            "COSMO_BG_MICRO24_DRYRUN_NONFLIP_CUSTODY_CHAIN_PARITY_AUDIT_ADJUDICATION: NOT_YET_DISCHARGED",
            "COSMO_BG_MICRO24_SCOPE_BOUNDARY_v0: DRYRUN_NONFLIP_CUSTODY_CHAIN_PARITY_AUDIT_ONLY_NONCLAIM",
            "COSMO_BG_MICRO24_PROGRESS_v0: DRYRUN_NONFLIP_CUSTODY_CHAIN_PARITY_AUDIT_TOKEN_PINNED",
            "COSMO_BG_MICRO24_DRYRUN_NONFLIP_CUSTODY_CHAIN_PARITY_AUDIT_ARTIFACT_v0: cosmo_bg_micro24_dryrun_nonflip_custody_chain_parity_audit_cycle01_v0",
            "COSMO_DRYRUN_NONFLIP_CUSTODY_CHAIN_PARITY_AUDIT_POLICY_v0: CYCLE08_09_10_11_12_13_14_15_16_17_18_19_20_21_22_23_DRYRUN_NONFLIP_CUSTODY_CHAIN_PARITY_AUDIT_LOCK_REQUIRED_NO_STATUS_FLIP_NO_COMPARATOR_AUTHORIZATION",
            "dryrun_nonflip_custody_chain_parity_audit_policy: CYCLE08_09_10_11_12_13_14_15_16_17_18_19_20_21_22_23_DRYRUN_NONFLIP_CUSTODY_CHAIN_PARITY_AUDIT_LOCK_REQUIRED_NO_STATUS_FLIP_NO_COMPARATOR_AUTHORIZATION",
            "dryrun_nonflip_custody_chain_parity_audit_gate: formal/python/tests/test_cosmo_bg_micro24_dryrun_nonflip_custody_chain_parity_audit_gate.py",
        ),
        expected_artifact_id="cosmo_bg_micro24_dryrun_nonflip_custody_chain_parity_audit_cycle01_v0",
        expected_cycle="CYCLE-024",
        expected_boundary_statement="DRYRUN_NONFLIP_LANE_ONLY_CUSTODY_CHAIN_PARITY_AUDIT_NO_ADJUDICATION_FLIP_NO_COMPARATOR_AUTHORIZATION",
        matrix_doc_key="dryrun_nonflip_custody_chain_parity_audit_doc",
        matrix_gate_key="dryrun_nonflip_custody_chain_parity_audit_gate",
        matrix_policy_key="dryrun_nonflip_custody_chain_parity_audit_policy",
        matrix_policy_value="CYCLE08_09_10_11_12_13_14_15_16_17_18_19_20_21_22_23_DRYRUN_NONFLIP_CUSTODY_CHAIN_PARITY_AUDIT_LOCK_REQUIRED_NO_STATUS_FLIP_NO_COMPARATOR_AUTHORIZATION",
        state_required_tokens=(
            "COSMO_DRYRUN_NONFLIP_CUSTODY_CHAIN_PARITY_AUDIT_POLICY_v0: CYCLE08_09_10_11_12_13_14_15_16_17_18_19_20_21_22_23_DRYRUN_NONFLIP_CUSTODY_CHAIN_PARITY_AUDIT_LOCK_REQUIRED_NO_STATUS_FLIP_NO_COMPARATOR_AUTHORIZATION",
            "formal/python/tests/test_cosmo_bg_micro24_dryrun_nonflip_custody_chain_parity_audit_gate.py",
        ),
        rollup_required_tokens=(
            "dryrun_nonflip_custody_chain_parity_audit_doc",
            "dryrun_nonflip_custody_chain_parity_audit_gate",
            "dryrun_nonflip_custody_chain_parity_audit_policy",
            "COSMO_DRYRUN_NONFLIP_CUSTODY_CHAIN_PARITY_AUDIT_POLICY_v0",
        ),
    ),
)

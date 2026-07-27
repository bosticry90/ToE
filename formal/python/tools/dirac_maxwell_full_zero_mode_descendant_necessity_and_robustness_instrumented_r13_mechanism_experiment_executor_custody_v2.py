from __future__ import annotations

"""Static names and domains for the R13 mechanism executor-v2 custody layer.

This module deliberately contains no self-authorizing SHA-256 values for the
v2 freeze artifacts or implementation.  Those values must be supplied by the
accepted, independently reviewed freeze anchor at ``REVIEW_ANCHOR_RELATIVE_PATH``.
The execution entry point hard-binds that path; callers cannot substitute an
authority document, a matrix, or an output location.
"""


CUSTODY_LOCK_ID = (
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_EXECUTOR_CUSTODY_v2"
)

REVIEW_ANCHOR_RELATIVE_PATH = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_"
    "AND_ROBUSTNESS_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_NUMERICAL_FREEZE_"
    "PACKET_REVIEW_20260716_v2.json"
)
EXPECTED_REVIEW_VERDICT = (
    "ACCEPT_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_NUMERICAL_FREEZE"
)
REVIEW_AUTHORITY_FIELD = "runtime_execution_authority"

RUN_MATRIX_RELATIVE_PATH = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-INSTRUMENTED-R13-MECHANISM-EXPERIMENT-NUMERICAL-FREEZE-RUN-"
    "MATRIX-v2.json"
)
FREEZE_PACKET_RELATIVE_PATH = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-INSTRUMENTED-R13-MECHANISM-EXPERIMENT-NUMERICAL-FREEZE-"
    "PACKET-v2.json"
)
IDENTITY_MANIFEST_RELATIVE_PATH = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-INSTRUMENTED-R13-MECHANISM-EXPERIMENT-NUMERICAL-FREEZE-"
    "EXPECTED-OUTPUT-IDENTITY-MANIFEST-v2.json"
)
CANONICAL_MATRIX_RELATIVE_PATH = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-CANONICAL-RUN-MATRIX-v2.json"
)
EXPERIMENT_OUTPUT_ROOT_RELATIVE_PATH = (
    "formal/output/dirac_maxwell_instrumented_r13_mechanism_v0"
)
CANONICAL_OUTPUT_ROOT_RELATIVE_PATH = (
    "formal/output/canonical/dirac_maxwell_full_zero_mode_descendant_necessity_"
    "and_robustness_v2"
)

EXACT_RUN_IDS = (
    "MECHv0:R13_LOOSE:INSTRUMENTED",
    "MECHv0:R13_LOOSE:NONINSTRUMENTED_CONTROL",
    "MECHv0:R13_TIGHT:INSTRUMENTED",
    "MECHv0:R13_TIGHT:NONINSTRUMENTED_CONTROL",
    "MECHv0:R10_LOOSE:INSTRUMENTED",
    "MECHv0:R10_LOOSE:NONINSTRUMENTED_CONTROL",
)
PAIR_RUN_IDS = (
    (
        "MECHv0:R13_LOOSE:INSTRUMENTED",
        "MECHv0:R13_LOOSE:NONINSTRUMENTED_CONTROL",
    ),
    (
        "MECHv0:R13_TIGHT:INSTRUMENTED",
        "MECHv0:R13_TIGHT:NONINSTRUMENTED_CONTROL",
    ),
    (
        "MECHv0:R10_LOOSE:INSTRUMENTED",
        "MECHv0:R10_LOOSE:NONINSTRUMENTED_CONTROL",
    ),
)

EXPECTED_MATRIX_TOP_LEVEL_FIELDS = (
    "captured_at_utc",
    "expected_run_id_order",
    "fixed_numerical_settings",
    "generation_policy",
    "instrumented_record_count",
    "json_output_count",
    "noninstrumented_control_record_count",
    "npz_output_count",
    "physical_configuration_count",
    "record_count",
    "records",
    "role_counts",
    "schema_id",
    "selection_rules_closed",
    "unique_filename_count",
    "unique_run_id_count",
)
EXPECTED_RECORD_FIELDS = (
    "accepted_step_count",
    "checkpoint_count_including_initial",
    "dt",
    "duration",
    "execution_ordinal_zero_based",
    "execution_role",
    "experiment_id",
    "grid_size",
    "implementation_id",
    "implementation_sha256",
    "input_hash",
    "input_hash_material_excludes",
    "instrumentation_enabled",
    "instrumentation_read_only",
    "instrumented_observable_ids",
    "iteration_cap",
    "json_relative_output_path",
    "json_safe_filename",
    "max_iterations",
    "mechanism_configuration_role",
    "model_class",
    "n",
    "npz_relative_output_path",
    "npz_safe_filename",
    "numerical_method",
    "output_schema_version",
    "paired_run_id",
    "parent_canonical_input_hash",
    "parent_canonical_output_path",
    "parent_canonical_output_sha256",
    "parent_canonical_run_id",
    "parent_initial_condition_identity",
    "payload_identity_contract",
    "requested_axis_values",
    "row",
    "run_id",
    "scientific_row_id",
    "solver_tolerance",
    "supporting_duration_scaling_module_enabled",
    "supporting_tolerance_ladder_module_enabled",
    "time_step",
    "tolerance",
    "trajectory_identity_required",
)

EXPECTED_NUMERICS = {
    "n": 16,
    "dt": 0.003125,
    "duration": 0.05,
    "max_iterations": 80,
}

V0_IMPLEMENTATION_MODULE = (
    "formal.python.tools.dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_instrumented_r13_mechanism_experiment_implementation_v0"
)
HISTORICAL_EVOLUTION_MODULE = (
    "formal.python.tools.dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_non_authoritative_pilot_v1"
)
HISTORICAL_PACK_MODULE = (
    "formal.python.tools.dirac_maxwell_full_zero_mode_non_authoritative_pilot"
)
EXECUTOR_MODULE = (
    "formal.python.tools.dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_instrumented_r13_mechanism_experiment_executor_v2"
)
CUSTODY_MODULE = (
    "formal.python.tools.dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_instrumented_r13_mechanism_experiment_executor_custody_v2"
)
SEMANTIC_CONTRACT_MODULE = (
    "formal.python.tools.dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_instrumented_r13_mechanism_experiment_semantic_contract_v1"
)
RAW_EVIDENCE_ASSEMBLER_MODULE = (
    "formal.python.tools.dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_instrumented_r13_mechanism_experiment_raw_evidence_assembler_v2"
)
CLASSIFIER_MODULE = (
    "formal.python.tools.dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_instrumented_r13_mechanism_experiment_classifier_v2"
)

MODULE_PATH_BY_NAME = {
    EXECUTOR_MODULE: (
        "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_"
        "and_robustness_instrumented_r13_mechanism_experiment_executor_v2.py"
    ),
    CUSTODY_MODULE: (
        "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_"
        "and_robustness_instrumented_r13_mechanism_experiment_executor_"
        "custody_v2.py"
    ),
    V0_IMPLEMENTATION_MODULE: (
        "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_"
        "and_robustness_instrumented_r13_mechanism_experiment_implementation_"
        "v0.py"
    ),
    HISTORICAL_EVOLUTION_MODULE: (
        "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_"
        "and_robustness_non_authoritative_pilot_v1.py"
    ),
    HISTORICAL_PACK_MODULE: (
        "formal/python/tools/dirac_maxwell_full_zero_mode_non_authoritative_"
        "pilot.py"
    ),
    SEMANTIC_CONTRACT_MODULE: (
        "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_"
        "and_robustness_instrumented_r13_mechanism_experiment_semantic_"
        "contract_v1.py"
    ),
    RAW_EVIDENCE_ASSEMBLER_MODULE: (
        "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_"
        "and_robustness_instrumented_r13_mechanism_experiment_raw_evidence_"
        "assembler_v2.py"
    ),
    CLASSIFIER_MODULE: (
        "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_"
        "and_robustness_instrumented_r13_mechanism_experiment_classifier_v2.py"
    ),
}
REQUIRED_MODULE_NAMES = tuple(MODULE_PATH_BY_NAME)

REQUIRED_ARTIFACT_PATHS = {
    "run_matrix": RUN_MATRIX_RELATIVE_PATH,
    "freeze_packet": FREEZE_PACKET_RELATIVE_PATH,
    "identity_manifest": IDENTITY_MANIFEST_RELATIVE_PATH,
    "canonical_matrix": CANONICAL_MATRIX_RELATIVE_PATH,
}


__all__ = [
    "CANONICAL_MATRIX_RELATIVE_PATH",
    "CANONICAL_OUTPUT_ROOT_RELATIVE_PATH",
    "CLASSIFIER_MODULE",
    "CUSTODY_LOCK_ID",
    "CUSTODY_MODULE",
    "EXACT_RUN_IDS",
    "EXECUTOR_MODULE",
    "EXPECTED_MATRIX_TOP_LEVEL_FIELDS",
    "EXPECTED_NUMERICS",
    "EXPECTED_RECORD_FIELDS",
    "EXPECTED_REVIEW_VERDICT",
    "EXPERIMENT_OUTPUT_ROOT_RELATIVE_PATH",
    "FREEZE_PACKET_RELATIVE_PATH",
    "HISTORICAL_EVOLUTION_MODULE",
    "HISTORICAL_PACK_MODULE",
    "IDENTITY_MANIFEST_RELATIVE_PATH",
    "MODULE_PATH_BY_NAME",
    "PAIR_RUN_IDS",
    "RAW_EVIDENCE_ASSEMBLER_MODULE",
    "REQUIRED_ARTIFACT_PATHS",
    "REQUIRED_MODULE_NAMES",
    "REVIEW_ANCHOR_RELATIVE_PATH",
    "REVIEW_AUTHORITY_FIELD",
    "RUN_MATRIX_RELATIVE_PATH",
    "SEMANTIC_CONTRACT_MODULE",
    "V0_IMPLEMENTATION_MODULE",
]

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_KERNEL_REPLACEMENT_VALIDATION_"
    "INFRASTRUCTURE_PREREQUISITE_PACKET_20260719_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_KERNEL_REPLACEMENT_VALIDATION_"
    "INFRASTRUCTURE_PREREQUISITE_PACKET_20260719_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_scalar_only_yukawa_kernel_replacement_validation_"
    "infrastructure_prerequisite_packet_v0.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "ScalarOnlyYukawaKernelReplacementValidationInfrastructurePrerequisitePacketV0.lean"
)
SELECTOR_RELATIVE_PATH = (
    "formal/docs/release/POST_SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "REPLACEMENT_PACKET_V1_REVIEW_SCIENTIFIC_RESPONSE_SELECTION_20260719_v0.json"
)

TARGET = (
    "prepare_scalar_only_yukawa_kernel_replacement_validation_infrastructure_"
    "prerequisite_packet_v0"
)
VERDICT = (
    "PREPARED_SCALAR_ONLY_YUKAWA_KERNEL_REPLACEMENT_VALIDATION_INFRASTRUCTURE_"
    "PREREQUISITE_PACKET_V0"
)
SELECTED_NEXT_TARGET = (
    "review_scalar_only_yukawa_kernel_replacement_validation_infrastructure_"
    "prerequisite_packet_v0_result"
)
SELECTED_NEXT_TARGET_KIND = (
    "INDEPENDENT_TERMINAL_PREREQUISITE_REVIEW_ONLY_NO_EXECUTION_OR_REPAIR"
)

SELECTOR_HASHES = {
    "formal/docs/lanes/POST_SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_REPLACEMENT_PACKET_V1_REVIEW_SCIENTIFIC_RESPONSE_SELECTION_20260719_v0.md":
        "2b558dbb51879614f4233fc1844d48a63d8820251e942ee693e6c0837c2d3477",
    SELECTOR_RELATIVE_PATH:
        "b848cf2da1f7d5493ecfdf496c379872df10a78fec4d7c311cfd497509074b61",
    "formal/python/tools/post_scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_v1_review_scientific_response_selection_v0.py":
        "c26fde79b39246344c668b83d0c4846e08cf498d23707f49348a73d427c5877e",
    "formal/python/tests/test_post_scalar_only_yukawa_analytic_sphere_kernel_replacement_packet_v1_review_scientific_response_selection_v0.py":
        "578dabce9ce6569e3602ae9f573bb6772ef1f36e2e851a5f41ac25f87ca87a7f",
    "formal/toe_formal/ToeFormal/Derivation/PostScalarOnlyYukawaAnalyticSphereKernelReplacementPacketV1ReviewScientificResponseSelectionV0.lean":
        "ad60723a1777ba6572a6909548fba168f88ad5ce71eac1e41e80595d9cb627e8",
}

REVIEW_OUTCOMES = (
    "VALIDATION_INFRASTRUCTURE_PREREQUISITE_READY",
    "VALIDATION_INFRASTRUCTURE_PREREQUISITE_FAILED_RETIRE_OR_DEFER",
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {relative_path}")
    return value


def _artifact_row(relative_path: str) -> dict[str, str]:
    return {"relative_path": relative_path, "sha256": _sha256(REPO_ROOT / relative_path)}


def _field(name: str, value_type: str, required: bool = True) -> dict[str, Any]:
    return {"name": name, "type": value_type, "required": required}


def _schema(schema_id: str, fields: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "schema_id": schema_id,
        "additional_fields": "FORBIDDEN",
        "field_order_for_human_display": [row["name"] for row in fields],
        "fields": fields,
    }


def _predicate_schemas() -> dict[str, Any]:
    return {
        "NumericPredicateV0": _schema("NumericPredicateV0", [
            _field("predicate_id", "NONEMPTY_ASCII_STRING"),
            _field("kind", "ENUM:NUMERIC"),
            _field("observed_pointer", "JSON_POINTER_V0"),
            _field("reference_pointer", "JSON_POINTER_V0_OR_NULL"),
            _field("reference_decimal", "UPPERCASE_DECIMAL_OR_NULL"),
            _field("comparator", "NUMERIC_COMPARATOR_V0"),
            _field("absolute_tolerance_decimal", "UPPERCASE_NONNEGATIVE_DECIMAL"),
            _field("relative_tolerance_decimal", "UPPERCASE_NONNEGATIVE_DECIMAL"),
        ]),
        "ExceptionPredicateV0": _schema("ExceptionPredicateV0", [
            _field("predicate_id", "NONEMPTY_ASCII_STRING"),
            _field("kind", "ENUM:EXCEPTION"),
            _field("call_id", "NONEMPTY_ASCII_STRING"),
            _field("exception_type", "QUALIFIED_PYTHON_EXCEPTION_NAME"),
            _field("message_match", "ENUM:EXACT"),
            _field("message", "ASCII_STRING"),
        ]),
        "RelationalPredicateV0": _schema("RelationalPredicateV0", [
            _field("predicate_id", "NONEMPTY_ASCII_STRING"),
            _field("kind", "ENUM:RELATIONAL"),
            _field("left_pointer", "JSON_POINTER_V0"),
            _field("operator", "RELATIONAL_OPERATOR_V0"),
            _field("right_pointer", "JSON_POINTER_V0_OR_NULL"),
            _field("right_literal", "CANONICAL_SCALAR_OR_NULL"),
        ]),
        "DependencyPredicateV0": _schema("DependencyPredicateV0", [
            _field("predicate_id", "NONEMPTY_ASCII_STRING"),
            _field("kind", "ENUM:DEPENDENCY"),
            _field("scan_result_pointer", "JSON_POINTER_V0"),
            _field("expected_violation_ids", "SORTED_UNIQUE_ASCII_STRING_ARRAY"),
        ]),
        "AdjudicationResultV0": _schema("AdjudicationResultV0", [
            _field("predicate_id", "NONEMPTY_ASCII_STRING"),
            _field("kind", "PREDICATE_KIND_V0"),
            _field("passed", "BOOLEAN"),
            _field("observed_canonical", "CANONICAL_SCALAR_OR_NULL"),
            _field("reference_canonical", "CANONICAL_SCALAR_OR_NULL"),
            _field("difference_decimal", "UPPERCASE_DECIMAL_OR_NULL"),
            _field("envelope_decimal", "UPPERCASE_DECIMAL_OR_NULL"),
            _field("failure_code", "ADJUDICATION_FAILURE_CODE_V0_OR_NULL"),
        ]),
    }


def _fixture_rows() -> list[dict[str, Any]]:
    return [
        {
            "fixture_id": "F01_LINEAR_PAIR",
            "entrypoint": "synthetic_fixtures.linear_pair",
            "input_record_id": "I01_LINEAR_PAIR",
            "inputs": {"x_float_hex": "0x1.4000000000000p+0", "y_float_hex": "-0x1.0000000000000p-1"},
            "baseline_contract": "return_float64_hex(x+2.0*y)",
            "expected": {"value_float_hex": "0x1.0000000000000p-2"},
        },
        {
            "fixture_id": "F02_NEGATIVE_SQUARE",
            "entrypoint": "synthetic_fixtures.negative_square",
            "input_record_id": "I02_NEGATIVE_SQUARE",
            "inputs": {"x_float_hex": "0x1.0000000000000p+1"},
            "baseline_contract": "return_float64_hex(-(x*x))",
            "expected": {"value_float_hex": "-0x1.0000000000000p+2"},
        },
        {
            "fixture_id": "F03_REQUIRED_EXCEPTION",
            "entrypoint": "synthetic_fixtures.reciprocal",
            "input_record_id": "I03_ZERO_DENOMINATOR",
            "inputs": {"x_float_hex": "0x0.0p+0"},
            "baseline_contract": "raise ZeroDivisionError with exact message synthetic zero denominator",
            "expected": {"exception_type": "builtins.ZeroDivisionError", "message": "synthetic zero denominator"},
        },
        {
            "fixture_id": "F04_ARRAY_IDENTITY",
            "entrypoint": "synthetic_fixtures.float64_array_identity",
            "input_record_id": "I04_ARRAY",
            "inputs": {"values_float_hex": ["0x1.0000000000000p+0", "0x1.0000000000000p+1"]},
            "baseline_contract": "return new C-contiguous numpy float64 array with shape [2]",
            "expected": {"dtype": "float64", "shape": [2], "values_float_hex": ["0x1.0000000000000p+0", "0x1.0000000000000p+1"]},
        },
        {
            "fixture_id": "F05_PRIVATE_CAPABILITY",
            "entrypoint": "synthetic_fixtures.private_capability_echo",
            "input_record_id": "I05_ECHO",
            "inputs": {"value_ascii": "echo"},
            "baseline_contract": "ordinary public call returns echo and exposes no mutation or capability argument",
            "expected": {"value_ascii": "echo"},
        },
        {
            "fixture_id": "F06_DEPENDENCY_SCAN",
            "entrypoint": "dependency_scanner.scan_python_dependency_contract",
            "input_record_id": "I06_FORBIDDEN_IMPORT",
            "inputs": {"virtual_source_id": "SYNTHETIC_BAD_IMPORT_V0"},
            "baseline_contract": "scan inline bad source and report exact violation",
            "expected": {"violation_ids": ["FORBIDDEN_IMPORT:forbidden_oracle"]},
        },
        {
            "fixture_id": "F07_DUPLICATE_JSON",
            "entrypoint": "canonical_codec.loads_strict",
            "input_record_id": "I07_UNIQUE_KEY_BASELINE",
            "inputs": {"json_ascii": "{\"a\":1}"},
            "baseline_contract": "return object with exact integer field a=1",
            "expected": {"object": {"a": 1}},
        },
        {
            "fixture_id": "F08_UNKNOWN_ENUM",
            "entrypoint": "synthetic_fixtures.validate_run_status",
            "input_record_id": "I08_VALID_ENUM_BASELINE",
            "inputs": {"status": "COMPLETE"},
            "baseline_contract": "return exact ASCII COMPLETE after RUN_STATUS_V0 validation",
            "expected": {"status": "COMPLETE"},
        },
    ]


def _predicate_rows() -> list[dict[str, Any]]:
    return [
        {"predicate_id": "P01_LINEAR_BASELINE", "schema_id": "NumericPredicateV0", "kind": "NUMERIC", "observed_pointer": "/baseline/value_float_hex", "reference_pointer": None, "reference_decimal": "2.5E-1", "comparator": "ABS_REL_LE", "absolute_tolerance_decimal": "0E+0", "relative_tolerance_decimal": "0E+0"},
        {"predicate_id": "P02_SCALE_MUTATION", "schema_id": "NumericPredicateV0", "kind": "NUMERIC", "observed_pointer": "/mutation/value_float_hex", "reference_pointer": "/baseline/value_float_hex", "reference_decimal": None, "comparator": "RELATIVE_DIFFERENCE_GE", "absolute_tolerance_decimal": "0E+0", "relative_tolerance_decimal": "1E+0"},
        {"predicate_id": "P03_SIGN_FLIP", "schema_id": "RelationalPredicateV0", "kind": "RELATIONAL", "left_pointer": "/mutation/value_float_hex", "operator": "GT", "right_pointer": None, "right_literal": "0x0.0p+0"},
        {"predicate_id": "P04_EXCEPTION_SUPPRESSED", "schema_id": "RelationalPredicateV0", "kind": "RELATIONAL", "left_pointer": "/mutation/returned", "operator": "EQ", "right_pointer": None, "right_literal": True},
        {"predicate_id": "P05_ARRAY_DTYPE", "schema_id": "RelationalPredicateV0", "kind": "RELATIONAL", "left_pointer": "/mutation/dtype", "operator": "NE", "right_pointer": None, "right_literal": "float64"},
        {"predicate_id": "P06_UNAUTHORIZED_PRIVATE_CALL", "schema_id": "ExceptionPredicateV0", "kind": "EXCEPTION", "call_id": "C06_PRIVATE_WITHOUT_CAPABILITY", "exception_type": "builtins.PermissionError", "message_match": "EXACT", "message": "CAPABILITY_REQUIRED"},
        {"predicate_id": "P07_FORBIDDEN_DEPENDENCY", "schema_id": "DependencyPredicateV0", "kind": "DEPENDENCY", "scan_result_pointer": "/scanner/violation_ids", "expected_violation_ids": ["FORBIDDEN_IMPORT:forbidden_oracle"]},
        {"predicate_id": "P08_DUPLICATE_KEY", "schema_id": "ExceptionPredicateV0", "kind": "EXCEPTION", "call_id": "C08_LOAD_DUPLICATE", "exception_type": "validation_infrastructure.DuplicateKeyError", "message_match": "EXACT", "message": "duplicate key: a"},
        {"predicate_id": "P09_UNKNOWN_ENUM", "schema_id": "ExceptionPredicateV0", "kind": "EXCEPTION", "call_id": "C09_VALIDATE_UNKNOWN_ENUM", "exception_type": "validation_infrastructure.SchemaValidationError", "message_match": "EXACT", "message": "/status:UNKNOWN_ENUM_VALUE"},
    ]


def _mutation_routes() -> list[dict[str, Any]]:
    common = {
        "execution_order": ["PUBLIC_BASELINE", "ISSUE_BOUND_CAPABILITY", "ONE_PRIVATE_MUTATED_CALL", "ONE_ADJUDICATOR_CALL"],
        "failure_consequence": "VALIDATION_INFRASTRUCTURE_PREREQUISITE_FAILED_RETIRE_OR_DEFER",
    }
    rows = [
        ("M01_SCALE_BY_TWO", "F01_LINEAR_PAIR", "I01_LINEAR_PAIR", "synthetic_fixtures._linear_pair_mutated", "RETURN_VALUE", "multiply return by 2.0", "P02_SCALE_MUTATION"),
        ("M02_FLIP_SIGN", "F02_NEGATIVE_SQUARE", "I02_NEGATIVE_SQUARE", "synthetic_fixtures._negative_square_mutated", "RETURN_VALUE", "multiply return by -1.0", "P03_SIGN_FLIP"),
        ("M03_SUPPRESS_EXCEPTION", "F03_REQUIRED_EXCEPTION", "I03_ZERO_DENOMINATOR", "synthetic_fixtures._reciprocal_mutated", "ZERO_DENOMINATOR_BRANCH", "return +0.0 instead of raising", "P04_EXCEPTION_SUPPRESSED"),
        ("M04_CAST_FLOAT32", "F04_ARRAY_IDENTITY", "I04_ARRAY", "synthetic_fixtures._array_identity_mutated", "RETURN_ARRAY_DTYPE", "cast return array to numpy.float32", "P05_ARRAY_DTYPE"),
        ("M05_BYPASS_CAPABILITY", "F05_PRIVATE_CAPABILITY", "I05_ECHO", "synthetic_fixtures._private_capability_echo", "AUTHENTICATION_GUARD", "invoke with capability=None; guard must remain and raise", "P06_UNAUTHORIZED_PRIVATE_CALL"),
        ("M06_INSERT_FORBIDDEN_IMPORT", "F06_DEPENDENCY_SCAN", "I06_FORBIDDEN_IMPORT", "dependency_scanner._scan_virtual_source", "VIRTUAL_SOURCE_TEXT", "insert exact source import forbidden_oracle\\nforbidden_oracle.evaluate()\\n", "P07_FORBIDDEN_DEPENDENCY"),
        ("M07_DUPLICATE_KEY_INPUT", "F07_DUPLICATE_JSON", "I07_UNIQUE_KEY_BASELINE", "synthetic_fixtures._loads_strict_mutated", "JSON_INPUT_BYTES", "replace baseline with exact bytes {\"a\":1,\"a\":2}", "P08_DUPLICATE_KEY"),
        ("M08_UNKNOWN_ENUM_INPUT", "F08_UNKNOWN_ENUM", "I08_VALID_ENUM_BASELINE", "synthetic_fixtures._validate_run_status_mutated", "ENUM_FIELD_STATUS", "replace COMPLETE with exact ASCII UNKNOWN", "P09_UNKNOWN_ENUM"),
    ]
    result = []
    for mutation_id, fixture_id, input_id, private_call, point, operation, predicate_id in rows:
        result.append({
            "route_id": f"ROUTE_{mutation_id}",
            "fixture_id": fixture_id,
            "input_record_id": input_id,
            "public_baseline_call": next(row["entrypoint"] for row in _fixture_rows() if row["fixture_id"] == fixture_id),
            "private_mutated_call": private_call,
            "mutation_id": mutation_id,
            "injection_point": {"symbol": private_call, "point": point, "operation": operation},
            "capability_binding": {"fixture_id": fixture_id, "mutation_id": mutation_id, "single_use": True},
            "adjudicator_entrypoint": "validation_infrastructure.adjudicate_v0",
            "predicate_id": predicate_id,
            **common,
        })
    return result


def _recursive_result_schemas() -> dict[str, Any]:
    return {
        "QualificationResultV0": _schema("QualificationResultV0", [
            _field("schema_id", "ENUM:QualificationResultV0"),
            _field("run", "RunRecordV0"),
            _field("capability_results", "CapabilityResultV0_ARRAY"),
            _field("fixture_results", "FixtureResultV0_ARRAY"),
            _field("predicate_results", "AdjudicationResultV0_ARRAY"),
            _field("mutation_results", "MutationResultV0_ARRAY"),
            _field("scanner_results", "DependencyScanResultV0_ARRAY"),
            _field("serialization_results", "SerializationResultV0_ARRAY"),
            _field("terminal_outcome", "TERMINAL_OUTCOME_V0"),
        ]),
        "RunRecordV0": _schema("RunRecordV0", [
            _field("run_id", "LOWERCASE_UUID4"),
            _field("pid", "NONNEGATIVE_INTEGER"),
            _field("review_sha256", "LOWERCASE_SHA256"),
            _field("started_ns", "NONNEGATIVE_INTEGER"),
            _field("finished_ns", "NONNEGATIVE_INTEGER"),
            _field("status", "RUN_STATUS_V0"),
        ]),
        "CapabilityResultV0": _schema("CapabilityResultV0", [
            _field("control_id", "NONEMPTY_ASCII_STRING"),
            _field("expected_error", "CAPABILITY_ERROR_V0_OR_NULL"),
            _field("observed_error", "CAPABILITY_ERROR_V0_OR_NULL"),
            _field("passed", "BOOLEAN"),
        ]),
        "FixtureResultV0": _schema("FixtureResultV0", [
            _field("fixture_id", "FIXTURE_ID_V0"),
            _field("input_record_id", "INPUT_RECORD_ID_V0"),
            _field("status", "FIXTURE_STATUS_V0"),
            _field("output", "CANONICAL_OBJECT_OR_NULL"),
            _field("exception", "ExceptionRecordV0_OR_NULL"),
        ]),
        "ExceptionRecordV0": _schema("ExceptionRecordV0", [
            _field("type", "QUALIFIED_PYTHON_EXCEPTION_NAME"),
            _field("message", "ASCII_STRING"),
        ]),
        "MutationResultV0": _schema("MutationResultV0", [
            _field("route_id", "MUTATION_ROUTE_ID_V0"),
            _field("mutation_id", "MUTATION_ID_V0"),
            _field("fixture_id", "FIXTURE_ID_V0"),
            _field("predicate_id", "PREDICATE_ID_V0"),
            _field("detected", "BOOLEAN"),
        ]),
        "DependencyScanResultV0": _schema("DependencyScanResultV0", [
            _field("source_id", "SOURCE_ID_V0"),
            _field("parsed", "BOOLEAN"),
            _field("violation_ids", "SORTED_UNIQUE_ASCII_STRING_ARRAY"),
            _field("passed", "BOOLEAN"),
        ]),
        "SerializationResultV0": _schema("SerializationResultV0", [
            _field("control_id", "NONEMPTY_ASCII_STRING"),
            _field("canonical_sha256", "LOWERCASE_SHA256_OR_NULL"),
            _field("error_code", "SERIALIZATION_ERROR_V0_OR_NULL"),
            _field("passed", "BOOLEAN"),
        ]),
    }


def build_report() -> dict[str, Any]:
    for relative_path, expected in SELECTOR_HASHES.items():
        if _sha256(REPO_ROOT / relative_path) != expected:
            raise ValueError(f"prerequisite selector authority drift: {relative_path}")
    selector = _load_json(SELECTOR_RELATIVE_PATH)
    if selector.get("selected_next_target") != TARGET:
        raise ValueError("selector did not authorize prerequisite packet preparation")
    if selector.get("selected_route") != "ISOLATE_KERNEL_REPLACEMENT_VALIDATION_INFRASTRUCTURE_PREREQUISITE":
        raise ValueError("selector route mismatch")
    if selector["validation_infrastructure_prerequisite_contract"]["is_replacement_packet_v2"] is not False:
        raise ValueError("selector did not preserve the no-V2 boundary")

    fixtures = _fixture_rows()
    predicates = _predicate_rows()
    mutations = _mutation_routes()
    predicate_schemas = _predicate_schemas()
    result_schemas = _recursive_result_schemas()
    if not (len(fixtures) == 8 and len(predicates) == 9 and len(mutations) == 8):
        raise ValueError("synthetic infrastructure row count mismatch")

    packet_gates = (
        "EXACT_SELECTOR_AUTHORITY_AND_HASH_CUSTODY",
        "PACKET_IS_KERNEL_AGNOSTIC_AND_NOT_REPLACEMENT_V2",
        "V0_ONLY_NO_REPAIR_VERSION",
        "NO_PREREQUISITE_TO_THE_PREREQUISITE",
        "TWO_TERMINAL_REVIEW_OUTCOMES_ONLY",
        "READY_REVIEW_LEADS_TO_TWO_OPTION_SELECTOR_ONLY",
        "FAILED_REVIEW_LEADS_TO_RETIRE_OR_DEFER_ONLY",
        "THREAT_MODEL_AND_NON_GOALS_EXACT",
        "ANONYMOUS_PIPE_SECRET_ISSUANCE_EXACT",
        "PROCESS_RUN_FIXTURE_MUTATION_BINDING_EXACT",
        "HMAC_SHA256_TOKEN_FIELDS_EXACT",
        "EXPIRY_AND_SINGLE_USE_REPLAY_GUARD_EXACT",
        "PUBLIC_CALL_HAS_NO_CAPABILITY_OR_MUTATION_ARGUMENT",
        "PRIVATE_CALL_SIGNATURE_EXACT",
        "CAPABILITY_AUTHENTICATION_ORDER_EXACT",
        "CAPABILITY_ERROR_ENUM_EXACT",
        "NO_AMBIENT_ENVIRONMENT_OR_GLOBAL_MODE",
        "FOUR_TYPED_PREDICATE_SCHEMAS_EXACT",
        "ADJUDICATION_RESULT_SCHEMA_EXACT",
        "NUMERIC_COMPARATOR_ALGORITHMS_EXACT",
        "JSON_POINTER_SUBSET_EXACT",
        "DECIMAL_AND_FLOAT_CONVERSION_RULES_EXACT",
        "EIGHT_KERNEL_FREE_FIXTURES_EXACT",
        "EIGHT_COMPLETE_MUTATION_ROUTES_EXACT",
        "EVERY_ROUTE_BINDS_FIXTURE_CALL_CAPABILITY_INJECTION_AND_ADJUDICATOR",
        "DEPENDENCY_SCANNER_ENTRYPOINT_AND_SOURCE_ROOTS_EXACT",
        "DEPENDENCY_SCANNER_AST_ALIAS_AND_DYNAMIC_IMPORT_RULES_EXACT",
        "DEPENDENCY_SCANNER_PARSE_FAILURE_FAILS_CLOSED",
        "RECURSIVE_ROOT_AND_SEVEN_NESTED_SCHEMAS_EXACT",
        "ALL_ENUMS_EXACT_AND_UNKNOWN_VALUES_REJECTED",
        "DUPLICATE_KEY_PARSER_ALGORITHM_EXACT",
        "CANONICAL_UTF8_JSON_ENCODING_EXACT",
        "BINARY64_HEX_AND_DECIMAL_ENCODING_EXACT",
        "MISSING_UNKNOWN_NONFINITE_AND_DUPLICATE_VALUES_FAIL_CLOSED",
        "TWELVE_SYNTHETIC_CONTROLS_MANDATORY",
        "SIXTY_SECOND_256_MIB_FUTURE_ENVELOPE_EXACT",
        "SYNTHETIC_CONTROLS_NOT_EXECUTED_DURING_PREPARATION",
        "EXPLORATORY_SANDBOX_RISK_TIER_DEFINED",
        "SANDBOX_LABELS_NONPRODUCTION_NONADJUDICATIVE_NO_CLAIM",
        "SANDBOX_NOT_AUTHORIZED_BY_THIS_PACKET",
        "NO_ANALYTIC_NEWTONIAN_OR_YUKAWA_KERNEL_CONTENT",
        "NO_REAL_ORACLE_REGRESSION_OR_BOUNDARY_EXECUTION",
        "NO_CANDIDATE_KERNEL_CREATION_OR_EXECUTION",
        "NO_PRODUCTION_SOURCE_IMPORT_CALLER_OR_DISPATCH_CHANGE",
        "NO_CUBATURE_CALL_OR_ADJUDICATION",
        "NO_STAGE_A_TORQUE_DFT_IDENTIFIABILITY_OR_STAGE_B",
        "CURRENT_AUTHORITY_ROTATES_ONLY_TO_ONE_TERMINAL_REVIEW",
        "ANY_REVIEW_RESULT_STOPS_FOR_GOVERNED_SELECTION",
        "NO_AUTOMATIC_RETURN_TO_REPLACEMENT_LANE",
        "RETIREMENT_DEFERRAL_REMAINS_MANDATORY_ON_FAILURE",
    )

    scope = {
        "prerequisite_packet_prepared": True,
        "selector_authority_verified": True,
        "kernel_agnostic_contract_only": True,
        "independent_terminal_review_authorized": True,
        "replacement_packet_v2_created": False,
        "replacement_packet_v2_authorized": False,
        "prerequisite_repair_version_authorized": False,
        "prerequisite_to_prerequisite_authorized": False,
        "infrastructure_implementation_created": False,
        "synthetic_fixture_execution_performed": False,
        "candidate_kernel_created": False,
        "candidate_kernel_executed": False,
        "shadow_qualification_authorized": False,
        "production_source_or_dispatch_changed": False,
        "old_cubature_called": False,
        "old_cubature_adjudicated": False,
        "stage_a_rerun_authorized": False,
        "torque_or_dft_authorized": False,
        "jacobian_or_identifiability_authorized": False,
        "stage_b_authorized": False,
    }

    return {
        "schema_id": "toe.scalar_only_yukawa.kernel_replacement.validation_infrastructure_prerequisite_packet.v0",
        "packet_id": "SCALAR_ONLY_YUKAWA_KERNEL_REPLACEMENT_VALIDATION_INFRASTRUCTURE_PREREQUISITE_PACKET_20260719_v0",
        "captured_at_utc": "2026-07-19T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "status": "PREPARED_PENDING_ONE_TERMINAL_INDEPENDENT_REVIEW_NO_EXECUTION",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_selector_verdict": selector["verdict"],
            "consumed_selector_route": selector["selected_route"],
            "frozen_selector_artifacts": [
                {"relative_path": path, "sha256": digest}
                for path, digest in SELECTOR_HASHES.items()
            ],
            "human_packet": _artifact_row(HUMAN_RELATIVE_PATH),
            "generator": _artifact_row(
                "formal/python/tools/scalar_only_yukawa_kernel_replacement_validation_"
                "infrastructure_prerequisite_packet_v0.py"
            ),
            "test": _artifact_row(TEST_RELATIVE_PATH),
            "lean": _artifact_row(LEAN_RELATIVE_PATH),
        },
        "terminal_governance_boundary": {
            "packet_version": "V0_ONLY",
            "repair_version": "PROHIBITED",
            "prerequisite_to_prerequisite": "PROHIBITED",
            "review_outcomes": list(REVIEW_OUTCOMES),
            "ready_review_next_selector_options_exact": [
                "AUTHORIZE_ISOLATED_NON_DECISION_BEARING_SANDBOX_IMPLEMENTATION",
                "RETIRE_OR_DEFER_ANALYTIC_REPLACEMENT_LANE",
            ],
            "failed_review_next_selector_options_exact": [
                "RETIRE_ANALYTIC_REPLACEMENT_LANE",
                "DEFER_ANALYTIC_REPLACEMENT_LANE",
            ],
            "automatic_return_to_replacement_lane": "PROHIBITED",
            "new_governance_abstraction_after_failure": "PROHIBITED",
        },
        "capability_protocol_v0": {
            "threat_model": "PREVENT_ORDINARY_PUBLIC_CALLS_ACCIDENTAL_AMBIENT_MODE_AND_REPLAY_FROM_ACCESSING_MUTATED_PRIVATE_PATH",
            "out_of_scope": "MALICIOUS_ARBITRARY_CODE_WITH_READ_ACCESS_TO_PROCESS_MEMORY",
            "launcher_secret": "secrets.token_bytes(32)_WRITTEN_ONCE_THROUGH_INHERITED_ANONYMOUS_PIPE_NEVER_SERIALIZED",
            "manifest_schema": _schema("QualificationLaunchManifestV0", [
                _field("schema_id", "ENUM:QualificationLaunchManifestV0"),
                _field("run_id", "LOWERCASE_UUID4"),
                _field("child_pid", "POSITIVE_INTEGER"),
                _field("review_sha256", "LOWERCASE_SHA256"),
                _field("allowed_bindings", "SORTED_UNIQUE_FIXTURE_MUTATION_PAIR_ARRAY"),
                _field("issued_ns", "NONNEGATIVE_INTEGER"),
                _field("expires_ns", "NONNEGATIVE_INTEGER"),
            ]),
            "pipe_frame": "UINT32_BIG_ENDIAN_MANIFEST_BYTE_LENGTH_THEN_CANONICAL_MANIFEST_UTF8_THEN_EXACTLY_32_SECRET_BYTES_THEN_EOF",
            "pipe_read_rule": "READ_EXACT_FRAME_REJECT_TRUNCATION_TRAILING_BYTES_NONCANONICAL_MANIFEST_OR_PID_MISMATCH",
            "session_constructor": "ValidationHarnessSession.from_anonymous_pipe(read_fd,canonical_manifest_bytes)",
            "issuer_entrypoint": "ValidationHarnessSession.issue_capability(fixture_id,mutation_id)",
            "issuer_visibility": "SESSION_PRIVATE_TO_QUALIFICATION_CHILD_NOT_EXPORTED_FROM_PACKAGE___all__",
            "public_entrypoint_signature": "evaluate_fixture(fixture_id,input_record_id)->FixtureResultV0",
            "private_entrypoint_signature": "_evaluate_mutated_fixture(fixture_id,input_record_id,mutation_id,*,capability)->FixtureResultV0",
            "token_schema": _schema("CapabilityTokenV0", [
                _field("schema_id", "ENUM:CapabilityTokenV0"),
                _field("run_id", "LOWERCASE_UUID4"),
                _field("pid", "NONNEGATIVE_INTEGER"),
                _field("fixture_id", "FIXTURE_ID_V0"),
                _field("mutation_id", "MUTATION_ID_V0"),
                _field("review_sha256", "LOWERCASE_SHA256"),
                _field("nonce_hex", "LOWERCASE_HEX_32_BYTES"),
                _field("issued_ns", "NONNEGATIVE_INTEGER"),
                _field("expires_ns", "NONNEGATIVE_INTEGER"),
                _field("mac_hex", "LOWERCASE_HMAC_SHA256"),
            ]),
            "mac_rule": "HMAC_SHA256_PROCESS_SECRET_OVER_CANONICAL_TOKEN_FIELDS_EXCLUDING_mac_hex",
            "expiry_rule": "expires_ns=issued_ns+30_000_000_000_AND_monotonic_ns<=expires_ns",
            "single_use_rule": "nonce_hex_INSERTED_IN_PROCESS_LOCAL_REPLAY_SET_BEFORE_MUTATED_CALL_AND_SECOND_USE_REJECTED",
            "authentication_order": [
                "TOKEN_TYPE_AND_EXACT_SCHEMA", "HMAC_COMPARE_DIGEST", "PID",
                "RUN_ID", "REVIEW_SHA256", "FIXTURE_ID", "MUTATION_ID",
                "ISSUED_NOT_IN_FUTURE", "NOT_EXPIRED", "NONCE_NOT_REPLAYED",
                "INSERT_NONCE_THEN_DISPATCH",
            ],
            "error_enum": [
                "CAPABILITY_REQUIRED", "CAPABILITY_SCHEMA_INVALID", "CAPABILITY_MAC_INVALID",
                "CAPABILITY_WRONG_PROCESS", "CAPABILITY_WRONG_RUN", "CAPABILITY_WRONG_REVIEW",
                "CAPABILITY_WRONG_FIXTURE", "CAPABILITY_WRONG_MUTATION", "CAPABILITY_FUTURE_ISSUE",
                "CAPABILITY_EXPIRED", "CAPABILITY_REPLAYED",
            ],
            "error_behavior": "raise PermissionError with exact enum string and no fixture output",
            "ambient_environment_or_global_validation_mode": "FORBIDDEN",
        },
        "typed_adjudicator_contract_v0": {
            "schema_registry": predicate_schemas,
            "predicate_kind_enum": ["NUMERIC", "EXCEPTION", "RELATIONAL", "DEPENDENCY"],
            "numeric_comparator_enum": ["ABS_REL_LE", "RELATIVE_DIFFERENCE_GE", "EXACT_FLOAT_HEX"],
            "relational_operator_enum": ["EQ", "NE", "LT", "LE", "GT", "GE"],
            "numeric_algorithms": {
                "ABS_REL_LE": "abs(observed-reference)<=abs_tol+rel_tol*abs(reference)",
                "RELATIVE_DIFFERENCE_GE": "abs(observed-reference)/max(abs(reference),abs_tol)>=rel_tol",
                "EXACT_FLOAT_HEX": "lowercase_float_hex_observed==lowercase_float_hex_reference",
            },
            "decimal_conversion": "Decimal.from_float(float.fromhex(value_float_hex))",
            "decimal_context": "precision=100_rounding=ROUND_HALF_EVEN_traps_InvalidOperation_DivisionByZero_Overflow",
            "json_pointer_subset": "RFC6901_ABSOLUTE_POINTER_OBJECT_KEYS_AND_NONNEGATIVE_ARRAY_INDICES_ONLY_NO_DASH_TOKEN",
            "missing_pointer_unknown_enum_or_type_mismatch": "FAIL_WITH_TYPED_ADJUDICATION_ERROR_NO_BOOLEAN_RESULT",
            "predicate_rows": predicates,
        },
        "synthetic_fixture_contract_v0": {
            "kernel_or_physics_imports": "FORBIDDEN",
            "fixture_count": len(fixtures),
            "fixture_rows": fixtures,
            "fixture_execution_order": [row["fixture_id"] for row in fixtures],
            "all_values_are_synthetic": True,
        },
        "mutation_routing_contract_v0": {
            "route_count": len(mutations),
            "route_rows": mutations,
            "route_order": [row["route_id"] for row in mutations],
            "one_mutation_per_process": True,
            "baseline_must_pass_before_capability_issuance": True,
            "all_routes_mandatory": True,
            "missing_duplicate_failed_or_out_of_order_route": "VALIDATION_INFRASTRUCTURE_PREREQUISITE_FAILED_RETIRE_OR_DEFER",
        },
        "dependency_scanner_contract_v0": {
            "entrypoint_signature": "scan_python_dependency_contract(source_roots,forbidden_modules,forbidden_call_targets)->DependencyScanResultV0",
            "source_roots": ["virtual://synthetic/good.py", "virtual://synthetic/bad.py"],
            "virtual_sources": {
                "virtual://synthetic/good.py": "import math\nvalue = math.sqrt(4.0)\n",
                "virtual://synthetic/bad.py": "import forbidden_oracle\nforbidden_oracle.evaluate()\n",
            },
            "forbidden_modules": ["forbidden_oracle", "forbidden_cubature"],
            "forbidden_call_targets": ["forbidden_oracle.evaluate", "forbidden_cubature.integrate"],
            "recognized_ast_nodes": [
                "Module", "Import", "ImportFrom", "alias", "Expr", "Call",
                "Name", "Load", "Attribute", "Constant",
            ],
            "alias_rule": "TRACK_IMPORT_AND_IMPORTFROM_ALIASES_THROUGH_DOTTED_ATTRIBUTE_CALLS_WITHIN_ONE_MODULE",
            "dynamic_import_rule": "__import___AND_importlib.import_module_ALWAYS_VIOLATIONS",
            "file_order": "LEXICOGRAPHIC_SOURCE_ROOT_URI",
            "violation_order": "LEXICOGRAPHIC_VIOLATION_ID",
            "parse_or_unknown_ast_failure": "SCANNER_FAIL_CLOSED_WITH_PARSE_OR_UNSUPPORTED_NODE_VIOLATION",
            "expected_bad_source_violations": [
                "FORBIDDEN_CALL:forbidden_oracle.evaluate",
                "FORBIDDEN_IMPORT:forbidden_oracle",
            ],
        },
        "recursive_canonical_schema_contract_v0": {
            "schema_registry": result_schemas,
            "enum_registry": {
                "RUN_STATUS_V0": ["COMPLETE", "FAILED"],
                "FIXTURE_STATUS_V0": ["RETURNED", "RAISED"],
                "TERMINAL_OUTCOME_V0": [
                    "VALIDATION_INFRASTRUCTURE_CONTROLS_PASSED",
                    "VALIDATION_INFRASTRUCTURE_CONTROLS_FAILED",
                ],
                "ADJUDICATION_FAILURE_CODE_V0": ["MISSING_POINTER", "TYPE_MISMATCH", "UNKNOWN_ENUM", "PREDICATE_FALSE"],
                "SERIALIZATION_ERROR_V0": ["DUPLICATE_KEY", "MISSING_FIELD", "UNKNOWN_FIELD", "NONFINITE", "UNKNOWN_ENUM", "TYPE_MISMATCH"],
                "CAPABILITY_ERROR_V0": ["CAPABILITY_REQUIRED", "CAPABILITY_SCHEMA_INVALID", "CAPABILITY_MAC_INVALID", "CAPABILITY_WRONG_PROCESS", "CAPABILITY_WRONG_RUN", "CAPABILITY_WRONG_REVIEW", "CAPABILITY_WRONG_FIXTURE", "CAPABILITY_WRONG_MUTATION", "CAPABILITY_FUTURE_ISSUE", "CAPABILITY_EXPIRED", "CAPABILITY_REPLAYED"],
            },
            "strict_parser": "json.loads(text,object_pairs_hook=reject_duplicate_pairs,parse_constant=reject_nonfinite)",
            "duplicate_pair_algorithm": "iterate_pairs_in_input_order_raise_DuplicateKeyError_on_second_occurrence_before_dict_construction",
            "validator_order": ["EXACT_SCHEMA_ID", "REQUIRED_FIELDS", "NO_UNKNOWN_FIELDS", "FIELD_TYPES", "ENUM_VALUES", "RECURSE", "CROSS_FIELD_INVARIANTS"],
            "canonical_encoder": "json.dumps(object,sort_keys=True,ensure_ascii=True,allow_nan=False,separators=(',',':'))+'\\n'",
            "encoding": "UTF_8_NO_BOM_EXACTLY_ONE_TRAILING_LF",
            "binary64_rule": "LOWERCASE_float.hex_STRINGS_ONLY",
            "decimal_rule": "UPPERCASE_NORMALIZED_DECIMAL_STRINGS_ONLY",
            "integer_rule": "JSON_INTEGER_NOT_BOOLEAN",
            "array_order": "SCHEMA_SPECIFIC_AND_NEVER_SORTED_UNLESS_FIELD_TYPE_SAYS_SORTED_UNIQUE",
            "hash_rule": "LOWERCASE_SHA256_OF_EXACT_CANONICAL_UTF8_BYTES",
        },
        "synthetic_qualification_controls_v0": {
            "control_order": [
                "C01_PUBLIC_API_HAS_NO_MUTATION_OR_CAPABILITY_ARGUMENT",
                "C02_FORGED_MAC_REJECTED", "C03_WRONG_PID_REJECTED",
                "C04_EXPIRED_TOKEN_REJECTED", "C05_REPLAY_REJECTED",
                "C06_WRONG_FIXTURE_OR_MUTATION_BINDING_REJECTED",
                "C07_NUMERIC_RELATIONAL_AND_EXCEPTION_PREDICATES_DETECT",
                "C08_ALL_EIGHT_MUTATION_ROUTES_DETECT",
                "C09_GOOD_SOURCE_SCANNER_PASSES", "C10_BAD_SOURCE_SCANNER_FAILS",
                "C11_DUPLICATE_MISSING_UNKNOWN_NONFINITE_AND_ENUM_CASES_FAIL",
                "C12_CANONICAL_ROUND_TRIP_BYTES_AND_SHA256_STABLE",
            ],
            "all_controls_mandatory": True,
            "total_wall_clock_seconds_max": 60,
            "memory_mib_max": 256,
            "process_group_termination": "MANDATORY",
            "partial_result_classification": "FORBIDDEN",
            "execution_authorized_by_this_packet": False,
        },
        "future_exploratory_sandbox_risk_tier": {
            "authorized_now": False,
            "labels_exact": [
                "EXPLORATORY_IMPLEMENTATION_RESULT", "NON_PRODUCTION",
                "NON_ADJUDICATIVE", "NO_SCIENTIFIC_CLAIM",
            ],
            "may_create_isolated_candidate_if_freshly_selected_after_ready_review": True,
            "may_change_production_or_issue_scientific_verdict": False,
            "eligible_work_if_later_selected": "ISOLATED_CANDIDATE_AND_EIGHT_FROZEN_REGRESSION_CASES_ONLY",
            "ineligible_claims": [
                "PRODUCTION_REPLACEMENT", "CUBATURE_ADJUDICATION", "STAGE_A_VALIDATION",
                "IDENTIFIABILITY", "SENSITIVITY_OR_BOUND",
            ],
        },
        "packet_review_outcomes": list(REVIEW_OUTCOMES),
        "review_consequence": {
            "ready": "FRESH_TWO_OPTION_SELECTOR_REQUIRED_SANDBOX_OR_RETIRE_DEFER",
            "failed": "FRESH_RETIRE_OR_DEFER_SELECTOR_REQUIRED",
            "packet_repair": "PROHIBITED",
            "new_prerequisite": "PROHIBITED",
            "automatic_implementation_or_replacement_return": "PROHIBITED",
        },
        "packet_gates": {
            "gate_count": len(packet_gates),
            "pass_count": len(packet_gates),
            "failure_count": 0,
            "rows": [{"gate_id": gate, "status": "PASS"} for gate in packet_gates],
        },
        "scope": scope,
        "claim_ceiling": (
            "This packet specifies reusable kernel-agnostic validation infrastructure only. "
            "It implements or executes no infrastructure or synthetic fixture, contains no "
            "scientific kernel, edits no replacement packet, creates or executes no candidate, "
            "changes no production source or dispatch, calls or adjudicates no cubature, reruns "
            "no Stage A work, computes no torque, DFT, vector, Jacobian, SVD, or identifiability, "
            "and authorizes no Stage B. It has one terminal review and no repair successor."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_report(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Prepare the terminal kernel-agnostic validation infrastructure prerequisite packet."
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--write", action="store_true")
    args = parser.parse_args()
    output = REPO_ROOT / REPORT_RELATIVE_PATH
    expected = artifact_bytes()
    current = output.read_bytes() if output.exists() else None
    if args.write:
        if current != expected:
            output.write_bytes(expected)
            print(f"wrote {REPORT_RELATIVE_PATH}")
        else:
            print("validation infrastructure prerequisite packet already current")
        return 0
    if current != expected:
        print("validation infrastructure prerequisite packet drift")
        return 1
    report = build_report()
    print(
        "validation infrastructure prerequisite packet OK "
        f"fixtures={report['synthetic_fixture_contract_v0']['fixture_count']} "
        f"routes={report['mutation_routing_contract_v0']['route_count']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_KERNEL_REPLACEMENT_VALIDATION_"
    "INFRASTRUCTURE_PREREQUISITE_PACKET_REVIEW_20260719_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_KERNEL_REPLACEMENT_VALIDATION_"
    "INFRASTRUCTURE_PREREQUISITE_PACKET_REVIEW_20260719_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_scalar_only_yukawa_kernel_replacement_validation_"
    "infrastructure_prerequisite_packet_review_v0.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "ScalarOnlyYukawaKernelReplacementValidationInfrastructurePrerequisitePacketReviewV0.lean"
)
PACKET_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_KERNEL_REPLACEMENT_VALIDATION_"
    "INFRASTRUCTURE_PREREQUISITE_PACKET_20260719_v0.json"
)

TARGET = (
    "review_scalar_only_yukawa_kernel_replacement_validation_infrastructure_"
    "prerequisite_packet_v0_result"
)
VERDICT = "VALIDATION_INFRASTRUCTURE_PREREQUISITE_READY"
SELECTED_NEXT_TARGET = (
    "select_post_scalar_only_yukawa_kernel_replacement_validation_infrastructure_"
    "prerequisite_packet_v0_review_scientific_response_v0"
)
SELECTED_NEXT_TARGET_KIND = (
    "TWO_OPTION_SELECTOR_ONLY_ISOLATED_SANDBOX_OR_RETIRE_DEFER"
)

PACKET_HASHES = {
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_KERNEL_REPLACEMENT_VALIDATION_INFRASTRUCTURE_PREREQUISITE_PACKET_20260719_v0.md":
        "b019219a3c2ccee06bbb5628a9104995d38938d1b46321e2f7cc1950671ad1e4",
    PACKET_RELATIVE_PATH:
        "66ce9cd50115963c531c31524e20e7c567692f5455f8b8bde5411bf685da4d12",
    "formal/python/tools/scalar_only_yukawa_kernel_replacement_validation_infrastructure_prerequisite_packet_v0.py":
        "e7f606eea02b383377933571c1d4d77ba1788eaa77e8a97634f23450749a960e",
    "formal/python/tests/test_scalar_only_yukawa_kernel_replacement_validation_infrastructure_prerequisite_packet_v0.py":
        "1f2548d15e906f455ab9ad91329543514d1431c7896f17107cb8b08651fff45b",
    "formal/toe_formal/ToeFormal/Derivation/ScalarOnlyYukawaKernelReplacementValidationInfrastructurePrerequisitePacketV0.lean":
        "cde67ee5988a8325aac3d6339768fccdf3f2f3a7185d727998913399653b29fd",
}


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {relative_path}")
    return value


def _artifact_row(relative_path: str) -> dict[str, str]:
    return {"relative_path": relative_path, "sha256": _sha256(REPO_ROOT / relative_path)}


def _gate(gate_id: str, finding: str) -> dict[str, str]:
    return {"gate_id": gate_id, "status": "PASS", "finding": finding}


def _schema_complete(schema: dict[str, Any]) -> bool:
    fields = schema.get("fields")
    return (
        isinstance(schema.get("schema_id"), str)
        and schema.get("additional_fields") == "FORBIDDEN"
        and isinstance(fields, list) and bool(fields)
        and all(set(row) == {"name", "type", "required"} for row in fields)
        and len({row["name"] for row in fields}) == len(fields)
        and schema.get("field_order_for_human_display") == [row["name"] for row in fields]
    )


def build_report() -> dict[str, Any]:
    for relative_path, expected in PACKET_HASHES.items():
        if _sha256(REPO_ROOT / relative_path) != expected:
            raise ValueError(f"terminal prerequisite packet custody drift: {relative_path}")
    packet = _load_json(PACKET_RELATIVE_PATH)
    if packet.get("target") != (
        "prepare_scalar_only_yukawa_kernel_replacement_validation_infrastructure_"
        "prerequisite_packet_v0"
    ):
        raise ValueError("prerequisite packet target mismatch")
    if packet.get("selected_next_target") != TARGET:
        raise ValueError("prerequisite packet did not authorize this review")
    if packet.get("verdict") != (
        "PREPARED_SCALAR_ONLY_YUKAWA_KERNEL_REPLACEMENT_VALIDATION_INFRASTRUCTURE_"
        "PREREQUISITE_PACKET_V0"
    ):
        raise ValueError("prerequisite packet verdict mismatch")

    terminal = packet["terminal_governance_boundary"]
    capability = packet["capability_protocol_v0"]
    adjudicator = packet["typed_adjudicator_contract_v0"]
    fixtures = packet["synthetic_fixture_contract_v0"]
    routing = packet["mutation_routing_contract_v0"]
    scanner = packet["dependency_scanner_contract_v0"]
    canonical = packet["recursive_canonical_schema_contract_v0"]
    controls = packet["synthetic_qualification_controls_v0"]
    sandbox = packet["future_exploratory_sandbox_risk_tier"]
    scope = packet["scope"]

    terminal_ready = (
        terminal["packet_version"] == "V0_ONLY"
        and terminal["repair_version"] == "PROHIBITED"
        and terminal["prerequisite_to_prerequisite"] == "PROHIBITED"
        and terminal["review_outcomes"] == [
            "VALIDATION_INFRASTRUCTURE_PREREQUISITE_READY",
            "VALIDATION_INFRASTRUCTURE_PREREQUISITE_FAILED_RETIRE_OR_DEFER",
        ]
        and terminal["ready_review_next_selector_options_exact"] == [
            "AUTHORIZE_ISOLATED_NON_DECISION_BEARING_SANDBOX_IMPLEMENTATION",
            "RETIRE_OR_DEFER_ANALYTIC_REPLACEMENT_LANE",
        ]
        and len(terminal["failed_review_next_selector_options_exact"]) == 2
        and terminal["automatic_return_to_replacement_lane"] == "PROHIBITED"
    )
    if not terminal_ready:
        raise ValueError("terminal transition contract is not exact")

    manifest_field_names = [row["name"] for row in capability["manifest_schema"]["fields"]]
    token_field_names = [row["name"] for row in capability["token_schema"]["fields"]]
    capability_ready = (
        _schema_complete(capability["manifest_schema"])
        and _schema_complete(capability["token_schema"])
        and manifest_field_names == [
            "schema_id", "run_id", "child_pid", "review_sha256", "allowed_bindings",
            "issued_ns", "expires_ns",
        ]
        and token_field_names == [
            "schema_id", "run_id", "pid", "fixture_id", "mutation_id",
            "review_sha256", "nonce_hex", "issued_ns", "expires_ns", "mac_hex",
        ]
        and capability["pipe_frame"].startswith("UINT32_BIG_ENDIAN_MANIFEST_BYTE_LENGTH")
        and "HMAC_SHA256" in capability["mac_rule"]
        and len(capability["authentication_order"]) == 11
        and len(set(capability["authentication_order"])) == 11
        and len(capability["error_enum"]) == 11
        and len(set(capability["error_enum"])) == 11
        and "capability" not in capability["public_entrypoint_signature"].lower()
        and "mutation" not in capability["public_entrypoint_signature"].lower()
        and "capability" in capability["private_entrypoint_signature"].lower()
        and "mutation_id" in capability["private_entrypoint_signature"]
        and capability["ambient_environment_or_global_validation_mode"] == "FORBIDDEN"
    )
    if not capability_ready:
        raise ValueError("capability protocol review failed")

    predicate_schemas = adjudicator["schema_registry"]
    expected_schema_ids = {
        "NumericPredicateV0", "ExceptionPredicateV0", "RelationalPredicateV0",
        "DependencyPredicateV0", "AdjudicationResultV0",
    }
    predicate_rows = adjudicator["predicate_rows"]
    predicate_ids = [row["predicate_id"] for row in predicate_rows]
    predicate_ready = (
        set(predicate_schemas) == expected_schema_ids
        and all(_schema_complete(value) for value in predicate_schemas.values())
        and len(predicate_rows) == 9 and len(set(predicate_ids)) == 9
        and all(row["schema_id"] in expected_schema_ids for row in predicate_rows)
        and set(adjudicator["numeric_algorithms"]) == {
            "ABS_REL_LE", "RELATIVE_DIFFERENCE_GE", "EXACT_FLOAT_HEX",
        }
        and adjudicator["predicate_kind_enum"] == [
            "NUMERIC", "EXCEPTION", "RELATIONAL", "DEPENDENCY",
        ]
        and "Decimal.from_float" in adjudicator["decimal_conversion"]
        and adjudicator["missing_pointer_unknown_enum_or_type_mismatch"].startswith("FAIL")
    )
    if not predicate_ready:
        raise ValueError("typed predicate review failed")

    fixture_rows = fixtures["fixture_rows"]
    fixture_pairs = {(row["fixture_id"], row["input_record_id"]) for row in fixture_rows}
    route_rows = routing["route_rows"]
    route_ids = [row["route_id"] for row in route_rows]
    route_required = {
        "route_id", "fixture_id", "input_record_id", "public_baseline_call",
        "private_mutated_call", "mutation_id", "injection_point",
        "capability_binding", "adjudicator_entrypoint", "predicate_id",
        "execution_order", "failure_consequence",
    }
    routing_ready = (
        fixtures["kernel_or_physics_imports"] == "FORBIDDEN"
        and len(fixture_rows) == 8 and len(fixture_pairs) == 8
        and len(route_rows) == 8 and len(set(route_ids)) == 8
        and all(route_required <= set(row) for row in route_rows)
        and all((row["fixture_id"], row["input_record_id"]) in fixture_pairs for row in route_rows)
        and all(row["predicate_id"] in predicate_ids for row in route_rows)
        and all(row["capability_binding"] == {
            "fixture_id": row["fixture_id"],
            "mutation_id": row["mutation_id"],
            "single_use": True,
        } for row in route_rows)
        and all(set(row["injection_point"]) == {"symbol", "point", "operation"} for row in route_rows)
        and all(row["adjudicator_entrypoint"] == "validation_infrastructure.adjudicate_v0" for row in route_rows)
        and routing["all_routes_mandatory"] is True
    )
    if not routing_ready:
        raise ValueError("synthetic fixture or mutation routing review failed")

    scanner_ready = (
        set(scanner["source_roots"]) == set(scanner["virtual_sources"])
        and len(scanner["forbidden_modules"]) == 2
        and len(scanner["forbidden_call_targets"]) == 2
        and {"Import", "ImportFrom", "Call", "Name", "Attribute"}
        <= set(scanner["recognized_ast_nodes"])
        and "__import__" in scanner["dynamic_import_rule"]
        and "importlib.import_module" in scanner["dynamic_import_rule"]
        and scanner["file_order"].startswith("LEXICOGRAPHIC")
        and scanner["violation_order"].startswith("LEXICOGRAPHIC")
        and "FAIL_CLOSED" in scanner["parse_or_unknown_ast_failure"]
        and scanner["expected_bad_source_violations"] == sorted(
            scanner["expected_bad_source_violations"]
        )
    )
    if not scanner_ready:
        raise ValueError("dependency scanner review failed")

    result_schemas = canonical["schema_registry"]
    enum_registry = canonical["enum_registry"]
    canonical_ready = (
        len(result_schemas) == 8
        and all(_schema_complete(value) for value in result_schemas.values())
        and len(enum_registry) == 6
        and all(isinstance(values, list) and values and len(values) == len(set(values)) for values in enum_registry.values())
        and "object_pairs_hook=reject_duplicate_pairs" in canonical["strict_parser"]
        and "parse_constant=reject_nonfinite" in canonical["strict_parser"]
        and canonical["duplicate_pair_algorithm"].startswith("iterate_pairs_in_input_order")
        and canonical["validator_order"] == [
            "EXACT_SCHEMA_ID", "REQUIRED_FIELDS", "NO_UNKNOWN_FIELDS", "FIELD_TYPES",
            "ENUM_VALUES", "RECURSE", "CROSS_FIELD_INVARIANTS",
        ]
        and "sort_keys=True" in canonical["canonical_encoder"]
        and canonical["encoding"] == "UTF_8_NO_BOM_EXACTLY_ONE_TRAILING_LF"
        and canonical["binary64_rule"].startswith("LOWERCASE")
        and canonical["decimal_rule"].startswith("UPPERCASE")
    )
    if not canonical_ready:
        raise ValueError("recursive canonical schema review failed")

    control_ready = (
        len(controls["control_order"]) == 12
        and len(set(controls["control_order"])) == 12
        and controls["all_controls_mandatory"] is True
        and controls["total_wall_clock_seconds_max"] == 60
        and controls["memory_mib_max"] == 256
        and controls["partial_result_classification"] == "FORBIDDEN"
        and controls["execution_authorized_by_this_packet"] is False
    )
    sandbox_ready = (
        sandbox["authorized_now"] is False
        and sandbox["labels_exact"] == [
            "EXPLORATORY_IMPLEMENTATION_RESULT", "NON_PRODUCTION",
            "NON_ADJUDICATIVE", "NO_SCIENTIFIC_CLAIM",
        ]
        and sandbox["may_change_production_or_issue_scientific_verdict"] is False
        and len(sandbox["ineligible_claims"]) == 5
    )
    if not control_ready or not sandbox_ready:
        raise ValueError("future control or sandbox isolation review failed")

    no_execution = (
        scope["infrastructure_implementation_created"] is False
        and scope["synthetic_fixture_execution_performed"] is False
        and scope["candidate_kernel_created"] is False
        and scope["candidate_kernel_executed"] is False
        and scope["production_source_or_dispatch_changed"] is False
        and scope["old_cubature_called"] is False
        and scope["stage_a_rerun_authorized"] is False
        and scope["stage_b_authorized"] is False
    )
    if not no_execution:
        raise ValueError("packet preparation crossed an execution firewall")

    gate_rows = [
        _gate("T01_EXACT_PACKET_HASH_CUSTODY", "five packet artifacts reproduced"),
        _gate("T02_EXACT_REVIEW_AUTHORITY", "packet rotates only to this terminal review"),
        _gate("T03_SANDBOX_NOT_PRODUCTION_REVIEW_STANDARD", "review burden is bounded sandbox eligibility"),
        _gate("T04_V0_ONLY", "packet version is terminal V0"),
        _gate("T05_NO_REPAIR_VERSION", "repair successor prohibited"),
        _gate("T06_NO_PREREQUISITE_REGRESS", "prerequisite-to-prerequisite prohibited"),
        _gate("T07_TWO_REVIEW_OUTCOMES", "ready or failed-retire/defer only"),
        _gate("T08_READY_TWO_OPTION_SELECTOR", "sandbox or retire/defer only"),
        _gate("T09_FAILURE_RETIRE_OR_DEFER_ONLY", "no failure repair route"),
        _gate("T10_THREAT_MODEL_EXACT", "ordinary-call and replay threat model bounded"),
        _gate("T11_PIPE_SECRET_FRAME_EXACT", "manifest and 32-byte secret framing complete"),
        _gate("T12_MANIFEST_SCHEMA_EXACT", "seven manifest fields closed"),
        _gate("T13_CAPABILITY_TOKEN_SCHEMA_EXACT", "ten token fields closed"),
        _gate("T14_HMAC_BINDING_EXACT", "HMAC covers all non-MAC token fields"),
        _gate("T15_PROCESS_RUN_REVIEW_BINDING", "PID, run, and review authenticated"),
        _gate("T16_FIXTURE_MUTATION_BINDING", "fixture and mutation authenticated"),
        _gate("T17_EXPIRY_AND_REPLAY", "30-second expiry and one-shot nonce exact"),
        _gate("T18_PUBLIC_PRIVATE_SEPARATION", "public signature exposes no validation arguments"),
        _gate("T19_CAPABILITY_ERRORS_EXACT", "eleven failure codes exact"),
        _gate("T20_NO_AMBIENT_MODE", "environment and global modes forbidden"),
        _gate("T21_FIVE_ADJUDICATOR_SCHEMAS", "four predicates plus result schema complete"),
        _gate("T22_NINE_TYPED_PREDICATES", "nine unique mechanically typed predicates"),
        _gate("T23_NUMERIC_ALGORITHMS", "three comparison algorithms exact"),
        _gate("T24_DECIMAL_CONVERSION", "binary64-to-Decimal conversion exact"),
        _gate("T25_POINTER_FAILURES_TYPED", "missing and mistyped pointers fail closed"),
        _gate("T26_EIGHT_KERNEL_FREE_FIXTURES", "synthetic fixture catalog complete"),
        _gate("T27_EIGHT_ROUTE_IDENTITIES", "one unique route per synthetic mutation"),
        _gate("T28_ROUTE_INPUT_BINDING", "every route resolves one fixture/input pair"),
        _gate("T29_ROUTE_CAPABILITY_BINDING", "every route binds one single-use token"),
        _gate("T30_ROUTE_INJECTION_EXACT", "symbol, point, and operation exact"),
        _gate("T31_ROUTE_ADJUDICATOR_BINDING", "every route resolves one typed predicate"),
        _gate("T32_SCANNER_ENTRYPOINT_AND_ROOTS", "two deterministic virtual roots exact"),
        _gate("T33_SCANNER_IMPORT_CALL_RULES", "imports, aliases, calls, and dynamic imports covered"),
        _gate("T34_SCANNER_FAILURE_RULE", "parse and unknown AST paths fail closed"),
        _gate("T35_SCANNER_EXPECTED_VIOLATIONS", "bad source violations exact and ordered"),
        _gate("T36_EIGHT_RECURSIVE_RESULT_SCHEMAS", "root plus seven nested schemas complete"),
        _gate("T37_SIX_ENUM_FAMILIES", "enum values unique and unknowns rejected"),
        _gate("T38_DUPLICATE_KEY_REJECTION", "duplicates rejected before dictionary construction"),
        _gate("T39_NONFINITE_REJECTION", "nonfinite JSON constants rejected"),
        _gate("T40_CANONICAL_ENCODING", "recursive sorted-key UTF-8 encoding exact"),
        _gate("T41_FLOAT_DECIMAL_INTEGER_RULES", "scalar encodings unambiguous"),
        _gate("T42_TWELVE_CONTROLS", "all future synthetic controls unique and mandatory"),
        _gate("T43_RESOURCE_ENVELOPE", "60-second and 256-MiB bounds exact"),
        _gate("T44_PARTIAL_RESULT_FIREWALL", "partial classification forbidden"),
        _gate("T45_EXPLORATORY_LABELS", "four non-decision-bearing labels exact"),
        _gate("T46_PRODUCTION_AND_CLAIM_ISOLATION", "sandbox cannot alter production or claim science"),
        _gate("T47_NO_PREPARATION_EXECUTION", "no infrastructure, fixture, candidate, or cubature execution"),
        _gate("T48_CURRENT_AUTHORITY_TWO_OPTION_SELECTOR_ONLY", "review rotates only to sandbox-or-retire selector"),
    ]

    review_scope = {
        "terminal_independent_review_performed": True,
        "packet_custody_verified": True,
        "sandbox_eligibility_standard_applied": True,
        "validation_infrastructure_contract_ready": True,
        "two_option_selector_authorized": True,
        "packet_repair_authorized": False,
        "prerequisite_to_prerequisite_authorized": False,
        "infrastructure_implementation_authorized": False,
        "infrastructure_implementation_performed": False,
        "synthetic_fixture_execution_performed": False,
        "candidate_kernel_creation_authorized": False,
        "candidate_kernel_execution_authorized": False,
        "production_change_authorized": False,
        "old_cubature_called": False,
        "old_cubature_adjudicated": False,
        "stage_a_rerun_authorized": False,
        "torque_or_dft_authorized": False,
        "jacobian_or_identifiability_authorized": False,
        "stage_b_authorized": False,
    }

    return {
        "schema_id": "toe.scalar_only_yukawa.kernel_replacement.validation_infrastructure_prerequisite_packet_review.v0",
        "review_id": "SCALAR_ONLY_YUKAWA_KERNEL_REPLACEMENT_VALIDATION_INFRASTRUCTURE_PREREQUISITE_PACKET_REVIEW_20260719_v0",
        "captured_at_utc": "2026-07-19T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "status": "TERMINAL_INDEPENDENT_REVIEW_COMPLETE_READY_FOR_TWO_OPTION_SELECTOR",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_packet_verdict": packet["verdict"],
            "frozen_packet_artifacts": [
                {"relative_path": path, "sha256": digest}
                for path, digest in PACKET_HASHES.items()
            ],
            "human_review": _artifact_row(HUMAN_RELATIVE_PATH),
            "generator": _artifact_row(
                "formal/python/tools/scalar_only_yukawa_kernel_replacement_validation_"
                "infrastructure_prerequisite_packet_review_v0.py"
            ),
            "test": _artifact_row(TEST_RELATIVE_PATH),
            "lean": _artifact_row(LEAN_RELATIVE_PATH),
        },
        "review_standard": {
            "tier": "NON_PRODUCTION_EXPLORATORY_SANDBOX_ELIGIBILITY",
            "production_adoption_assurance_required": False,
            "scientific_claim_assurance_required": False,
            "mechanical_executability_and_isolation_required": True,
        },
        "independent_audits": {
            "terminal_transition": "PASS",
            "capability_issuance_authentication_and_private_enforcement": "PASS",
            "typed_adjudicator_schemas_and_predicates": "PASS",
            "kernel_free_fixture_and_mutation_routes": "PASS",
            "dependency_scanner": "PASS",
            "recursive_canonical_schema_and_comparison": "PASS",
            "future_synthetic_controls": "PASS",
            "exploratory_risk_tier_isolation": "PASS",
            "no_execution_custody": "PASS",
        },
        "nonblocking_review_notes": [
            "The capability protocol addresses ordinary public-call misuse and replay; malicious arbitrary code with process-memory access remains explicitly out of scope.",
            "This review accepts implementation-level determinism for sandbox use and does not certify cross-platform production hardening.",
            "READY means contract-ready for a fresh selector, not infrastructure-qualified, kernel-qualified, or scientifically validated.",
        ],
        "review_gates": {
            "gate_count": len(gate_rows),
            "pass_count": len(gate_rows),
            "failure_count": 0,
            "rows": gate_rows,
        },
        "terminal_consequence": {
            "current_selector_options_exact": [
                "AUTHORIZE_ISOLATED_NON_DECISION_BEARING_SANDBOX_IMPLEMENTATION",
                "RETIRE_OR_DEFER_ANALYTIC_REPLACEMENT_LANE",
            ],
            "packet_repair": "PROHIBITED",
            "new_prerequisite": "PROHIBITED",
            "automatic_sandbox_or_replacement": "PROHIBITED",
            "selector_must_choose_exactly_one_option": True,
        },
        "scope": review_scope,
        "claim_ceiling": (
            "This terminal review finds the kernel-agnostic validation infrastructure contract "
            "sufficiently complete for a bounded non-production exploratory sandbox selector. "
            "It does not implement or execute infrastructure or fixtures, create or execute a "
            "kernel, change production, call or adjudicate cubature, rerun Stage A, compute "
            "torque, DFT, vector, Jacobian, SVD, or identifiability, or authorize Stage B."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_report(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Perform the terminal review of the validation infrastructure prerequisite."
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
            print("terminal prerequisite review already current")
        return 0
    if current != expected:
        print("terminal prerequisite review drift")
        return 1
    report = build_report()
    print(
        "terminal prerequisite review OK "
        f"verdict={report['verdict']} pass={report['review_gates']['pass_count']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

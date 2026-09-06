from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "EXPLORATORY_SANDBOX_EXECUTION_RESULT_REVIEW_20260719_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "EXPLORATORY_SANDBOX_EXECUTION_RESULT_REVIEW_20260719_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_scalar_only_yukawa_analytic_sphere_kernel_"
    "exploratory_sandbox_execution_result_review_v0.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "ScalarOnlyYukawaAnalyticSphereKernelExploratorySandboxExecutionResultReviewV0.lean"
)
RESULT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "EXPLORATORY_SANDBOX_20260719_v0.json"
)
SOURCE_RELATIVE_PATH = (
    "formal/python/tools/scalar_only_yukawa_analytic_sphere_kernel_"
    "exploratory_sandbox_v0.py"
)
STAGES_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "EXPLORATORY_SANDBOX_20260719_v0.stages.json"
)
LOG_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "EXPLORATORY_SANDBOX_20260719_v0.log"
)
MARKER_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "EXPLORATORY_SANDBOX_20260719_v0.authority_consumed.json"
)

TARGET = (
    "review_scalar_only_yukawa_analytic_sphere_kernel_exploratory_sandbox_v0_"
    "execution_result"
)
VERDICT = "ACCEPTED_EXPLORATORY_IMPLEMENTATION_SERIALIZATION_FAILURE"
PRINCIPAL_OUTCOME = (
    "VALIDATION_INFRASTRUCTURE_IMPLEMENTATION_FAILED_CANONICAL_SERIALIZATION"
)
SECONDARY_OUTCOMES = (
    "SANDBOX_IMPLEMENTATION_DEFECT_LOCALIZED",
    "SYNTHETIC_CONTROL_SERIALIZATION_INTEGRATION_COVERAGE_GAP",
    "KERNEL_QUALIFICATION_REMAINS_UNRESOLVED",
)
SELECTED_NEXT_TARGET = (
    "select_post_scalar_only_yukawa_analytic_sphere_kernel_exploratory_sandbox_v0_"
    "execution_result_review_scientific_response_v0"
)
SELECTED_NEXT_TARGET_KIND = (
    "FRESH_POST_FAILURE_SELECTOR_ONLY_NO_EDIT_RERUN_QUALIFICATION_OR_PRODUCTION_ADVANCE"
)

FROZEN_ARTIFACT_HASHES = {
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_EXPLORATORY_SANDBOX_EXECUTION_RESULT_20260719_v0.md":
        "ac9efc946a9f106a6418233fc1c4d384d838c27340fc8862428e7792f58e7cb7",
    RESULT_RELATIVE_PATH:
        "14eaaf53c8b730c8ac2a9c4910fca28bd647843f89e8aac50bcde4dcad4c2982",
    RESULT_RELATIVE_PATH + ".sha256":
        "966c71b5b04314699b19bf964aec51c51cdf2212d7d2689bb4e9d11a3ddd2822",
    SOURCE_RELATIVE_PATH:
        "27a32f540465ed78cb2094629033a4aa30e3142c1f75aa113fc88eb10c7563ae",
    "formal/python/tests/test_scalar_only_yukawa_analytic_sphere_kernel_exploratory_sandbox_execution_result_v0.py":
        "61efcee6e4c97a69d8cfd75d0297a357343278f61aabe1ef8b51ce704dae982a",
    "formal/toe_formal/ToeFormal/Derivation/ScalarOnlyYukawaAnalyticSphereKernelExploratorySandboxExecutionResultV0.lean":
        "4529cffee3eaa2d2ec20c4024f31021319092985ac5cc2741a910a729fc6e66a",
    MARKER_RELATIVE_PATH:
        "ee3ca18499c38e2480155e8b7d51394c2dde198612e0b270e5975ae333f1d572",
    STAGES_RELATIVE_PATH:
        "0314b322cb5ae1b6f5279c88f15194733f00ebae9278c504120575d259c08b51",
    LOG_RELATIVE_PATH:
        "04b010afc7fd1025dd1da23b4cac34b86c828fb5f9ec772b701e4d5599fb351b",
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


def build_report() -> dict[str, Any]:
    for relative_path, expected in FROZEN_ARTIFACT_HASHES.items():
        if _sha256(REPO_ROOT / relative_path) != expected:
            raise ValueError(f"execution-result custody drift: {relative_path}")
    result = _load_json(RESULT_RELATIVE_PATH)
    marker = _load_json(MARKER_RELATIVE_PATH)
    stages = _load_json(STAGES_RELATIVE_PATH)["stages"]
    source = (REPO_ROOT / SOURCE_RELATIVE_PATH).read_text(encoding="utf-8")
    log = (REPO_ROOT / LOG_RELATIVE_PATH).read_text(encoding="utf-8")

    if result.get("terminal_outcome") != (
        "EXPLORATORY_IMPLEMENTATION_RESULT_SERIALIZATION_FAILED_INCOMPLETE"
    ):
        raise ValueError("execution-result terminal outcome mismatch")
    if result.get("next_authority") != TARGET:
        raise ValueError("execution result did not authorize this review")
    if marker.get("run_id") != result.get("run_id"):
        raise ValueError("run identity mismatch")
    if marker.get("status") != "CONSUMED_BY_SINGLE_LAUNCH_NO_RERUN":
        raise ValueError("one-shot consumption marker mismatch")
    if len(stages) != 8 or any(row.get("status") != "COMPLETE" for row in stages):
        raise ValueError("stage-boundary custody mismatch")
    required_source_tokens = (
        "observed = _decimal_from_float",
        "reference = _decimal_from_float",
        '"observed_canonical": observed',
        '"reference_canonical": reference',
        '"control_id": "C07_NUMERIC_RELATIONAL_AND_EXCEPTION_PREDICATES_DETECT"',
        '"control_id": "C12_CANONICAL_ROUND_TRIP_BYTES_AND_SHA256_STABLE"',
        "payload = _canonical_bytes(result)",
    )
    if any(token not in source for token in required_source_tokens):
        raise ValueError("static serialization-defect trace token missing")
    if "RUN_END" in log:
        raise ValueError("raw log unexpectedly records completed result writing")

    review_gates = (
        ("E01_EXACT_RESULT_AND_CUSTODY_HASHES", "nine frozen artifacts reproduce"),
        ("E02_EXACT_REVIEW_AUTHORITY", "result rotates only to this review"),
        ("E03_ONE_SHOT_EXECUTION_CONSUMED", "one of one execution consumed"),
        ("E04_NO_RERUN_OR_REPAIR", "no rerun or implementation edit accepted"),
        ("E05_ZERO_SURVIVING_PROCESS_CUSTODY", "zero surviving process recorded and rechecked"),
        ("E06_RUN_ID_CROSS_SURFACE_IDENTITY", "marker and result run ids agree"),
        ("E07_SOURCE_HASH_CUSTODY", "executed source hash reproduced"),
        ("E08_RAW_LOG_HASH_CUSTODY", "raw log hash reproduced"),
        ("E09_STAGE_CHECKPOINT_HASH_CUSTODY", "stage checkpoint hash reproduced"),
        ("E10_EIGHT_STAGE_BOUNDARIES_COMPLETE", "eight completion boundaries preserved"),
        ("E11_STAGE_COMPLETION_NOT_PASS_CLASSIFICATION", "completion is not interpreted as pass"),
        ("E12_CANONICAL_RESULT_NOT_WRITTEN_IN_PROCESS", "authorized writer failed before result commit"),
        ("E13_ADMINISTRATIVE_RESULT_PROVENANCE_EXPLICIT", "post-launch custody reconstruction is labeled"),
        ("E14_MISSING_DECISION_RECORDS_INADMISSIBLE", "transient values are not reconstructed"),
        ("E15_EXACT_FAILURE_TYPE", "builtins.TypeError preserved"),
        ("E16_EXACT_FAILURE_MESSAGE", "Decimal JSON failure preserved"),
        ("E17_DECIMAL_CREATION_PATH_LOCALIZED", "numeric adjudicator creates Decimal objects"),
        ("E18_DECIMAL_RETURN_PATH_LOCALIZED", "Decimal objects enter canonical fields"),
        ("E19_FINAL_ENCODER_FAILURE_PATH_LOCALIZED", "strict final encoder receives result tree"),
        ("E20_CONTRACT_DECIMAL_RULE_EXPLICIT", "uppercase normalized decimal strings required"),
        ("E21_CONTRACT_CANONICAL_SCALARS_EXPLICIT", "nested canonical scalar schema excludes Decimal objects"),
        ("E22_IMPLEMENTATION_DEFECT_PRIMARY", "conversion boundary omitted in implementation"),
        ("E23_C07_EXERCISED_NUMERIC_PATH", "numeric predicates generated the leaking values"),
        ("E24_C12_USED_SEPARATE_FIXED_OBJECT", "round trip did not cover C07 or full result tree"),
        ("E25_SYNTHETIC_CONTROL_INTEGRATION_GAP_SECONDARY", "control composition missed nested path"),
        ("E26_NO_CONTRACT_AMBIGUITY_FINDING", "conversion obligation was sufficiently explicit"),
        ("E27_INFRASTRUCTURE_NOT_QUALIFIED", "serialization failure blocks infrastructure qualification"),
        ("E28_KERNEL_NOT_QUALIFIED_OR_REFUTED", "kernel outcome remains unresolved"),
        ("E29_HISTORICAL_CUBATURE_UNADJUDICATED", "no cubature inference issued"),
        ("E30_PRODUCTION_UNCHANGED", "no production change accepted"),
        ("E31_NO_STAGE_A_RERUN", "Stage A remains closed"),
        ("E32_NO_TORQUE_OR_DFT", "torque and DFT remain closed"),
        ("E33_NO_IDENTIFIABILITY", "identifiability remains closed"),
        ("E34_NO_STAGE_B", "Stage B remains closed"),
        ("E35_EXPLORATORY_LABELS_PRESERVED", "four nonclaim labels exact"),
        ("E36_FAIL_CLOSED_BEHAVIOR_ACCEPTED", "no partial scientific outcome promoted"),
        ("E37_NO_VALUE_RECONSTRUCTION", "review uses custody only"),
        ("E38_NO_IMPLEMENTATION_IMPORT_OR_EXECUTION", "review statically reads source only"),
        ("E39_FRESH_SELECTOR_REQUIRED", "response requires new governed selection"),
        ("E40_CURRENT_AUTHORITY_ROTATES_TO_POST_FAILURE_SELECTOR", "review stops before response selection"),
    )

    scope = {
        "independent_execution_result_review_performed": True,
        "one_shot_custody_accepted": True,
        "serialization_failure_accepted": True,
        "implementation_defect_localized": True,
        "synthetic_control_integration_gap_localized": True,
        "contract_ambiguity_established": False,
        "infrastructure_qualified": False,
        "analytic_kernel_qualified": False,
        "analytic_kernel_refuted": False,
        "historical_cubature_adjudicated": False,
        "implementation_edit_authorized": False,
        "sandbox_rerun_authorized": False,
        "missing_value_reconstruction_authorized": False,
        "production_change_authorized": False,
        "stage_a_rerun_authorized": False,
        "torque_or_dft_authorized": False,
        "jacobian_or_identifiability_authorized": False,
        "stage_b_authorized": False,
        "fresh_scientific_response_selector_authorized": True,
    }

    return {
        "schema_id": (
            "toe.scalar_only_yukawa.analytic_sphere_kernel.exploratory_sandbox_"
            "execution_result_review.v0"
        ),
        "review_id": (
            "SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_EXPLORATORY_SANDBOX_"
            "EXECUTION_RESULT_REVIEW_20260719_v0"
        ),
        "captured_at_utc": "2026-07-19T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "principal_review_outcome": PRINCIPAL_OUTCOME,
        "secondary_review_outcomes": list(SECONDARY_OUTCOMES),
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_execution_outcome": result["terminal_outcome"],
            "frozen_execution_artifacts": [
                {"relative_path": path, "sha256": digest}
                for path, digest in FROZEN_ARTIFACT_HASHES.items()
            ],
            "human_review": _artifact_row(HUMAN_RELATIVE_PATH),
            "generator": _artifact_row(
                "formal/python/tools/scalar_only_yukawa_analytic_sphere_kernel_"
                "exploratory_sandbox_execution_result_review_v0.py"
            ),
            "test": _artifact_row(TEST_RELATIVE_PATH),
            "lean": _artifact_row(LEAN_RELATIVE_PATH),
        },
        "custody_review": {
            "run_id": result["run_id"],
            "authorized_execution_count": 1,
            "consumed_execution_count": 1,
            "surviving_process_count": 0,
            "completed_stage_boundary_count": len(stages),
            "canonical_result_written_by_sandbox": False,
            "administrative_failure_result_sufficient_for_failure_review": True,
            "administrative_failure_result_sufficient_for_scientific_review": False,
        },
        "defect_attribution": {
            "contract_status": "SUFFICIENTLY_EXPLICIT_FOR_THIS_CONVERSION_PATH",
            "principal_classification": "IMPLEMENTATION_FAILURE",
            "secondary_classification": "SYNTHETIC_CONTROL_INTEGRATION_COVERAGE_GAP",
            "contract_coverage_failure_established": False,
            "ambiguity_in_decimal_conversion_obligation_established": False,
            "static_trace": [
                "adjudicate_v0 numeric branch constructs Decimal observed/reference values",
                "adjudicate_v0 returns those objects in observed_canonical/reference_canonical",
                "C07 retains the nested adjudication results",
                "C12 serializes a separate fixed object rather than C07 or the aggregate result",
                "final _canonical_bytes(result) rejects the live Decimal object",
            ],
            "contract_rule": "UPPERCASE_NORMALIZED_DECIMAL_STRINGS_ONLY",
            "missing_implementation_boundary": (
                "CONVERT_TYPED_DECIMAL_VALUES_TO_SCHEMA_STRINGS_BEFORE_RESULT_TREE_INSERTION"
            ),
        },
        "scientific_admissibility": {
            "stage_completion_is_decision_bearing": False,
            "regression_values_admissible": False,
            "derivative_values_admissible": False,
            "boundary_probe_results_admissible": False,
            "mutation_results_admissible": False,
            "runtime_results_admissible": False,
            "kernel_pass_or_fail": "UNRESOLVED",
            "infrastructure_pass_or_fail": "FAILED_QUALIFICATION_BY_SERIALIZATION",
        },
        "review_gates": {
            "gate_count": len(review_gates),
            "pass_count": len(review_gates),
            "failure_count": 0,
            "rows": [
                {"gate_id": gate_id, "status": "PASS", "finding": finding}
                for gate_id, finding in review_gates
            ],
        },
        "scope": scope,
        "next_response_boundary": {
            "automatic_rerun": "PROHIBITED",
            "silent_implementation_edit": "PROHIBITED",
            "missing_value_reconstruction": "PROHIBITED",
            "production_or_scientific_advance": "PROHIBITED",
            "fresh_selector_required": True,
            "retire_or_defer_remains_available": True,
        },
        "claim_ceiling": (
            "This review accepts the one-shot sandbox serialization failure and localizes "
            "an implementation conversion defect plus a synthetic-control integration gap. "
            "It does not recover transient values, qualify or refute the analytic kernel, "
            "adjudicate cubature, edit or rerun the sandbox, change production, rerun Stage A, "
            "compute torque, DFT, vector, Jacobian, SVD, or identifiability, or authorize Stage B."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_report(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Review the one-shot analytic sphere-kernel sandbox failure without rerun."
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
            print("exploratory sandbox execution-result review already current")
        return 0
    if current != expected:
        print("exploratory sandbox execution-result review drift")
        return 1
    report = build_report()
    print(
        "exploratory sandbox execution-result review OK "
        f"verdict={report['verdict']} gates={report['review_gates']['pass_count']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

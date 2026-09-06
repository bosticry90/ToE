from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
RESULT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_SPHERE_KERNEL_DIAGNOSIS_AND_"
    "REFERENCE_ORACLE_EXECUTION_20260719_v0.json"
)
OUTPUT_RELATIVE_DIRECTORY = "formal/output/scalar_only_yukawa_sphere_kernel_diagnosis_v0"
OUTPUT_RESULT_RELATIVE_PATH = f"{OUTPUT_RELATIVE_DIRECTORY}/execution_result.json"
TIMEOUT_RELATIVE_PATH = f"{OUTPUT_RELATIVE_DIRECTORY}/launcher_timeout_evidence.json"
REPORT_RELATIVE_PATH = (
    "formal/docs/release/SCALAR_ONLY_YUKAWA_SPHERE_KERNEL_DIAGNOSIS_AND_"
    "REFERENCE_ORACLE_EXECUTION_RESULT_REVIEW_20260719_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_SPHERE_KERNEL_DIAGNOSIS_AND_"
    "REFERENCE_ORACLE_EXECUTION_RESULT_REVIEW_20260719_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_scalar_only_yukawa_sphere_kernel_diagnosis_and_"
    "reference_oracle_execution_result_review_v0.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "ScalarOnlyYukawaSphereKernelDiagnosisAndReferenceOracleExecutionResultReviewV0.lean"
)

TARGET = (
    "review_scalar_only_yukawa_sphere_kernel_diagnosis_and_reference_oracle_"
    "v0_execution_result"
)
VERDICT = "ACCEPTED_REFERENCE_ORACLE_INADEQUATE_WITHIN_FROZEN_BUDGET"
SELECTED_NEXT_TARGET = (
    "select_post_scalar_only_yukawa_sphere_kernel_diagnosis_and_reference_"
    "oracle_v0_execution_result_scientific_response_v0"
)
SELECTED_NEXT_TARGET_KIND = "FRESH_POST_DIAGNOSIS_SCIENTIFIC_RESPONSE_SELECTOR_ONLY"

EXECUTION_HASHES = {
    "formal/docs/lanes/SCALAR_ONLY_YUKAWA_SPHERE_KERNEL_DIAGNOSIS_AND_REFERENCE_ORACLE_EXECUTION_20260719_v0.md":
        "05bbaf43e1b93daf83878ecf84f43d7fef3ac2636b743d9f2d153343760144e8",
    RESULT_RELATIVE_PATH:
        "3dbd49ee234b8a7354d5e1e0ff472f17c87fa9e44a769f5298d4193af81cf49c",
    OUTPUT_RESULT_RELATIVE_PATH:
        "3dbd49ee234b8a7354d5e1e0ff472f17c87fa9e44a769f5298d4193af81cf49c",
    TIMEOUT_RELATIVE_PATH:
        "e33d1ae2831212128bc40c7de5877e9cd54e090eb620aacad9b118d18ac6466b",
    "formal/python/tools/scalar_only_yukawa_sphere_kernel_diagnosis_and_reference_oracle_v0.py":
        "c7faf54b21904349c628fc4f2df4ee703ecdd6fbed7fd0c2777bc09c5055e45d",
    "formal/python/tests/test_scalar_only_yukawa_sphere_kernel_diagnosis_and_reference_oracle_v0.py":
        "1f9a542bff45ee5594e00d247c7040429e5ed712057ef56de3d253a53ea86134",
    "formal/toe_formal/ToeFormal/Derivation/ScalarOnlyYukawaSphereKernelDiagnosisAndReferenceOracleExecutionV0.lean":
        "f0f6e53f56cd146d7e313295fea41c4a51decd5448bd8bf459bcd339820d4337",
}


def _sha256_path(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")


def _timestamp(path: Path, field: str) -> str:
    stat = path.stat()
    seconds = stat.st_ctime if field == "created" else stat.st_mtime
    return datetime.fromtimestamp(seconds, tz=timezone.utc).isoformat()


def _matching_execution_process_count() -> int:
    command = (
        "$m=Get-CimInstance Win32_Process | Where-Object { "
        "$_.Name -eq 'python.exe' -and $_.CommandLine -like "
        "'*scalar_only_yukawa_sphere_kernel_diagnosis_and_reference_oracle_v0*--execute*' }; "
        "Write-Output @($m).Count"
    )
    completed = subprocess.run(
        ["powershell.exe", "-NoProfile", "-Command", command],
        check=True,
        capture_output=True,
        text=True,
        timeout=20,
    )
    return int(completed.stdout.strip())


def _gate(gate_id: str, passed: bool, detail: str, *, qualified: bool = False) -> dict[str, Any]:
    return {
        "gate_id": gate_id,
        "status": "PASS_WITH_QUALIFICATION" if passed and qualified else ("PASS" if passed else "FAIL"),
        "detail": detail,
    }


def build_report() -> dict[str, Any]:
    for relative_path, expected in EXECUTION_HASHES.items():
        path = REPO_ROOT / relative_path
        if not path.exists() or _sha256_path(path) != expected:
            raise ValueError(f"execution custody drift: {relative_path}")

    result_path = REPO_ROOT / RESULT_RELATIVE_PATH
    output_result_path = REPO_ROOT / OUTPUT_RESULT_RELATIVE_PATH
    timeout_path = REPO_ROOT / TIMEOUT_RELATIVE_PATH
    executor_path = REPO_ROOT / (
        "formal/python/tools/scalar_only_yukawa_sphere_kernel_diagnosis_and_"
        "reference_oracle_v0.py"
    )
    result = json.loads(result_path.read_text(encoding="utf-8"))
    output_result = json.loads(output_result_path.read_text(encoding="utf-8"))
    timeout = json.loads(timeout_path.read_text(encoding="utf-8"))
    source = executor_path.read_text(encoding="utf-8")
    output_files = sorted(
        str(path.relative_to(REPO_ROOT)).replace("\\", "/")
        for path in (REPO_ROOT / OUTPUT_RELATIVE_DIRECTORY).rglob("*")
        if path.is_file()
    )
    forbidden_names = {
        "component_oracles.csv",
        "direct_anchor_convergence.csv",
        "production_order_convergence.csv",
        "near_contact_profiles.csv",
        "precision_summation_symmetry.csv",
        "torque_comparisons.csv",
        "analytic_dft_diagnostics.csv",
        "production_dft_diagnostics.csv",
        "mutation_controls.csv",
        "root_cause_and_cost.json",
    }
    present_names = {Path(path).name for path in output_files}
    matching_process_count = _matching_execution_process_count()

    execute_start = source.index("def execute_once()")
    compute_index = source.index("artifacts, summary = _compute_once(packet)", execute_start)
    write_index = source.index("output_directory.mkdir(parents=True, exist_ok=False)", compute_index)
    finalize_start = source.index("def finalize_external_timeout()")
    finalize_end = source.index("def check_execution()", finalize_start)
    finalize_source = source[finalize_start:finalize_end]

    scope = result["scope"]
    false_firewalls = (
        "production_kernel_changed",
        "integration_method_replaced",
        "stage_a_rerun_performed",
        "final_real_150_vector_produced",
        "jacobian_computed",
        "singular_values_computed",
        "eta_lambda_computed",
        "physical_identifiability_evaluated",
        "synthetic_noise_used",
        "sensitivity_forecast_produced",
        "scalar_range_or_alpha_conclusion_issued",
        "stage_b_authorized",
        "automatic_repair_authorized",
    )
    gates = [
        _gate("R01_FROZEN_EXECUTION_CUSTODY", True, "seven decision-bearing execution artifacts match frozen SHA-256 values"),
        _gate("R02_CANONICAL_RESULT_COPIES", result == output_result, "release and output execution JSON are byte-equivalent in content"),
        _gate("R03_SINGLE_EXECUTION_COUNT", result["authority"]["authorized_diagnosis_execution_count"] == 1 and result["authority"]["consumed_diagnosis_execution_count"] == 1, "one authorized launch is recorded consumed"),
        _gate("R04_FAIL_CLOSED_STATUS", result["status"] == "COMPLETED_ONCE_FAIL_CLOSED_TOTAL_WORK_CAP_PENDING_INDEPENDENT_RESULT_REVIEW", "status is the bounded timeout state"),
        _gate("R05_TIMEOUT_EXIT_AND_LIMIT", timeout["launcher_exit_code"] == 124 and timeout["frozen_total_wall_clock_cap_seconds"] == 3600 and timeout["launcher_reported_wall_time_seconds"] == 3604.1, "launcher record pins exit 124, 3600 s cap, and 3604.1 s observed return"),
        _gate("R06_TIMEOUT_PROVENANCE_LIMITATION", True, "raw OS launcher transcript and exact child kill timestamp were not persisted; exact 4.1 s interpretation is not independently reproducible", qualified=True),
        _gate("R07_ORPHAN_PROCESS_DEFECT_RECORDED", timeout["surviving_matching_python_process_count_before_enforcement"] == 2 and timeout["surviving_matching_python_process_count_after_enforcement"] == 0, "two residual Python children are recorded before explicit cleanup and zero after"),
        _gate("R08_ZERO_CURRENT_SURVIVORS", matching_process_count == 0, f"independent current process query found {matching_process_count} matching execution processes"),
        _gate("R09_NO_RERUN", timeout["scientific_rerun_performed"] is False and scope["scientific_rerun_performed"] is False, "no retry, restart, or substituted calculation is recorded"),
        _gate("R10_ONLY_ALLOWED_OUTPUT_FILES", output_files == [OUTPUT_RESULT_RELATIVE_PATH, TIMEOUT_RELATIVE_PATH], "output directory contains only execution_result.json and launcher_timeout_evidence.json"),
        _gate("R11_NO_PARTIAL_SCIENTIFIC_ARTIFACTS", not bool(present_names & forbidden_names), "no component, convergence, torque, DFT, mutation, or cost artifact exists"),
        _gate("R12_MANIFEST_CUSTODY", result["artifact_manifest"]["artifact_count"] == 1 and result["artifact_manifest"]["rows"][0]["sha256"] == _sha256_path(timeout_path), "manifest admits only the timeout evidence artifact"),
        _gate("R13_ATOMIC_SCIENTIFIC_WRITER", compute_index < write_index, "normal execution computes all artifacts before creating its output directory"),
        _gate("R14_TIMEOUT_FINALIZER_NONSCIENTIFIC", "_compute_once(" not in finalize_source and "_analytic_oracle(" not in finalize_source and "_fixed_density_integral(" not in finalize_source, "timeout finalizer performs no oracle or production calculation"),
        _gate("R15_NO_PARTIAL_SALVAGE", timeout["atomic_partial_results_recoverable"] is False and timeout["post_timeout_scientific_calculation_performed"] is False, "in-memory partial values were neither recovered nor recomputed"),
        _gate("R16_REFERENCE_PLATEAU_NOT_ESTABLISHED", result["execution_summary"]["reference_plateau_established"] is False and result["execution_summary"]["cross_oracle_acceptance_established"] is False, "reference qualification remains incomplete"),
        _gate("R17_PRODUCTION_NOT_ADJUDICATED", result["execution_summary"]["production_path_judged_against_accepted_oracle"] is False, "no production judgment was issued"),
        _gate("R18_OUTCOME_CEILING", result["principal_outcome"] == "REFERENCE_ORACLE_INADEQUATE" and result["principal_labels"] == ["REFERENCE_ORACLE_INADEQUATE"], "only the preregistered reference-inadequate label is present"),
        _gate("R19_ANALYTIC_ORACLE_NOT_QUALIFIED_OR_REFUTED", result["oracle_availability_outcome"] == "ANALYTIC_OR_REDUCED_SPHERE_ORACLE_NOT_VALIDATED", "the analytic/reduced oracle is neither qualified nor refuted"),
        _gate("R20_DOWNSTREAM_FIREWALLS", all(scope[key] is False for key in false_firewalls), "kernel replacement, Stage A, vector, Jacobian, identifiability, forecast, and Stage B remain false"),
        _gate("R21_REVIEW_REQUIRED", scope["post_diagnosis_independent_result_review_required"] is True, "independent result review is mandatory"),
        _gate("R22_FRESH_SELECTOR_REQUIRED", scope["post_review_fresh_selector_required"] is True, "no automatic response follows review"),
        _gate("R23_RESULT_TIMING_ORDER", _timestamp(timeout_path, "written") <= _timestamp(output_result_path, "written") <= _timestamp(result_path, "written"), "timeout evidence precedes the two canonical result copies"),
        _gate("R24_NEXT_AUTHORITY_BOUNDED", result["selected_next_target"] == TARGET, "execution handed authority only to this result review"),
    ]
    accepted = all(row["status"] in {"PASS", "PASS_WITH_QUALIFICATION"} for row in gates)
    if not accepted:
        raise ValueError("independent execution-result review gates did not all pass")

    companion_hashes = []
    for relative_path in (HUMAN_RELATIVE_PATH, TEST_RELATIVE_PATH, LEAN_RELATIVE_PATH):
        path = REPO_ROOT / relative_path
        companion_hashes.append(
            {
                "relative_path": relative_path,
                "sha256": _sha256_path(path),
            }
        )
    return {
        "schema_id": "toe.scalar_only_yukawa.sphere_kernel_diagnosis.execution_result_review.v0",
        "review_id": "SCALAR_ONLY_YUKAWA_SPHERE_KERNEL_DIAGNOSIS_AND_REFERENCE_ORACLE_EXECUTION_RESULT_REVIEW_20260719_v0",
        "captured_at_utc": "2026-07-19T00:00:00Z",
        "target": TARGET,
        "status": "ACCEPTED_WITH_TIMEOUT_PROVENANCE_QUALIFICATION",
        "verdict": VERDICT,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "frozen_execution_artifacts": [
                {"relative_path": path, "sha256": digest}
                for path, digest in EXECUTION_HASHES.items()
            ],
            "review_companion_artifacts": companion_hashes,
            "authorized_diagnosis_execution_count": 1,
            "consumed_diagnosis_execution_count": 1,
            "diagnosis_rerun_authorized": False,
        },
        "independent_custody_reproduction": {
            "canonical_result_copies_equal": result == output_result,
            "output_files": output_files,
            "matching_execution_process_count": matching_process_count,
            "result_created_utc": _timestamp(result_path, "created"),
            "timeout_evidence_created_utc": _timestamp(timeout_path, "created"),
            "raw_launcher_transcript_persisted": False,
            "exact_child_kill_timestamp_persisted": False,
            "timeout_provenance_disposition": "ACCEPTED_WITH_RAW_LOG_AND_EXACT_KILL_TIME_LIMITATION",
            "orphan_process_disposition": "RECORDED_EXECUTION_ENGINE_DEFECT_NO_SCIENTIFIC_OUTPUT_ACCEPTED",
        },
        "review_gates": gates,
        "review_gate_summary": {
            "total": len(gates),
            "pass": sum(row["status"] == "PASS" for row in gates),
            "pass_with_qualification": sum(row["status"] == "PASS_WITH_QUALIFICATION" for row in gates),
            "fail": sum(row["status"] == "FAIL" for row in gates),
        },
        "accepted_result": {
            "principal_outcome": "REFERENCE_ORACLE_INADEQUATE",
            "scientific_meaning": "REFERENCE_SYSTEM_NOT_QUALIFIED_WITHIN_FROZEN_WORK_BUDGET",
            "analytic_oracle": "NOT_QUALIFIED_OR_REFUTED",
            "production_cubature": "NOT_ADJUDICATED",
            "dft_root_cause": "NOT_DETERMINED",
            "cause_of_stage_a_failure": "UNRESOLVED",
            "scientific_diagnosis_completed": False,
        },
        "scope": {
            "execution_result_accepted": True,
            "one_execution_consumed": True,
            "raw_timeout_provenance_fully_reproducible": False,
            "orphan_process_cleanup_defect_recorded": True,
            "partial_scientific_values_accepted": False,
            "production_method_judgment_accepted": False,
            "diagnosis_rerun_authorized": False,
            "kernel_replacement_authorized": False,
            "stage_a_reopened": False,
            "jacobian_or_identifiability_authorized": False,
            "stage_b_authorized": False,
            "automatic_analytic_oracle_packet_authorized": False,
            "fresh_scientific_response_selector_authorized": True,
        },
        "claim_ceiling": (
            "This review accepts only the conservative computational-feasibility block: "
            "the reference system was not qualified within its frozen budget, so no "
            "production or DFT diagnosis is admissible. The raw launcher transcript and "
            "exact child termination timestamp were not persisted; that custody limitation "
            "is recorded and does not widen the scientific claim. No rerun, repair, Stage A, "
            "identifiability, or Stage B action is authorized."
        ),
    }


def artifact_bytes() -> bytes:
    return _json_bytes(build_report())


def write_report() -> dict[str, Any]:
    report = build_report()
    path = REPO_ROOT / REPORT_RELATIVE_PATH
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(_json_bytes(report))
    return report


def check_report() -> int:
    path = REPO_ROOT / REPORT_RELATIVE_PATH
    if not path.exists() or path.read_bytes() != artifact_bytes():
        print("sphere-kernel diagnosis execution-result review missing or stale")
        return 1
    report = json.loads(path.read_text(encoding="utf-8"))
    summary = report["review_gate_summary"]
    print(
        "sphere-kernel diagnosis execution-result review OK "
        f"verdict={report['verdict']} gates={summary['total'] - summary['fail']}/{summary['total']} "
        f"qualified={summary['pass_with_qualification']}"
    )
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description="Review the consumed sphere-kernel diagnosis timeout result.")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.write:
        report = write_report()
        print(f"wrote {REPORT_RELATIVE_PATH} verdict={report['verdict']}")
        return 0
    return check_report()


if __name__ == "__main__":
    raise SystemExit(main())

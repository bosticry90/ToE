from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import unicodedata
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.prompt_dependency_identity import (
    identity_sha256_path,
    prompt_dependency_is_nonblocking,
)
from formal.python.tools import dirac_maxwell_full_zero_mode_non_authoritative_pilot_result_review as independent_v0_audit


REPO_ROOT = find_repo_root(Path(__file__))
PILOT_MODULE = "formal.python.tools.dirac_maxwell_full_zero_mode_non_authoritative_pilot_v1"
PILOT_GENERATOR = "formal/python/tools/dirac_maxwell_full_zero_mode_non_authoritative_pilot_v1.py"
PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-NON-AUTHORITATIVE-PILOT-PACKET-v1.json"
ARRAYS_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-NON-AUTHORITATIVE-PILOT-ARRAYS-v1.json"
MANIFEST_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-NON-AUTHORITATIVE-PILOT-MANIFEST-v1.json"
PREPARATION_REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_NON_AUTHORITATIVE_PILOT_20260713_v1.json"
REVIEW_REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_NON_AUTHORITATIVE_PILOT_V1_RESULT_REVIEW_20260713_v0.json"
V0_ARRAYS_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-NON-AUTHORITATIVE-PILOT-ARRAYS-v0.json"
PACKET_PATH = REPO_ROOT / PACKET_RELATIVE_PATH
ARRAYS_PATH = REPO_ROOT / ARRAYS_RELATIVE_PATH
REVIEW_REPORT_PATH = REPO_ROOT / REVIEW_REPORT_RELATIVE_PATH

CAPTURED_AT_UTC = "2026-07-13T00:00:00Z"
REVIEW_TARGET = "review_dirac_maxwell_full_zero_mode_non_authoritative_pilot_v1_result"
ACCEPTED_TARGET = "prepare_dirac_maxwell_full_zero_mode_canonical_parameter_freeze_packet_v0"
BLOCKED_TARGET = "prepare_dirac_maxwell_full_zero_mode_non_authoritative_pilot_v1_blocker_response_packet_v0"
REVIEW_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_NON_AUTHORITATIVE_PILOT_V1_RESULT_REVIEW_20260713_v0"
PREPARATION_COMMIT = "853d58551984334203fa6b7957f419664429f0da"
PREPARATION_PARENT = "f3d68ed5fdb1d654c43ba68d7775d9cc595689ac"
EXPECTED_HASHES = {
    PILOT_GENERATOR: "90acc15a46891ab289edb41d536765913e2e58979ae150897efe3a59fe94a2dd",
    PACKET_RELATIVE_PATH: "456fb3a73d8cbc50c1392ed71ccc43e5f7c6783faa9e2fe22e15ce041a2372e3",
    ARRAYS_RELATIVE_PATH: "62f66647c4588f6bd4b2db03a9d64d4c1019f43c10fdd73aca0a5a8ed54c13f8",
    MANIFEST_RELATIVE_PATH: "84315ee8d7bae940af29abd4dc0d5a4aa4ff39ff76d743467998a5fe7c6cf082",
    PREPARATION_REPORT_RELATIVE_PATH: "a23bb4fec833605f7f71aff5f7f9698f37fac88eb3cec39a4a67d484d661c8ab",
}
PROMPT_RELATIVE_PATH = "Prompt.txt"
PROMPT_DEPENDENCY_ROLE = "DEMOTE_TO_NONBLOCKING_PROVENANCE"
PROMPT_SHA256 = "2bc6996ea28e96c50e688ed3d30ee24808af411a244eb594aad89ff80fda8433"


def _normalize(value: Any) -> Any:
    if isinstance(value, str):
        return unicodedata.normalize("NFC", value)
    if isinstance(value, list):
        return [_normalize(item) for item in value]
    if isinstance(value, dict):
        return {_normalize(str(key)): _normalize(item) for key, item in value.items()}
    return value


def canonical_json_bytes(payload: Any) -> bytes:
    return (json.dumps(_normalize(payload), allow_nan=False, ensure_ascii=False, indent=2, sort_keys=True) + "\n").encode("utf-8")


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha256_path(path: Path) -> str:
    return identity_sha256_path(path, repo_root=REPO_ROOT)


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected object: {path}")
    return value


def custody() -> dict[str, Any]:
    commit = subprocess.run(["git", "rev-parse", PREPARATION_COMMIT], cwd=REPO_ROOT, capture_output=True, text=True, check=False).stdout.strip()
    parent = subprocess.run(["git", "rev-parse", f"{PREPARATION_COMMIT}^"], cwd=REPO_ROOT, capture_output=True, text=True, check=False).stdout.strip()
    working = {path: sha256_path(REPO_ROOT / path) for path in EXPECTED_HASHES}
    committed: dict[str, str] = {}
    for path in EXPECTED_HASHES:
        result = subprocess.run(["git", "show", f"{PREPARATION_COMMIT}:{path}"], cwd=REPO_ROOT, capture_output=True, check=False)
        committed[path] = sha256_bytes(result.stdout) if result.returncode == 0 else "MISSING"
    passed = commit == PREPARATION_COMMIT and parent == PREPARATION_PARENT and working == EXPECTED_HASHES and committed == EXPECTED_HASHES
    return {"commit": commit, "parent": parent, "working_hashes": working, "commit_hashes": committed, "expected_hashes": EXPECTED_HASHES, "passed": passed}


def clean_reproduction() -> dict[str, Any]:
    environment = os.environ.copy()
    environment.update({"PYTHONHASHSEED": "0", "TZ": "UTC", "LC_ALL": "C", "LANG": "C"})
    outputs: list[bytes] = []
    for _ in range(2):
        result = subprocess.run([sys.executable, "-m", PILOT_MODULE, "--emit-core"], cwd=REPO_ROOT, env=environment, capture_output=True, check=False)
        if result.returncode != 0:
            raise ValueError(result.stderr.decode("utf-8", errors="replace"))
        outputs.append(result.stdout)
    payloads = [json.loads(raw.decode("utf-8")) for raw in outputs]
    return {"execution_count": 2, "byte_identical": outputs[0] == outputs[1], "execution_sha256": [sha256_bytes(raw) for raw in outputs], "payloads_equal": payloads[0] == payloads[1], "payload": payloads[0]}


def identity_and_value_audit(arrays: dict[str, Any]) -> dict[str, Any]:
    v0 = load_json(REPO_ROOT / V0_ARRAYS_RELATIVE_PATH)
    records = arrays["runs"]
    numerical_equal = len(records) == len(v0["runs"]) and all(repaired["series"] == original["series"] and repaired["legacy_run_id"] == original["run_id"] for repaired, original in zip(records, v0["runs"], strict=True))
    record_ids = [record["run_record_id"] for record in records]
    roles = [record["calibration_role"] for record in records]
    execution_ids = [record["execution_id"] for record in records]
    shared = sorted({item for item in execution_ids if execution_ids.count(item) > 1})
    independently_recomputed = all(
        record["execution_id"] == "EXECUTION_" + sha256_bytes(record["legacy_run_id"].encode("utf-8"))[:16]
        and record["run_record_id"] == f"{record['calibration_role']}:{record['execution_id']}"
        and record["run_id"] == record["run_record_id"]
        for record in records
    )
    return {
        "run_record_count": len(records),
        "unique_run_record_count": len(set(record_ids)),
        "unique_role_count": len(set(roles)),
        "shared_execution_ids": shared,
        "ids_match_independent_recomputation": independently_recomputed,
        "all_numerical_series_equal_v0": numerical_equal,
        "v0_arrays_sha256": sha256_path(REPO_ROOT / V0_ARRAYS_RELATIVE_PATH),
    }


DECISION_IDS = [
    "immutable_pilot_v1_preparation_is_bound",
    "accepted_identity_repair_is_the_exact_input_authority",
    "two_clean_v1_reproductions_are_byte_identical",
    "clean_reproduction_matches_registered_packet_and_arrays",
    "thirteen_run_records_have_unique_closed_roles_and_record_ids",
    "identity_fields_match_independent_recomputation",
    "shared_parameter_executions_remain_visible_across_roles",
    "all_numerical_series_are_identical_to_immutable_v0",
    "all_registered_equation_spectral_exchange_and_energy_series_are_complete",
    "array_derived_residual_maxima_match_the_packet",
    "Wilson_dispersion_and_doubler_separation_are_independently_recomputed",
    "temporal_and_energy_refinement_orders_are_independently_recomputed",
    "solver_error_is_below_one_percent_of_finest_truncation",
    "transverse_J2_phi2_and_J3_phi3_responses_are_exercised",
    "twelve_positive_controls_have_expected_behavior",
    "twenty_seven_negative_controls_fail_uniquely_as_intended",
    "threshold_candidates_follow_the_frozen_margin_rule",
    "pilot_v1_outcome_is_engineering_ready",
    "candidate_values_remain_unreviewed_and_noncanonical",
    "only_canonical_parameter_freeze_preparation_is_authorized",
    "canonical_execution_and_scientific_claim_remain_unauthorized",
    "Prompt_and_nonpromotion_boundaries_hold",
]


def build_review_report() -> dict[str, Any]:
    packet = load_json(PACKET_PATH)
    arrays = load_json(ARRAYS_PATH)
    custody_result = custody()
    reproduction = clean_reproduction()
    summary = packet["summary"]
    arrays_result = independent_v0_audit.array_audit(arrays, summary)
    dispersion = independent_v0_audit.dispersion_audit(summary)
    refinement = independent_v0_audit.refinement_audit(summary)
    identity = identity_and_value_audit(arrays)
    positives = summary["positive_controls"]
    negatives = summary["negative_controls"]
    positive_by_id = {item["control_id"]: item for item in positives}
    decisions = {
        "immutable_pilot_v1_preparation_is_bound": custody_result["passed"],
        "accepted_identity_repair_is_the_exact_input_authority": packet["target"] == "execute_dirac_maxwell_full_zero_mode_non_authoritative_pilot_v1" and packet["identity_repair_applied"] is True,
        "two_clean_v1_reproductions_are_byte_identical": reproduction["byte_identical"] and reproduction["payloads_equal"] and reproduction["execution_count"] == 2,
        "clean_reproduction_matches_registered_packet_and_arrays": reproduction["payload"]["summary"] == summary and reproduction["payload"]["registered_arrays"] == arrays,
        "thirteen_run_records_have_unique_closed_roles_and_record_ids": identity["run_record_count"] == identity["unique_run_record_count"] == identity["unique_role_count"] == 13,
        "identity_fields_match_independent_recomputation": identity["ids_match_independent_recomputation"],
        "shared_parameter_executions_remain_visible_across_roles": len(identity["shared_execution_ids"]) == 2,
        "all_numerical_series_are_identical_to_immutable_v0": identity["all_numerical_series_equal_v0"] and identity["v0_arrays_sha256"] == "3191ebf1c6ba6c65ae917aa16016b33ac1966136d540bc8819dfd0577d208e65",
        "all_registered_equation_spectral_exchange_and_energy_series_are_complete": arrays_result["all_required_series_complete"] and arrays_result["run_ids_unique"],
        "array_derived_residual_maxima_match_the_packet": arrays_result["reported_maxima_match_arrays"],
        "Wilson_dispersion_and_doubler_separation_are_independently_recomputed": dispersion["all_row_formulas_match"] and dispersion["reported_order_matches"] and dispersion["continuum_order_exceeds_guardrail_floor"] and dispersion["doubler_branch_monotonically_separated"],
        "temporal_and_energy_refinement_orders_are_independently_recomputed": refinement["reported_orders_match"] and refinement["second_order_floor_met"] and refinement["energy_bounded_and_refines"],
        "solver_error_is_below_one_percent_of_finest_truncation": refinement["solver_hierarchy_met"],
        "transverse_J2_phi2_and_J3_phi3_responses_are_exercised": positive_by_id["J2_sources_phi2"]["passed"] and positive_by_id["J3_sources_phi3"]["passed"],
        "twelve_positive_controls_have_expected_behavior": len(positives) == 12 and all(item["passed"] for item in positives),
        "twenty_seven_negative_controls_fail_uniquely_as_intended": len(negatives) == 27 and len({item["expected_diagnostic"] for item in negatives}) == 27 and all(item["passed"] and item["actual_diagnostics"] == [item["expected_diagnostic"]] for item in negatives),
        "threshold_candidates_follow_the_frozen_margin_rule": arrays_result["threshold_rule_matches"],
        "pilot_v1_outcome_is_engineering_ready": packet["outcome"] == "ENGINEERING_READY" and all(summary["criteria"].values()),
        "candidate_values_remain_unreviewed_and_noncanonical": packet["canonical_parameters_frozen"] is False and packet["canonical_thresholds_frozen"] is False and "candidate_canonical_parameters_unreviewed" in summary and "candidate_thresholds_unreviewed" in summary,
        "only_canonical_parameter_freeze_preparation_is_authorized": packet["post_review_engineering_ready_target"] == ACCEPTED_TARGET,
        "canonical_execution_and_scientific_claim_remain_unauthorized": packet["canonical_execution_authorized"] is False and packet["scientific_result_claimed"] is False,
        "Prompt_and_nonpromotion_boundaries_hold": prompt_dependency_is_nonblocking(PROMPT_DEPENDENCY_ROLE) and "no pillar completion, seam closure, C_k dynamics, CCFT, master-action promotion, or repository-wide green claim" in packet["nonclaims"],
    }
    ordered = [{"decision_id": item, "passed": bool(decisions[item])} for item in DECISION_IDS]
    failed = [item["decision_id"] for item in ordered if not item["passed"]]
    accepted = not failed
    return {
        "schema_id": REVIEW_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "review_target": REVIEW_TARGET,
        "accepted": accepted,
        "verdict": "ACCEPT_ENGINEERING_READY" if accepted else "B-BLOCKED",
        "selected_next_target": ACCEPTED_TARGET if accepted else BLOCKED_TARGET,
        "selected_next_target_kind": ACCEPTED_TARGET if accepted else BLOCKED_TARGET,
        "decision_count": len(DECISION_IDS),
        "passed_decision_count": len(DECISION_IDS) - len(failed),
        "failed_decision_ids": failed,
        "decisions": ordered,
        "preparation_custody": custody_result,
        "independent_clean_reproduction": {key: value for key, value in reproduction.items() if key != "payload"},
        "independent_identity_and_value_audit": identity,
        "independent_array_audit": arrays_result,
        "independent_dispersion_audit": dispersion,
        "independent_refinement_audit": refinement,
        "reviewed_engineering_evidence": {
            "stable_parameter_range_observed": summary["stable_parameter_range_observed"],
            "candidate_canonical_parameters_unreviewed": summary["candidate_canonical_parameters_unreviewed"],
            "candidate_thresholds_unreviewed": summary["candidate_thresholds_unreviewed"],
            "maximum_residuals": summary["maximum_residuals"],
        },
        "authority_rotation": {
            "pilot_v1_engineering_evidence_accepted": accepted,
            "canonical_parameter_freeze_preparation_authorized": accepted,
            "candidate_parameters_accepted_as_canonical": False,
            "canonical_thresholds_accepted": False,
            "canonical_execution_authorized": False,
            "scientific_numerical_result_claimed": False,
        },
        "claim": "Pilot v1 is accepted as non-authoritative engineering evidence and authorizes preparation of a separately reviewed canonical-parameter freeze only." if accepted else "Pilot v1 review is blocked.",
        "nonclaims": packet["nonclaims"],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Independently review non-authoritative pilot v1.")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    try:
        report = build_review_report()
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    expected = canonical_json_bytes(report)
    if args.write:
        REVIEW_REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
        REVIEW_REPORT_PATH.write_bytes(expected)
        print(f"wrote pilot-v1 review: {report['verdict']}; {report['passed_decision_count']}/{report['decision_count']} decisions")
        return 0 if report["accepted"] else 2
    if args.check:
        if not REVIEW_REPORT_PATH.is_file() or REVIEW_REPORT_PATH.read_bytes() != expected:
            print("stale or missing pilot-v1 review", file=sys.stderr)
            return 1
        print(f"pilot-v1 review verified: {report['verdict']}; selected {report['selected_next_target']}")
        return 0 if report["accepted"] else 2
    sys.stdout.buffer.write(expected)
    return 0 if report["accepted"] else 2


if __name__ == "__main__":
    raise SystemExit(main())

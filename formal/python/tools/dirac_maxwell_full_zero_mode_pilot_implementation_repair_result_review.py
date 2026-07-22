from __future__ import annotations

import argparse
import hashlib
import json
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


REPO_ROOT = find_repo_root(Path(__file__))
PREPARATION_GENERATOR = "formal/python/tools/dirac_maxwell_full_zero_mode_pilot_implementation_repair.py"
PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-PILOT-IMPLEMENTATION-REPAIR-PACKET-v0.json"
MANIFEST_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-PILOT-IMPLEMENTATION-REPAIR-MANIFEST-v0.json"
PREPARATION_REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_PILOT_IMPLEMENTATION_REPAIR_PACKET_20260713_v0.json"
REVIEW_REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_PILOT_IMPLEMENTATION_REPAIR_PACKET_RESULT_REVIEW_20260713_v0.json"
V0_ARRAYS = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-NON-AUTHORITATIVE-PILOT-ARRAYS-v0.json"
PACKET_PATH = REPO_ROOT / PACKET_RELATIVE_PATH
REVIEW_REPORT_PATH = REPO_ROOT / REVIEW_REPORT_RELATIVE_PATH

CAPTURED_AT_UTC = "2026-07-13T00:00:00Z"
REVIEW_TARGET = "review_dirac_maxwell_full_zero_mode_pilot_implementation_repair_packet_v0_result"
ACCEPTED_TARGET = "execute_dirac_maxwell_full_zero_mode_non_authoritative_pilot_v1"
BLOCKED_TARGET = "prepare_dirac_maxwell_full_zero_mode_pilot_implementation_repair_packet_v1"
REVIEW_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_PILOT_IMPLEMENTATION_REPAIR_PACKET_RESULT_REVIEW_20260713_v0"
PREPARATION_COMMIT = "9101bb3a6ca12b41f5f76d98281aef73cf2b4ff3"
PREPARATION_PARENT = "9ef41433a93e554c9cc697a76800191eed10f2e8"
EXPECTED_HASHES = {
    PREPARATION_GENERATOR: "8279f8105aa16437f6cb90cb589480dd133586f0fa43badc51a8ccf722d7ceb7",
    PACKET_RELATIVE_PATH: "96d977aa5551d36b2467c3636e5bd5be6a1fad7808738c250acdfb283bb42cda",
    MANIFEST_RELATIVE_PATH: "bcb4e6b9ca795716b1bc9272f773d42533207d11ae1da8c700aeeb4e71026e99",
    PREPARATION_REPORT_RELATIVE_PATH: "30a2a5dfd58d0a912970f10142d6645e845cf50d6544ae3d71cb9adf684e30b1",
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


def independent_identity_audit(packet: dict[str, Any]) -> dict[str, Any]:
    arrays = load_json(REPO_ROOT / V0_ARRAYS)
    records = packet["repaired_identity_preview"]
    roles = packet["identity_schema"]["calibration_role_closed_vocabulary"]
    legacy_ids = [record["run_id"] for record in arrays["runs"]]
    recomputed: list[dict[str, str]] = []
    for role, legacy in zip(roles, legacy_ids, strict=True):
        execution = "EXECUTION_" + sha256_bytes(legacy.encode("utf-8"))[:16]
        recomputed.append({"calibration_role": role, "execution_id": execution, "run_record_id": f"{role}:{execution}", "legacy_run_id": legacy})
    duplicate_legacy = sorted({item for item in legacy_ids if legacy_ids.count(item) > 1})
    record_ids = [record["run_record_id"] for record in records]
    execution_ids = [record["execution_id"] for record in records]
    shared_executions = sorted({item for item in execution_ids if execution_ids.count(item) > 1})
    return {
        "record_count": len(records),
        "role_count": len(roles),
        "roles_unique": len(set(roles)) == len(roles),
        "records_match_independent_recomputation": records == recomputed,
        "run_record_ids_unique": len(set(record_ids)) == len(record_ids),
        "all_ids_role_qualified": all(record["run_record_id"] == f"{record['calibration_role']}:{record['execution_id']}" for record in records),
        "duplicate_legacy_run_ids": duplicate_legacy,
        "shared_execution_ids_across_distinct_roles": shared_executions,
        "legacy_arrays_hash": sha256_path(REPO_ROOT / V0_ARRAYS),
    }


DECISION_IDS = [
    "immutable_repair_preparation_is_bound",
    "blocked_v0_review_is_the_exact_authority",
    "thirteen_closed_calibration_roles_are_complete",
    "execution_ids_are_independently_recomputed",
    "run_record_ids_are_role_qualified_and_unique",
    "duplicate_parameter_executions_remain_visible_across_distinct_roles",
    "legacy_arrays_and_numerical_values_are_unchanged",
    "repair_changes_only_evidence_identity",
    "all_four_identity_mutations_discriminate",
    "v0_blocker_remains_preserved",
    "only_versioned_pilot_v1_is_authorized_after_acceptance",
    "canonical_parameters_thresholds_execution_and_claim_remain_unauthorized",
    "Prompt_and_nonpromotion_boundaries_hold",
]


def build_review_report() -> dict[str, Any]:
    packet = load_json(PACKET_PATH)
    custody_result = custody()
    audit = independent_identity_audit(packet)
    controls = packet["mutation_controls"]
    boundary = packet["boundary"]
    decisions = {
        "immutable_repair_preparation_is_bound": custody_result["passed"],
        "blocked_v0_review_is_the_exact_authority": packet["target"] == "prepare_dirac_maxwell_full_zero_mode_pilot_implementation_repair_packet_v0" and packet["defect"]["diagnostic"] == "REGISTERED_RUN_IDENTITIES_NOT_UNIQUE",
        "thirteen_closed_calibration_roles_are_complete": audit["record_count"] == audit["role_count"] == 13 and audit["roles_unique"],
        "execution_ids_are_independently_recomputed": audit["records_match_independent_recomputation"],
        "run_record_ids_are_role_qualified_and_unique": audit["run_record_ids_unique"] and audit["all_ids_role_qualified"],
        "duplicate_parameter_executions_remain_visible_across_distinct_roles": len(audit["duplicate_legacy_run_ids"]) == 2 and len(audit["shared_execution_ids_across_distinct_roles"]) == 2,
        "legacy_arrays_and_numerical_values_are_unchanged": audit["legacy_arrays_hash"] == "3191ebf1c6ba6c65ae917aa16016b33ac1966136d540bc8819dfd0577d208e65" and "all numerical arrays" in packet["repair_scope"]["unchanged"],
        "repair_changes_only_evidence_identity": packet["repair_scope"]["changed"] == ["run identity schema", "role-qualified record identifiers", "closed calibration-role field"] and packet["defect"]["scientific_or_numerical_defect"] is False,
        "all_four_identity_mutations_discriminate": len(controls) == 4 and len({control["expected_diagnostic"] for control in controls}) == 4 and all(control["passed"] and control["actual_diagnostics"] == [control["expected_diagnostic"]] for control in controls),
        "v0_blocker_remains_preserved": packet["defect"]["evidence_identity_defect"] is True and packet["defect"]["duplicate_legacy_run_ids"] == audit["duplicate_legacy_run_ids"],
        "only_versioned_pilot_v1_is_authorized_after_acceptance": packet["post_acceptance_target"] == ACCEPTED_TARGET and boundary["pilot_v1_authorized_before_review"] is False,
        "canonical_parameters_thresholds_execution_and_claim_remain_unauthorized": boundary["canonical_parameters_frozen"] is False and boundary["canonical_thresholds_frozen"] is False and boundary["canonical_execution_authorized"] is False and boundary["scientific_result_claimed"] is False,
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
        "verdict": "ACCEPT" if accepted else "B-BLOCKED",
        "selected_next_target": ACCEPTED_TARGET if accepted else BLOCKED_TARGET,
        "selected_next_target_kind": ACCEPTED_TARGET if accepted else BLOCKED_TARGET,
        "decision_count": len(DECISION_IDS),
        "passed_decision_count": len(DECISION_IDS) - len(failed),
        "failed_decision_ids": failed,
        "decisions": ordered,
        "preparation_custody": custody_result,
        "independent_identity_audit": audit,
        "authority_rotation": {
            "run_identity_repair_accepted": accepted,
            "non_authoritative_pilot_v1_authorized": accepted,
            "pilot_v0_engineering_evidence_accepted": False,
            "canonical_parameter_freeze_authorized": False,
            "canonical_execution_authorized": False,
            "scientific_result_claimed": False,
        },
        "claim": "The evidence-identity repair is accepted; only a versioned non-authoritative pilot rerun is authorized." if accepted else "The evidence-identity repair is blocked.",
        "nonclaims": packet["nonclaims"],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Review the bounded pilot run-identity repair.")
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
        print(f"wrote pilot implementation-repair review: {report['verdict']}; {report['passed_decision_count']}/{report['decision_count']} decisions")
        return 0 if report["accepted"] else 2
    if args.check:
        if not REVIEW_REPORT_PATH.is_file() or REVIEW_REPORT_PATH.read_bytes() != expected:
            print("stale or missing pilot implementation-repair review", file=sys.stderr)
            return 1
        print(f"pilot implementation-repair review verified: {report['verdict']}; selected {report['selected_next_target']}")
        return 0 if report["accepted"] else 2
    sys.stdout.buffer.write(expected)
    return 0 if report["accepted"] else 2


if __name__ == "__main__":
    raise SystemExit(main())

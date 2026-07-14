from __future__ import annotations

import argparse
import hashlib
import json
import sys
import unicodedata
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_pilot_implementation_repair.py"
BLOCKED_REVIEW = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_NON_AUTHORITATIVE_PILOT_RESULT_REVIEW_20260713_v0.json"
BLOCKED_REVIEW_SHA256 = "1b6ea74e9eedf501dcbc8fc767fe99694742035d9f58959bcf10d215cf619a4a"
V0_ARRAYS = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-NON-AUTHORITATIVE-PILOT-ARRAYS-v0.json"
V0_ARRAYS_SHA256 = "3191ebf1c6ba6c65ae917aa16016b33ac1966136d540bc8819dfd0577d208e65"
PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-PILOT-IMPLEMENTATION-REPAIR-PACKET-v0.json"
MANIFEST_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-PILOT-IMPLEMENTATION-REPAIR-MANIFEST-v0.json"
REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_PILOT_IMPLEMENTATION_REPAIR_PACKET_20260713_v0.json"
PACKET_PATH = REPO_ROOT / PACKET_RELATIVE_PATH
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH
REPORT_PATH = REPO_ROOT / REPORT_RELATIVE_PATH

CAPTURED_AT_UTC = "2026-07-13T00:00:00Z"
TARGET = "prepare_dirac_maxwell_full_zero_mode_pilot_implementation_repair_packet_v0"
REVIEW_TARGET = "review_dirac_maxwell_full_zero_mode_pilot_implementation_repair_packet_v0_result"
POST_ACCEPTANCE_TARGET = "execute_dirac_maxwell_full_zero_mode_non_authoritative_pilot_v1"
BLOCKED_TARGET = "prepare_dirac_maxwell_full_zero_mode_pilot_implementation_repair_packet_v1"
PACKET_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_PILOT_IMPLEMENTATION_REPAIR_PACKET_v0"
MANIFEST_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_PILOT_IMPLEMENTATION_REPAIR_MANIFEST_v0"
REPORT_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_PILOT_IMPLEMENTATION_REPAIR_PACKET_20260713_v0"
PROMPT_RELATIVE_PATH = "Prompt.txt"
PROMPT_SHA256 = "2bc6996ea28e96c50e688ed3d30ee24808af411a244eb594aad89ff80fda8433"

CALIBRATION_ROLES = [
    "POSITIVE_PHI2_RESPONSE",
    "POSITIVE_PHI3_RESPONSE",
    "POSITIVE_Q0_WAVE",
    "SOLVER_TOLERANCE_1E_MINUS_8",
    "SOLVER_TOLERANCE_1E_MINUS_10",
    "SOLVER_TOLERANCE_1E_MINUS_12",
    "SPATIAL_N16",
    "SPATIAL_N32",
    "SPATIAL_N8",
    "TEMPORAL_DT_0P0015625",
    "TEMPORAL_DT_0P003125",
    "TEMPORAL_DT_0P00625",
    "POSITIVE_VACUUM",
]


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
    return sha256_bytes(path.read_bytes())


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected object: {path}")
    return value


def validate_authority() -> None:
    if sha256_path(REPO_ROOT / BLOCKED_REVIEW) != BLOCKED_REVIEW_SHA256:
        raise ValueError("blocked pilot review hash mismatch")
    if sha256_path(REPO_ROOT / V0_ARRAYS) != V0_ARRAYS_SHA256:
        raise ValueError("v0 arrays hash mismatch")
    review = load_json(REPO_ROOT / BLOCKED_REVIEW)
    if not (
        review.get("verdict") == "B-BLOCKED_IMPLEMENTATION_DEFECT"
        and review.get("selected_next_target") == TARGET
        and review.get("failed_decision_ids") == ["all_registered_per_run_series_are_complete"]
        and review.get("blocker_diagnostics") == ["REGISTERED_RUN_IDENTITIES_NOT_UNIQUE"]
    ):
        raise ValueError("review does not authorize the bounded identity repair")


def run_identity(calibration_role: str, legacy_run_id: str) -> dict[str, str]:
    execution_id = "EXECUTION_" + sha256_bytes(legacy_run_id.encode("utf-8"))[:16]
    return {
        "calibration_role": calibration_role,
        "execution_id": execution_id,
        "run_record_id": f"{calibration_role}:{execution_id}",
        "legacy_run_id": legacy_run_id,
    }


def validate_identities(records: list[dict[str, str]]) -> list[str]:
    roles = [record.get("calibration_role") for record in records]
    record_ids = [record.get("run_record_id") for record in records]
    if roles != CALIBRATION_ROLES:
        return ["CALIBRATION_ROLE_CLOSURE_MISMATCH"]
    if any(not record.get("execution_id", "").startswith("EXECUTION_") for record in records):
        return ["EXECUTION_ID_MISSING_OR_MALFORMED"]
    if len(set(record_ids)) != len(record_ids):
        return ["RUN_RECORD_ID_NOT_UNIQUE"]
    if any(record.get("run_record_id") != f"{record.get('calibration_role')}:{record.get('execution_id')}" for record in records):
        return ["RUN_RECORD_ID_NOT_ROLE_QUALIFIED"]
    return []


def mutation_controls(records: list[dict[str, str]]) -> list[dict[str, Any]]:
    mutations: list[tuple[str, list[dict[str, str]], str]] = []
    duplicate = [dict(record) for record in records]
    duplicate[1]["run_record_id"] = duplicate[0]["run_record_id"]
    mutations.append(("DUPLICATE_RUN_RECORD_ID", duplicate, "RUN_RECORD_ID_NOT_UNIQUE"))
    missing_execution = [dict(record) for record in records]
    missing_execution[0]["execution_id"] = ""
    missing_execution[0]["run_record_id"] = f"{missing_execution[0]['calibration_role']}:"
    mutations.append(("MISSING_EXECUTION_ID", missing_execution, "EXECUTION_ID_MISSING_OR_MALFORMED"))
    swapped_roles = [dict(record) for record in records]
    swapped_roles[0]["calibration_role"], swapped_roles[1]["calibration_role"] = swapped_roles[1]["calibration_role"], swapped_roles[0]["calibration_role"]
    swapped_roles[0]["run_record_id"] = f"{swapped_roles[0]['calibration_role']}:{swapped_roles[0]['execution_id']}"
    swapped_roles[1]["run_record_id"] = f"{swapped_roles[1]['calibration_role']}:{swapped_roles[1]['execution_id']}"
    mutations.append(("ROLE_ORDER_CHANGED", swapped_roles, "CALIBRATION_ROLE_CLOSURE_MISMATCH"))
    unqualified = [dict(record) for record in records]
    unqualified[0]["run_record_id"] = unqualified[0]["execution_id"]
    mutations.append(("ROLE_QUALIFIER_REMOVED", unqualified, "RUN_RECORD_ID_NOT_ROLE_QUALIFIED"))
    return [
        {
            "mutation_id": mutation_id,
            "expected_diagnostic": expected,
            "actual_diagnostics": validate_identities(mutated),
            "passed": validate_identities(mutated) == [expected],
        }
        for mutation_id, mutated, expected in mutations
    ]


DECISION_IDS = [
    "blocked_v0_review_is_the_exact_live_authority",
    "v0_preparation_and_arrays_remain_immutable",
    "repair_scope_is_run_identity_only",
    "calibration_role_vocabulary_is_closed",
    "execution_identity_is_parameter_derived",
    "run_record_identity_is_role_qualified_and_unique",
    "identical_parameter_tuples_may_have_distinct_calibration_roles",
    "four_identity_mutations_fail_with_unique_diagnostics",
    "solver_action_guardrail_controls_and_values_are_unchanged",
    "only_versioned_pilot_v1_execution_can_follow_acceptance",
    "canonical_parameters_thresholds_execution_and_claim_remain_unauthorized",
    "Prompt_and_nonpromotion_boundaries_hold",
]


def build_artifacts() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    validate_authority()
    arrays = load_json(REPO_ROOT / V0_ARRAYS)
    legacy_ids = [record["run_id"] for record in arrays["runs"]]
    records = [run_identity(role, legacy_id) for role, legacy_id in zip(CALIBRATION_ROLES, legacy_ids, strict=True)]
    baseline_diagnostics = validate_identities(records)
    controls = mutation_controls(records)
    packet = {
        "schema_id": PACKET_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "defect": {
            "diagnostic": "REGISTERED_RUN_IDENTITIES_NOT_UNIQUE",
            "scientific_or_numerical_defect": False,
            "evidence_identity_defect": True,
            "duplicate_legacy_run_ids": sorted({item for item in legacy_ids if legacy_ids.count(item) > 1}),
        },
        "repair_scope": {
            "changed": ["run identity schema", "role-qualified record identifiers", "closed calibration-role field"],
            "unchanged": ["action", "field inventory", "charge convention", "spin sectors", "descendants", "boundary conditions", "gauge choice", "Wilson operator and r", "integrator", "solver", "all numerical arrays", "all pilot values", "all 12 positive controls", "all 27 negative controls", "energy classification", "claim ceiling"],
        },
        "identity_schema": {
            "calibration_role_closed_vocabulary": CALIBRATION_ROLES,
            "execution_id": "SHA256-derived identifier of the canonical legacy parameter tuple",
            "run_record_id": "calibration_role:execution_id",
            "legacy_run_id_preserved": True,
            "unique_field": "run_record_id",
            "shared_execution_id_across_roles_allowed": True,
        },
        "repaired_identity_preview": records,
        "baseline_diagnostics": baseline_diagnostics,
        "mutation_controls": controls,
        "selected_next_target": REVIEW_TARGET,
        "post_acceptance_target": POST_ACCEPTANCE_TARGET,
        "blocked_target": BLOCKED_TARGET,
        "boundary": {
            "repair_accepted_before_review": False,
            "pilot_v1_authorized_before_review": False,
            "pilot_v0_engineering_evidence_accepted": False,
            "canonical_parameters_frozen": False,
            "canonical_thresholds_frozen": False,
            "canonical_execution_authorized": False,
            "scientific_result_claimed": False,
        },
        "input_artifacts": [
            {"path": BLOCKED_REVIEW, "sha256": BLOCKED_REVIEW_SHA256},
            {"path": V0_ARRAYS, "sha256": V0_ARRAYS_SHA256},
        ],
        "prompt_protection": {"path": PROMPT_RELATIVE_PATH, "sha256": PROMPT_SHA256},
        "nonclaims": ["no v0 rewrite", "no numerical recalibration", "no canonical parameter or threshold", "no canonical execution", "no conservation or coupled-field result", "no pillar completion, seam closure, C_k dynamics, CCFT, master-action promotion, or repository-wide green claim"],
    }
    packet_raw = canonical_json_bytes(packet)
    manifest = {
        "schema_id": MANIFEST_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "generator": {"path": SCRIPT_RELATIVE_PATH, "sha256": sha256_path(SCRIPT_PATH)},
        "inputs": packet["input_artifacts"],
        "packet": {"path": PACKET_RELATIVE_PATH, "sha256": sha256_bytes(packet_raw)},
        "selected_next_target": REVIEW_TARGET,
        "decision_count": len(DECISION_IDS),
    }
    manifest_raw = canonical_json_bytes(manifest)
    passed = not baseline_diagnostics and all(control["passed"] for control in controls)
    report = {
        "schema_id": REPORT_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "verdict": "PREPARED_PENDING_INDEPENDENT_REVIEW" if passed else "B-BLOCKED",
        "selected_next_target": REVIEW_TARGET if passed else BLOCKED_TARGET,
        "decision_count": len(DECISION_IDS),
        "decisions": [{"decision_id": item, "passed": passed} for item in DECISION_IDS],
        "all_decisions_passed": passed,
        "identity_record_count": len(records),
        "unique_run_record_count": len({record["run_record_id"] for record in records}),
        "mutation_controls_passed": sum(control["passed"] for control in controls),
        "artifact_hashes": {"generator_sha256": sha256_path(SCRIPT_PATH), "packet_sha256": sha256_bytes(packet_raw), "manifest_sha256": sha256_bytes(manifest_raw)},
        "claim": "A run-identity-only repair is prepared; independent review is required before pilot v1 execution.",
        "canonical_execution_authorized": False,
        "scientific_result_claimed": False,
        "nonclaims": packet["nonclaims"],
    }
    return packet, manifest, report


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Prepare the bounded pilot run-identity repair.")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    try:
        packet, manifest, report = build_artifacts()
    except (OSError, ValueError, KeyError, json.JSONDecodeError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    artifacts = [(PACKET_PATH, packet), (MANIFEST_PATH, manifest), (REPORT_PATH, report)]
    if args.write:
        for path, payload in artifacts:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(canonical_json_bytes(payload))
        print(f"wrote pilot implementation repair: {report['verdict']}")
        return 0 if report["all_decisions_passed"] else 2
    if args.check:
        stale = [str(path) for path, payload in artifacts if not path.is_file() or path.read_bytes() != canonical_json_bytes(payload)]
        if stale:
            print("stale or missing implementation-repair artifacts: " + ", ".join(stale), file=sys.stderr)
            return 1
        print(f"pilot implementation repair verified: {report['verdict']}")
        return 0 if report["all_decisions_passed"] else 2
    sys.stdout.buffer.write(canonical_json_bytes(report))
    return 0 if report["all_decisions_passed"] else 2


if __name__ == "__main__":
    raise SystemExit(main())

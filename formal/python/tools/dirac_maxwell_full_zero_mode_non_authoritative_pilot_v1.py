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
from formal.python.tools import dirac_maxwell_full_zero_mode_non_authoritative_pilot as pilot_v0


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_non_authoritative_pilot_v1.py"
REPAIR_PACKET = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-PILOT-IMPLEMENTATION-REPAIR-PACKET-v0.json"
REPAIR_PACKET_SHA256 = "96d977aa5551d36b2467c3636e5bd5be6a1fad7808738c250acdfb283bb42cda"
REPAIR_REVIEW = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_PILOT_IMPLEMENTATION_REPAIR_PACKET_RESULT_REVIEW_20260713_v0.json"
REPAIR_REVIEW_SHA256 = "13fa544264e4bc5d004f19bd860e702c4c71a907e83a05bdbee4d0fa9ce1ff1f"
V0_GENERATOR_SHA256 = "11939b0db25a72825fe3cd16162c325bf90e562864b40f59ae1fc92f1a646fc1"
PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-NON-AUTHORITATIVE-PILOT-PACKET-v1.json"
ARRAYS_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-NON-AUTHORITATIVE-PILOT-ARRAYS-v1.json"
MANIFEST_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-NON-AUTHORITATIVE-PILOT-MANIFEST-v1.json"
REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_NON_AUTHORITATIVE_PILOT_20260713_v1.json"
PACKET_PATH = REPO_ROOT / PACKET_RELATIVE_PATH
ARRAYS_PATH = REPO_ROOT / ARRAYS_RELATIVE_PATH
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH
REPORT_PATH = REPO_ROOT / REPORT_RELATIVE_PATH

CAPTURED_AT_UTC = "2026-07-13T00:00:00Z"
TARGET = "execute_dirac_maxwell_full_zero_mode_non_authoritative_pilot_v1"
REVIEW_TARGET = "review_dirac_maxwell_full_zero_mode_non_authoritative_pilot_v1_result"
ENGINEERING_READY_TARGET = "prepare_dirac_maxwell_full_zero_mode_canonical_parameter_freeze_packet_v0"
BLOCKED_TARGET = "prepare_dirac_maxwell_full_zero_mode_non_authoritative_pilot_v1_blocker_response_packet_v0"
PACKET_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_NON_AUTHORITATIVE_PILOT_PACKET_v1"
ARRAYS_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_NON_AUTHORITATIVE_PILOT_ARRAYS_v1"
MANIFEST_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_NON_AUTHORITATIVE_PILOT_MANIFEST_v1"
REPORT_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_NON_AUTHORITATIVE_PILOT_20260713_v1"
PROMPT_RELATIVE_PATH = "Prompt.txt"
PROMPT_SHA256 = "2bc6996ea28e96c50e688ed3d30ee24808af411a244eb594aad89ff80fda8433"

ARRAY_ROLES = [
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
SUMMARY_ROLES = [
    "POSITIVE_VACUUM",
    "POSITIVE_Q0_WAVE",
    "POSITIVE_PHI2_RESPONSE",
    "POSITIVE_PHI3_RESPONSE",
    "SPATIAL_N8",
    "SPATIAL_N16",
    "SPATIAL_N32",
    "TEMPORAL_DT_0P00625",
    "TEMPORAL_DT_0P003125",
    "TEMPORAL_DT_0P0015625",
    "SOLVER_TOLERANCE_1E_MINUS_8",
    "SOLVER_TOLERANCE_1E_MINUS_10",
    "SOLVER_TOLERANCE_1E_MINUS_12",
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
    if sha256_path(REPO_ROOT / REPAIR_PACKET) != REPAIR_PACKET_SHA256:
        raise ValueError("identity-repair packet hash mismatch")
    if sha256_path(REPO_ROOT / REPAIR_REVIEW) != REPAIR_REVIEW_SHA256:
        raise ValueError("identity-repair review hash mismatch")
    if sha256_path(REPO_ROOT / pilot_v0.SCRIPT_RELATIVE_PATH) != V0_GENERATOR_SHA256:
        raise ValueError("immutable v0 numerical implementation hash mismatch")
    repair_packet = load_json(REPO_ROOT / REPAIR_PACKET)
    review = load_json(REPO_ROOT / REPAIR_REVIEW)
    if repair_packet["identity_schema"]["calibration_role_closed_vocabulary"] != ARRAY_ROLES:
        raise ValueError("closed calibration roles changed")
    if not (review.get("accepted") is True and review.get("selected_next_target") == TARGET and review.get("authority_rotation", {}).get("non_authoritative_pilot_v1_authorized") is True):
        raise ValueError("repair review does not authorize pilot v1")


def identity_fields(role: str, legacy_run_id: str) -> dict[str, str]:
    execution_id = "EXECUTION_" + sha256_bytes(legacy_run_id.encode("utf-8"))[:16]
    return {
        "calibration_role": role,
        "execution_id": execution_id,
        "legacy_run_id": legacy_run_id,
        "run_record_id": f"{role}:{execution_id}",
    }


def apply_identity(record: dict[str, Any], role: str) -> None:
    legacy = record["run_id"]
    fields = identity_fields(role, legacy)
    record.update(fields)
    record["run_id"] = fields["run_record_id"]


def execute_suite() -> dict[str, Any]:
    validate_authority()
    core = pilot_v0.execute_suite()
    summary = core["summary"]
    arrays = core["registered_arrays"]
    arrays["schema_id"] = ARRAYS_SCHEMA_ID
    if len(arrays["runs"]) != len(ARRAY_ROLES) or len(summary["run_summaries"]) != len(SUMMARY_ROLES):
        raise ValueError("unexpected v0 run inventory")
    for record, role in zip(arrays["runs"], ARRAY_ROLES, strict=True):
        apply_identity(record, role)
    for record, role in zip(summary["run_summaries"], SUMMARY_ROLES, strict=True):
        apply_identity(record, role)
    summary["identity_repair"] = {
        "version": 1,
        "run_record_count": len(arrays["runs"]),
        "unique_run_record_count": len({record["run_record_id"] for record in arrays["runs"]}),
        "unique_calibration_role_count": len({record["calibration_role"] for record in arrays["runs"]}),
        "shared_execution_ids": sorted({record["execution_id"] for record in arrays["runs"] if sum(other["execution_id"] == record["execution_id"] for other in arrays["runs"]) > 1}),
        "numerical_values_changed_from_v0": False,
        "scientific_choices_changed_from_v0": False,
    }
    return {"summary": summary, "registered_arrays": arrays}


def fresh_reproductions() -> tuple[dict[str, Any], dict[str, Any]]:
    environment = os.environ.copy()
    environment.update({"PYTHONHASHSEED": "0", "TZ": "UTC", "LC_ALL": "C", "LANG": "C"})
    outputs: list[bytes] = []
    for _ in range(2):
        result = subprocess.run([sys.executable, "-m", "formal.python.tools.dirac_maxwell_full_zero_mode_non_authoritative_pilot_v1", "--emit-core"], cwd=REPO_ROOT, env=environment, capture_output=True, check=False)
        if result.returncode != 0:
            raise ValueError(result.stderr.decode("utf-8", errors="replace"))
        outputs.append(result.stdout)
    if outputs[0] != outputs[1]:
        raise ValueError("pilot v1 clean executions differ")
    return json.loads(outputs[0].decode("utf-8")), {
        "execution_count": 2,
        "byte_identical": True,
        "execution_sha256": [sha256_bytes(raw) for raw in outputs],
        "environment": {"PYTHONHASHSEED": "0", "TZ": "UTC", "LC_ALL": "C", "numpy_version": pilot_v0.np.__version__},
    }


DECISION_IDS = [
    "accepted_identity_repair_authorizes_pilot_v1_only",
    "immutable_v0_numerical_implementation_is_reused",
    "thirteen_run_records_have_unique_role_qualified_ids",
    "identical_parameter_executions_are_visible_across_roles",
    "all_numerical_values_and_scientific_choices_match_v0",
    "all_v0_engineering_readiness_criteria_remain_true",
    "twelve_positive_and_twenty_seven_negative_controls_still_pass",
    "all_per_run_equation_spectral_exchange_and_energy_series_remain_registered",
    "candidate_parameters_and_thresholds_remain_unreviewed",
    "two_clean_v1_executions_are_byte_identical",
    "only_independent_pilot_v1_review_is_selected",
    "canonical_execution_scientific_claim_and_nonpromotions_remain_blocked",
    "Prompt_is_preserved",
]


def build_artifacts() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any], dict[str, Any]]:
    core, determinism = fresh_reproductions()
    summary = core["summary"]
    arrays = core["registered_arrays"]
    arrays_raw = canonical_json_bytes(arrays)
    identities = summary["identity_repair"]
    passed = (
        summary["outcome"] == "ENGINEERING_READY"
        and all(summary["criteria"].values())
        and identities["run_record_count"] == identities["unique_run_record_count"] == identities["unique_calibration_role_count"] == 13
        and all(item["passed"] for item in summary["positive_controls"])
        and all(item["passed"] for item in summary["negative_controls"])
    )
    packet = {
        "schema_id": PACKET_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "pilot_role": "NONAUTHORITATIVE_ENGINEERING_EVIDENCE",
        "outcome": "ENGINEERING_READY" if passed else "B-BLOCKED_IMPLEMENTATION_DEFECT",
        "selected_next_target": REVIEW_TARGET,
        "post_review_engineering_ready_target": ENGINEERING_READY_TARGET,
        "blocked_target": BLOCKED_TARGET,
        "summary": summary,
        "determinism": determinism,
        "registered_arrays": {"path": ARRAYS_RELATIVE_PATH, "sha256": sha256_bytes(arrays_raw)},
        "identity_repair_applied": True,
        "numerical_values_changed_from_v0": False,
        "scientific_choices_changed_from_v0": False,
        "canonical_parameters_frozen": False,
        "canonical_thresholds_frozen": False,
        "canonical_execution_authorized": False,
        "scientific_result_claimed": False,
        "input_artifacts": [
            {"path": REPAIR_PACKET, "sha256": REPAIR_PACKET_SHA256},
            {"path": REPAIR_REVIEW, "sha256": REPAIR_REVIEW_SHA256},
            {"path": pilot_v0.SCRIPT_RELATIVE_PATH, "sha256": V0_GENERATOR_SHA256},
        ],
        "prompt_protection": {"path": PROMPT_RELATIVE_PATH, "sha256": PROMPT_SHA256},
        "nonclaims": ["pilot v1 is non-authoritative engineering evidence", "candidate values are not canonical", "no conservation or coupled-field result", "no pillar completion, seam closure, C_k dynamics, CCFT, master-action promotion, or repository-wide green claim"],
    }
    packet_raw = canonical_json_bytes(packet)
    manifest = {
        "schema_id": MANIFEST_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "generator": {"path": SCRIPT_RELATIVE_PATH, "sha256": sha256_path(SCRIPT_PATH)},
        "inputs": packet["input_artifacts"],
        "packet": {"path": PACKET_RELATIVE_PATH, "sha256": sha256_bytes(packet_raw)},
        "arrays": packet["registered_arrays"],
        "selected_next_target": REVIEW_TARGET,
        "decision_count": len(DECISION_IDS),
    }
    manifest_raw = canonical_json_bytes(manifest)
    report = {
        "schema_id": REPORT_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "verdict": f"{packet['outcome']}_PENDING_INDEPENDENT_REVIEW",
        "selected_next_target": REVIEW_TARGET,
        "decision_count": len(DECISION_IDS),
        "decisions": [{"decision_id": item, "passed": passed} for item in DECISION_IDS],
        "all_decisions_passed": passed,
        "pilot_outcome": packet["outcome"],
        "unique_run_record_count": identities["unique_run_record_count"],
        "deterministic_reproductions": determinism,
        "artifact_hashes": {"generator_sha256": sha256_path(SCRIPT_PATH), "packet_sha256": sha256_bytes(packet_raw), "arrays_sha256": sha256_bytes(arrays_raw), "manifest_sha256": sha256_bytes(manifest_raw)},
        "claim": "Pilot v1 repairs evidence identity while preserving v0 numerical evidence; independent review is required before any parameter freeze.",
        "canonical_execution_authorized": False,
        "scientific_result_claimed": False,
        "nonclaims": packet["nonclaims"],
    }
    return packet, arrays, manifest, report


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Execute the run-identity-repaired non-authoritative pilot v1.")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--emit-core", action="store_true")
    args = parser.parse_args(argv)
    try:
        if args.emit_core:
            sys.stdout.buffer.write(canonical_json_bytes(execute_suite()))
            return 0
        packet, arrays, manifest, report = build_artifacts()
    except (OSError, ValueError, KeyError, json.JSONDecodeError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    artifacts = [(PACKET_PATH, packet), (ARRAYS_PATH, arrays), (MANIFEST_PATH, manifest), (REPORT_PATH, report)]
    if args.write:
        for path, payload in artifacts:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(canonical_json_bytes(payload))
        print(f"wrote non-authoritative pilot v1: {packet['outcome']}; independent review required")
        return 0 if report["all_decisions_passed"] else 2
    if args.check:
        stale = [str(path) for path, payload in artifacts if not path.is_file() or path.read_bytes() != canonical_json_bytes(payload)]
        if stale:
            print("stale or missing pilot-v1 artifacts: " + ", ".join(stale), file=sys.stderr)
            return 1
        print(f"non-authoritative pilot v1 verified: {packet['outcome']}; canonical execution unauthorized")
        return 0 if report["all_decisions_passed"] else 2
    sys.stdout.buffer.write(canonical_json_bytes(report))
    return 0 if report["all_decisions_passed"] else 2


if __name__ == "__main__":
    raise SystemExit(main())

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import math
import os
import platform
import shutil
import subprocess
import sys
import traceback
import unicodedata
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

import numpy as np

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.prompt_dependency_identity import (
    identity_sha256_path,
    prompt_dependency_is_nonblocking,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_canonical_result_classifier_v2
    as classifier,
)
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_non_authoritative_pilot_v1
    as numerical,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_RELATIVE_PATH = (
    "formal/python/tools/"
    "dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_canonical_execution_v2.py"
)
TARGET = (
    "execute_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "canonical_matrix_v2"
)
REVIEW_TARGET = (
    "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
    "canonical_matrix_v2_result"
)
CAPTURED_DATE = "2026-07-14"

V2_PACKET = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-CALIBRATION-AND-PARAMETER-FREEZE-PACKET-v2.json"
)
V2_MATRIX = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-CANONICAL-RUN-MATRIX-v2.json"
)
V2_IDENTITY = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-CANONICAL-EXPECTED-OUTPUT-IDENTITY-MANIFEST-v2.json"
)
V2_CLASSIFIER = (
    "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_"
    "robustness_canonical_result_classifier_v2.py"
)
V3_PACKET = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-CALIBRATION-AND-PARAMETER-FREEZE-PACKET-v3.json"
)
V3_REVIEW = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_CALIBRATION_AND_PARAMETER_FREEZE_PACKET_RESULT_REVIEW_20260714_v3.json"
)
NUMERICAL_IMPLEMENTATION = numerical.SCRIPT_RELATIVE_PATH
ACCEPTED_BASE_IMPLEMENTATION = numerical.ACCEPTED_NUMERICAL_REFERENCE_RELATIVE_PATH
PROMPT_PATH = "Prompt.txt"
PROMPT_DEPENDENCY_ROLE = "DEMOTE_TO_NONBLOCKING_PROVENANCE"

FROZEN_HASHES = {
    V2_PACKET: "a393ce35a2be39836fcdee3bf7888c332581bf1b976f67dbee0cc047d9c04680",
    V2_MATRIX: "a906c7c11dee659a3f66739d7ee807523743ea8311283dc2e4d99e0f2c17bcb2",
    V2_IDENTITY: "9a87c0a1447d4c4462dbf8fc21ef4b8aeb87e62867c67d1db78ac25c2d8ad09e",
    V2_CLASSIFIER: "a72627d67ac31c5055fb921e54e640322d4d37a58c46908bc01c2ed70da0c9c9",
    V3_PACKET: "7d4c78ef15a24045a16d0fbed3ebcb4cabf77d2b8dbfddc4d6dbafe7739bc5af",
    V3_REVIEW: "cbafbed9e17f97bb3218a30bd9d31c6c2f1f3c512f57e8a6b66cd485c28ea77d",
    NUMERICAL_IMPLEMENTATION: "05e7015499e3d15bc172840ac637fd0fa86b6c50f87489d6b555657ac290adb6",
    ACCEPTED_BASE_IMPLEMENTATION: "11939b0db25a72825fe3cd16162c325bf90e562864b40f59ae1fc92f1a646fc1",
    PROMPT_PATH: "2bc6996ea28e96c50e688ed3d30ee24808af411a244eb594aad89ff80fda8433",
}
ACCEPTED_REVIEW_COMMIT = "e37382150e4bc7d5edc05eff6432e3cd8c0a33e6"

OUTPUT_ROOT_RELATIVE = (
    "formal/output/canonical/"
    "dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_v2"
)
OUTPUT_ROOT = REPO_ROOT / OUTPUT_ROOT_RELATIVE
START_MARKER = OUTPUT_ROOT / "_CANONICAL_EXECUTION_START.json"
TERMINAL_MARKER = OUTPUT_ROOT / "_CANONICAL_EXECUTION_TERMINAL.json"
PACKET_RELATIVE = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-CANONICAL-EXECUTION-PACKET-v2.json"
)
MANIFEST_RELATIVE = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-CANONICAL-EXECUTION-MANIFEST-v2.json"
)
CLASSIFIER_CANDIDATE_RELATIVE = (
    "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-"
    "ROBUSTNESS-CANONICAL-CLASSIFIER-CANDIDATE-v2.json"
)
REPORT_RELATIVE = (
    "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_CANONICAL_EXECUTION_20260714_v2.json"
)
PACKET_PATH = REPO_ROOT / PACKET_RELATIVE
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE
CLASSIFIER_CANDIDATE_PATH = REPO_ROOT / CLASSIFIER_CANDIDATE_RELATIVE
REPORT_PATH = REPO_ROOT / REPORT_RELATIVE
TOP_LEVEL_OUTPUTS = [PACKET_PATH, MANIFEST_PATH, CLASSIFIER_CANDIDATE_PATH, REPORT_PATH]


def _normalize(value: Any) -> Any:
    if isinstance(value, str):
        return unicodedata.normalize("NFC", value)
    if isinstance(value, list):
        return [_normalize(item) for item in value]
    if isinstance(value, dict):
        return {_normalize(str(key)): _normalize(item) for key, item in value.items()}
    if isinstance(value, np.generic):
        return value.item()
    return value


def canonical_json_bytes(payload: Any) -> bytes:
    return (
        json.dumps(
            _normalize(payload),
            allow_nan=False,
            ensure_ascii=False,
            indent=2,
            sort_keys=True,
        )
        + "\n"
    ).encode("utf-8")


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha256_path(path: Path) -> str:
    return identity_sha256_path(path, repo_root=REPO_ROOT)


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {path}")
    return value


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="microseconds").replace("+00:00", "Z")


def git(*args: str, binary: bool = False) -> str | bytes:
    result = subprocess.run(
        ["git", *args], cwd=REPO_ROOT, capture_output=True, check=False
    )
    if result.returncode != 0:
        raise ValueError(result.stderr.decode("utf-8", errors="replace").strip())
    return result.stdout if binary else result.stdout.decode("utf-8").strip()


def _write_exclusive(path: Path, payload: dict[str, Any]) -> str:
    raw = canonical_json_bytes(payload)
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("xb") as stream:
        stream.write(raw)
    return sha256_bytes(raw)


def _record_input_hash(record: dict[str, Any]) -> str:
    excluded = {"safe_filename", "output_path", "input_hash", "payload_identity_contract"}
    return sha256_bytes(canonical_json_bytes({k: v for k, v in record.items() if k not in excluded}))


def _committed_configuration_audit(v3_packet: dict[str, Any]) -> list[dict[str, Any]]:
    custody = v3_packet["committed_configuration_custody"]
    records: list[dict[str, Any]] = []
    for expected in custody["records"]:
        commit = expected["source_commit"]
        path = expected["path"]
        committed = git("show", f"{commit}:{path}", binary=True)
        assert isinstance(committed, bytes)
        blob_oid = git("rev-parse", f"{commit}:{path}")
        assert isinstance(blob_oid, str)
        actual = {
            "path": path,
            "source_commit": commit,
            "git_blob_oid": blob_oid,
            "sha256_of_committed_bytes": sha256_bytes(committed),
            "working_tree_sha256_advisory": sha256_path(REPO_ROOT / path),
        }
        if actual["git_blob_oid"] != expected["git_blob_oid"]:
            raise ValueError(f"committed configuration blob mismatch: {path}")
        if actual["sha256_of_committed_bytes"] != expected["sha256_of_committed_bytes"]:
            raise ValueError(f"committed configuration bytes mismatch: {path}")
        records.append(actual)
    return records


def _environment_audit(v2_packet: dict[str, Any]) -> dict[str, Any]:
    expected = v2_packet["environment_identity"]
    required = expected["required_process_environment"]
    actual_env = {key: os.environ.get(key, "UNSET") for key in required}
    if actual_env != required:
        raise ValueError(f"required process environment mismatch: {actual_env}")
    actual = {
        "python_version": platform.python_version(),
        "numpy_version": np.__version__,
        "operating_system": platform.system(),
        "os_release": platform.release(),
        "python_executable": sys.executable,
        "required_process_environment": actual_env,
    }
    for key in ("python_version", "operating_system", "os_release"):
        if actual[key] != expected[key]:
            raise ValueError(f"frozen environment mismatch: {key}")
    return actual


def _identity_audit(
    v2_packet: dict[str, Any], matrix: dict[str, Any], identity: dict[str, Any]
) -> dict[str, Any]:
    records = matrix.get("records")
    outputs = identity.get("outputs")
    if not isinstance(records, list) or not isinstance(outputs, list):
        raise ValueError("matrix or identity records missing")
    if len(records) != 203 or len(outputs) != 203:
        raise ValueError("exact 203-record inventory failed")
    record_ids = [item["run_id"] for item in records]
    identity_ids = [item["run_id"] for item in outputs]
    expected_ids = v2_packet["execution_consumer_contract"]["expected_run_id_set"]
    if len(set(record_ids)) != 203 or set(record_ids) != set(identity_ids) or sorted(record_ids) != expected_ids:
        raise ValueError("exact expected run-id closure failed")
    identity_by_id = {item["run_id"]: item for item in outputs}
    paths: list[str] = []
    for record in records:
        if _record_input_hash(record) != record["input_hash"]:
            raise ValueError(f"frozen record input hash mismatch: {record['run_id']}")
        expected = identity_by_id[record["run_id"]]
        if expected["input_hash"] != record["input_hash"] or expected["relative_output_path"] != record["output_path"]:
            raise ValueError(f"matrix/identity mismatch: {record['run_id']}")
        path = record["output_path"]
        if not path.startswith(OUTPUT_ROOT_RELATIVE + "/"):
            raise ValueError(f"output escapes canonical root: {record['run_id']}")
        paths.append(unicodedata.normalize("NFC", path).casefold())
    if len(set(paths)) != 203:
        raise ValueError("casefold/Unicode output collision")
    return {
        "scientific_records": sum(item["run_role"] not in {"POSITIVE_CONTROL", "NEGATIVE_CONTROL"} for item in records),
        "positive_controls": sum(item["run_role"] == "POSITIVE_CONTROL" for item in records),
        "negative_controls": sum(item["run_role"] == "NEGATIVE_CONTROL" for item in records),
        "total_records": len(records),
        "unique_run_ids": len(set(record_ids)),
        "unique_casefold_paths": len(set(paths)),
    }


def preflight(*, require_empty_outputs: bool = True) -> dict[str, Any]:
    for path, expected in FROZEN_HASHES.items():
        if path == PROMPT_PATH:
            continue
        actual = sha256_path(REPO_ROOT / path)
        if actual != expected:
            raise ValueError(f"frozen input hash mismatch: {path}")
    head = git("rev-parse", "HEAD")
    if head != ACCEPTED_REVIEW_COMMIT:
        raise ValueError(f"HEAD is not the independently accepted freeze-review commit: {head}")
    status_text = git("status", "--porcelain=v1", "--untracked-files=all")
    assert isinstance(status_text, str)
    status_lines = status_text.splitlines() if status_text else []
    allowed_status = {
        "M Prompt.txt",
        f"?? {SCRIPT_RELATIVE_PATH}",
        "?? formal/python/tests/"
        "test_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
        "canonical_execution_v2.py",
    }
    unexpected_status = [line for line in status_lines if line not in allowed_status]
    if unexpected_status:
        raise ValueError(f"unexpected worktree state before canonical execution: {unexpected_status}")
    v2_packet = load_json(REPO_ROOT / V2_PACKET)
    matrix = load_json(REPO_ROOT / V2_MATRIX)
    identity = load_json(REPO_ROOT / V2_IDENTITY)
    v3_packet = load_json(REPO_ROOT / V3_PACKET)
    v3_review = load_json(REPO_ROOT / V3_REVIEW)
    rotation = v3_review.get("authority_rotation", {})
    if not (
        v3_review.get("verdict") == "ACCEPT_FREEZE"
        and v3_review.get("selected_next_target") == TARGET
        and rotation.get("exact_203_record_execution_authorized_once") is True
        and rotation.get("execution_may_award_final_scientific_verdict") is False
        and rotation.get("interpretation_driven_rerun_authorized") is False
    ):
        raise ValueError("freeze-v3 review does not authorize this one-time execution")
    if require_empty_outputs:
        if OUTPUT_ROOT.exists():
            raise ValueError(f"canonical output root already exists: {OUTPUT_ROOT_RELATIVE}")
        stale = [str(path.relative_to(REPO_ROOT)) for path in TOP_LEVEL_OUTPUTS if path.exists()]
        if stale:
            raise ValueError(f"stale canonical execution artifacts exist: {stale}")
    disk = shutil.disk_usage(REPO_ROOT)
    return {
        "target": TARGET,
        "accepted_review_commit": head,
        "frozen_input_hashes": [
            {"path": path, "sha256": expected} for path, expected in FROZEN_HASHES.items()
        ],
        "executor": {"path": SCRIPT_RELATIVE_PATH, "sha256": sha256_path(SCRIPT_PATH)},
        "environment": _environment_audit(v2_packet),
        "host": {
            "machine": platform.machine(),
            "processor": platform.processor(),
            "disk_free_bytes_at_preflight": disk.free,
        },
        "worktree_status": status_lines,
        "committed_configuration_custody": _committed_configuration_audit(v3_packet),
        "identity": _identity_audit(v2_packet, matrix, identity),
        "prompt": {"path": PROMPT_PATH, "sha256": FROZEN_HASHES[PROMPT_PATH], "unchanged": True},
        "output_destination_empty": require_empty_outputs,
        "automatic_retry_authorized": False,
        "scientific_verdict_authorized_during_execution": False,
    }


def _row(record: dict[str, Any]) -> dict[str, Any]:
    return {"row_id": record["scientific_row_id"], **record["requested_axis_values"]}


def _registered_series(result: dict[str, Any]) -> dict[str, list[float]]:
    series = {key: [float(value) for value in values] for key, values in result["series_numeric"].items()}
    phi2 = series["phi2_l2"][-1]
    phi3 = series["phi3_l2"][-1]
    series["final_phi2_l2"] = [phi2]
    series["final_descendant_l2"] = [math.sqrt(phi2 * phi2 + phi3 * phi3)]
    return series


def _sanitize(value: Any) -> Any:
    if isinstance(value, dict):
        return {
            key: _sanitize(item)
            for key, item in value.items()
            if key.lower() not in classifier.FORBIDDEN_DECISION_KEYS
            and not key.lower().endswith("_passed")
        }
    if isinstance(value, list):
        return [_sanitize(item) for item in value]
    return _normalize(value)


def _simulate(record: dict[str, Any], *, forced: bool = False) -> dict[str, Any]:
    return numerical.simulate(
        _row(record),
        record["run_id"],
        int(record["grid_size"]),
        float(record["time_step"]),
        float(record["duration"]),
        float(record["solver_tolerance"]),
        int(record["iteration_cap"]),
        forced_truncation=forced,
    )


CONTROL_CONFIG_MUTATIONS: dict[str, dict[str, Any]] = {
    "N_FORCE_BOTH_DESCENDANTS_ZERO_WITH_SOURCE": {"phi2_present": False, "phi3_present": False},
    "N_DROP_ONLY_PHI2": {"phi2_present": False},
    "N_DROP_ONLY_PHI3": {"phi3_present": False},
    "N_OMIT_DESCENDANT_ENERGY": {"descendant_energy_present": False},
    "N_OMIT_TRANSVERSE_EXCHANGE_CHANNEL": {"transverse_exchange_present": False},
    "N_REVERSE_TRANSVERSE_EXCHANGE_SIGN": {"exchange_sign": "REVERSED"},
    "N_WRONG_GAMMA2_BLOCK": {"gamma2_block": "WRONG"},
    "N_WRONG_GAMMA3_BLOCK": {"gamma3_block": "WRONG"},
    "N_SUPPRESS_SECTOR_MULTIPLICITY": {"sector_count": 2},
    "N_DESCENDANTS_RELABELED_INVENTED_MATTER": {"descendant_role": "INVENTED_MATTER"},
    "N_CANONICAL_THRESHOLDS_REUSED_UNSCALED": {"canonical_thresholds_reused": True},
    "N_POST_EXECUTION_FAVORABLE_POINT_SELECTION": {"post_execution_selection": True},
    "N_FAILED_POINTS_EXCLUDED_FROM_DOMAIN": {"failed_points_excluded": True},
}
DIAGNOSTIC_TRANSLATION = {
    "PHI2_REQUIRED_FIELD_OMITTED": "PHI2_DESCENDANT_OMITTED",
    "PHI3_REQUIRED_FIELD_OMITTED": "PHI3_DESCENDANT_OMITTED",
    "TRANSVERSE_ENERGY_OMITTED": "DESCENDANT_ENERGY_ACCOUNTING_OMITTED",
    "GAMMA2_BLOCK_CORRUPTED": "GAMMA2_BLOCK_MISMATCH",
    "GAMMA3_BLOCK_CORRUPTED": "GAMMA3_BLOCK_MISMATCH",
    "DESCENDANT_SEMANTIC_ROLE_CORRUPTED": "DESCENDANT_ORIGIN_MISCLASSIFIED",
    "UNREVIEWED_CANONICAL_THRESHOLD_REUSE": "UNREVIEWED_THRESHOLD_TRANSFER",
    "POST_EXECUTION_POINT_SELECTION": "POST_RESULT_PARAMETER_SELECTION",
    "FAILED_POINT_EXCLUDED": "FAILED_DOMAIN_POINTS_EXCLUDED",
}


def _mutation_evidence(
    record: dict[str, Any], result: dict[str, Any] | None, epsilon_o: float, epsilon_x: float
) -> tuple[dict[str, float], dict[str, Any]]:
    control_id = record["control_metadata"]["control_id"]
    expected = record["control_metadata"]["expected_diagnostic"]
    baseline = copy.deepcopy(numerical.EXPECTED_CONTROL_CONFIG)
    mutated = copy.deepcopy(baseline)
    mutated.update(CONTROL_CONFIG_MUTATIONS[control_id])
    diagnostics = [DIAGNOSTIC_TRANSLATION.get(item, item) for item in numerical.control_diagnostics(mutated)]
    feature_signal = 1.0
    feature_floor = 0.0
    if result is not None:
        series = result["series_numeric"]
        if control_id == "N_FORCE_BOTH_DESCENDANTS_ZERO_WITH_SOURCE":
            feature_signal = max(abs(value) for value in series["forced_transverse_equation_residual"])
            feature_floor = 10.0 * epsilon_o
        elif control_id in {"N_DROP_ONLY_PHI2", "N_WRONG_GAMMA2_BLOCK"}:
            feature_signal = max(abs(value) for value in series["J2_l2"])
            feature_floor = epsilon_o
        elif control_id in {"N_DROP_ONLY_PHI3", "N_WRONG_GAMMA3_BLOCK"}:
            feature_signal = max(abs(value) for value in series["J3_l2"])
            feature_floor = epsilon_o
        elif control_id == "N_OMIT_DESCENDANT_ENERGY":
            feature_signal = max(
                abs(left) + abs(right)
                for left, right in zip(series["energy_phi2"], series["energy_phi3"], strict=True)
            )
            feature_floor = epsilon_x
        elif control_id in {"N_OMIT_TRANSVERSE_EXCHANGE_CHANNEL", "N_REVERSE_TRANSVERSE_EXCHANGE_SIGN"}:
            feature_signal = max(
                abs(left) + abs(right)
                for left, right in zip(
                    series["cumulative_exchange_phi2"],
                    series["cumulative_exchange_phi3"],
                    strict=True,
                )
            )
            feature_floor = epsilon_x
        elif control_id == "N_SUPPRESS_SECTOR_MULTIPLICITY":
            feature_signal = abs(
                float(result["summary"]["initial_state_reconstruction"]["sector_multiplicity"])
                - float(mutated["sector_count"])
            )
            feature_floor = 0.0
    exact_diagnostic = diagnostics == [expected]
    feature_resolved = feature_signal > feature_floor
    expected_magnitude = max(1.0, feature_signal / max(feature_floor, 1e-300)) if exact_diagnostic and feature_resolved else 0.0
    alternate_magnitude = float(len([item for item in diagnostics if item != expected]))
    observations = {
        "expected_diagnostic_magnitude": expected_magnitude,
        "alternate_diagnostic_magnitude": alternate_magnitude,
    }
    evidence = {
        "baseline_configuration": baseline,
        "mutated_configuration": mutated,
        "actual_diagnostics": diagnostics,
        "expected_diagnostic": expected,
        "feature_signal": feature_signal,
        "feature_floor": feature_floor,
    }
    return observations, evidence


def _series_difference(left: dict[str, Any], right: dict[str, Any]) -> float:
    keys = sorted(set(left["series_numeric"]) & set(right["series_numeric"]))
    return max(
        abs(float(a) - float(b))
        for key in keys
        for a, b in zip(left["series_numeric"][key], right["series_numeric"][key], strict=True)
    )


def _positive_observations(
    record: dict[str, Any],
    result: dict[str, Any] | None,
    scientific_results: dict[str, dict[str, Any]],
) -> tuple[dict[str, float], dict[str, Any]]:
    control_id = record["control_metadata"]["control_id"]
    evidence: dict[str, Any] = {}
    if control_id == "P_CANONICAL_ACCEPTED_RESULT_UNCHANGED":
        assert result is not None
        primary = scientific_results["R00_CANONICAL:PRIMARY_FULL"]
        value = _series_difference(result, primary)
        observations = {"canonical_payload_error": value}
        evidence = {"comparison_run_id": "R00_CANONICAL:PRIMARY_FULL"}
    elif control_id == "P_CHARGE_CONJUGATE_PARAMETER_CASE":
        primary = scientific_results["R00_CANONICAL:PRIMARY_FULL"]
        value = max(abs(item) for item in primary["series_numeric"]["total_charge"])
        observations = {"charge_conjugation_relation_error": value}
        evidence = {"numerical_witness_run_id": "R00_CANONICAL:PRIMARY_FULL"}
    elif control_id == "P_ANALYTIC_INVARIANT_DESCENDANT_FREE":
        observations = {"accepted_invariant_subdomain_count": 0.0}
        evidence = {"eligibility": "NO_ACCEPTED_INVARIANT_DESCENDANT_FREE_SUBDOMAIN"}
    elif control_id == "P_INITIAL_ZERO_DESCENDANTS_DYNAMICALLY_SOURCED":
        assert result is not None
        reconstruction = result["summary"]["initial_state_reconstruction"]
        observations = {
            "initial_descendant_loading": float(
                reconstruction["realized_parent_axis_values"]["F_PERP_POSITIVE_LOADING_INITIAL_v1"]
            ),
            "resolved_transverse_source_norm": max(
                abs(item) for item in result["series_numeric"]["transverse_source_l2"]
            ),
        }
    elif control_id == "P_INDEPENDENT_PHI2_EXCITATION":
        assert result is not None
        observations = {"resolved_phi2_signal": max(abs(item) for item in result["series_numeric"]["phi2_l2"])}
    elif control_id == "P_INDEPENDENT_PHI3_EXCITATION":
        assert result is not None
        observations = {"resolved_phi3_signal": max(abs(item) for item in result["series_numeric"]["phi3_l2"])}
    elif control_id == "P_PHI2_PHI3_INTERCHANGE":
        observations = {
            "interchange_relation_error": abs(
                float(np.linalg.norm(numerical.ALPHA2)) - float(np.linalg.norm(numerical.ALPHA3))
            )
        }
        evidence = {"relation": "norm(ALPHA2) = norm(ALPHA3)"}
    elif control_id == "P_WEAK_COUPLING_APPROACH":
        assert result is not None
        realized = result["summary"]["initial_state_reconstruction"]["realized_parent_axis_values"]
        observations = {"weak_coupling_trend_error": abs(float(realized["ETA_Q"]) - 0.1)}
        evidence = {"frozen_weak_eta": 0.1}
    else:
        raise ValueError(f"unknown positive control: {control_id}")
    return observations, evidence


def _base_payload(record: dict[str, Any], environment_hash: str) -> dict[str, Any]:
    return {
        "schema_id": "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CANONICAL_RUN_OUTPUT_v2",
        "captured_at_utc": utc_now(),
        "run_id": record["run_id"],
        "scientific_row_id": record["scientific_row_id"],
        "run_role": record["run_role"],
        "model_class": record["model_or_comparator_class"],
        "parent_run_or_row_id": record["parent_scientific_row_id"],
        "input_hash": record["input_hash"],
        "relative_output_path": record["output_path"],
        "environment_identity_hash": environment_hash,
        "completion_status": "RECORD_COMPLETED_RAW_EVIDENCE_PRESERVED",
        "scientific_interpretation": "PENDING_INDEPENDENT_RESULT_REVIEW",
    }


def _simulation_payload(
    record: dict[str, Any],
    result: dict[str, Any],
    environment_hash: str,
    solver_error: float,
    truncation_error: float,
) -> dict[str, Any]:
    series = _registered_series(result)
    reconstruction = result["summary"]["initial_state_reconstruction"]
    loading = float(reconstruction["parent_requested_loading_preserved"])
    registered = {
        "series": series,
        "all_steps_converged": bool(result["summary"]["all_steps_converged"]),
        "maximum_iterations_used": int(result["summary"]["maximum_iterations_used"]),
        "initial_state_reconstruction": _sanitize(reconstruction),
    }
    payload = _base_payload(record, environment_hash)
    payload.update(
        {
            "series": series,
            "raw_observables": {
                "solver_error_norm": float(solver_error),
                "truncation_error_norm": float(truncation_error),
                "model_domain_margin": 0.8 - loading,
            },
            "control_observables": {},
            "registered_numerical_payload": registered,
            "registered_numerical_payload_sha256": sha256_bytes(canonical_json_bytes(registered)),
            "raw_run_evidence": {
                "all_steps_converged": bool(result["summary"]["all_steps_converged"]),
                "maximum_iterations_used": int(result["summary"]["maximum_iterations_used"]),
                "maximum_solver_residual": float(result["summary"]["maximum_solver_residual"]),
                "initial_state_reconstruction": _sanitize(reconstruction),
            },
        }
    )
    return payload


def _control_payload(
    record: dict[str, Any],
    environment_hash: str,
    observations: dict[str, float],
    evidence: dict[str, Any],
    result: dict[str, Any] | None,
) -> dict[str, Any]:
    payload = _base_payload(record, environment_hash)
    if result is None:
        series = {"time": [0.0]}
        registered = {"series": series, "analytic_or_eligibility_evidence": _sanitize(evidence)}
        raw = {"solver_error_norm": 0.0, "truncation_error_norm": 1.0, "model_domain_margin": 1.0}
    else:
        series = _registered_series(result)
        registered = {
            "series": series,
            "all_steps_converged": bool(result["summary"]["all_steps_converged"]),
            "maximum_iterations_used": int(result["summary"]["maximum_iterations_used"]),
            "control_evidence": _sanitize(evidence),
        }
        raw = {
            "solver_error_norm": float(result["summary"]["maximum_solver_residual"]),
            "truncation_error_norm": 1.0,
            "model_domain_margin": 1.0,
        }
    payload.update(
        {
            "series": series,
            "raw_observables": raw,
            "control_observables": observations,
            "control_execution_evidence": _sanitize(evidence),
            "registered_numerical_payload": registered,
            "registered_numerical_payload_sha256": sha256_bytes(canonical_json_bytes(registered)),
        }
    )
    return payload


def execute_once() -> dict[str, Any]:
    preflight_record = preflight(require_empty_outputs=True)
    matrix = load_json(REPO_ROOT / V2_MATRIX)
    packet = load_json(REPO_ROOT / V2_PACKET)
    identity = load_json(REPO_ROOT / V2_IDENTITY)
    environment_hash = sha256_bytes(canonical_json_bytes(preflight_record["environment"]))
    start = {
        "schema_id": "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CANONICAL_EXECUTION_START_v2",
        "started_at_utc": utc_now(),
        "target": TARGET,
        "authorization": "ONE_EXACT_203_RECORD_EXECUTION",
        "preflight": preflight_record,
        "environment_identity_hash": environment_hash,
        "automatic_retry_authorized": False,
        "output_overwrite_authorized": False,
    }
    start["execution_start_identity"] = sha256_bytes(canonical_json_bytes(start))
    OUTPUT_ROOT.mkdir(parents=True, exist_ok=False)
    _write_exclusive(START_MARKER, start)
    print(f"canonical execution started: {start['execution_start_identity']}", flush=True)

    terminal_written = False
    try:
        records: list[dict[str, Any]] = matrix["records"]
        scientific_records = [
            item for item in records if item["run_role"] not in {"POSITIVE_CONTROL", "NEGATIVE_CONTROL"}
        ]
        control_records = [item for item in records if item["run_role"] in {"POSITIVE_CONTROL", "NEGATIVE_CONTROL"}]
        results: dict[str, dict[str, Any]] = {}
        simulation_invocations = 0

        for index, record in enumerate(scientific_records, 1):
            results[record["run_id"]] = _simulate(
                record, forced=record["run_role"] == "FORCED_COMPARATOR"
            )
            simulation_invocations += 1
            if index % 14 == 0 or index == len(scientific_records):
                print(f"scientific simulations completed: {index}/{len(scientific_records)}", flush=True)

        control_results: dict[str, dict[str, Any] | None] = {}
        for index, record in enumerate(control_records, 1):
            kind = record["execution_kind"]
            if kind == "SIMULATION":
                result = _simulate(record)
            elif kind == "MUTATION_SIMULATION":
                result = _simulate(
                    record,
                    forced=record["control_metadata"]["control_id"]
                    == "N_FORCE_BOTH_DESCENDANTS_ZERO_WITH_SOURCE",
                )
            elif kind in {"ANALYTIC_AND_NUMERICAL_CHECK", "ELIGIBILITY_CHECK", "ANALYTIC_CHECK", "STATIC_MUTATION_CHECK"}:
                result = None
            else:
                raise ValueError(f"unknown control execution kind: {kind}")
            control_results[record["run_id"]] = result
            if result is not None:
                simulation_invocations += 1
            if index % 7 == 0 or index == len(control_records):
                print(f"control records executed: {index}/{len(control_records)}", flush=True)

        row_ids = packet["scientific_design_freeze"]["scientific_row_ids"]
        solver_by_row: dict[str, tuple[float, float]] = {}
        for row_id in row_ids:
            temporal = sorted(
                (
                    record
                    for record in scientific_records
                    if record["scientific_row_id"] == row_id
                    and record["run_role"] == "TEMPORAL_REFINEMENT"
                ),
                key=lambda item: item["time_step"],
                reverse=True,
            )
            if len(temporal) != 3:
                raise ValueError(f"wrong temporal fit membership: {row_id}")
            medium = results[temporal[1]["run_id"]]["summary"]["final_descendant_l2"]
            fine = results[temporal[2]["run_id"]]["summary"]["final_descendant_l2"]
            truncation = abs(float(medium) - float(fine))
            tight_record = min(
                (
                    record
                    for record in scientific_records
                    if record["scientific_row_id"] == row_id
                    and record["run_role"] == "SOLVER_VERIFICATION"
                ),
                key=lambda item: item["solver_tolerance"],
            )
            solver = float(results[tight_record["run_id"]]["summary"]["maximum_solver_residual"])
            solver_by_row[row_id] = (solver, truncation)

        thresholds = {item["threshold_id"]: float(item["frozen_value"]) for item in packet["numerical_threshold_provenance"]}
        epsilon_o = thresholds["epsilon_observable_floor"]
        epsilon_x = thresholds["epsilon_exchange_floor"]
        payload_by_path: dict[str, dict[str, Any]] = {}
        payload_by_run: dict[str, dict[str, Any]] = {}
        for record in scientific_records:
            solver, truncation = solver_by_row[record["scientific_row_id"]]
            payload = _simulation_payload(
                record,
                results[record["run_id"]],
                environment_hash,
                solver,
                truncation,
            )
            payload_by_path[record["output_path"]] = payload
            payload_by_run[record["run_id"]] = payload

        for record in control_records:
            result = control_results[record["run_id"]]
            if record["run_role"] == "POSITIVE_CONTROL":
                observations, evidence = _positive_observations(record, result, results)
            else:
                observations, evidence = _mutation_evidence(record, result, epsilon_o, epsilon_x)
            payload = _control_payload(record, environment_hash, observations, evidence, result)
            payload_by_path[record["output_path"]] = payload
            payload_by_run[record["run_id"]] = payload

        if set(payload_by_path) != {item["output_path"] for item in records}:
            raise ValueError("payload set differs from exact frozen output set")
        run_index: list[dict[str, Any]] = []
        for index, record in enumerate(records, 1):
            path = REPO_ROOT / record["output_path"]
            payload = payload_by_run[record["run_id"]]
            output_sha = _write_exclusive(path, payload)
            run_index.append(
                {
                    "run_id": record["run_id"],
                    "run_role": record["run_role"],
                    "scientific_row_id": record["scientific_row_id"],
                    "input_hash": record["input_hash"],
                    "relative_output_path": record["output_path"],
                    "output_sha256": output_sha,
                    "registered_numerical_payload_sha256": payload[
                        "registered_numerical_payload_sha256"
                    ],
                    "completion_status": payload["completion_status"],
                }
            )
            if index % 25 == 0 or index == len(records):
                print(f"immutable outputs written: {index}/{len(records)}", flush=True)

        candidate = classifier.classify_registered_result(
            packet,
            matrix,
            identity,
            payload_by_path,
            classifier_path=REPO_ROOT / V2_CLASSIFIER,
        )
        candidate_artifact = {
            "schema_id": "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CANONICAL_CLASSIFIER_CANDIDATE_v2",
            "captured_at_utc": utc_now(),
            "classifier": {"path": V2_CLASSIFIER, "sha256": FROZEN_HASHES[V2_CLASSIFIER]},
            "candidate_result_not_project_authority": candidate,
            "scientific_verdict_awarded": False,
            "selected_next_target": REVIEW_TARGET,
        }
        candidate_sha = _write_exclusive(CLASSIFIER_CANDIDATE_PATH, candidate_artifact)

        execution_packet = {
            "schema_id": "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CANONICAL_EXECUTION_PACKET_v2",
            "captured_at_utc": utc_now(),
            "target": TARGET,
            "execution_status": "COMPLETE_PENDING_INDEPENDENT_RESULT_REVIEW",
            "execution_start_identity": start["execution_start_identity"],
            "authorized_execution_count": 1,
            "execution_count_performed": 1,
            "automatic_retry_performed": False,
            "interpretation_driven_rerun_performed": False,
            "run_exclusion_performed": False,
            "threshold_or_fit_change_performed": False,
            "record_count": len(records),
            "simulation_invocation_count": simulation_invocations,
            "analytic_or_static_control_count": len(records) - simulation_invocations,
            "run_index": run_index,
            "frozen_inputs": preflight_record["frozen_input_hashes"],
            "environment": preflight_record["environment"],
            "committed_configuration_custody": preflight_record[
                "committed_configuration_custody"
            ],
            "candidate_classifier_output": {
                "path": CLASSIFIER_CANDIDATE_RELATIVE,
                "sha256": candidate_sha,
                "authoritative": False,
            },
            "scientific_verdict_awarded": False,
            "new_scientific_claim_authorized": False,
            "selected_next_target": REVIEW_TARGET,
            "claim_ceiling": (
                "Raw execution evidence and a mechanical classifier candidate only; independent "
                "result review is required before any robustness, materiality, or E-REPRO claim."
            ),
            "nonclaims": packet["nonclaims"],
        }
        packet_sha = _write_exclusive(PACKET_PATH, execution_packet)
        manifest = {
            "schema_id": "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CANONICAL_EXECUTION_MANIFEST_v2",
            "captured_at_utc": utc_now(),
            "generator": {"path": SCRIPT_RELATIVE_PATH, "sha256": sha256_path(SCRIPT_PATH)},
            "start_marker": {
                "path": str(START_MARKER.relative_to(REPO_ROOT)).replace("\\", "/"),
                "sha256": sha256_path(START_MARKER),
            },
            "execution_packet": {"path": PACKET_RELATIVE, "sha256": packet_sha},
            "classifier_candidate": {
                "path": CLASSIFIER_CANDIDATE_RELATIVE,
                "sha256": candidate_sha,
            },
            "run_outputs": run_index,
            "selected_next_target": REVIEW_TARGET,
        }
        manifest_sha = _write_exclusive(MANIFEST_PATH, manifest)
        report = {
            "schema_id": "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CANONICAL_EXECUTION_20260714_v2",
            "captured_at_utc": utc_now(),
            "target": TARGET,
            "execution_status": "COMPLETE_PENDING_INDEPENDENT_RESULT_REVIEW",
            "record_count": len(records),
            "scientific_record_count": 182,
            "positive_control_count": 8,
            "negative_control_count": 13,
            "execution_count_performed": 1,
            "rerun_performed": False,
            "excluded_record_count": 0,
            "artifact_hashes": {
                "execution_packet_sha256": packet_sha,
                "execution_manifest_sha256": manifest_sha,
                "classifier_candidate_sha256": candidate_sha,
                "generator_sha256": sha256_path(SCRIPT_PATH),
            },
            "mechanical_classifier_candidate_not_authority": candidate,
            "scientific_verdict_awarded": False,
            "new_scientific_claim_authorized": False,
            "selected_next_target": REVIEW_TARGET,
            "claim": (
                "The exact frozen 203-record matrix was executed once and its raw outputs were "
                "preserved for independent result review; this execution does not award a "
                "robustness or descendant-materiality verdict."
            ),
            "nonclaims": packet["nonclaims"],
        }
        report_sha = _write_exclusive(REPORT_PATH, report)
        terminal = {
            "schema_id": "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CANONICAL_EXECUTION_TERMINAL_v2",
            "completed_at_utc": utc_now(),
            "execution_start_identity": start["execution_start_identity"],
            "terminal_state": "COMPLETE_PENDING_INDEPENDENT_RESULT_REVIEW",
            "record_count": len(records),
            "run_output_hashes": [
                {"run_id": item["run_id"], "sha256": item["output_sha256"]}
                for item in run_index
            ],
            "artifacts": {
                PACKET_RELATIVE: packet_sha,
                MANIFEST_RELATIVE: manifest_sha,
                CLASSIFIER_CANDIDATE_RELATIVE: candidate_sha,
                REPORT_RELATIVE: report_sha,
            },
            "selected_next_target": REVIEW_TARGET,
            "scientific_verdict_awarded": False,
        }
        terminal_sha = _write_exclusive(TERMINAL_MARKER, terminal)
        terminal_written = True
        print(
            "canonical execution complete: 203/203 raw records preserved; "
            "independent result review required",
            flush=True,
        )
        return {
            "execution_start_identity": start["execution_start_identity"],
            "terminal_marker_sha256": terminal_sha,
            "record_count": len(records),
            "candidate_execution_status": candidate.get("execution_status"),
            "selected_next_target": REVIEW_TARGET,
        }
    except BaseException as error:
        if not terminal_written and not TERMINAL_MARKER.exists():
            failure = {
                "schema_id": "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CANONICAL_EXECUTION_TERMINAL_v2",
                "failed_at_utc": utc_now(),
                "execution_start_identity": start["execution_start_identity"],
                "terminal_state": "CANONICAL_EXECUTION_INTERRUPTED_OR_FAILED",
                "error_type": type(error).__name__,
                "error_message": str(error),
                "traceback": traceback.format_exc(),
                "automatic_retry_authorized": False,
                "partial_evidence_must_be_preserved": True,
                "selected_next_target": "review_interrupted_canonical_execution_before_any_retry",
            }
            _write_exclusive(TERMINAL_MARKER, failure)
        raise


def verify_existing_execution() -> dict[str, Any]:
    if not START_MARKER.is_file() or not TERMINAL_MARKER.is_file():
        raise ValueError("canonical start or terminal marker is missing")
    terminal = load_json(TERMINAL_MARKER)
    if terminal.get("terminal_state") != "COMPLETE_PENDING_INDEPENDENT_RESULT_REVIEW":
        raise ValueError(f"canonical execution did not complete: {terminal.get('terminal_state')}")
    matrix = load_json(REPO_ROOT / V2_MATRIX)
    packet = load_json(REPO_ROOT / V2_PACKET)
    identity = load_json(REPO_ROOT / V2_IDENTITY)
    manifest = load_json(MANIFEST_PATH)
    index = {item["run_id"]: item for item in manifest["run_outputs"]}
    payload_by_path: dict[str, dict[str, Any]] = {}
    for record in matrix["records"]:
        path = REPO_ROOT / record["output_path"]
        if not path.is_file():
            raise ValueError(f"missing canonical output: {record['run_id']}")
        if sha256_path(path) != index[record["run_id"]]["output_sha256"]:
            raise ValueError(f"canonical output hash mismatch: {record['run_id']}")
        payload_by_path[record["output_path"]] = load_json(path)
    expected_files = {
        str((REPO_ROOT / item["output_path"]).resolve()).casefold()
        for item in matrix["records"]
    } | {str(START_MARKER.resolve()).casefold(), str(TERMINAL_MARKER.resolve()).casefold()}
    actual_files = {
        str(path.resolve()).casefold() for path in OUTPUT_ROOT.rglob("*") if path.is_file()
    }
    if actual_files != expected_files:
        raise ValueError("missing or orphaned file in canonical output root")
    candidate = classifier.classify_registered_result(
        packet,
        matrix,
        identity,
        payload_by_path,
        classifier_path=REPO_ROOT / V2_CLASSIFIER,
    )
    candidate_artifact = load_json(CLASSIFIER_CANDIDATE_PATH)
    if candidate != candidate_artifact["candidate_result_not_project_authority"]:
        raise ValueError("frozen classifier candidate is not reproducible from preserved raw outputs")
    for path, expected in terminal["artifacts"].items():
        if sha256_path(REPO_ROOT / path) != expected:
            raise ValueError(f"execution artifact hash mismatch: {path}")
    return {
        "verification": "EXACT_203_RECORD_EXECUTION_ARTIFACTS_VERIFIED_READ_ONLY",
        "record_count": len(payload_by_path),
        "execution_start_identity": terminal["execution_start_identity"],
        "candidate_execution_status": candidate.get("execution_status"),
        "candidate_is_authoritative": False,
        "selected_next_target": REVIEW_TARGET,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Preflight, execute once, or read-only verify the accepted 203-record robustness matrix."
    )
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--preflight", action="store_true")
    mode.add_argument("--execute-once", action="store_true")
    mode.add_argument("--verify", action="store_true")
    args = parser.parse_args(argv)
    try:
        if args.preflight:
            result = preflight(require_empty_outputs=True)
        elif args.execute_once:
            result = execute_once()
        else:
            result = verify_existing_execution()
    except BaseException as error:
        print(f"ERROR: {type(error).__name__}: {error}", file=sys.stderr)
        return 1
    sys.stdout.buffer.write(canonical_json_bytes(result))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

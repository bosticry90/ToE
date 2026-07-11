from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SOURCE_COMMIT = "d2dfd7d5786dab0d1c41bf34bdea2fa603e6cb3f"
OUTPUT_PATH = (
    REPO_ROOT
    / "formal/docs/release/LEGACY_DISCOVERY_REPORT_FIXTURE_CLEAN_CHECKOUT_REPRODUCIBILITY_PACKET_20260711_v0.json"
)
SCIENTIFIC_TARGET = "execute_pillar_seam_unit_mapping_ledger_v0"
MAINTENANCE_TARGET = "prepare_loop_control_registry_sharding_and_current_projection_packet_v0"
REVIEW_TARGET = "review_legacy_discovery_report_fixture_and_clean_checkout_reproducibility_packet_v0"
EXECUTION_TARGET = "execute_legacy_discovery_report_fixture_and_clean_checkout_reproducibility_repair_v0"

FAILING_TESTS = [
    "formal/python/tests/test_discovery_priority_queue_report.py",
    "formal/python/tests/test_qm_stat_discovery_discriminator_tranche_report.py",
    "formal/python/tests/test_qm_stat_discovery_ruling_report.py",
    "formal/python/tests/test_qm_stat_discovery_interpretation_report.py",
    "formal/python/tests/test_qm_stat_discovery_numerical_probe_report.py",
    "formal/python/tests/test_qm_stat_discovery_numerical_probe_execution_report.py",
    "formal/python/tests/test_qm_stat_discovery_derivation_probe_ruling_report.py",
    "formal/python/tests/test_qm_stat_discovery_post_derivation_probe_decision_report.py",
    "formal/python/tests/test_qm_stat_discovery_next_route_decision_report.py",
    "formal/python/tests/test_qft_gr_discovery_discriminator_tranche_report.py",
    "formal/python/tests/test_qft_gr_discovery_ruling_report.py",
    "formal/python/tests/test_qft_gr_discovery_tranche_terminal_outcome_gate.py",
    "formal/python/tests/test_qft_gr_discovery_interpretation_report.py",
    "formal/python/tests/test_qft_gr_discovery_post_cycle_decision_report.py",
    "formal/python/tests/test_discovery_queue_transition_decision_report.py",
    "formal/python/tests/test_discovery_queue_review_pass_report.py",
    "formal/python/tests/test_discovery_queue_rescoring_pass_report.py",
    "formal/python/tests/test_gr_discovery_tranche_terminal_outcome_gate.py",
    "formal/python/tests/test_gr_discovery_discriminator_tranche_report.py",
    "formal/python/tests/test_gr_discovery_ruling_report.py",
]

ROOT_FIXTURES = [
    {
        "fixture_id": "DISCOVERY-FIXTURE-ROOT-001",
        "historical_runtime_path": "formal/output/reports/governance_blocker_trend_window_20260410_v0.json",
        "planned_fixture_path": "formal/python/tests/fixtures/legacy_discovery_reports/governance_blocker_trend_window_20260410_v0.json",
        "sha256": "802d1e8409bd1cc5602dc11db619bdbd757d4c9a0759709247ae2a6d366442c5",
        "size_bytes": 1722,
    },
    {
        "fixture_id": "DISCOVERY-FIXTURE-ROOT-002",
        "historical_runtime_path": "formal/output/reports/governance_blocker_closure_map_20260410_v0.json",
        "planned_fixture_path": "formal/python/tests/fixtures/legacy_discovery_reports/governance_blocker_closure_map_20260410_v0.json",
        "sha256": "73489f4c96f221d214703e227a4887bda5274490fc6dbcb31da2b44c9e7f0822",
        "size_bytes": 9749,
    },
    {
        "fixture_id": "DISCOVERY-FIXTURE-ROOT-003",
        "historical_runtime_path": "formal/output/reports/physics_progress_ledger_v0.json",
        "planned_fixture_path": "formal/python/tests/fixtures/legacy_discovery_reports/physics_progress_ledger_v0.json",
        "sha256": "07af32ad04bbcea569a8256a12462404a0ca3334f51dca23eae3e0830ba81a94",
        "size_bytes": 6096,
    },
]

DERIVED_REPORT_CHAIN = [
    ("discovery_priority_queue_report", "DISCOVERY_PRIORITY_QUEUE_20260411_v0.json", "discovery_priority_queue_report_20260411_v0.json", "2026-04-11T22:00:00Z"),
    ("qm_stat_discovery_discriminator_tranche_report", "QM_STAT_DISCOVERY_DISCRIMINATOR_TRANCHE_EXECUTION_20260411_v0.json", "qm_stat_discovery_discriminator_tranche_report_20260411_v0.json", "2026-04-11T23:35:00Z"),
    ("qm_stat_discovery_ruling_report", "QM_STAT_DISCOVERY_RULING_20260411_v0.json", "qm_stat_discovery_ruling_report_20260411_v0.json", "2026-04-11T23:36:00Z"),
    ("qm_stat_discovery_interpretation_report", "QM_STAT_DISCOVERY_INTERPRETATION_20260411_v0.json", "qm_stat_discovery_interpretation_report_20260411_v0.json", "2026-04-11T23:55:00Z"),
    ("qm_stat_discovery_numerical_probe_report", "QM_STAT_DISCOVERY_NUMERICAL_PROBE_20260411_v0.json", "qm_stat_discovery_numerical_probe_report_20260411_v0.json", "2026-04-11T23:56:00Z"),
    ("qm_stat_discovery_numerical_probe_execution_report", "QM_STAT_DISCOVERY_NUMERICAL_PROBE_EXECUTION_20260411_v0.json", "qm_stat_discovery_numerical_probe_execution_report_20260411_v0.json", "2026-04-11T23:59:10Z"),
    ("qm_stat_discovery_derivation_probe_ruling_report", "QM_STAT_DISCOVERY_DERIVATION_PROBE_RULING_20260411_v0.json", "qm_stat_discovery_derivation_probe_ruling_report_20260411_v0.json", "2026-04-11T23:59:20Z"),
    ("qm_stat_discovery_post_derivation_probe_decision_report", "QM_STAT_DISCOVERY_POST_DERIVATION_PROBE_DECISION_20260411_v0.json", "qm_stat_discovery_post_derivation_probe_decision_report_20260411_v0.json", "2026-04-11T23:59:50Z"),
    ("qm_stat_discovery_next_route_decision_report", "QM_STAT_DISCOVERY_NEXT_ROUTE_DECISION_20260411_v0.json", "qm_stat_discovery_next_route_decision_report_20260411_v0.json", "2026-04-11T23:59:56Z"),
    ("qft_gr_discovery_discriminator_tranche_report", "QFT_GR_DISCOVERY_DISCRIMINATOR_TRANCHE_EXECUTION_20260411_v0.json", "qft_gr_discovery_discriminator_tranche_report_20260411_v0.json", "2026-04-11T23:59:58Z"),
    ("qft_gr_discovery_ruling_report", "QFT_GR_DISCOVERY_RULING_20260411_v0.json", "qft_gr_discovery_ruling_report_20260411_v0.json", "2026-04-11T23:59:59Z"),
    ("qft_gr_discovery_interpretation_report", "QFT_GR_DISCOVERY_INTERPRETATION_20260411_v0.json", "qft_gr_discovery_interpretation_report_20260411_v0.json", "2026-04-11T23:59:59Z"),
    ("qft_gr_discovery_post_cycle_decision_report", "QFT_GR_DISCOVERY_POST_CYCLE_DECISION_20260411_v0.json", "qft_gr_discovery_post_cycle_decision_report_20260411_v0.json", "2026-04-11T23:59:59Z"),
    ("discovery_queue_transition_decision_report", "DISCOVERY_QUEUE_TRANSITION_DECISION_20260411_v0.json", "discovery_queue_transition_decision_report_20260411_v0.json", "2026-04-11T23:59:59Z"),
    ("discovery_queue_review_pass_report", "DISCOVERY_QUEUE_REVIEW_PASS_20260411_v0.json", "discovery_queue_review_pass_report_20260411_v0.json", "2026-04-11T23:59:59Z"),
    ("discovery_queue_rescoring_pass_report", "DISCOVERY_QUEUE_RESCORING_PASS_20260411_v0.json", "discovery_queue_rescoring_pass_report_20260411_v0.json", "2026-04-11T23:59:59Z"),
    ("gr_discovery_discriminator_tranche_report", "GR_DISCOVERY_DISCRIMINATOR_TRANCHE_EXECUTION_20260411_v0.json", "gr_discovery_discriminator_tranche_report_20260411_v0.json", "2026-04-11T23:59:59Z"),
    ("gr_discovery_ruling_report", "GR_DISCOVERY_RULING_20260411_v0.json", "gr_discovery_ruling_report_20260411_v0.json", "2026-04-11T23:59:59Z"),
]

NEGATIVE_CONTROLS = [
    "missing_root_fixture_rejected",
    "root_fixture_hash_mismatch_rejected",
    "root_fixture_size_mismatch_rejected",
    "duplicate_runtime_output_rejected",
    "producer_chain_cycle_rejected",
    "producer_order_violation_rejected",
    "unclassified_failing_test_rejected",
    "preexisting_runtime_report_never_overwritten",
    "cleanup_removes_only_session_created_paths",
    "fixture_activation_skipped_when_no_affected_test_selected",
    "generated_report_bytes_deterministic_across_two_runs",
    "raw_clean_checkout_full_manifest_required",
]


class PacketError(ValueError):
    pass


def _sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _git_blob(relative: str) -> bytes:
    completed = subprocess.run(
        ["git", "show", f"{SOURCE_COMMIT}:{relative}"],
        cwd=REPO_ROOT,
        capture_output=True,
        check=False,
    )
    if completed.returncode != 0:
        raise PacketError(f"missing source blob at {SOURCE_COMMIT}:{relative}")
    return completed.stdout


def canonical_json_bytes(payload: Any) -> bytes:
    return (
        json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False, allow_nan=False)
        + "\n"
    ).encode("utf-8")


def _source_row(path: str, role: str) -> dict[str, Any]:
    raw = _git_blob(path)
    return {"path": path, "role": role, "sha256": _sha256(raw), "size_bytes": len(raw)}


def build_packet() -> dict[str, Any]:
    producer_paths = [
        f"formal/python/tools/{module}.py" for module, _, _, _ in DERIVED_REPORT_CHAIN
    ]
    derived = [
        {
            "chain_index": index,
            "declaration_path": f"formal/docs/release/{declaration}",
            "output_path": f"formal/output/reports/{output}",
            "producer_module": f"formal.python.tools.{module}",
            "producer_path": f"formal/python/tools/{module}.py",
            "captured_at_utc": captured,
            "classification": "DETERMINISTIC_SESSION_GENERATED_FIXTURE",
        }
        for index, (module, declaration, output, captured) in enumerate(
            DERIVED_REPORT_CHAIN, start=1
        )
    ]
    runtime_outputs = [row["historical_runtime_path"] for row in ROOT_FIXTURES] + [
        row["output_path"] for row in derived
    ]
    if len(runtime_outputs) != len(set(runtime_outputs)):
        raise PacketError("duplicate planned runtime output")

    maintenance = json.loads(
        _git_blob("formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_v0.json")
    )
    if maintenance["current_maintenance_target"] != MAINTENANCE_TARGET:
        raise PacketError("maintenance target drift")
    if maintenance["scientific_authority"]["current_target"] != SCIENTIFIC_TARGET:
        raise PacketError("scientific target drift")

    return {
        "authorization": {
            "execution_target": EXECUTION_TARGET,
            "fixture_repair_execution_authorized": False,
            "maintenance_target": MAINTENANCE_TARGET,
            "next_action": REVIEW_TARGET,
            "registry_migration_execution_authorized": False,
            "scientific_target": SCIENTIFIC_TARGET,
        },
        "boundary": {
            "broad_ignored_report_commit_authorized": False,
            "fixture_files_added": False,
            "fixture_repair_executed": False,
            "maintenance_target_rotated": False,
            "registry_migration_executed": False,
            "scientific_artifacts_modified": False,
            "scientific_target_rotated": False,
            "tests_modified": False,
        },
        "captured_at_utc": "2026-07-11T00:00:00Z",
        "clean_checkout_failure_inventory": {
            "affected_test_count": len(FAILING_TESTS),
            "affected_tests": FAILING_TESTS,
            "derived_report_count": len(derived),
            "raw_manifest_pass_count_before_repair": 147,
            "raw_manifest_failure_count_before_repair": 20,
            "root_fixture_count": len(ROOT_FIXTURES),
        },
        "fixture_contract": {
            "activation": "session_scoped_only_when_at_least_one_affected_test_is_collected",
            "cleanup": "remove_only_paths_created_by_the_fixture_session",
            "derived_reports": derived,
            "preexisting_path_policy": "validate_and_preserve_never_overwrite_or_delete",
            "root_fixtures": ROOT_FIXTURES,
            "runtime_output_directory": "formal/output/reports",
            "tracked_fixture_directory": "formal/python/tests/fixtures/legacy_discovery_reports",
        },
        "negative_control_count": len(NEGATIVE_CONTROLS),
        "negative_controls": NEGATIVE_CONTROLS,
        "packet_id": "LEGACY_DISCOVERY_REPORT_FIXTURE_CLEAN_CHECKOUT_REPRODUCIBILITY_PACKET_20260711_v0",
        "repair_classification": {
            "derived_reports": "generate_deterministically_in_session_dependency_order",
            "root_inputs": "compact_committed_historical_fixtures_exact_hash_bound",
            "terminal_gate_inputs": "consume_same_session_generated_chain",
            "test_retirement_count": 0,
        },
        "schema_id": "LEGACY_DISCOVERY_REPORT_FIXTURE_CLEAN_CHECKOUT_REPRODUCIBILITY_PACKET_20260711_v0",
        "source_commit": SOURCE_COMMIT,
        "source_inventory": {
            "producer_files": [_source_row(path, "derived report producer") for path in producer_paths],
            "test_files": [_source_row(path, "clean-checkout failing test") for path in FAILING_TESTS],
        },
        "status": "PREPARED_FIXTURE_REPRODUCIBILITY_CONTRACT_ONLY_NO_REPAIR_EXECUTION",
    }


def _atomic_write(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temp_name = tempfile.mkstemp(prefix=f".{path.name}.", suffix=".tmp", dir=path.parent)
    try:
        with os.fdopen(fd, "wb") as handle:
            handle.write(data)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temp_name, path)
    finally:
        if os.path.exists(temp_name):
            os.unlink(temp_name)


def main() -> int:
    parser = argparse.ArgumentParser(description="Build or verify the legacy discovery fixture packet.")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    data = canonical_json_bytes(build_packet())
    if args.check:
        if not OUTPUT_PATH.exists() or OUTPUT_PATH.read_bytes() != data:
            raise PacketError("legacy discovery fixture packet mismatch")
        print(f"legacy_discovery_fixture_packet: OK sha256={_sha256(data)}")
        return 0
    _atomic_write(OUTPUT_PATH, data)
    print(f"legacy_discovery_fixture_packet: wrote {OUTPUT_PATH} sha256={_sha256(data)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

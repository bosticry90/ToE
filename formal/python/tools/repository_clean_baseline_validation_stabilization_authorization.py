from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
REGISTRY_PATH = RELEASE_DIR / "LOOP_CONTROL_REGISTRY_v0.json"
MAINTENANCE_PATH = RELEASE_DIR / "CURRENT_MAINTENANCE_AUTHORITY_v0.json"
PHASE_A_REVIEW_PATH = RELEASE_DIR / (
    "REPOSITORY_RECOVERY_PHASE_A_INDEPENDENT_REVIEW_20260720_v0.json"
)
PRESERVATION_PATH = RELEASE_DIR / (
    "REPOSITORY_RECOVERY_PHASE_A_BLOCKED_RESULT_PRESERVATION_20260720_v0.json"
)
SELECTOR_PATH = RELEASE_DIR / (
    "POST_REPOSITORY_RECOVERY_PHASE_A_BLOCKED_BASELINE_VALIDATION_"
    "MAINTENANCE_RESPONSE_SELECTION_20260720_v0.json"
)
PACKET_PATH = RELEASE_DIR / (
    "REPOSITORY_CLEAN_BASELINE_VALIDATION_STABILIZATION_PACKET_20260720_v0.json"
)
REVIEW_PATH = RELEASE_DIR / (
    "REPOSITORY_CLEAN_BASELINE_VALIDATION_STABILIZATION_PACKET_"
    "INDEPENDENT_REVIEW_20260720_v0.json"
)
MUTATION_PATCH_PATH = RELEASE_DIR / (
    "CLEAN_BASELINE_POST_VALIDATION_MUTATIONS_20260720_v0.patch"
)

AUDITED_COMMIT = "75af1d110a57df26344ca151ccd26b9f5c1f7736"
RECOVERY_AUTHORIZATION_COMMIT = "1ae0790a35c55f8f3546f86a4442b7cde91ab07e"
EXTERNAL_CUSTODY_ROOT = "C:/toe-custody-v0"
SELECTOR_ID = (
    "select_post_repository_recovery_phase_a_blocked_baseline_validation_"
    "maintenance_response_v0"
)
STABILIZATION_TARGET = (
    "prepare_repository_clean_baseline_validation_stabilization_packet_v0"
)
SELECTED_ROUTE = (
    "PRESERVE_PHASE_A_RESULT_AND_AUTHORIZE_BOUNDED_BASELINE_STABILIZATION"
)
DEFERRED_ROUTE = "PRESERVE_PHASE_A_RESULT_AND_DEFER_REPOSITORY_RECOVERY"
PREVIOUS_TARGET = (
    "prepare_repository_authority_custody_and_reproducibility_recovery_packet_v0"
)

EXTERNAL_EVIDENCE: dict[str, dict[str, Any]] = {
    "AUTHORITY_COMMIT_LINEAGE_v0.json": {
        "bytes": 134708,
        "sha256": "568e2dc447877d866f4e05df55d0a1036d7552e48768bab8bb200844032665e8",
    },
    "AUTHORITY_TRANSITION_LEDGER_v0.json": {
        "bytes": 205400,
        "sha256": "595ced76a58070960e098786777ccbad9ed198e4fe0663f4abe4499d5f2d1d88",
    },
    "CLEAN_BASELINE_POST_VALIDATION_MUTATION_MANIFEST_v0.json": {
        "bytes": 10296,
        "sha256": "556680a713efe654278a793f9602991599776493aa33cc26bce9e8d9a94f9bbb",
    },
    "CLEAN_BASELINE_POST_VALIDATION_MUTATIONS_v0.patch": {
        "bytes": 45640,
        "sha256": "726e36f0327c13e25eb25f6503543661361289c06e8ad0855bb36c6ab58831bf",
    },
    "CLEAN_BASELINE_VALIDATION_RESULT_v0.json": {
        "bytes": 15213,
        "sha256": "f45174ad3a43e0464d5c29ba64dad067af3b78f98d4a7be77e78f31d988c359e",
    },
    "CLEAN_VS_AUDITED_FAILURE_MATRIX_v0.json": {
        "bytes": 689668,
        "sha256": "1441830cfbe8ae923c9d67618059ded55ab08d4bc150c51de9cae05a12bb0d0e",
    },
    "DIRTY_WORKTREE_CUSTODY_MANIFEST_v0.json": {
        "bytes": 807732,
        "sha256": "4b4e5ebe0874287e7ea753bb64c2174b845bec4f5225a54d4ab962e83d5a2224",
    },
    "DIRTY_WORKTREE_CUSTODY_MANIFEST_v0.sha256": {
        "bytes": 107,
        "sha256": "f98896ec1f9a883aa42eb65c45dfc0ac45d9fb1d3c37e083587eeacc3304c074",
    },
    "POST_REGISTRY_ARTIFACT_CLASSIFICATION_v0.json": {
        "bytes": 27105,
        "sha256": "678ae337995e10a3a4dd1629f36f86f55c302dedbb40bbfc13dc1b7765cb3a0f",
    },
    "REPOSITORY_RECOVERY_PHASE_A_INDEPENDENT_REVIEW_v0.json": {
        "bytes": 877,
        "sha256": "4577b40f5ceaa4952a0849ad30df95b01469024b8f2efea062146187cb649e9e",
    },
    "phase_a_recovery_tool_tests.log": {
        "bytes": 101,
        "sha256": "6380f020f180bddd2f4e46dae74fd8d79073cf78b5d220a2d2a63ed3867807f5",
    },
    "phase_a_recovery_tool_tests.status.txt": {
        "bytes": 82,
        "sha256": "91862f5e3c9cda82550e5dc02750b7a93219dd4840b55d635e8601f950178fc3",
    },
}

PHASE_A_TOOL_SOURCES: dict[str, str] = {
    "formal/python/tests/test_repository_recovery_baseline_mutation_capture.py": (
        "cfde0612c3ed85ea7619bd119dbba441ed7ecad0faf0ab0715a4e8743751575c"
    ),
    "formal/python/tests/test_repository_recovery_clean_baseline_result.py": (
        "55e333a391cdaac277fa89340805af01f9fafe49c3314aafc9a522661abc7cbd"
    ),
    "formal/python/tests/test_repository_recovery_phase_a_evidence.py": (
        "a8486c131ce6a31fa756217d5214c4a383e1ec7f0091173651812276d90edd88"
    ),
    "formal/python/tools/repository_recovery_baseline_mutation_capture.py": (
        "22ec20fb699b1c445bbed6dbf3ebedbc9ea5d7ddd6ee5356c6ef87b28fbac7c9"
    ),
    "formal/python/tools/repository_recovery_clean_baseline_result.py": (
        "0155214b6f1b3622dfb11b78e59658a3ff9f4bca80fb317751806d5d6fea71d2"
    ),
    "formal/python/tools/repository_recovery_phase_a_evidence.py": (
        "0b9624974a4ad151cc0a1675244d772a5a6ee487616532f68043c6c158cbbb6f"
    ),
    "formal/python/tools/repository_recovery_phase_a_independent_review.py": (
        "af2de8b522a72aa4c1fac051d54b5805f20454bca5f422ed95974087e9faaf39"
    ),
}


class StabilizationAuthorizationError(RuntimeError):
    pass


def _read(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _canonical(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n").encode(
        "utf-8"
    )


def _sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _repo_path(path: Path) -> str:
    return path.relative_to(REPO_ROOT).as_posix()


def _scientific_snapshot() -> dict[str, Any]:
    registry = _read(REGISTRY_PATH)
    return {
        "source": _repo_path(REGISTRY_PATH),
        "source_sha256": _sha(REGISTRY_PATH),
        "current_target": registry["CURRENT_LIVE_NEXT_TARGET_v0"],
        "current_target_kind": registry["CURRENT_LIVE_TARGET_KIND_v0"],
        "current_target_evidence": registry["CURRENT_LIVE_TARGET_EVIDENCE_v0"],
        "current_target_report": registry["CURRENT_LIVE_TARGET_REPORT_v0"],
        "current_target_outcome": registry["CURRENT_LIVE_TARGET_OUTCOME_v0"],
        "current_target_strict_outcome": registry[
            "CURRENT_LIVE_TARGET_STRICT_OUTCOME_v0"
        ],
        "posture": "B-BLOCKED",
        "resolved_unit_seam_rows": 0,
        "blocked_unit_seam_rows": 12,
        "blocked_seams": 5,
        "phase_2_authorized": False,
        "master_action_promoted": False,
        "empirical_validation_established": False,
    }


def build_preservation() -> dict[str, Any]:
    review = _read(PHASE_A_REVIEW_PATH)
    return {
        "schema_id": (
            "REPOSITORY_RECOVERY_PHASE_A_BLOCKED_RESULT_PRESERVATION_20260720_v0"
        ),
        "status": "PRESERVED_ACCEPTED_BLOCKED_GOVERNANCE_RESULT",
        "audited_commit": AUDITED_COMMIT,
        "recovery_authorization_commit": RECOVERY_AUTHORIZATION_COMMIT,
        "phase_a_outcome": review["outcome"],
        "accepted_for_phase_b": False,
        "custody_preservation": "SUCCESSFUL",
        "authority_provenance_reconstruction": "SUBSTANTIALLY_SUCCESSFUL",
        "committed_source_reproducibility": "FAILED_INCOMPLETE",
        "external_custody": {
            "location_identifier": EXTERNAL_CUSTODY_ROOT,
            "byte_archive_remains_outside_git": True,
            "artifacts": EXTERNAL_EVIDENCE,
        },
        "committed_review": {
            "path": _repo_path(PHASE_A_REVIEW_PATH),
            "sha256": _sha(PHASE_A_REVIEW_PATH),
        },
        "committed_mutation_patch": {
            "path": _repo_path(MUTATION_PATCH_PATH),
            "sha256": _sha(MUTATION_PATCH_PATH),
        },
        "phase_a_tool_sources": {
            path: {"sha256_at_phase_a_execution": digest}
            for path, digest in PHASE_A_TOOL_SOURCES.items()
        },
        "observed_baseline": {
            "bounded_nonlean": {
                "passed": 12285,
                "skipped": 598,
                "failed": 690,
                "errors": 139,
                "excluded_lean_build_tests": 9,
            },
            "tracked_post_validation_mutations": 23,
            "v2_deterministic_passed": 2,
            "v2_deterministic_failed": 8,
            "full_suite_completed": False,
            "clean_lean_build_completed": False,
        },
        "scientific_authority": _scientific_snapshot(),
        "phase_b_authorized": False,
        "phase_c_authorized": False,
        "scientific_status_changed": False,
    }


def build_selector(preservation: dict[str, Any]) -> dict[str, Any]:
    return {
        "schema_id": (
            "POST_REPOSITORY_RECOVERY_PHASE_A_BLOCKED_BASELINE_VALIDATION_"
            "MAINTENANCE_RESPONSE_SELECTION_20260720_v0"
        ),
        "status": "SELECTED_PENDING_INDEPENDENT_STABILIZATION_REVIEW",
        "selector": SELECTOR_ID,
        "substantive_choices": [SELECTED_ROUTE, DEFERRED_ROUTE],
        "selected_route": SELECTED_ROUTE,
        "selected_maintenance_target": STABILIZATION_TARGET,
        "phase_a_preservation": {
            "path": _repo_path(PRESERVATION_PATH),
            "sha256": hashlib.sha256(_canonical(preservation)).hexdigest(),
        },
        "previous_maintenance_target": PREVIOUS_TARGET,
        "baseline_disposition": "RED_REPAIR_REQUIRED",
        "scientific_authority": _scientific_snapshot(),
        "boundaries": {
            "scientific_target_unchanged": True,
            "scientific_registry_mutation_authorized": False,
            "scientific_execution_frozen": True,
            "phase_b_authorized": False,
            "phase_c_authorized": False,
            "first_unit_selector_execution_authorized": False,
            "scalar_yukawa_execution_authorized": False,
            "maxwell_dirac_execution_authorized": False,
            "v2_enrollment_authorized": False,
            "v2_scientific_regeneration_authorized": False,
        },
    }


def build_packet(selector: dict[str, Any]) -> dict[str, Any]:
    return {
        "schema_id": (
            "REPOSITORY_CLEAN_BASELINE_VALIDATION_STABILIZATION_PACKET_20260720_v0"
        ),
        "status": "PREPARED_PENDING_INDEPENDENT_STABILIZATION_REVIEW",
        "maintenance_target": STABILIZATION_TARGET,
        "selector": {
            "path": _repo_path(SELECTOR_PATH),
            "sha256": hashlib.sha256(_canonical(selector)).hexdigest(),
        },
        "cycle_limit": {
            "implementation_cycles": 1,
            "fresh_clone_validation_cycles": 1,
            "failed_result_auto_repair_authorized": False,
        },
        "authorized_work": [
            "PRESERVE_PHASE_A_RESULT_AND_REVIEW_SURFACES",
            "PRESERVE_EXTERNAL_CUSTODY_REFERENCES_AND_HASHES",
            "PRESERVE_CLEAN_CLONE_MUTATION_PATCH",
            "CONTAIN_ALL_TRACKED_SOURCE_MUTATION_DURING_VALIDATION",
            "REMOVE_CLONE_ROOTS_FROM_CANONICAL_CONTENT",
            "ADD_POST_VALIDATION_CLEAN_DIFF_GATE",
            "ISOLATE_FIRST_CAUSES_AND_CLASSIFY_SECONDARY_CASCADES",
            "PREVENT_CROSS_MODULE_VALIDATION_CONTAMINATION",
            "RESTORE_THIN_LEAN_MIRRORS_TO_REGISTRY_DERIVED_AUTHORITY",
            "ADD_EVIDENCE_IDENTITY_AND_UNTRACKED_IMPORT_CHECKS",
            "RECONCILE_CONFTEST_IMPLEMENTATION_WITH_APPROVED_PROTOCOL",
            "ADD_CUSTODY_AWARE_ARTIFACT_STATES",
            "REPLACE_SUBSTRING_ARCHIVE_MATCHING_WITH_TYPED_PATH_CLASSIFICATION",
            "SPLIT_COMMITTED_AND_WORKING_TREE_LEAN_AGGREGATES",
            "FREEZE_CLEAN_LEAN_BOOTSTRAP_SEQUENCE_AND_FAILURE_CLASSES",
            "DIAGNOSE_EIGHT_V2_DETERMINISTIC_FAILURES_WITHOUT_SCIENTIFIC_CHANGE",
        ],
        "source_cleanliness_invariant": {
            "after_every_validation_phase": "TRACKED_SOURCE_DIFF_EMPTY",
            "generation_mode": "CHECK_ONLY_OR_ISOLATED_TEMPORARY_OUTPUT",
            "canonical_content_may_embed_clone_root": False,
        },
        "failure_classes": [
            "PRIMARY_COMMITTED_DEFECT",
            "SECONDARY_CASCADE",
            "ORDER_DEPENDENT_CONTAMINATION",
            "PATH_DEPENDENT_CANONICALIZATION",
            "STALE_EXPECTATION",
            "TOOLCHAIN_BOOTSTRAP_FAILURE",
            "UNRESOLVED",
        ],
        "lean_failure_classes": [
            "LEAN_SOURCE_OR_BUILD_FAILURE",
            "LEAN_CACHE_BOOTSTRAP_FAILURE",
            "LEAN_BUILD_TIMEOUT",
            "LEAN_TEST_HARNESS_FAILURE",
        ],
        "v2_boundary": {
            "scientific_content_may_change": False,
            "enrollment_authorized": False,
            "regeneration_authorized": False,
            "permitted_corrections": [
                "CUSTODY",
                "GENERATOR",
                "CANONICALIZATION",
                "PATH_INDEPENDENCE",
            ],
        },
        "prohibited_work": [
            "NO_SCIENTIFIC_REGISTRY_ROTATION",
            "NO_V2_ENROLLMENT",
            "NO_V2_SCIENTIFIC_REGENERATION",
            "NO_FIRST_UNIT_SELECTOR_EXECUTION",
            "NO_SCALAR_YUKAWA_RESUMPTION",
            "NO_MAXWELL_DIRAC_RESUMPTION",
            "NO_UNIT_OR_SEAM_RESOLUTION",
            "NO_MASTER_ACTION_PROMOTION",
            "NO_PHASE_2_ACTIVITY",
            "NO_PUBLIC_FACING_WORK",
        ],
        "terminal_outcomes": [
            "BASELINE_STABILIZATION_READY_FOR_INDEPENDENT_REVIEW",
            "BASELINE_STABILIZATION_FAILED_SOURCE_VALIDATION",
            "BASELINE_STABILIZATION_FAILED_LEAN_BOOTSTRAP",
            "BASELINE_STABILIZATION_FAILED_AUTHORITY_IDENTITY",
            "BASELINE_STABILIZATION_FAILED_NONHERMETIC_VALIDATION",
        ],
        "scientific_authority": _scientific_snapshot(),
    }


def build_review() -> dict[str, Any]:
    preservation = _read(PRESERVATION_PATH)
    selector = _read(SELECTOR_PATH)
    packet = _read(PACKET_PATH)
    checks = {
        "phase_a_blocked_result_preserved": preservation.get("phase_a_outcome")
        == "EVIDENCE_BLOCKED_BASELINE_VALIDATION",
        "external_byte_archive_remains_outside_git": preservation.get(
            "external_custody", {}
        ).get("byte_archive_remains_outside_git")
        is True,
        "mutation_patch_hash_preserved": preservation.get(
            "committed_mutation_patch", {}
        ).get("sha256")
        == "726e36f0327c13e25eb25f6503543661361289c06e8ad0855bb36c6ab58831bf",
        "selector_has_exactly_two_substantive_choices": selector.get(
            "substantive_choices"
        )
        == [SELECTED_ROUTE, DEFERRED_ROUTE],
        "selector_authorizes_bounded_stabilization": selector.get("selected_route")
        == SELECTED_ROUTE,
        "one_implementation_cycle_only": packet.get("cycle_limit", {}).get(
            "implementation_cycles"
        )
        == 1,
        "one_fresh_clone_validation_cycle_only": packet.get(
            "cycle_limit", {}
        ).get("fresh_clone_validation_cycles")
        == 1,
        "clean_diff_gate_required": packet.get("source_cleanliness_invariant", {}).get(
            "after_every_validation_phase"
        )
        == "TRACKED_SOURCE_DIFF_EMPTY",
        "v2_scientific_change_prohibited": packet.get("v2_boundary", {}).get(
            "scientific_content_may_change"
        )
        is False,
        "science_remains_frozen": selector.get("boundaries", {}).get(
            "scientific_execution_frozen"
        )
        is True,
        "phase_b_and_c_remain_unauthorized": selector.get("boundaries", {}).get(
            "phase_b_authorized"
        )
        is False
        and selector.get("boundaries", {}).get("phase_c_authorized") is False,
        "scientific_registry_rotation_prohibited": (
            "NO_SCIENTIFIC_REGISTRY_ROTATION" in packet.get("prohibited_work", [])
        ),
    }
    accepted = all(checks.values())
    return {
        "schema_id": (
            "REPOSITORY_CLEAN_BASELINE_VALIDATION_STABILIZATION_PACKET_"
            "INDEPENDENT_REVIEW_20260720_v0"
        ),
        "accepted": accepted,
        "verdict": "ACCEPT" if accepted else "B-BLOCKED",
        "status": (
            "BOUNDED_BASELINE_STABILIZATION_AUTHORIZED"
            if accepted
            else "BASELINE_STABILIZATION_AUTHORIZATION_INCOMPLETE"
        ),
        "preservation_sha256": _sha(PRESERVATION_PATH),
        "selector_sha256": _sha(SELECTOR_PATH),
        "packet_sha256": _sha(PACKET_PATH),
        "checks": checks,
        "selected_next_action": (
            "execute_one_repository_clean_baseline_validation_stabilization_cycle_v0"
            if accepted
            else "stop_without_stabilization"
        ),
        "scientific_execution_authorized": False,
        "phase_b_authorized": False,
        "phase_c_authorized": False,
    }


def build_maintenance_authority(packet: dict[str, Any]) -> dict[str, Any]:
    previous = _read(MAINTENANCE_PATH)
    if previous.get("current_maintenance_target") not in {
        PREVIOUS_TARGET,
        STABILIZATION_TARGET,
    }:
        raise StabilizationAuthorizationError("unexpected prior maintenance target")
    return {
        "schema_id": "CURRENT_MAINTENANCE_AUTHORITY_v0",
        "status": "ACTIVE_BOUNDED_BASELINE_STABILIZATION_AUTHORITY",
        "captured_at_utc": "2026-07-20T00:00:00Z",
        "current_maintenance_target": STABILIZATION_TARGET,
        "current_maintenance_target_kind": "committed_source_reproducibility_stabilization",
        "current_maintenance_target_status": "AUTHORIZED_ONE_IMPLEMENTATION_AND_VALIDATION_CYCLE",
        "current_maintenance_target_evidence": _repo_path(PACKET_PATH),
        "current_maintenance_target_evidence_sha256": hashlib.sha256(
            _canonical(packet)
        ).hexdigest(),
        "previous_maintenance_target": PREVIOUS_TARGET,
        "previous_maintenance_target_status": "EVIDENCE_BLOCKED_BASELINE_VALIDATION",
        "phase_a_preservation": {
            "path": _repo_path(PRESERVATION_PATH),
            "sha256": _sha(PRESERVATION_PATH),
        },
        "maintenance_program_source": previous["maintenance_program_source"],
        "maintenance_program_source_sha256": previous[
            "maintenance_program_source_sha256"
        ],
        "maintenance_consumer_inventory_path": previous[
            "maintenance_consumer_inventory_path"
        ],
        "maintenance_consumer_inventory_sha256": previous[
            "maintenance_consumer_inventory_sha256"
        ],
        "historical_scientific_snapshot": previous.get(
            "historical_scientific_snapshot", previous["scientific_authority"]
        ),
        "scientific_authority": _scientific_snapshot(),
        "boundary": {
            "baseline_stabilization_authorized": True,
            "stabilization_implementation_cycles_remaining": 1,
            "fresh_clone_validation_cycles_remaining": 1,
            "scientific_target_displaced": False,
            "scientific_target_rotated": False,
            "scientific_execution_authorized": False,
            "phase_b_authorized": False,
            "phase_c_authorized": False,
            "registry_sharding_migration_authorized": False,
            "v2_enrollment_authorized": False,
            "v2_regeneration_authorized": False,
            "first_unit_selector_execution_authorized": False,
        },
    }


def _write(path: Path, value: Any) -> None:
    path.write_bytes(_canonical(value))


def prepare(*, write: bool) -> None:
    preservation = build_preservation()
    selector = build_selector(preservation)
    packet = build_packet(selector)
    expected = {
        PRESERVATION_PATH: preservation,
        SELECTOR_PATH: selector,
        PACKET_PATH: packet,
    }
    for path, value in expected.items():
        content = _canonical(value)
        if write:
            path.write_bytes(content)
        elif not path.exists() or path.read_bytes() != content:
            raise StabilizationAuthorizationError(f"stale artifact: {path.name}")


def review(*, write: bool) -> None:
    result = build_review()
    content = _canonical(result)
    if write:
        REVIEW_PATH.write_bytes(content)
    elif not REVIEW_PATH.exists() or REVIEW_PATH.read_bytes() != content:
        raise StabilizationAuthorizationError("stabilization review is stale")
    if not result["accepted"]:
        raise StabilizationAuthorizationError("stabilization review did not accept")


def activate() -> None:
    prepare(write=False)
    review(write=False)
    packet = _read(PACKET_PATH)
    _write(MAINTENANCE_PATH, build_maintenance_authority(packet))


def check_activated() -> None:
    prepare(write=False)
    review(write=False)
    packet = _read(PACKET_PATH)
    expected = _canonical(build_maintenance_authority(packet))
    if MAINTENANCE_PATH.read_bytes() != expected:
        raise StabilizationAuthorizationError("stabilization authority is not active")


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--write-review", action="store_true")
    mode.add_argument("--activate", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.write:
        prepare(write=True)
    elif args.write_review:
        prepare(write=False)
        review(write=True)
    elif args.activate:
        activate()
    else:
        check_activated()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess
import sys
from typing import Any, Iterator

from jsonschema.validators import validator_for

from formal.python.tools import (
    loop_control_registry_sharding_read_only_prototype_execution_packet_independent_review
    as review,
)


PREPARATION_COMMIT = "0261ec32029535e70f19587ed2f2755bb0bb9f22"
PACKET_SHA256 = "661655d3a6ba8f77b75652f45e1709275f0c0ae372b87a18a868316502a76168"
CONTRACT_SHA256 = "272279d414591b25b3a519d22d92659f4a662ce1c9cbd5fadf3067f1eaa8f0bb"
EXPECTED_STATUS = (
    "ACCEPTED_PREPARATION_PACKET_AND_AUTHORIZED_BOUNDED_STAGE_A_"
    "READ_ONLY_PROTOTYPE_EXECUTION_ONLY"
)


def _artifact() -> dict[str, Any]:
    return json.loads(review.OUTPUT_PATH.read_text(encoding="utf-8"))


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _git(*args: str, check: bool = True) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["git", *args],
        cwd=review.REPO_ROOT,
        capture_output=True,
        text=True,
        check=check,
    )


def _scalars(value: Any) -> Iterator[Any]:
    if isinstance(value, dict):
        for child in value.values():
            yield from _scalars(child)
    elif isinstance(value, list):
        for child in value:
            yield from _scalars(child)
    else:
        yield value


def _reviewed_json(relative: str) -> dict[str, Any]:
    return json.loads(review._git_blob(relative))


def test_review_is_deterministic_from_exact_preparation_commit() -> None:
    assert review.SOURCE_COMMIT == PREPARATION_COMMIT
    raw = review.canonical_json_bytes(review.build_review())
    assert review.OUTPUT_PATH.read_bytes() == raw
    before = review.OUTPUT_PATH.read_bytes()
    completed = subprocess.run(
        [
            sys.executable,
            "-m",
            "formal.python.tools."
            "loop_control_registry_sharding_read_only_prototype_execution_packet_independent_review",
            "--check",
        ],
        cwd=review.REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert completed.returncode == 0, completed.stderr
    assert review.OUTPUT_PATH.read_bytes() == before
    artifact = _artifact()
    assert artifact["reviewed_commit"] == PREPARATION_COMMIT
    assert artifact["status"] == EXPECTED_STATUS
    assert artifact["schema_id"] == (
        "LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_"
        "PACKET_INDEPENDENT_REVIEW_20260711_v0"
    )


def test_review_binds_every_committed_input_by_sha_and_git_object() -> None:
    assert review.EXPECTED_SHA256[review.PACKET_REL] == PACKET_SHA256
    assert review.EXPECTED_SHA256[review.CONTRACT_REL] == CONTRACT_SHA256
    assert set(review.EXPECTED_SHA256) == set(review.EXPECTED_GIT_BLOBS)
    for relative, expected_sha in review.EXPECTED_SHA256.items():
        raw = review._git_blob(relative)
        assert _sha256(raw) == expected_sha
        assert review._git_blob_oid(relative) == review.EXPECTED_GIT_BLOBS[relative]

    reviewed_values = set(_scalars(_artifact()["reviewed_inputs"]))
    assert PACKET_SHA256 in reviewed_values
    assert CONTRACT_SHA256 in reviewed_values


def test_independent_reproduction_confirms_closed_runtime_contract() -> None:
    packet = _reviewed_json(review.PACKET_REL)
    contract = _reviewed_json(review.CONTRACT_REL)
    assert packet["contract_bundle"]["sha256"] == CONTRACT_SHA256
    assert packet["counts"] == {
        "future_stage_b_total_control_count": 78,
        "historical_absence_gate_count": 9,
        "primary_control_count": 52,
        "readiness_control_count": 8,
        "runtime_schema_count": 10,
        "stage_a_distinct_control_count": 58,
        "stage_a_runtime_contract_control_count": 18,
        "stage_a_total_control_count": 76,
        "stage_b_distinct_control_count": 60,
    }
    schemas = contract["runtime_schemas"]
    assert contract["runtime_schema_count"] == len(schemas) == 10
    assert len({schema["$id"] for schema in schemas.values()}) == 10
    for schema in schemas.values():
        validator_for(schema).check_schema(schema)

    runtime = contract["runtime_validator_contract"]
    assert runtime["negative_control_count"] == len(runtime["negative_controls"]) == 18
    assert runtime["entrypoint_count"] == len(runtime["entrypoints"]) == 11
    assert runtime["execution_complete"] is False
    assert [row["control_id"] for row in runtime["negative_controls"]] == [
        f"RUNTIME-NC-{index:03d}" for index in range(1, 19)
    ]
    assert all(row["fresh_baseline"] for row in runtime["negative_controls"])
    assert all(
        row["subsequent_controls_unmodified"]
        for row in runtime["negative_controls"]
    )

    reproduced = _artifact()["schema_and_runtime_contract_review"]
    assert reproduced == {
        "all_schemas_closed": True,
        "authorized_stage_a_total_control_count": 76,
        "deferred_stage_b_inherited_control_count": 60,
        "deferred_stage_b_total_control_count": 78,
        "excluded_cutover_control_ids": [
            "REGISTRY-V1-NC-044",
            "REGISTRY-READINESS-V1-RC-001",
        ],
        "inherited_stage_a_control_count": 58,
        "runtime_negative_control_count": 18,
        "runtime_schema_count": 10,
        "runtime_validator_entrypoint_count": 11,
        "stage_a_runtime_control_count": 18,
        "stage_b_requires_successor": True,
    }


def test_review_authorizes_only_bounded_stage_a_and_exact_76_controls() -> None:
    artifact = _artifact()
    authorization = artifact["authorization"]
    assert authorization["bounded_read_only_prototype_implementation_authorized"] is True
    assert authorization[
        "bounded_stage_a_read_only_prototype_execution_authorized"
    ] is True
    assert authorization["stage_a_76_control_harness_execution_authorized"] is True
    assert authorization["execution_target"] == review.EXECUTION_TARGET
    assert review.EXECUTION_TARGET == (
        "execute_loop_control_registry_sharding_read_only_prototype_v0"
    )

    packet = _reviewed_json(review.PACKET_REL)
    contract = _reviewed_json(review.CONTRACT_REL)
    stage_a = contract["lifecycle"][
        "stage_a_precutover_execution_after_separate_authorization"
    ]
    assert stage_a["distinct_control_count"] == 58
    assert stage_a["runtime_contract_control_count"] == 18
    assert stage_a["total_stage_a_control_count"] == 76
    assert len(stage_a["control_result_order"]) == 58
    assert packet["counts"]["stage_a_total_control_count"] == 76

    focused = artifact["focused_validation"]
    assert focused["discovered_test_count"] == 23
    assert focused["passed_test_count"] == 23
    assert focused["failed_test_count"] == 0
    assert focused["result"] == "PASS"
    assert focused["test_path"] == (
        "formal/python/tests/"
        "test_loop_control_registry_sharding_read_only_prototype_execution_packet.py"
    )


def test_stage_b_and_every_broader_authority_remain_deferred() -> None:
    authorization = _artifact()["authorization"]
    false_fields = [
        "stage_b_full_harness_authorized",
        "registry_migration_execution_authorized",
        "registry_cutover_authorized",
        "consumer_migration_authorized",
        "new_api_writes_authorized",
        "legacy_monolith_modification_or_retirement_authorized",
        "authority_cutover_authorized",
        "maintenance_target_rotation_authorized",
        "scientific_target_rotation_authorized",
        "unit_ledger_execution_authorized",
        "scientific_claim_or_blocker_movement_authorized",
    ]
    for field in false_fields:
        assert authorization[field] is False, field

    contract = _reviewed_json(review.CONTRACT_REL)
    stage_b = contract["lifecycle"]["stage_b_full_harness_deferred_obligation"]
    assert stage_b["authorized_or_executable_under_this_contract"] is False
    assert stage_b["counts_are_frozen_obligations_not_execution_evidence"] is True
    assert stage_b["distinct_control_count"] == 60
    assert stage_b["runtime_contract_control_count"] == 18
    assert stage_b["future_total_control_count"] == 78
    assert stage_b["effective_profile_invocation_count"] == 199
    residual_text = json.dumps(_artifact()["residual_obligations"], sort_keys=True)
    assert "STAGE_B" in residual_text.upper()
    assert "INDEPENDENT" in residual_text.upper()


def test_review_preserves_current_targets_without_selection_or_rotation() -> None:
    authorization = _artifact()["authorization"]
    assert authorization["scientific_target"] == review.SCIENTIFIC_TARGET
    assert authorization["maintenance_target"] == review.MAINTENANCE_TARGET
    assert review.SCIENTIFIC_TARGET == "execute_pillar_seam_unit_mapping_ledger_v0"
    assert review.MAINTENANCE_TARGET == (
        "prepare_loop_control_registry_sharding_and_current_projection_packet_v0"
    )
    assert authorization["maintenance_target_rotation_authorized"] is False
    assert authorization["scientific_target_rotation_authorized"] is False
    assert authorization["authority_cutover_authorized"] is False

    packet = _reviewed_json(review.PACKET_REL)
    assert packet["authorization"]["packet_target_is_current_maintenance_authority"] is False
    assert packet["execution_target_recommended_not_selected"] == review.EXECUTION_TARGET
    assert all(value is False for value in packet["boundary"].values())


def test_forbidden_paths_were_absent_at_reviewed_preparation_boundary() -> None:
    assert len(review.FORBIDDEN_PATHS) == 7
    for relative in review.FORBIDDEN_PATHS:
        result = _git(
            "cat-file",
            "-e",
            f"{PREPARATION_COMMIT}:{relative}",
            check=False,
        )
        assert result.returncode != 0, relative

    transition = _artifact()["historical_transition_review"]
    values = set(_scalars(transition))
    assert 9 in values
    assert 10 in values
    assert all(relative in json.dumps(transition) for relative in review.FORBIDDEN_PATHS)


def test_protected_state_and_external_roots_are_independently_unchanged() -> None:
    contract = _reviewed_json(review.CONTRACT_REL)
    protected = {
        "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json": (
            "eda451133e8bbfe1ba0e815b29735f874e8b33e61d7fc5085999c4ba38df0543"
        ),
        "formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_v0.json": (
            "ada2c9c9c4622c64f0ab0fb7033b8e39b790d55a29ee492dd03fea06afc3695b"
        ),
        "formal/docs/release/CURRENT_AUTHORITATIVE_SURFACES_v0.md": (
            "cca3e7cb1855919bae8e5f189f04eb485bf2e2529aaff5e22c2a06e48b316248"
        ),
        "formal/docs/release/SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0.json": (
            "6a4273b3f95bca657bbc9dcdbab82d118a8223ab6de55a213374421b560838a1"
        ),
    }
    for relative, expected_sha in protected.items():
        assert contract["external_bindings"][relative]["sha256"] == expected_sha
        raw = review._git_blob(relative)
        assert _sha256(raw) == expected_sha

    protected_values = set(_scalars(_artifact()["protected_state_review"]))
    root_values = set(_scalars(_artifact()["external_root_review"]))
    for expected_sha in protected.values():
        assert expected_sha in protected_values or expected_sha in root_values
    assert PACKET_SHA256 in root_values
    assert CONTRACT_SHA256 in root_values


def test_review_findings_accept_only_preparation_and_stage_a_scope() -> None:
    artifact = _artifact()
    findings = artifact["independent_findings"]
    assert isinstance(findings, list) and findings
    finding_text = json.dumps(findings, sort_keys=True).upper()
    assert "STAGE_A" in finding_text
    assert "76" in finding_text
    assert "STAGE_B" in finding_text
    assert "MIGRATION" in finding_text
    assert "CUTOVER" in finding_text
    assert "PREPARATION" in finding_text


def test_review_lean_certificate_binds_authorization_and_nonauthorization() -> None:
    lean_path = review.REPO_ROOT / (
        "formal/toe_formal/ToeFormal/Release/"
        "LoopControlRegistryShardingReadOnlyPrototypeExecutionPacketIndependentReview.lean"
    )
    lean = lean_path.read_text(encoding="utf-8")
    assert _sha256(review.OUTPUT_PATH.read_bytes()) in lean
    assert PACKET_SHA256 in lean
    assert CONTRACT_SHA256 in lean
    assert PREPARATION_COMMIT in lean
    assert review.EXECUTION_TARGET in lean
    assert review.SCIENTIFIC_TARGET in lean
    assert review.MAINTENANCE_TARGET in lean
    assert "boundedStageAImplementationAuthorized : Bool := true" in lean
    assert "boundedStageAExecutionAuthorized : Bool := true" in lean
    assert "stageAControlCount : Nat := 76" in lean
    assert "stageBFullHarnessAuthorized : Bool := false" in lean
    assert "registryMigrationExecutionAuthorized : Bool := false" in lean
    assert "registryCutoverAuthorized : Bool := false" in lean
    assert "maintenanceTargetRotated : Bool := false" in lean
    assert "scientificTargetRotated : Bool := false" in lean


def test_review_integration_enrolls_one_integrity_gate_and_one_lean_module() -> None:
    relative_test = (
        "formal/python/tests/"
        "test_loop_control_registry_sharding_read_only_prototype_execution_packet_"
        "independent_review.py"
    )
    manifest = json.loads(
        (
            review.REPO_ROOT
            / "formal/docs/release/GOVERNANCE_TEST_MANIFEST_v1.json"
        ).read_text(encoding="utf-8")
    )
    assert manifest["test_tiers"][relative_test] == "TIER_INTEGRITY"
    integrity = manifest["groups"]["integrity_gates"]
    assert relative_test in integrity["tests"]
    assert integrity["expected_count"] == len(integrity["tests"]) == 67
    assert integrity["expected_sha256"] == _sha256(
        "\n".join(integrity["tests"]).encode("utf-8")
    )

    expected_paths = [
        review.OUTPUT_PATH,
        Path(review.__file__),
        review.REPO_ROOT / relative_test,
        review.REPO_ROOT
        / "formal/toe_formal/ToeFormal/Release/"
        "LoopControlRegistryShardingReadOnlyPrototypeExecutionPacketIndependentReview.lean",
    ]
    attributes = (review.REPO_ROOT / ".gitattributes").read_text(encoding="utf-8")
    for path in expected_paths:
        relative = path.resolve().relative_to(review.REPO_ROOT).as_posix()
        assert f"{relative} text eol=lf" in attributes

    command = (
        "formal.python.tools."
        "loop_control_registry_sharding_read_only_prototype_execution_packet_"
        "independent_review --check"
    )
    assert command in (review.REPO_ROOT / "README.md").read_text(encoding="utf-8")
    assert command in (review.REPO_ROOT / "DEVELOPMENT.md").read_text(encoding="utf-8")

    aggregate = (
        review.REPO_ROOT / "formal/toe_formal/ToeFormalAll.lean"
    ).read_text(encoding="utf-8")
    assert (
        "import ToeFormal.Release."
        "LoopControlRegistryShardingReadOnlyPrototypeExecutionPacketIndependentReview"
    ) in aggregate
    assert "def trackedModuleCount : Nat := 1064" in aggregate

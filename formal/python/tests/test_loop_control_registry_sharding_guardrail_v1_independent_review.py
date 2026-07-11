from __future__ import annotations

import hashlib
import json

from formal.python.tools import (
    loop_control_registry_sharding_guardrail_v1_independent_review as review,
)


EXPECTED_SHA256 = "4b99d6d3801a8bbd2f918311116dfdfce8ef595f7c0e1b629bc3595820612dca"


def _artifact() -> dict:
    return json.loads(review.OUTPUT_PATH.read_text(encoding="utf-8"))


def test_v1_review_is_deterministic_from_immutable_preparation_commit() -> None:
    raw = review.canonical_json_bytes(review.build_review())
    assert review.OUTPUT_PATH.read_bytes() == raw
    assert hashlib.sha256(raw).hexdigest() == EXPECTED_SHA256


def test_v1_review_accepts_preparation_but_rejects_migration_readiness() -> None:
    artifact = _artifact()
    assert artifact["status"] == (
        "ACCEPTED_CORRECTIVE_V1_PREPARATION_GUARDRAIL_ONLY_"
        "MIGRATION_EXECUTION_AND_CUTOVER_NOT_READY_OR_AUTHORIZED"
    )
    accepted = artifact["accepted_scope"]
    assert accepted["corrective_v1_preparation_guardrail"] is True
    assert accepted["byte_exact_compatibility_architecture"] is True
    assert accepted["committed_external_authority_binding"] is True
    assert accepted["migration_execution_readiness"] is False
    assert accepted["runtime_consumer_coverage"] is False
    assert accepted["typed_controls_executed_against_production_validator"] is False


def test_v1_review_preserves_targets_and_authorizes_no_migration_component() -> None:
    artifact = _artifact()
    authorization = artifact["authorization"]
    assert authorization["scientific_target"] == review.SCIENTIFIC_TARGET
    assert authorization["maintenance_target"] == review.MAINTENANCE_TARGET
    assert authorization["migration_execution_authorized"] is False
    assert authorization["next_migration_execution_target_selected"] is False
    assert all(value is False for value in artifact["boundary"].values())


def test_v1_review_binds_counts_custody_consumers_and_controls() -> None:
    artifact = _artifact()
    assert artifact["packet_sha256"] == review.EXPECTED_PACKET_SHA256
    assert artifact["record_review"]["total_record_count"] == 4_691
    assert artifact["consumer_review"]["consumer_count"] == 496
    assert artifact["consumer_review"]["runtime_completeness_proved"] is False
    assert artifact["custody_review"]["byte_exact_source_size_bytes"] == 52_340_650
    assert artifact["custody_review"]["byte_exact_source_sha256"] == review.REGISTRY_SHA256
    controls = artifact["negative_control_review"]
    assert controls["control_count"] == 52
    assert controls["v0_false_acceptance_count"] == 8
    assert controls["all_v0_false_acceptances_permanently_named"] is True
    assert controls["typed_error_codes_unique"] is True


def test_v1_review_keeps_open_obligations_explicit() -> None:
    findings = _artifact()["findings"]
    assert len(findings) == 4
    assert sum(row["severity"] == "HIGH" for row in findings) == 3
    assert all(row["status"].startswith("OPEN_") for row in findings)
    summaries = " ".join(row["summary"] for row in findings)
    assert "production-validator regression harness" in summaries
    assert "concrete recursively closed schemas" in summaries
    assert "runtime shadow-trace completeness" in summaries


def test_v1_review_lean_certificate_binds_nonauthorization_ceiling() -> None:
    lean = (
        review.REPO_ROOT
        / "formal/toe_formal/ToeFormal/Release/LoopControlRegistryShardingGuardrailV1IndependentReview.lean"
    ).read_text(encoding="utf-8")
    assert EXPECTED_SHA256 in lean
    assert review.EXPECTED_PACKET_SHA256 in lean
    assert review.SCIENTIFIC_TARGET in lean
    assert "migrationExecutionReady : Bool := false" in lean
    assert "registryMigrationExecutionAuthorized : Bool := false" in lean

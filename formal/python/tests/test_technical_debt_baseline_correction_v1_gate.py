from __future__ import annotations

import hashlib
import json
import subprocess

from formal.python.tools import technical_debt_baseline_correction_v1 as correction


EXPECTED_ARTIFACT_SHA256 = (
    "a15b323953eb2e27de531dff9a094944ca398e80ddd1fe7bb04015c2889766ce"
)


def _artifact() -> dict:
    return json.loads(correction.OUTPUT_PATH.read_text(encoding="utf-8"))


def _git_blob(commit: str, path: str) -> bytes:
    return subprocess.run(
        ["git", "show", f"{commit}:{path}"],
        cwd=correction.REPO_ROOT,
        capture_output=True,
        check=True,
    ).stdout


def test_v1_baseline_correction_is_deterministic_and_current() -> None:
    expected = correction.canonical_json_bytes(correction.build_baseline())
    assert correction.OUTPUT_PATH.read_bytes() == expected
    assert hashlib.sha256(expected).hexdigest() == EXPECTED_ARTIFACT_SHA256


def test_v1_preserves_v0_and_corrects_only_reviewed_evidence_defects() -> None:
    artifact = _artifact()
    contract = artifact["correction_contract"]
    assert artifact["schema_id"] == "TECHNICAL_DEBT_BASELINE_20260711_v1"
    assert artifact["source_commit"] == correction.SOURCE_COMMIT
    assert contract["superseded_v0_sha256"] == correction.EXPECTED_V0_SHA256
    assert hashlib.sha256(
        _git_blob(correction.V0_COMMIT, correction.V0_REL)
    ).hexdigest() == correction.EXPECTED_V0_SHA256
    assert contract["corrected_review_findings"] == [
        "REGISTRY-REVIEW-009",
        "REGISTRY-REVIEW-011",
    ]
    assert contract["generator_bindings"]["reviewed_v0_generator_commit"] == (
        correction.V0_COMMIT
    )
    assert contract["generator_bindings"]["reviewed_v0_generator_sha256"] == (
        hashlib.sha256(_git_blob(correction.V0_COMMIT, correction.V0_TOOL_REL)).hexdigest()
    )
    assert contract["statement_line_hash_corrections"] == {
        "axiom_rows_empty_after_correction": 0,
        "axiom_rows_previously_empty": 50,
        "opaque_rows_empty_after_correction": 0,
        "opaque_rows_previously_empty": 20,
    }


def test_v1_counts_and_stable_identity_sets_equal_v0() -> None:
    v1 = _artifact()["technical_debt_baselines"]
    v0 = json.loads(_git_blob(correction.V0_COMMIT, correction.V0_REL))["technical_debt_baselines"]
    pairs = [
        ("quarantined_assertions", "assertion_count"),
        ("quarantined_assertions", "stable_identity_set_sha256"),
        ("lean_axioms", "axiom_count"),
        ("lean_axioms", "blocking_full_pillar_target_count"),
        ("lean_axioms", "stable_identity_set_sha256"),
        ("lean_opaque_definitions", "candidate_count"),
        ("lean_opaque_definitions", "stable_identity_set_sha256"),
        ("tooling_snapshots", "tracked_snapshot_path_count"),
        ("tooling_snapshots", "duplicate_group_count"),
        ("tooling_snapshots", "redundant_worktree_bytes"),
    ]
    for section, key in pairs:
        assert v1[section][key] == v0[section][key]


def test_v1_source_hashes_bind_review_commit_blobs() -> None:
    artifact = _artifact()
    bindings = artifact["correction_contract"]["source_bindings"]
    for binding in bindings.values():
        assert binding["reviewed_commit"] == correction.SOURCE_COMMIT
        assert binding["reviewed_blob_sha256"] == hashlib.sha256(
            _git_blob(correction.SOURCE_COMMIT, binding["path"])
        ).hexdigest()
    assert bindings["retirements_source_ledger"]["reviewed_blob_sha256"] == (
        "78c534f097205dcb117ad34161ecf4357a6a434a5ed02dd8bdaacb782ba58691"
    )
    assert artifact["technical_debt_baselines"]["quarantined_assertions"][
        "source_ledger_sha256"
    ] == bindings["retirements_source_ledger"]["reviewed_blob_sha256"]
    assert artifact["verification_contract"][
        "clean_checkout_reproducible_source_binding"
    ] is True


def test_v1_statement_line_hashes_bind_actual_declaration_lines() -> None:
    debt = _artifact()["technical_debt_baselines"]
    rows = debt["lean_axioms"]["axioms"] + debt["lean_opaque_definitions"]["candidates"]
    empty_sha = hashlib.sha256(b"").hexdigest()
    for row in rows:
        lines = (correction.REPO_ROOT / row["file"]).read_text(encoding="utf-8").splitlines()
        statement = lines[row["line"] - 1].strip()
        assert statement
        assert row["declaration"] in statement
        assert row["statement_line_sha256"] == hashlib.sha256(
            statement.encode("utf-8")
        ).hexdigest()
        assert row["statement_line_sha256"] != empty_sha


def test_v1_preserves_authority_and_authorizes_no_maintenance_execution() -> None:
    artifact = _artifact()
    contract = artifact["correction_contract"]
    assert contract["retained_scientific_target"] == correction.legacy.SCIENTIFIC_TARGET
    assert contract["retained_maintenance_target"] == correction.legacy.MAINTENANCE_TARGET
    assert artifact["maintenance_program"]["scientific_target_displacement"] is False
    assert all(value is False for value in artifact["boundary"].values())
    assert artifact["status"] == (
        "VERSIONED_EVIDENCE_CORRECTION_COUNTS_AND_AUTHORITY_UNCHANGED_"
        "NO_REMEDIATION_OR_MIGRATION_EXECUTION"
    )


def test_lean_certificate_binds_v1_hash_and_nonauthorization() -> None:
    path = (
        correction.REPO_ROOT
        / "formal/toe_formal/ToeFormal/Release/TechnicalDebtBaselineCorrectionV1.lean"
    )
    text = path.read_text(encoding="utf-8")
    assert EXPECTED_ARTIFACT_SHA256 in text
    assert correction.SOURCE_COMMIT in text
    assert correction.EXPECTED_V0_SHA256 in text
    assert correction.legacy.SCIENTIFIC_TARGET in text
    assert correction.legacy.MAINTENANCE_TARGET in text
    assert "registryMigrationExecutionAuthorized : Bool := false" in text
    assert "scientificTargetRotated : Bool := false" in text

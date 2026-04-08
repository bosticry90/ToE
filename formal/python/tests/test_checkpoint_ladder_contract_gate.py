from __future__ import annotations

from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
LADDER_PATH = REPO_ROOT / "checkpoint_ladder.ps1"
MANIFEST_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "CHECKPOINT_LADDER_GENERATED_OUTPUTS_MANIFEST_v0.json"
)
PROGRESS_PATH = REPO_ROOT / "formal" / "output" / "reports" / "checkpoint_ladder_progress_v0.json"
SUMMARY_PATH = REPO_ROOT / "formal" / "output" / "reports" / "checkpoint_ladder_acceptance_summary_v0.json"


def _read_ladder() -> str:
    assert LADDER_PATH.exists(), "Missing checkpoint ladder runner script."
    return LADDER_PATH.read_text(encoding="utf-8")


def _read_manifest() -> str:
    assert MANIFEST_PATH.exists(), "Missing checkpoint-ladder generated-output manifest."
    return MANIFEST_PATH.read_text(encoding="utf-8")


def _index_or_fail(content: str, needle: str) -> int:
    idx = content.find(needle)
    assert idx >= 0, f"Expected ladder contract text not found: {needle}"
    return idx


def test_checkpoint_ladder_contract_gate_required_steps_in_order() -> None:
    content = _read_ladder()

    s1 = _index_or_fail(content, "Invoke-Step -StepKey 'render_apply_verify' -Name '1) renderer apply/verify'")
    s2 = _index_or_fail(content, "Invoke-Step -StepKey 'state_core_integrity' -Name '2) state-core integrity gate'")
    s3 = _index_or_fail(content, "Invoke-Step -StepKey 'compression_yield' -Name '3) compression/yield gate'")
    s4 = _index_or_fail(content, "Invoke-Step -StepKey 'full_governance_suite' -Name '4) full governance suite'")

    assert s1 < s2 < s3 < s4, "Checkpoint ladder step order contract violated."


def test_checkpoint_ladder_contract_gate_restores_generated_outputs() -> None:
    content = _read_ladder()
    manifest = _read_manifest()

    _index_or_fail(content, "$generatedOutputsManifestPath = 'formal/docs/release/CHECKPOINT_LADDER_GENERATED_OUTPUTS_MANIFEST_v0.json'")
    _index_or_fail(content, "$generatedOutputs = @(Get-GeneratedOutputs -ManifestPath $generatedOutputsManifestPath)")
    _index_or_fail(content, "Get-Content $ManifestPath -Raw | ConvertFrom-Json")
    _index_or_fail(content, "CHECKPOINT_LADDER_GENERATED_OUTPUTS_MANIFEST_v0")

    _index_or_fail(manifest, '"path": "formal/output/state_core_compression_yield_report_v0.json"')
    _index_or_fail(manifest, '"path": "formal/output/state_core_generated/state_core_tracker_snippet_v0.md"')
    _index_or_fail(manifest, '"path": "formal/output/state_core_generated/state_core_ws10_snippet_v0.md"')
    _index_or_fail(manifest, '"restore": true')

    finally_idx = _index_or_fail(content, "finally {")
    restore_idx = _index_or_fail(content, "git restore -- $existing")
    assert finally_idx < restore_idx, (
        "Generated output restore must occur in finally block to guarantee post-run hygiene."
    )


def test_checkpoint_ladder_contract_gate_exits_nonzero_on_failure() -> None:
    content = _read_ladder()

    catch_idx = _index_or_fail(content, "catch {")
    flag_idx = _index_or_fail(content, "$failed = $true")
    fail_exit_idx = _index_or_fail(content, "if ($failed) {")
    exit_one_idx = _index_or_fail(content, "exit 1")

    assert catch_idx < flag_idx < fail_exit_idx < exit_one_idx, (
        "Failure contract violated: runner must set failed flag and exit non-zero on failure."
    )


def test_checkpoint_ladder_contract_gate_requires_no_new_drift_after_restore() -> None:
    content = _read_ladder()

    pre_snapshot_idx = _index_or_fail(content, "$preRunStatus = @(Get-GitStatusSnapshot)")
    post_snapshot_idx = _index_or_fail(content, "$postRunStatus = @(Get-GitStatusSnapshot)")
    compare_idx = _index_or_fail(content, "Compare-Object -ReferenceObject $preRunStatus -DifferenceObject $postRunStatus")
    side_indicator_idx = _index_or_fail(content, "Where-Object { $_.SideIndicator -eq '=>' }")
    dirty_guard_idx = _index_or_fail(content, "if ($newDrift.Count -gt 0) {")
    hygiene_msg_idx = _index_or_fail(
        content,
        "Checkpoint ladder post-run hygiene failed: new working-tree drift detected relative to pre-run baseline.",
    )
    fail_flag_idx = content.rfind("$failed = $true")

    assert pre_snapshot_idx < post_snapshot_idx < compare_idx < side_indicator_idx < dirty_guard_idx < hygiene_msg_idx < fail_flag_idx, (
        "Hygiene guard violated: checkpoint ladder must fail only on new drift relative to pre-run baseline."
    )


def test_checkpoint_ladder_contract_gate_resume_and_summary_contracts_present() -> None:
    content = _read_ladder()

    _index_or_fail(content, "param(")
    _index_or_fail(content, "[switch]$Resume")
    _index_or_fail(content, "$progressPath = 'formal/output/reports/checkpoint_ladder_progress_v0.json'")
    _index_or_fail(content, "$summaryPath = 'formal/output/reports/checkpoint_ladder_acceptance_summary_v0.json'")
    _index_or_fail(content, "schema_id = 'CHECKPOINT_LADDER_PROGRESS_v0'")
    _index_or_fail(content, "schema_id = 'CHECKPOINT_LADDER_ACCEPTANCE_SUMMARY_v0'")
    _index_or_fail(content, "(resume skip)")
    _index_or_fail(content, "Write-AcceptanceSummary")


def test_checkpoint_ladder_contract_gate_summary_and_progress_paths_are_release_stable() -> None:
    # Contract path guards help preserve downstream automation expectations.
    assert str(PROGRESS_PATH).endswith("formal\\output\\reports\\checkpoint_ladder_progress_v0.json")
    assert str(SUMMARY_PATH).endswith("formal\\output\\reports\\checkpoint_ladder_acceptance_summary_v0.json")

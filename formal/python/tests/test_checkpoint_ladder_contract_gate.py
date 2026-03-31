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


def _read_ladder() -> str:
    assert LADDER_PATH.exists(), "Missing checkpoint ladder runner script."
    return LADDER_PATH.read_text(encoding="utf-8")


def _index_or_fail(content: str, needle: str) -> int:
    idx = content.find(needle)
    assert idx >= 0, f"Expected ladder contract text not found: {needle}"
    return idx


def test_checkpoint_ladder_contract_gate_required_steps_in_order() -> None:
    content = _read_ladder()

    s1 = _index_or_fail(content, "Invoke-Step -Name '1) renderer apply/verify'")
    s2 = _index_or_fail(content, "Invoke-Step -Name '2) state-core integrity gate'")
    s3 = _index_or_fail(content, "Invoke-Step -Name '3) compression/yield gate'")
    s4 = _index_or_fail(content, "Invoke-Step -Name '4) full governance suite'")

    assert s1 < s2 < s3 < s4, "Checkpoint ladder step order contract violated."


def test_checkpoint_ladder_contract_gate_restores_generated_outputs() -> None:
    content = _read_ladder()

    _index_or_fail(content, "formal/output/state_core_compression_yield_report_v0.json")
    _index_or_fail(content, "formal/output/state_core_generated/state_core_tracker_snippet_v0.md")
    _index_or_fail(content, "formal/output/state_core_generated/state_core_ws10_snippet_v0.md")

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

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
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_cosmo_state_rollup_checkpoint_tokens_are_pinned() -> None:
    text = _read(STATE_PATH)

    required_tokens = [
        "COSMO rollup checkpoint (2026-03-01):",
        "formal/docs/paper/TOE_COSMO_BACKGROUND_PILLAR_SUMMARY_v0.md",
        "formal/markdown/locks/policy/COSMO_BACKGROUND_PILLAR_PACKAGE_v0.md",
        "COSMO_BACKGROUND_PILLAR_PACKAGE_STATUS_v0: FROZEN_CONTENTS_PINNED",
        "COSMO_BACKGROUND_PILLAR_PACKAGE_PROGRESS_v0: REQUIRED_CONTENTS_PINNED",
        "COSMO_BACKGROUND_REOPEN_POLICY_v0: FROZEN_WATCH_REOPEN_ON_REGRESSION",
        "REOPEN_TRIGGER_COSMO_SURFACE_DRIFT_v0",
        "REOPEN_TRIGGER_COSMO_SCOPE_BOUNDARY_REGRESSION_v0",
        "REOPEN_TRIGGER_COSMO_PACKAGE_CONTENT_MISMATCH_v0",
        "formal/python/tests/test_cosmo_background_pillar_package_rollup_gate.py",
        "formal/python/tests/test_cosmo_state_rollup_checkpoint_gate.py",
        "NEXT_PILLAR_FOCUS_v0: PILLAR-COSMO",
        "NEXT_PILLAR_PRIMARY_LANE_v0: TARGET-COSMO-BG-PLAN",
    ]

    missing = [token for token in required_tokens if token not in text]
    assert not missing, "State COSMO rollup checkpoint token drift: " + ", ".join(missing)

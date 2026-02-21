from __future__ import annotations

from pathlib import Path

from formal.python.tests._lane_separation_policy_lib import assert_lane_separation_policy


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
EM_TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_EM_U1_MAXWELL_OBJECT_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"

PILLAR_ADJUDICATION_TOKEN = "PILLAR_EM_FULL_DERIVATION_DISCHARGE_ADJUDICATION"
MICRO_ADJUDICATION_TOKEN = "EM_U1_MAXWELL_ADJUDICATION"
OVERRIDE_TOKEN = "EM_LANE_SEPARATION_MICRO_DISCHARGED_WITHOUT_PILLAR_OVERRIDE_v0"


def test_em_lane_separation_policy_invariant() -> None:
    target_text = EM_TARGET_PATH.read_text(encoding="utf-8")
    state_text = STATE_PATH.read_text(encoding="utf-8")
    assert_lane_separation_policy(
        target_text=target_text,
        state_text=state_text,
        pillar_adjudication_token=PILLAR_ADJUDICATION_TOKEN,
        micro_adjudication_token=MICRO_ADJUDICATION_TOKEN,
        override_token=OVERRIDE_TOKEN,
        override_allow_value="ALLOW",
    )

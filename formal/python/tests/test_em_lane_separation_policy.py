from __future__ import annotations

import re
from pathlib import Path


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
OVERRIDE_ALLOW_VALUE = "ALLOW"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _extract_token_value(token: str, text: str) -> str:
    m = re.search(rf"{re.escape(token)}:\s*([A-Za-z0-9_\-,./]+)", text)
    assert m is not None, f"Missing token: {token}"
    return m.group(1)


def _extract_optional_token_value(token: str, text: str) -> str | None:
    m = re.search(rf"{re.escape(token)}:\s*([A-Za-z0-9_\-,./]+)", text)
    return None if m is None else m.group(1)


def _assert_supported_adjudication(token: str, value: str) -> None:
    assert (
        value == "NOT_YET_DISCHARGED" or value.startswith("DISCHARGED_")
    ), f"{token} must be NOT_YET_DISCHARGED or DISCHARGED_* (found `{value}`)."


def test_em_lane_separation_policy_invariant() -> None:
    target_text = _read(EM_TARGET_PATH)
    state_text = _read(STATE_PATH)

    pillar_target = _extract_token_value(PILLAR_ADJUDICATION_TOKEN, target_text)
    pillar_state = _extract_token_value(PILLAR_ADJUDICATION_TOKEN, state_text)
    micro_target = _extract_token_value(MICRO_ADJUDICATION_TOKEN, target_text)
    micro_state = _extract_token_value(MICRO_ADJUDICATION_TOKEN, state_text)

    assert pillar_target == pillar_state, (
        "EM pillar adjudication token must stay synchronized between target doc and state checkpoint."
    )
    assert micro_target == micro_state, (
        "EM micro-lane adjudication token must stay synchronized between target doc and state checkpoint."
    )

    _assert_supported_adjudication(PILLAR_ADJUDICATION_TOKEN, pillar_target)
    _assert_supported_adjudication(MICRO_ADJUDICATION_TOKEN, micro_target)

    override_target = _extract_optional_token_value(OVERRIDE_TOKEN, target_text)
    override_state = _extract_optional_token_value(OVERRIDE_TOKEN, state_text)
    override_values = {value for value in [override_target, override_state] if value is not None}
    assert len(override_values) <= 1, (
        f"{OVERRIDE_TOKEN} must be synchronized if declared across EM target/state surfaces."
    )
    if override_values:
        override_value = next(iter(override_values))
        assert override_value == OVERRIDE_ALLOW_VALUE, (
            f"{OVERRIDE_TOKEN} must use `{OVERRIDE_ALLOW_VALUE}` when present."
        )
        override_enabled = True
    else:
        override_enabled = False

    pillar_discharged = pillar_target.startswith("DISCHARGED_")
    micro_discharged = micro_target.startswith("DISCHARGED_")

    # Allowed divergence: pillar lane may be discharged while micro lane remains pending.
    if pillar_discharged and micro_target == "NOT_YET_DISCHARGED":
        assert True

    # Forbidden inverse divergence unless explicit override is pinned.
    assert not (micro_discharged and not pillar_discharged and not override_enabled), (
        "EM micro-lane cannot be DISCHARGED_* while pillar lane is not DISCHARGED_* "
        f"without explicit override token `{OVERRIDE_TOKEN}: {OVERRIDE_ALLOW_VALUE}`."
    )

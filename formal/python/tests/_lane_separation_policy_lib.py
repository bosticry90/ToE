from __future__ import annotations

import re


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


def assert_lane_separation_policy(
    *,
    target_text: str,
    state_text: str,
    pillar_adjudication_token: str,
    micro_adjudication_token: str,
    override_token: str | None = None,
    override_allow_value: str = "ALLOW",
) -> None:
    pillar_target = _extract_token_value(pillar_adjudication_token, target_text)
    pillar_state = _extract_token_value(pillar_adjudication_token, state_text)
    micro_target = _extract_token_value(micro_adjudication_token, target_text)
    micro_state = _extract_token_value(micro_adjudication_token, state_text)

    assert pillar_target == pillar_state, (
        "Pillar adjudication token must stay synchronized between target doc and state checkpoint."
    )
    assert micro_target == micro_state, (
        "Micro-lane adjudication token must stay synchronized between target doc and state checkpoint."
    )

    _assert_supported_adjudication(pillar_adjudication_token, pillar_target)
    _assert_supported_adjudication(micro_adjudication_token, micro_target)

    override_enabled = False
    if override_token is not None:
        override_target = _extract_optional_token_value(override_token, target_text)
        override_state = _extract_optional_token_value(override_token, state_text)
        override_values = {value for value in [override_target, override_state] if value is not None}
        assert len(override_values) <= 1, (
            f"{override_token} must be synchronized if declared across target/state surfaces."
        )
        if override_values:
            override_value = next(iter(override_values))
            assert override_value == override_allow_value, (
                f"{override_token} must use `{override_allow_value}` when present."
            )
            override_enabled = True

    pillar_discharged = pillar_target.startswith("DISCHARGED_")
    micro_discharged = micro_target.startswith("DISCHARGED_")

    # Allowed divergence: pillar discharged while micro pending.
    if pillar_discharged and micro_target == "NOT_YET_DISCHARGED":
        return

    # Forbidden inverse divergence unless override explicitly enabled.
    assert not (micro_discharged and not pillar_discharged and not override_enabled), (
        "Micro-lane cannot be DISCHARGED_* while pillar lane is not DISCHARGED_* "
        "without explicit override token."
    )

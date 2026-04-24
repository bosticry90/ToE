from __future__ import annotations

import json
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PHYS_MATH_THROUGHPUT_REMEDIATION_PROGRAM_v0.md"
T13_CHECKPOINT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "physics_math_throughput_phase6_t13_first_live_matrix_packet_20260407_v0.json"
)
T14_CHECKPOINT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "physics_math_throughput_phase6_t14_second_live_matrix_packet_20260407_v0.json"
)
T15_CHECKPOINT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "physics_math_throughput_phase6_t15_third_live_matrix_packet_20260407_v0.json"
)
T16_CHECKPOINT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "physics_math_throughput_phase6_t16_fourth_live_matrix_packet_20260407_v0.json"
)
T17_CHECKPOINT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "physics_math_throughput_phase6_t17_fifth_live_matrix_packet_20260407_v0.json"
)
T18_CHECKPOINT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "physics_math_throughput_phase6_t18_sixth_live_matrix_packet_20260407_v0.json"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_program_token_for_promotion_policy_gate_present() -> None:
    text = _read(PROGRAM_PATH)
    token = (
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE6_PROMOTION_POLICY_GATE_v0: "
        "formal/python/tests/test_physics_math_throughput_phase6_live_promotion_policy_gate.py"
    )
    assert token in text


def test_packet1_holds_packet2_until_two_consecutive_green_packets() -> None:
    payload = _read_json(T13_CHECKPOINT_PATH)
    promotion = payload.get("live_matrix_packet", {}).get("promotion_decision", {})

    assert promotion.get("policy") == "CONSERVATIVE_TWO_CONSECUTIVE_GREEN_LIVE_PACKETS_REQUIRED"
    assert promotion.get("required_consecutive_green_packets") == 2
    assert promotion.get("consecutive_green_packets") < 2
    assert promotion.get("packet2_authorized") is False
    assert promotion.get("scope_escalation_authorized") is False


def test_packet1_promotion_hold_decision_is_explicit() -> None:
    payload = _read_json(T13_CHECKPOINT_PATH)
    promotion = payload.get("live_matrix_packet", {}).get("promotion_decision", {})

    assert promotion.get("current_packet_id") == 1
    assert promotion.get("current_packet_result") == "GREEN_NONLIVE_BOUNDED_PACKET"
    assert promotion.get("decision") == "HOLD_REQUIRE_SECOND_GREEN_PACKET"


def test_packet2_unlocks_next_packet_after_second_consecutive_green() -> None:
    payload = _read_json(T14_CHECKPOINT_PATH)
    promotion = payload.get("live_matrix_packet", {}).get("promotion_decision", {})

    assert promotion.get("policy") == "CONSERVATIVE_TWO_CONSECUTIVE_GREEN_LIVE_PACKETS_REQUIRED"
    assert promotion.get("required_consecutive_green_packets") == 2
    assert promotion.get("consecutive_green_packets") == 2
    assert promotion.get("packet3_authorized") is True
    assert promotion.get("scope_escalation_authorized") is True
    assert promotion.get("decision") == "AUTHORIZE_NEXT_BOUNDED_PACKET"


def test_packet3_preserves_conservative_policy_and_authorizes_packet4() -> None:
    payload = _read_json(T15_CHECKPOINT_PATH)
    promotion = payload.get("live_matrix_packet", {}).get("promotion_decision", {})

    assert promotion.get("policy") == "CONSERVATIVE_TWO_CONSECUTIVE_GREEN_LIVE_PACKETS_REQUIRED"
    assert promotion.get("required_consecutive_green_packets") == 2
    assert promotion.get("consecutive_green_packets") == 3
    assert promotion.get("packet4_authorized") is True
    assert promotion.get("scope_escalation_authorized") is True
    assert promotion.get("decision") == "AUTHORIZE_NEXT_BOUNDED_PACKET"


def test_packet4_preserves_conservative_policy_and_authorizes_packet5() -> None:
    payload = _read_json(T16_CHECKPOINT_PATH)
    promotion = payload.get("live_matrix_packet", {}).get("promotion_decision", {})

    assert promotion.get("policy") == "CONSERVATIVE_TWO_CONSECUTIVE_GREEN_LIVE_PACKETS_REQUIRED"
    assert promotion.get("required_consecutive_green_packets") == 2
    assert promotion.get("consecutive_green_packets") == 4
    assert promotion.get("packet5_authorized") is True
    assert promotion.get("scope_escalation_authorized") is True
    assert promotion.get("decision") == "AUTHORIZE_NEXT_BOUNDED_PACKET"


def test_packet5_preserves_conservative_policy_and_authorizes_packet6() -> None:
    payload = _read_json(T17_CHECKPOINT_PATH)
    promotion = payload.get("live_matrix_packet", {}).get("promotion_decision", {})

    assert promotion.get("policy") == "CONSERVATIVE_TWO_CONSECUTIVE_GREEN_LIVE_PACKETS_REQUIRED"
    assert promotion.get("required_consecutive_green_packets") == 2
    assert promotion.get("consecutive_green_packets") == 5
    assert promotion.get("packet6_authorized") is True
    assert promotion.get("scope_escalation_authorized") is True
    assert promotion.get("decision") == "AUTHORIZE_NEXT_BOUNDED_PACKET"


def test_packet6_preserves_conservative_policy_and_authorizes_packet7() -> None:
    payload = _read_json(T18_CHECKPOINT_PATH)
    promotion = payload.get("live_matrix_packet", {}).get("promotion_decision", {})

    assert promotion.get("policy") == "CONSERVATIVE_TWO_CONSECUTIVE_GREEN_LIVE_PACKETS_REQUIRED"
    assert promotion.get("required_consecutive_green_packets") == 2
    assert promotion.get("consecutive_green_packets") == 6
    assert promotion.get("packet7_authorized") is True
    assert promotion.get("scope_escalation_authorized") is True
    assert promotion.get("decision") == "AUTHORIZE_NEXT_BOUNDED_PACKET"

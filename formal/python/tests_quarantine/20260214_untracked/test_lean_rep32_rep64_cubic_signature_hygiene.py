from __future__ import annotations

from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
REP32_LANE = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "ActionRep32CubicLane.lean"
)
REP64_LANE = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "ActionRep64CubicLane.lean"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing Lean module: {path}"
    return path.read_text(encoding="utf-8")


def _slice(text: str, start_token: str, end_token: str) -> str:
    start = text.find(start_token)
    assert start >= 0, f"Missing token: {start_token}"
    end = text.find(end_token, start)
    assert end >= 0, f"Missing token: {end_token}"
    return text[start:end]


def test_rep32_declared_g_signature_does_not_expose_hp_parameter() -> None:
    text = _read(REP32_LANE)
    segment = _slice(
        text,
        "theorem Rep32_cubic_lane_declared_g",
        "end",
    )
    signature = segment.split(":=", 1)[0]
    assert "(hP :" not in signature, (
        "Rep32_cubic_lane_declared_g must not expose hP as a caller-supplied parameter."
    )
    assert "have hP : P_rep32 = P_cubic_rep32_def declared_g_rep32" in segment


def test_rep64_assumptions_do_not_carry_hp_field_and_callsite_uses_new_signature() -> None:
    text = _read(REP64_LANE)
    struct_segment = _slice(
        text,
        "structure Rep64CubicLaneAssumptions",
        "theorem Rep64_cubic_lane_declared",
    )
    assert "hP :" not in struct_segment, (
        "Rep64CubicLaneAssumptions must not carry an hP field after Rep32 default-path specialization."
    )
    assert "(Rep32_cubic_lane_declared_g ε h.hε h.hAction h.hRAC).1" in text

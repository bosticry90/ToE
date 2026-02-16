from __future__ import annotations

from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
TARGET = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "ActionRep32CubicLane.lean"
)


def _read_target() -> str:
    assert TARGET.exists(), f"Missing Rep32 cubic lane module: {TARGET}"
    return TARGET.read_text(encoding="utf-8")


def test_rep32_cubic_lane_routes_el_identification_through_bridge_path() -> None:
    text = _read_target()
    assert "theorem Rep32_cubic_lane'" in text
    assert "ActionRep32ELMatchesP_of_bridge_and_finiteDifferenceRepresentsP" in text

    start = text.find("theorem Rep32_cubic_lane'")
    assert start >= 0
    end = text.find("theorem Rep32_cubic_lane_declared", start)
    assert end >= 0
    segment = text[start:end]
    assert "EL_toe_eq_P_rep32" not in segment, (
        "Rep32 cubic lane should not use the legacy EL_toe_eq_P_rep32 shortcut in its main route."
    )

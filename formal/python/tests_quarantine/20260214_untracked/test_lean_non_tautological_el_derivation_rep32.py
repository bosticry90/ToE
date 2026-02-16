from __future__ import annotations

from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
TARGET = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "ActionToFirstVariationBridgeRep32.lean"
)


def _read_target() -> str:
    assert TARGET.exists(), f"Missing Rep32 bridge module: {TARGET}"
    return TARGET.read_text(encoding="utf-8")


def _slice(text: str, start_token: str, end_token: str) -> str:
    start = text.find(start_token)
    assert start >= 0, f"Missing token: {start_token}"
    end = text.find(end_token, start)
    assert end >= 0, f"Missing token: {end_token}"
    return text[start:end]


def test_rep32_bridge_has_non_tautological_el_derivation_theorems() -> None:
    text = _read_target()
    required = [
        "theorem ActionRep32FiniteDifferenceRepresentsEL_of_bridge",
        "theorem ActionRep32ELMatchesP_of_finiteDifferenceRepresentations",
        "theorem ActionRep32ELMatchesP_of_bridge_and_finiteDifferenceRepresentsP",
        "theorem ActionRep32PairingRespectsELP_of_bridge_and_finiteDifferenceRepresentsP",
        "pairingRep32_nondegenerate'",
        "variations_surjective_const_rep32",
    ]
    for token in required:
        assert token in text, f"Missing non-tautological Rep32 derivation token: {token}"


def test_bridge_based_el_match_does_not_use_legacy_el_toe_shortcut() -> None:
    text = _read_target()
    segment = _slice(
        text,
        "theorem ActionRep32ELMatchesP_of_bridge_and_finiteDifferenceRepresentsP",
        "theorem ActionRep32PairingRespectsELP_of_bridge_and_finiteDifferenceRepresentsP",
    )
    assert "EL_toe_eq_P_rep32" not in segment, (
        "Bridge-based EL/P derivation must not rely on legacy EL_toe_eq_P_rep32 shortcut."
    )

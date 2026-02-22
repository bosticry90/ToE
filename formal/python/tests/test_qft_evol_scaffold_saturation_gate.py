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
QFT_EVOL_TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_EVOLUTION_OBJECT_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
SATURATION_GATE_PATH = "formal/python/tests/test_qft_evol_scaffold_saturation_gate.py"
MILESTONE_GATE_PATH = "formal/python/tests/test_qft_evol_semantic_hardening_milestone_gate.py"
TRANCHE_GATE_PATH = "formal/python/tests/test_qft_evol_micro_tranche_01_52_completeness_gate.py"
SATURATION_TOKEN = "QFT_EVOL_SCAFFOLD_SATURATION_v0: MICRO_01_TO_MICRO_52_TRANCHE_01_52_FROZEN"
EXPANSION_POLICY_TOKEN = (
    "QFT_EVOL_MICRO_EXPANSION_POLICY_v0: NO_NEW_MICRO_BEYOND_52_UNTIL_SEMANTIC_HARDENING_MILESTONE"
)
MILESTONE_TOKEN = (
    "QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_v0: "
    "CANONICAL_MOMENTUM_HAMILTONIAN_UNITARITY_CHAIN_PINNED"
)

FORBIDDEN_MICRO_TOKENS = [
    "TARGET-QFT-EVOL-MICRO-53-",
    "test_qft_evol_micro53_",
    "test_qft_evol_micro_tranche_01_53_completeness_gate.py",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_qft_evol_scaffold_saturation_artifacts_exist() -> None:
    assert QFT_EVOL_TARGET_PATH.exists(), "Missing QFT evolution umbrella target document."
    assert ROADMAP_PATH.exists(), "Missing PHYSICS roadmap document."
    assert STATE_PATH.exists(), "Missing state checkpoint document."


def test_qft_evol_umbrella_contains_saturation_and_expansion_policy_tokens() -> None:
    text = _read(QFT_EVOL_TARGET_PATH)
    required_tokens = [SATURATION_TOKEN, EXPANSION_POLICY_TOKEN, MILESTONE_TOKEN]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "QFT evolution umbrella target missing saturation token(s): " + ", ".join(missing)


def test_qft_evol_micro52_tranche_pin_remains_authoritative() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)

    assert TRANCHE_GATE_PATH in roadmap_text, (
        f"Roadmap authority surface must pin `{TRANCHE_GATE_PATH}` while saturation is active."
    )
    assert TRANCHE_GATE_PATH in state_text, (
        f"State authority surface must pin `{TRANCHE_GATE_PATH}` while saturation is active."
    )


def test_qft_evol_scaffold_saturation_gate_is_pinned_in_authority_surfaces() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)

    assert SATURATION_GATE_PATH in roadmap_text, (
        f"Roadmap authority surface must pin `{SATURATION_GATE_PATH}`."
    )
    assert SATURATION_GATE_PATH in state_text, (
        f"State authority surface must pin `{SATURATION_GATE_PATH}`."
    )
    assert MILESTONE_GATE_PATH in roadmap_text, (
        f"Roadmap authority surface must pin `{MILESTONE_GATE_PATH}`."
    )
    assert MILESTONE_GATE_PATH in state_text, (
        f"State authority surface must pin `{MILESTONE_GATE_PATH}`."
    )


def test_qft_evol_scaffold_saturation_forbids_micro53_roll_forward_without_reauthorization() -> None:
    target_text = _read(QFT_EVOL_TARGET_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)

    for forbidden in FORBIDDEN_MICRO_TOKENS:
        assert forbidden not in target_text, f"QFT evolution umbrella target must not include `{forbidden}`."
        assert forbidden not in roadmap_text, f"Roadmap must not include `{forbidden}` under saturation freeze."
        assert forbidden not in state_text, f"State must not include `{forbidden}` under saturation freeze."

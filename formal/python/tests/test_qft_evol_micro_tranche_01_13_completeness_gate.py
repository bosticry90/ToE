from __future__ import annotations

from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
QFT_EVOL_TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_EVOLUTION_OBJECT_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
TRANCHE_GATE_PATH = "formal/python/tests/test_qft_evol_micro_tranche_01_13_completeness_gate.py"
LEGACY_TRANCHE_GATE_PATH = "formal/python/tests/test_qft_evol_micro_tranche_01_12_completeness_gate.py"

TRANCHE_ORDERED_TOKENS = [
    "TARGET-QFT-EVOL-MICRO-01-TIME-STATE-OPERATOR-SURFACE-v0",
    "formal/docs/paper/DERIVATION_TARGET_QFT_EVOL_MICRO_01_TIME_STATE_OPERATOR_SURFACE_v0.md",
    "formal/python/tests/test_qft_evol_micro01_time_state_operator_surface_gate.py",
    "TARGET-QFT-EVOL-MICRO-02-EVOLUTION-CONTEXT-SURFACE-v0",
    "formal/docs/paper/DERIVATION_TARGET_QFT_EVOL_MICRO_02_EVOLUTION_CONTEXT_SURFACE_v0.md",
    "formal/python/tests/test_qft_evol_micro02_evolution_context_surface_gate.py",
    "TARGET-QFT-EVOL-MICRO-03-ACTION-DENSITY-SURFACE-v0",
    "formal/docs/paper/DERIVATION_TARGET_QFT_EVOL_MICRO_03_ACTION_DENSITY_SURFACE_v0.md",
    "formal/python/tests/test_qft_evol_micro03_action_density_surface_gate.py",
    "TARGET-QFT-EVOL-MICRO-04-EULER-LAGRANGE-SURFACE-v0",
    "formal/docs/paper/DERIVATION_TARGET_QFT_EVOL_MICRO_04_EULER_LAGRANGE_SURFACE_v0.md",
    "formal/python/tests/test_qft_evol_micro04_euler_lagrange_surface_gate.py",
    "TARGET-QFT-EVOL-MICRO-05-UNITARITY-SURFACE-v0",
    "formal/docs/paper/DERIVATION_TARGET_QFT_EVOL_MICRO_05_UNITARITY_SURFACE_v0.md",
    "formal/python/tests/test_qft_evol_micro05_unitarity_surface_gate.py",
    "TARGET-QFT-EVOL-MICRO-06-CANONICAL-MOMENTUM-SURFACE-v0",
    "formal/docs/paper/DERIVATION_TARGET_QFT_EVOL_MICRO_06_CANONICAL_MOMENTUM_SURFACE_v0.md",
    "formal/python/tests/test_qft_evol_micro06_canonical_momentum_surface_gate.py",
    "TARGET-QFT-EVOL-MICRO-07-EVOLUTION-GENERATOR-SURFACE-v0",
    "formal/docs/paper/DERIVATION_TARGET_QFT_EVOL_MICRO_07_EVOLUTION_GENERATOR_SURFACE_v0.md",
    "formal/python/tests/test_qft_evol_micro07_evolution_generator_surface_gate.py",
    "TARGET-QFT-EVOL-MICRO-08-HAMILTONIAN-SURFACE-v0",
    "formal/docs/paper/DERIVATION_TARGET_QFT_EVOL_MICRO_08_HAMILTONIAN_SURFACE_v0.md",
    "formal/python/tests/test_qft_evol_micro08_hamiltonian_surface_gate.py",
    "TARGET-QFT-EVOL-MICRO-09-HAMILTONIAN-GENERATOR-INTERFACE-SURFACE-v0",
    "formal/docs/paper/DERIVATION_TARGET_QFT_EVOL_MICRO_09_HAMILTONIAN_GENERATOR_INTERFACE_SURFACE_v0.md",
    "formal/python/tests/test_qft_evol_micro09_hamiltonian_generator_interface_surface_gate.py",
    "TARGET-QFT-EVOL-MICRO-10-EVOLUTION-CONTRACT-INTERFACE-SURFACE-v0",
    "formal/docs/paper/DERIVATION_TARGET_QFT_EVOL_MICRO_10_EVOLUTION_CONTRACT_INTERFACE_SURFACE_v0.md",
    "formal/python/tests/test_qft_evol_micro10_evolution_contract_interface_surface_gate.py",
    "TARGET-QFT-EVOL-MICRO-11-EVOLVES-UNDER-CONTRACT-INTERFACE-SURFACE-v0",
    "formal/docs/paper/DERIVATION_TARGET_QFT_EVOL_MICRO_11_EVOLVES_UNDER_CONTRACT_INTERFACE_SURFACE_v0.md",
    "formal/python/tests/test_qft_evol_micro11_evolves_under_contract_interface_surface_gate.py",
    "TARGET-QFT-EVOL-MICRO-12-QFT-EVOLUTION-UNDER-CONTRACT-ASSUMPTIONS-INTERFACE-SURFACE-v0",
    "formal/docs/paper/DERIVATION_TARGET_QFT_EVOL_MICRO_12_QFT_EVOLUTION_UNDER_CONTRACT_ASSUMPTIONS_INTERFACE_SURFACE_v0.md",
    "formal/python/tests/test_qft_evol_micro12_qft_evolution_under_contract_assumptions_interface_surface_gate.py",
    "TARGET-QFT-EVOL-MICRO-13-QFT-EVOLUTION-CONTRACT-THEOREM-INTERFACE-SURFACE-v0",
    "formal/docs/paper/DERIVATION_TARGET_QFT_EVOL_MICRO_13_QFT_EVOLUTION_CONTRACT_THEOREM_INTERFACE_SURFACE_v0.md",
    "formal/python/tests/test_qft_evol_micro13_qft_evolution_contract_theorem_interface_surface_gate.py",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _assert_present_in_order(text: str, ordered_tokens: list[str]) -> None:
    idx = -1
    for token in ordered_tokens:
        next_idx = text.find(token, idx + 1)
        assert next_idx >= 0, f"Missing ordered tranche token `{token}` in QFT evolution umbrella target."
        assert next_idx > idx, f"Out-of-order tranche token `{token}` in QFT evolution umbrella target."
        idx = next_idx


def test_qft_evol_micro_tranche_artifacts_exist() -> None:
    assert QFT_EVOL_TARGET_PATH.exists(), "Missing QFT evolution umbrella target document."
    assert ROADMAP_PATH.exists(), "Missing PHYSICS roadmap document."
    assert STATE_PATH.exists(), "Missing state checkpoint document."
    assert INVENTORY_PATH.exists(), "Missing TOE_MATH_PHYSICS_INVENTORY authority surface."


def test_qft_evol_umbrella_contains_micro_tranche_01_13_in_order() -> None:
    text = _read(QFT_EVOL_TARGET_PATH)
    _assert_present_in_order(text, TRANCHE_ORDERED_TOKENS)


def test_qft_evol_micro_tranche_gate_is_pinned_in_authority_surfaces() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)
    inventory_text = _read(INVENTORY_PATH)

    assert TRANCHE_GATE_PATH in roadmap_text, (
        f"Roadmap authority surface must pin `{TRANCHE_GATE_PATH}`."
    )
    assert TRANCHE_GATE_PATH in state_text or TRANCHE_GATE_PATH in inventory_text, (
        f"State or inventory authority surface must pin `{TRANCHE_GATE_PATH}`."
    )
    assert LEGACY_TRANCHE_GATE_PATH not in roadmap_text, (
        f"Roadmap authority surface must not pin legacy `{LEGACY_TRANCHE_GATE_PATH}`."
    )
    assert LEGACY_TRANCHE_GATE_PATH not in state_text and LEGACY_TRANCHE_GATE_PATH not in inventory_text, (
        f"State and inventory authority surfaces must not pin legacy `{LEGACY_TRANCHE_GATE_PATH}`."
    )

from __future__ import annotations

from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
QFT_EVOL_TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_EVOLUTION_OBJECT_v0.md"
QFT_EVOL_MICRO12_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_QFT_EVOL_MICRO_12_QFT_EVOLUTION_UNDER_CONTRACT_ASSUMPTIONS_INTERFACE_SURFACE_v0.md"
)
QFT_EVOL_OBJECT_SCAFFOLD_LEAN_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "QFT" / "Evolution" / "ObjectScaffold.lean"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_qft_evol_micro12_artifacts_exist() -> None:
    assert QFT_EVOL_TARGET_PATH.exists(), "Missing QFT evolution target document."
    assert QFT_EVOL_MICRO12_PATH.exists(), "Missing QFT evolution Cycle-012 micro document."
    assert QFT_EVOL_OBJECT_SCAFFOLD_LEAN_PATH.exists(), "Missing QFT evolution object scaffold Lean module."


def test_qft_evol_target_references_micro12_and_gate() -> None:
    text = _read(QFT_EVOL_TARGET_PATH)
    required_tokens = [
        "TARGET-QFT-EVOL-MICRO-12-QFT-EVOLUTION-UNDER-CONTRACT-ASSUMPTIONS-INTERFACE-SURFACE-v0",
        "formal/docs/paper/DERIVATION_TARGET_QFT_EVOL_MICRO_12_QFT_EVOLUTION_UNDER_CONTRACT_ASSUMPTIONS_INTERFACE_SURFACE_v0.md",
        "formal/python/tests/test_qft_evol_micro12_qft_evolution_under_contract_assumptions_interface_surface_gate.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "QFT evolution target document is missing required micro-12 token(s): " + ", ".join(missing)


def test_qft_evol_micro12_contains_interface_boundary_and_lean_pointer_tokens() -> None:
    text = _read(QFT_EVOL_MICRO12_PATH)
    required_tokens = [
        "DERIVATION_TARGET_QFT_EVOL_MICRO_12_QFT_EVOLUTION_UNDER_CONTRACT_ASSUMPTIONS_INTERFACE_SURFACE_v0",
        "TARGET-QFT-EVOL-MICRO-12-QFT-EVOLUTION-UNDER-CONTRACT-ASSUMPTIONS-INTERFACE-SURFACE-v0",
        "QFT_EVOL_MICRO12_QFT_EVOLUTION_UNDER_CONTRACT_ASSUMPTIONS_INTERFACE_ADJUDICATION: NOT_YET_DISCHARGED",
        "QFT_EVOL_MICRO12_SCOPE_BOUNDARY_v0: QFT_EVOLUTION_UNDER_CONTRACT_ASSUMPTIONS_INTERFACE_SURFACE_ONLY_NONCLAIM",
        "QFT_EVOL_MICRO12_PROGRESS_v0: QFT_EVOLUTION_UNDER_CONTRACT_ASSUMPTIONS_INTERFACE_SURFACE_TOKEN_PINNED",
        "QFT_EVOL_MICRO12_QFT_EVOLUTION_UNDER_CONTRACT_ASSUMPTIONS_INTERFACE_SURFACE_v0: QFT_EVOLUTION_UNDER_CONTRACT_ASSUMPTIONS_INTERFACE_STATEMENT_ONLY_PINNED",
        "formal/toe_formal/ToeFormal/QFT/Evolution/ObjectScaffold.lean",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "QFT evolution micro-12 document is missing required token(s): " + ", ".join(missing)


def test_qft_evol_micro12_nonclaim_boundary_is_explicit() -> None:
    text = _read(QFT_EVOL_MICRO12_PATH)
    required_nonclaim_phrases = [
        "qft-evolution-under-contract-assumptions interface statement-only surface (no proof/closure).",
        "no quantization claim.",
        "no dynamics derivation claim.",
        "no Standard Model recovery claim.",
        "no external truth claim.",
    ]
    missing = [phrase for phrase in required_nonclaim_phrases if phrase not in text]
    assert not missing, "QFT evolution micro-12 non-claim boundary phrase(s) missing: " + ", ".join(missing)


def test_qft_evol_micro12_lean_scaffold_has_interface_statement_tokens() -> None:
    text = _read(QFT_EVOL_OBJECT_SCAFFOLD_LEAN_PATH)
    required_tokens = [
        "def QFTEvolutionUnderContractAssumptionsInterfaceStatementOnly",
        "theorem QFTEvolutionUnderContractAssumptionsInterfaceStatementOnly_holds",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "QFT evolution object scaffold Lean module missing micro-12 token(s): " + ", ".join(missing)

import re
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
TARGET = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Variational" / "DeclaredDynamics.lean"


def _read_target() -> str:
    assert TARGET.exists(), f"Missing declared dynamics module: {TARGET}"
    return TARGET.read_text(encoding="utf-8")


def test_declared_dynamics_module_has_canonical_symbols():
    text = _read_target()
    required_tokens = [
        "def declaredDynamics",
        "def declaredInvariant",
        "theorem declared_dynamics_flow_law",
        "theorem declared_invariant_conserved",
    ]
    for token in required_tokens:
        assert token in text, f"Missing required declared-dynamics symbol: {token}"


def test_declared_dynamics_module_imports_declared_action_and_evolution():
    text = _read_target()
    assert "import ToeFormal.Variational.DeclaredAction" in text
    assert "import ToeFormal.Variational.EvolutionDeclared" in text


def test_declared_dynamics_route_uses_flow_law_and_noether_path():
    text = _read_target()
    assert re.search(r"FlowLaw\s+Field\s+declaredDynamics\s+declaredEvolution", text), (
        "Declared dynamics must be tied to the operator-driven flow-law surface."
    )
    assert re.search(r"Conserved\s+declaredEvolution\s+declaredInvariant", text), (
        "Declared invariant must be routed along declared evolution."
    )
    assert "noether_conserved_for_declared_evolution" in text, (
        "Noether routing must use the declared evolution linkage path."
    )

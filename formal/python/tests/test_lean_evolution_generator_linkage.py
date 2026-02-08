from __future__ import annotations

import re
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
VARIATIONAL = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Variational"

EVOL_GEN = VARIATIONAL / "EvolutionGeneratorLaw.lean"
SEMI_WITH_GEN = VARIATIONAL / "SemigroupWithGenerator.lean"
EVOL_DECL = VARIATIONAL / "EvolutionDeclared.lean"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing Lean module: {path}"
    return path.read_text(encoding="utf-8")


def test_discrete_generator_contract_replaces_generator_at_zero_assumption():
    text = _read(EVOL_GEN)

    required = [
        "def StepGenerator",
        "structure GeneratorStepLaw",
        "theorem GeneratorStepLaw.evolution_step_update",
        "structure GeneratorLawStrong",
        "step_law : GeneratorStepLaw",
    ]
    for token in required:
        assert token in text, f"Missing discrete generator token: {token}"

    assert "structure GeneratorAt0Law" not in text, (
        "Generator-at-0 structural assumption should be removed from the main linkage path."
    )
    assert "def DerivAt0" not in text, (
        "Abstract derivative-at-0 placeholder should not remain in the main linkage path."
    )
    assert not re.search(r"\bat0\s*:\s*GeneratorAt0Law", text), (
        "GeneratorLawStrong should not depend on GeneratorAt0Law."
    )


def test_semigroup_wrapper_exposes_discrete_step_update_projection():
    text = _read(SEMI_WITH_GEN)

    assert "theorem SemigroupWithGenerator.evolution_step_update" in text
    assert "G.generator.step_law.step" in text
    assert "GeneratorStepLaw.evolution_step_update" in text


def test_declared_evolution_module_routes_discrete_step_update():
    text = _read(EVOL_DECL)

    assert "theorem declared_evolution_step_update" in text
    assert re.search(r"declaredEvolution\.flow\s*\(t\s*\+\s*declaredSemigroupWithGenerator\.generator\.step_law\.step\)", text), (
        "Declared evolution step-update theorem must expose the semigroup step parameter."
    )
    assert "SemigroupWithGenerator.evolution_step_update" in text


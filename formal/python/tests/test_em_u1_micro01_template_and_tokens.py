from __future__ import annotations

import re
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
EM_TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_EM_U1_MAXWELL_OBJECT_v0.md"
EM_MICRO01_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_EM_U1_MICRO_01_OBJECT_SCAFFOLD_v0.md"
)
EM_OBJECT_SCAFFOLD_LEAN_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "EM" / "U1" / "ObjectScaffold.lean"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_em_cycle001_artifacts_exist() -> None:
    assert EM_TARGET_PATH.exists(), "Missing EM U1 target document."
    assert EM_MICRO01_PATH.exists(), "Missing EM U1 Cycle-001 micro scaffold document."
    assert EM_OBJECT_SCAFFOLD_LEAN_PATH.exists(), "Missing EM U1 object scaffold Lean module."


def test_em_target_references_cycle001_micro_artifact_and_lean_scaffold() -> None:
    text = _read(EM_TARGET_PATH)
    required_tokens = [
        "TARGET-EM-U1-MICRO-01-OBJECT-SCAFFOLD-v0",
        "EM_U1_PROGRESS_v0: CYCLE1_OBJECT_SCAFFOLD_TOKEN_PINNED",
        "formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_01_OBJECT_SCAFFOLD_v0.md",
        "formal/toe_formal/ToeFormal/EM/U1/ObjectScaffold.lean",
        "EM_U1_NO_SHORTCUT_GUARD_v0: OBJECT_ROUTE_REQUIRED",
        "EM_U1_MAXWELL_ADJUDICATION: NOT_YET_DISCHARGED",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM target document is missing required Cycle-001 token(s): " + ", ".join(missing)


def test_em_micro01_contains_required_object_route_and_assumption_tokens() -> None:
    text = _read(EM_MICRO01_PATH)
    required_tokens = [
        "DERIVATION_TARGET_EM_U1_MICRO_01_OBJECT_SCAFFOLD_v0",
        "TARGET-EM-U1-MICRO-01-OBJECT-SCAFFOLD-v0",
        "EM_U1_MICRO01_OBJECT_SCAFFOLD_ADJUDICATION: NOT_YET_DISCHARGED",
        "EM_U1_NO_SHORTCUT_GUARD_v0: OBJECT_ROUTE_REQUIRED",
        "EMU1Assumptions_v0",
        "EM_U1_PROGRESS_v0: CYCLE1_OBJECT_SCAFFOLD_TOKEN_PINNED",
        "EM_U1_INDEPENDENT_NECESSITY_CLASS_v0: OBJECT_CONSTRUCTIVE_ROUTE",
        "formal/toe_formal/ToeFormal/EM/U1/ObjectScaffold.lean",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM Cycle-001 micro document is missing required token(s): " + ", ".join(missing)


def test_em_micro01_is_object_scaffold_only_and_avoids_equation_form_dynamics_claims() -> None:
    text = _read(EM_MICRO01_PATH)
    forbidden_equation_patterns = [
        r"∇\s*·\s*E\s*=",
        r"∇\s*×\s*B\s*=",
        r"∂\s*_\s*μ\s*F\s*\^?\s*μ\s*ν\s*=",
        r"dF\s*=\s*0",
        r"d\*F\s*=\s*J",
    ]
    violations = [pattern for pattern in forbidden_equation_patterns if re.search(pattern, text)]
    assert not violations, (
        "Cycle-001 object scaffold must not include Maxwell-equation-form dynamics expressions. "
        "Forbidden pattern(s) present: "
        + ", ".join(violations)
    )


def test_em_object_scaffold_lean_has_typed_objects_and_gauge_contract_surface() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    required_tokens = [
        "namespace ToeFormal",
        "namespace EM",
        "namespace U1",
        "structure GaugePotential",
        "structure FieldStrength",
        "structure CurrentSource",
        "def gaugeTransform",
        "def fieldStrengthOfPotential",
        "def continuityAssumptionSurface",
        "def gaugeInvarianceContractSurface",
        "theorem em_u1_field_strength_invariance_under_contract_assumptions_v0",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM U1 object scaffold Lean module is missing required token(s): " + ", ".join(missing)

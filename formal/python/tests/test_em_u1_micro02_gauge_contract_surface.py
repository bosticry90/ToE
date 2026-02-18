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
EM_MICRO02_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_EM_U1_MICRO_02_GAUGE_CONTRACT_SURFACE_v0.md"
)
EM_OBJECT_SCAFFOLD_LEAN_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "EM" / "U1" / "ObjectScaffold.lean"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_em_cycle002_artifacts_exist() -> None:
    assert EM_TARGET_PATH.exists(), "Missing EM U1 target document."
    assert EM_MICRO02_PATH.exists(), "Missing EM U1 Cycle-002 gauge-contract micro document."
    assert EM_OBJECT_SCAFFOLD_LEAN_PATH.exists(), "Missing EM U1 object scaffold Lean module."


def test_em_target_references_cycle002_artifact_and_tokens() -> None:
    text = _read(EM_TARGET_PATH)
    required_tokens = [
        "TARGET-EM-U1-MICRO-02-GAUGE-CONTRACT-SURFACE-v0",
        "EM_U1_PROGRESS_CYCLE2_v0: GAUGE_CONTRACT_SURFACE_TOKEN_PINNED",
        "EM_U1_GAUGE_CONTRACT_ASSUMPTION_SURFACE_v0: COMMUTATIVITY_LINEARITY_PINNED",
        "EM_U1_GAUGE_CONTRACT_DERIVATION_TOKEN_v0: FIELD_STRENGTH_INVARIANCE_FROM_DIFFERENTIAL_BUNDLE_ASSUMPTIONS",
        "formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_02_GAUGE_CONTRACT_SURFACE_v0.md",
        "formal/toe_formal/ToeFormal/EM/U1/ObjectScaffold.lean",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM target document is missing required Cycle-002 token(s): " + ", ".join(missing)


def test_em_micro02_contains_assumption_surface_and_non_claim_boundaries() -> None:
    text = _read(EM_MICRO02_PATH)
    required_tokens = [
        "DERIVATION_TARGET_EM_U1_MICRO_02_GAUGE_CONTRACT_SURFACE_v0",
        "TARGET-EM-U1-MICRO-02-GAUGE-CONTRACT-SURFACE-v0",
        "EM_U1_MICRO02_GAUGE_CONTRACT_SURFACE_ADJUDICATION: NOT_YET_DISCHARGED",
        "EM_U1_GAUGE_CONTRACT_ASSUMPTION_SURFACE_v0: COMMUTATIVITY_LINEARITY_PINNED",
        "EM_U1_GAUGE_CONTRACT_DERIVATION_TOKEN_v0: FIELD_STRENGTH_INVARIANCE_FROM_DIFFERENTIAL_BUNDLE_ASSUMPTIONS",
        "EM_U1_NO_SHORTCUT_GUARD_v0: OBJECT_ROUTE_REQUIRED",
        "MATH|DEF|POLICY|SCOPE",
        "non-claim boundary is explicit and binding for this micro artifact.",
        "no non-Abelian completion claim.",
        "no Standard Model completion claim.",
        "no external truth claim.",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM Cycle-002 micro document is missing required token(s): " + ", ".join(missing)


def test_em_micro02_forbids_maxwell_equation_form_expressions() -> None:
    text = _read(EM_MICRO02_PATH)
    forbidden_equation_patterns = [
        r"∇\s*·\s*E\s*=",
        r"∇\s*×\s*B\s*=",
        r"∂\s*_\s*μ\s*F\s*\^?\s*μ\s*ν\s*=",
        r"dF\s*=\s*0",
        r"d\*F\s*=\s*J",
    ]
    violations = [pattern for pattern in forbidden_equation_patterns if re.search(pattern, text)]
    assert not violations, (
        "Cycle-002 gauge-contract scaffold must not include Maxwell-equation-form dynamics expressions. "
        "Forbidden pattern(s) present: "
        + ", ".join(violations)
    )


def test_em_object_scaffold_lean_cycle002_derivation_is_assumption_driven_not_tautological() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    required_tokens = [
        "structure DifferentialBundleGaugeAssumptions",
        "partialVector_add",
        "scalar_second_partial_comm",
        "EM_U1_GAUGE_CONTRACT_ASSUMPTION_SURFACE_v0: COMMUTATIVITY_LINEARITY_PINNED",
        "EM_U1_GAUGE_CONTRACT_DERIVATION_TOKEN_v0: FIELD_STRENGTH_INVARIANCE_FROM_DIFFERENTIAL_BUNDLE_ASSUMPTIONS",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM U1 Lean scaffold is missing required Cycle-002 token(s): " + ", ".join(missing)

    theorem_match = re.search(
        r"theorem\s+em_u1_field_strength_invariance_under_contract_assumptions_v0[\s\S]*?:=\s*by[\s\S]*?ring",
        text,
    )
    assert theorem_match is not None, (
        "EM Cycle-002 theorem must exist as an explicit proof block and not be a direct assumption passthrough."
    )

    theorem_block = theorem_match.group(0)
    assert "hGaugeInvariant" not in theorem_block, (
        "EM Cycle-002 theorem remains tautological (direct gauge-invariance assumption is still present)."
    )
    assert "hDiff : DifferentialBundleGaugeAssumptions d" in theorem_block, (
        "EM Cycle-002 theorem must depend on explicit differential-bundle assumptions."
    )

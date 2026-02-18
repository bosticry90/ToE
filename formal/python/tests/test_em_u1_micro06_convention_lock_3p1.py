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
EM_MICRO05_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_EM_U1_MICRO_05_MAXWELL_FORM_SEMANTICS_MAPPING_v0.md"
)
EM_MICRO06_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_EM_U1_MICRO_06_CONVENTION_LOCK_3P1_v0.md"
)
EM_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
EM_OBJECT_SCAFFOLD_LEAN_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "EM" / "U1" / "ObjectScaffold.lean"


NEW_PHYSICS_RULES = {
    "constitutive_relations": {
        "patterns": [
            r"\bD\s*=\s*ε\s*E\b",
            r"\bH\s*=\s*B\s*/\s*μ\b",
            r"\bB\s*=\s*μ\s*H\b",
            r"\bε0\b",
            r"\bμ0\b",
        ],
        "required_ids": ["ASM-EM-U1-PHY-CONSTITUTIVE-01"],
    },
    "unit_systems": {
        "patterns": [
            r"\bSI units\b",
            r"\bGaussian units\b",
            r"\bHeaviside-?Lorentz\b",
            r"\bc\s*=\s*1\b",
        ],
        "required_ids": ["ASM-EM-U1-PHY-UNITS-01"],
    },
    "gauge_fixing": {
        "patterns": [
            r"\bLorenz gauge\b",
            r"\bCoulomb gauge\b",
            r"\btemporal gauge\b",
            r"\baxial gauge\b",
            r"\bFeynman gauge\b",
        ],
        "required_ids": ["ASM-EM-U1-PHY-GFIX-01"],
    },
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _strip_wrapping_backticks(text: str) -> str:
    s = text.strip()
    if s.startswith("`") and s.endswith("`") and len(s) >= 2:
        return s[1:-1]
    return s


def test_em_cycle006_artifacts_exist() -> None:
    assert EM_TARGET_PATH.exists(), "Missing EM U1 target document."
    assert EM_MICRO05_PATH.exists(), "Missing EM U1 Cycle-005 mapping package document."
    assert EM_MICRO06_PATH.exists(), "Missing EM U1 Cycle-006 convention-lock package document."
    assert EM_ROADMAP_PATH.exists(), "Missing physics roadmap document."
    assert EM_OBJECT_SCAFFOLD_LEAN_PATH.exists(), "Missing EM U1 object scaffold Lean module."


def test_em_micro06_contains_required_convention_lock_tokens() -> None:
    text = _read(EM_MICRO06_PATH)
    required_tokens = [
        "DERIVATION_TARGET_EM_U1_MICRO_06_CONVENTION_LOCK_3P1_v0",
        "TARGET-EM-U1-MICRO-06-CONVENTION-LOCK-3P1-v0",
        "EM_U1_PROGRESS_CYCLE6_v0: CONVENTION_LOCK_3P1_TOKEN_PINNED",
        "EM_U1_CONVENTION_LOCK_SIGNATURE_v0: METRIC_SIGNATURE_FIXED",
        "EM_U1_CONVENTION_LOCK_INDEX_v0: INDEX_POSITION_RULES_FIXED",
        "EM_U1_CONVENTION_LOCK_EB_v0: E_B_SIGN_AND_EPSILON_FIXED",
        "EM_U1_CONVENTION_LOCK_UNITS_POLICY_v0: UNITS_NOT_SELECTED",
        "EM_U1_CONVENTION_LOCK_NO_DYNAMICS_v0: DEFINITIONAL_ONLY",
        "EM_U1_NEW_PHYSICS_ASSUMPTION_ID_GATE_v0: CONSTITUTIVE_UNITS_GAUGE_FIXING_REQUIRE_IDS",
        "EM_U1_MICRO06_CONVENTION_LOCK_3P1_ADJUDICATION: NOT_YET_DISCHARGED",
        "(-,+,+,+)",
        "E_i := F_{0i}",
        "F_{ij} := - ε_{ijk} B^k",
        "ε^{0123} = +1",
        "formal/python/tests/test_em_u1_micro06_convention_lock_3p1.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM Cycle-006 micro document is missing required token(s): " + ", ".join(missing)


def test_em_target_references_cycle006_artifact_and_tokens() -> None:
    text = _read(EM_TARGET_PATH)
    required_tokens = [
        "TARGET-EM-U1-MICRO-06-CONVENTION-LOCK-3P1-v0",
        "EM_U1_PROGRESS_CYCLE6_v0: CONVENTION_LOCK_3P1_TOKEN_PINNED",
        "EM_U1_CONVENTION_LOCK_SIGNATURE_v0: METRIC_SIGNATURE_FIXED",
        "EM_U1_CONVENTION_LOCK_INDEX_v0: INDEX_POSITION_RULES_FIXED",
        "EM_U1_CONVENTION_LOCK_EB_v0: E_B_SIGN_AND_EPSILON_FIXED",
        "EM_U1_CONVENTION_LOCK_UNITS_POLICY_v0: UNITS_NOT_SELECTED",
        "EM_U1_CONVENTION_LOCK_NO_DYNAMICS_v0: DEFINITIONAL_ONLY",
        "EM_U1_NEW_PHYSICS_ASSUMPTION_ID_GATE_v0: CONSTITUTIVE_UNITS_GAUGE_FIXING_REQUIRE_IDS",
        "EM_U1_MICRO06_CONVENTION_LOCK_3P1_ADJUDICATION: NOT_YET_DISCHARGED",
        "formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_06_CONVENTION_LOCK_3P1_v0.md",
        "formal/python/tests/test_em_u1_micro06_convention_lock_3p1.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM target document is missing required Cycle-006 token(s): " + ", ".join(missing)


def test_em_roadmap_references_cycle006_target_and_artifact() -> None:
    roadmap_text = _read(EM_ROADMAP_PATH)
    rows = [line.strip() for line in roadmap_text.splitlines() if line.strip().startswith("| `PILLAR-EM` |")]
    assert len(rows) == 1, f"Expected one `PILLAR-EM` roadmap row, found {len(rows)}."
    cells = [cell.strip() for cell in rows[0].split("|")]
    assert len(cells) >= 7, "Malformed `PILLAR-EM` roadmap row."
    targets_raw = _strip_wrapping_backticks(cells[3])
    artifacts_raw = _strip_wrapping_backticks(cells[4])
    targets = {item.strip() for item in targets_raw.split(";") if item.strip()}
    artifacts = {item.strip() for item in artifacts_raw.split(";") if item.strip()}
    assert "TARGET-EM-U1-MICRO-06-CONVENTION-LOCK-3P1-v0" in targets
    assert "formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_06_CONVENTION_LOCK_3P1_v0.md" in artifacts


def test_cycle006_is_definitional_only_and_avoids_dynamics_claim_language() -> None:
    text = _read(EM_MICRO06_PATH)
    forbidden_dynamics_claim_patterns = [
        r"\bwave equation\b",
        r"\bradiative solution\b",
        r"\bpropagation speed\b",
        r"\bLagrangian density\b",
        r"\bEuler-?Lagrange\b",
        r"\bfull dynamics closure\b",
        r"\btheorem discharge\b",
    ]
    violations = [pattern for pattern in forbidden_dynamics_claim_patterns if re.search(pattern, text, flags=re.IGNORECASE)]
    assert not violations, (
        "Cycle-006 convention lock must remain definitional/structural only. "
        "Forbidden dynamics-claim pattern(s) found: "
        + ", ".join(violations)
    )


def test_cycle006_new_physics_imports_require_explicit_assumption_ids() -> None:
    text = _read(EM_MICRO06_PATH)
    violations: list[str] = []
    for lane_name, rule in NEW_PHYSICS_RULES.items():
        patterns: list[str] = rule["patterns"]
        required_ids: list[str] = rule["required_ids"]
        lane_hits = [pattern for pattern in patterns if re.search(pattern, text, flags=re.IGNORECASE)]
        if not lane_hits:
            continue
        missing_ids = [assumption_id for assumption_id in required_ids if assumption_id not in text]
        if missing_ids:
            violations.append(
                f"{lane_name}: matched {lane_hits} but missing required assumption ID(s): {', '.join(missing_ids)}"
            )

    assert not violations, (
        "Cycle-006 new-physics import gate violation. "
        "Constitutive/units/gauge-fixing imports require explicit assumption IDs:\n- "
        + "\n- ".join(violations)
    )


def test_em_lean_cycle006_tokens_are_pinned() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    required_tokens = [
        "EM_U1_PROGRESS_CYCLE6_v0: CONVENTION_LOCK_3P1_TOKEN_PINNED",
        "EM_U1_CONVENTION_LOCK_SIGNATURE_v0: METRIC_SIGNATURE_FIXED",
        "EM_U1_CONVENTION_LOCK_INDEX_v0: INDEX_POSITION_RULES_FIXED",
        "EM_U1_CONVENTION_LOCK_EB_v0: E_B_SIGN_AND_EPSILON_FIXED",
        "EM_U1_CONVENTION_LOCK_UNITS_POLICY_v0: UNITS_NOT_SELECTED",
        "EM_U1_CONVENTION_LOCK_NO_DYNAMICS_v0: DEFINITIONAL_ONLY",
        "theorem em_u1_cycle006_token_binding_stub_v0",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM U1 Lean scaffold is missing required Cycle-006 token(s): " + ", ".join(missing)

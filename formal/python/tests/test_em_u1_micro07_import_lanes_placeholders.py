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
EM_MICRO02_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_EM_U1_MICRO_02_GAUGE_CONTRACT_SURFACE_v0.md"
)
EM_MICRO03_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_EM_U1_MICRO_03_PREDISCHARGE_GATE_BUNDLE_v0.md"
)
EM_MICRO04_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_EM_U1_MICRO_04_MAXWELL_FORM_ATTEMPT_PACKAGE_v0.md"
)
EM_MICRO05_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_EM_U1_MICRO_05_MAXWELL_FORM_SEMANTICS_MAPPING_v0.md"
)
EM_MICRO06_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_EM_U1_MICRO_06_CONVENTION_LOCK_3P1_v0.md"
)
EM_MICRO07_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_EM_U1_MICRO_07_IMPORT_LANES_PLACEHOLDERS_v0.md"
)
EM_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
ASSUMPTION_REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "ASSUMPTION_REGISTRY_v1.md"
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


def test_em_cycle007_artifacts_exist() -> None:
    assert EM_TARGET_PATH.exists(), "Missing EM U1 target document."
    assert EM_MICRO07_PATH.exists(), "Missing EM U1 Cycle-007 import-lanes placeholder document."
    assert EM_ROADMAP_PATH.exists(), "Missing physics roadmap document."
    assert ASSUMPTION_REGISTRY_PATH.exists(), "Missing assumption registry."
    assert EM_OBJECT_SCAFFOLD_LEAN_PATH.exists(), "Missing EM U1 object scaffold Lean module."


def test_em_micro07_contains_required_import_lane_tokens_and_ids() -> None:
    text = _read(EM_MICRO07_PATH)
    required_tokens = [
        "DERIVATION_TARGET_EM_U1_MICRO_07_IMPORT_LANES_PLACEHOLDERS_v0",
        "TARGET-EM-U1-MICRO-07-IMPORT-LANES-PLACEHOLDERS-v0",
        "EM_U1_PROGRESS_CYCLE7_v0: IMPORT_LANES_PLACEHOLDERS_TOKEN_PINNED",
        "EM_U1_IMPORT_LANES_LOCALIZATION_GATE_v0: CONSTITUTIVE_UNITS_GFIXING_ONLY_IN_CYCLE7_ARTIFACTS",
        "EM_U1_IMPORT_LANES_NO_DYNAMICS_v0: PLACEHOLDER_ONLY",
        "EM_U1_MICRO07_IMPORT_LANES_ADJUDICATION: NOT_YET_DISCHARGED",
        "EM_U1_NEW_PHYSICS_ASSUMPTION_ID_GATE_v0: CONSTITUTIVE_UNITS_GAUGE_FIXING_REQUIRE_IDS",
        "ASM-EM-U1-PHY-CONSTITUTIVE-01",
        "ASM-EM-U1-PHY-UNITS-01",
        "ASM-EM-U1-PHY-GFIX-01",
        "formal/python/tests/test_em_u1_micro07_import_lanes_placeholders.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM Cycle-007 micro document is missing required token(s): " + ", ".join(missing)


def test_assumption_registry_contains_cycle007_import_lane_ids_and_pointer() -> None:
    text = _read(ASSUMPTION_REGISTRY_PATH)
    required_tokens = [
        "| `ASM-EM-U1-PHY-CONSTITUTIVE-01` |",
        "| `ASM-EM-U1-PHY-UNITS-01` |",
        "| `ASM-EM-U1-PHY-GFIX-01` |",
        "`em_u1_import_lanes_placeholders_v0`",
        "- `ASM-EM-U1-PHY-CONSTITUTIVE-01`",
        "- `ASM-EM-U1-PHY-UNITS-01`",
        "- `ASM-EM-U1-PHY-GFIX-01`",
        "formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_07_IMPORT_LANES_PLACEHOLDERS_v0.md",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "Assumption registry is missing required Cycle-007 import-lane linkage token(s): " + ", ".join(
        missing
    )


def test_em_target_references_cycle007_artifact_and_tokens() -> None:
    text = _read(EM_TARGET_PATH)
    required_tokens = [
        "TARGET-EM-U1-MICRO-07-IMPORT-LANES-PLACEHOLDERS-v0",
        "EM_U1_PROGRESS_CYCLE7_v0: IMPORT_LANES_PLACEHOLDERS_TOKEN_PINNED",
        "EM_U1_IMPORT_LANES_LOCALIZATION_GATE_v0: CONSTITUTIVE_UNITS_GFIXING_ONLY_IN_CYCLE7_ARTIFACTS",
        "EM_U1_IMPORT_LANES_NO_DYNAMICS_v0: PLACEHOLDER_ONLY",
        "EM_U1_MICRO07_IMPORT_LANES_ADJUDICATION: NOT_YET_DISCHARGED",
        "EM_U1_NEW_PHYSICS_ASSUMPTION_ID_GATE_v0: CONSTITUTIVE_UNITS_GAUGE_FIXING_REQUIRE_IDS",
        "ASM-EM-U1-PHY-CONSTITUTIVE-01",
        "ASM-EM-U1-PHY-UNITS-01",
        "ASM-EM-U1-PHY-GFIX-01",
        "formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_07_IMPORT_LANES_PLACEHOLDERS_v0.md",
        "formal/python/tests/test_em_u1_micro07_import_lanes_placeholders.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM target document is missing required Cycle-007 token(s): " + ", ".join(missing)


def test_em_roadmap_references_cycle007_target_and_artifact() -> None:
    roadmap_text = _read(EM_ROADMAP_PATH)
    rows = [line.strip() for line in roadmap_text.splitlines() if line.strip().startswith("| `PILLAR-EM` |")]
    assert len(rows) == 1, f"Expected one `PILLAR-EM` roadmap row, found {len(rows)}."
    cells = [cell.strip() for cell in rows[0].split("|")]
    assert len(cells) >= 7, "Malformed `PILLAR-EM` roadmap row."
    targets_raw = _strip_wrapping_backticks(cells[3])
    artifacts_raw = _strip_wrapping_backticks(cells[4])
    targets = {item.strip() for item in targets_raw.split(";") if item.strip()}
    artifacts = {item.strip() for item in artifacts_raw.split(";") if item.strip()}
    assert "TARGET-EM-U1-MICRO-07-IMPORT-LANES-PLACEHOLDERS-v0" in targets
    assert "formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_07_IMPORT_LANES_PLACEHOLDERS_v0.md" in artifacts


def test_cycle007_is_definitional_only_and_avoids_dynamics_claim_language() -> None:
    text = _read(EM_MICRO07_PATH)
    forbidden_dynamics_claim_patterns = [
        r"\bwave equation\b",
        r"\bradiative solution\b",
        r"\bpropagation speed\b",
        r"\bLagrangian density\b",
        r"\bEuler-?Lagrange\b",
        r"\bfull dynamics closure\b",
        r"\bequations of motion\b",
    ]
    violations = [pattern for pattern in forbidden_dynamics_claim_patterns if re.search(pattern, text, flags=re.IGNORECASE)]
    assert not violations, (
        "Cycle-007 import-lanes placeholders must remain definitional/structural only. "
        "Forbidden dynamics-claim pattern(s) found: "
        + ", ".join(violations)
    )


def test_cycle007_localizes_new_physics_mentions_and_enforces_assumption_ids() -> None:
    cycle07_text = _read(EM_MICRO07_PATH)
    non_cycle07_paths = [
        EM_TARGET_PATH,
        EM_MICRO01_PATH,
        EM_MICRO02_PATH,
        EM_MICRO03_PATH,
        EM_MICRO04_PATH,
        EM_MICRO05_PATH,
        EM_MICRO06_PATH,
    ]

    violations: list[str] = []
    for lane_name, rule in NEW_PHYSICS_RULES.items():
        patterns: list[str] = rule["patterns"]
        required_ids: list[str] = rule["required_ids"]

        lane_hits_cycle07 = [pattern for pattern in patterns if re.search(pattern, cycle07_text, flags=re.IGNORECASE)]
        if lane_hits_cycle07:
            missing_ids = [assumption_id for assumption_id in required_ids if assumption_id not in cycle07_text]
            if missing_ids:
                violations.append(
                    f"{lane_name}: Cycle-007 includes pattern(s) {lane_hits_cycle07} but misses assumption ID(s): "
                    + ", ".join(missing_ids)
                )

        for path in non_cycle07_paths:
            text = _read(path)
            lane_hits_other = [pattern for pattern in patterns if re.search(pattern, text, flags=re.IGNORECASE)]
            if lane_hits_other:
                violations.append(
                    f"{lane_name}: disallowed pattern(s) {lane_hits_other} found outside Cycle-007 in "
                    f"{path.relative_to(REPO_ROOT)}"
                )

    assert not violations, (
        "Cycle-007 localization/assumption-ID gate violation:\n- " + "\n- ".join(violations)
    )


def test_em_lean_cycle007_tokens_are_pinned() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    required_tokens = [
        "EM_U1_PROGRESS_CYCLE7_v0: IMPORT_LANES_PLACEHOLDERS_TOKEN_PINNED",
        "EM_U1_IMPORT_LANES_LOCALIZATION_GATE_v0: CONSTITUTIVE_UNITS_GFIXING_ONLY_IN_CYCLE7_ARTIFACTS",
        "EM_U1_IMPORT_LANES_NO_DYNAMICS_v0: PLACEHOLDER_ONLY",
        "EM_U1_NEW_PHYSICS_ASSUMPTION_ID_GATE_v0: CONSTITUTIVE_UNITS_GAUGE_FIXING_REQUIRE_IDS",
        "theorem em_u1_cycle007_token_binding_stub_v0",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM U1 Lean scaffold is missing required Cycle-007 token(s): " + ", ".join(missing)

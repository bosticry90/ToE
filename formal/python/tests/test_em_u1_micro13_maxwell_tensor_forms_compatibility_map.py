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
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
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
EM_MICRO08_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_EM_U1_MICRO_08_IMPORT_LANES_INTERFACE_CONTRACTS_v0.md"
)
EM_MICRO09_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_EM_U1_MICRO_09_DUAL_HODGE_CONVENTION_LOCK_v0.md"
)
EM_MICRO10_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_EM_U1_MICRO_10_SOURCE_CURRENT_INTERFACE_CONTRACTS_v0.md"
)
EM_MICRO11_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_EM_U1_MICRO_11_MAXWELL_EQUATION_SURFACES_STATEMENT_LOCK_v0.md"
)
EM_MICRO12_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_EM_U1_MICRO_12_POTENTIAL_FIELDSTRENGTH_BRIDGE_LOCK_v0.md"
)
EM_MICRO13_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_EM_U1_MICRO_13_MAXWELL_TENSOR_FORMS_COMPATIBILITY_MAP_v0.md"
)
EM_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
EM_OBJECT_SCAFFOLD_LEAN_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "EM" / "U1" / "ObjectScaffold.lean"

SOURCE_ASSUMPTION_ID = "ASM-EM-U1-PHY-SOURCE-01"
LOCALIZATION_TOKEN = "EM_U1_MAXWELL_COMPATIBILITY_LOCALIZATION_GATE_v0: CYCLE13_ARTIFACTS_ONLY"
PREREQUISITE_TOKENS = [
    "EM_U1_CONVENTION_LOCK_SIGNATURE_v0: METRIC_SIGNATURE_FIXED",
    "EM_U1_HODGE_STAR_CONVENTION_v0: STARSTAR_SIGN_FIXED_UNDER_SIGNATURE",
    "EM_U1_CONVENTION_LOCK_EB_v0: E_B_SIGN_AND_EPSILON_FIXED",
    "EM_U1_SOURCE_OBJECT_CONVENTION_v0: CURRENT_OBJECT_DEFINED",
]
NON_SELECTION_TOKENS = [
    "EM_U1_IMPORT_LANES_INTERFACE_NO_SELECTION_v0: NO_UNITS_OR_GAUGE_SELECTION",
    "EM_U1_NEW_PHYSICS_ASSUMPTION_ID_GATE_v0: CONSTITUTIVE_UNITS_GAUGE_FIXING_REQUIRE_IDS",
]

MAXWELL_COMPATIBILITY_MAP_PATTERNS = {
    "inhomogeneous_map": re.escape("∂_μ F^{μν} = J^ν ↔ d⋆F = J"),
    "homogeneous_map": re.escape("∂_[α F_{βγ]} = 0 ↔ dF = 0"),
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _strip_wrapping_backticks(text: str) -> str:
    s = text.strip()
    if s.startswith("`") and s.endswith("`") and len(s) >= 2:
        return s[1:-1]
    return s


def test_em_cycle013_artifacts_exist() -> None:
    assert STATE_PATH.exists(), "Missing State_of_the_Theory.md."
    assert EM_TARGET_PATH.exists(), "Missing EM U1 target document."
    assert EM_MICRO13_PATH.exists(), "Missing EM U1 Cycle-013 document."
    assert EM_ROADMAP_PATH.exists(), "Missing physics roadmap document."
    assert EM_OBJECT_SCAFFOLD_LEAN_PATH.exists(), "Missing EM U1 object scaffold Lean module."


def test_em_micro13_contains_required_tokens_and_compatibility_map() -> None:
    text = _read(EM_MICRO13_PATH)
    required_tokens = [
        "DERIVATION_TARGET_EM_U1_MICRO_13_MAXWELL_TENSOR_FORMS_COMPATIBILITY_MAP_v0",
        "TARGET-EM-U1-MICRO-13-MAXWELL-TENSOR-FORMS-COMPATIBILITY-MAP-v0",
        "EM_U1_PROGRESS_CYCLE13_v0: MAXWELL_COMPATIBILITY_MAP_TOKEN_PINNED",
        "EM_U1_MAXWELL_TENSOR_FORMS_MAP_v0: STATEMENT_SURFACE_TRANSLATION_PINNED",
        LOCALIZATION_TOKEN,
        "EM_U1_MAXWELL_COMPATIBILITY_NO_DERIVATION_v0: STATEMENT_ONLY",
        "EM_U1_MICRO13_MAXWELL_COMPATIBILITY_ADJUDICATION: NOT_YET_DISCHARGED",
        SOURCE_ASSUMPTION_ID,
        "formal/python/tests/test_em_u1_micro13_maxwell_tensor_forms_compatibility_map.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM Cycle-013 micro document is missing required token(s): " + ", ".join(missing)

    missing_patterns = [
        label for label, pattern in MAXWELL_COMPATIBILITY_MAP_PATTERNS.items() if re.search(pattern, text) is None
    ]
    assert not missing_patterns, (
        "EM Cycle-013 micro document is missing required Maxwell compatibility-map expression(s): "
        + ", ".join(missing_patterns)
    )


def test_em_target_references_cycle013_artifact_and_tokens() -> None:
    text = _read(EM_TARGET_PATH)
    required_tokens = [
        "TARGET-EM-U1-MICRO-13-MAXWELL-TENSOR-FORMS-COMPATIBILITY-MAP-v0",
        "EM_U1_PROGRESS_CYCLE13_v0: MAXWELL_COMPATIBILITY_MAP_TOKEN_PINNED",
        "EM_U1_MAXWELL_TENSOR_FORMS_MAP_v0: STATEMENT_SURFACE_TRANSLATION_PINNED",
        LOCALIZATION_TOKEN,
        "EM_U1_MAXWELL_COMPATIBILITY_NO_DERIVATION_v0: STATEMENT_ONLY",
        "EM_U1_MICRO13_MAXWELL_COMPATIBILITY_ADJUDICATION: NOT_YET_DISCHARGED",
        SOURCE_ASSUMPTION_ID,
        "formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_13_MAXWELL_TENSOR_FORMS_COMPATIBILITY_MAP_v0.md",
        "formal/python/tests/test_em_u1_micro13_maxwell_tensor_forms_compatibility_map.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM target document is missing required Cycle-013 token(s): " + ", ".join(missing)


def test_em_roadmap_references_cycle013_target_and_artifact_with_single_row() -> None:
    roadmap_text = _read(EM_ROADMAP_PATH)
    rows = [line.strip() for line in roadmap_text.splitlines() if line.strip().startswith("| `PILLAR-EM` |")]
    assert len(rows) == 1, f"Expected one `PILLAR-EM` roadmap row, found {len(rows)}."
    cells = [cell.strip() for cell in rows[0].split("|")]
    assert len(cells) >= 7, "Malformed `PILLAR-EM` roadmap row."
    targets_raw = _strip_wrapping_backticks(cells[3])
    artifacts_raw = _strip_wrapping_backticks(cells[4])
    targets = {item.strip() for item in targets_raw.split(";") if item.strip()}
    artifacts = {item.strip() for item in artifacts_raw.split(";") if item.strip()}
    assert "TARGET-EM-U1-MICRO-13-MAXWELL-TENSOR-FORMS-COMPATIBILITY-MAP-v0" in targets
    assert (
        "formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_13_MAXWELL_TENSOR_FORMS_COMPATIBILITY_MAP_v0.md"
        in artifacts
    )


def test_state_mentions_cycle013_checkpoint_and_tokens() -> None:
    text = _read(STATE_PATH)
    required_tokens = [
        "EM Cycle-013 Maxwell tensor/forms compatibility-map checkpoint",
        "TARGET-EM-U1-MICRO-13-MAXWELL-TENSOR-FORMS-COMPATIBILITY-MAP-v0",
        "EM_U1_PROGRESS_CYCLE13_v0: MAXWELL_COMPATIBILITY_MAP_TOKEN_PINNED",
        "EM_U1_MAXWELL_TENSOR_FORMS_MAP_v0: STATEMENT_SURFACE_TRANSLATION_PINNED",
        LOCALIZATION_TOKEN,
        "EM_U1_MAXWELL_COMPATIBILITY_NO_DERIVATION_v0: STATEMENT_ONLY",
        "EM_U1_MICRO13_MAXWELL_COMPATIBILITY_ADJUDICATION: NOT_YET_DISCHARGED",
        SOURCE_ASSUMPTION_ID,
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "State_of_the_Theory.md is missing required Cycle-013 token(s): " + ", ".join(missing)


def test_em_lean_cycle013_tokens_and_harness_stubs_are_pinned() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    required_tokens = [
        "structure MaxwellStatementCompatibilityMap where",
        "def maxwellCompatibilityHarness",
        "EM_U1_PROGRESS_CYCLE13_v0: MAXWELL_COMPATIBILITY_MAP_TOKEN_PINNED",
        "EM_U1_MAXWELL_TENSOR_FORMS_MAP_v0: STATEMENT_SURFACE_TRANSLATION_PINNED",
        LOCALIZATION_TOKEN,
        "EM_U1_MAXWELL_COMPATIBILITY_NO_DERIVATION_v0: STATEMENT_ONLY",
        "theorem em_u1_cycle013_token_binding_stub_v0",
        "theorem em_u1_cycle013_compatibility_harness_stub_v0",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM U1 Lean scaffold is missing required Cycle-013 token(s): " + ", ".join(missing)


def test_cycle013_compatibility_map_is_localized_to_cycle13_artifact() -> None:
    allowed_paths = [EM_MICRO13_PATH]
    scoped_paths = [
        EM_TARGET_PATH,
        EM_MICRO01_PATH,
        EM_MICRO02_PATH,
        EM_MICRO03_PATH,
        EM_MICRO04_PATH,
        EM_MICRO05_PATH,
        EM_MICRO06_PATH,
        EM_MICRO07_PATH,
        EM_MICRO08_PATH,
        EM_MICRO09_PATH,
        EM_MICRO10_PATH,
        EM_MICRO11_PATH,
        EM_MICRO12_PATH,
        EM_ROADMAP_PATH,
        STATE_PATH,
        EM_OBJECT_SCAFFOLD_LEAN_PATH,
    ]

    violations: list[str] = []

    for path in allowed_paths:
        text = _read(path)
        hits = [label for label, pattern in MAXWELL_COMPATIBILITY_MAP_PATTERNS.items() if re.search(pattern, text)]
        if not hits:
            violations.append(f"cycle013 artifact {path.relative_to(REPO_ROOT)} is missing localized map expressions")
            continue
        has_assumption_id = SOURCE_ASSUMPTION_ID in text
        has_localization_gate = LOCALIZATION_TOKEN in text
        has_prereq = all(token in text for token in PREREQUISITE_TOKENS)
        has_non_selection = all(token in text for token in NON_SELECTION_TOKENS)
        if not (has_assumption_id and has_localization_gate and has_prereq and has_non_selection):
            violations.append(
                f"cycle013 artifact {path.relative_to(REPO_ROOT)} contains map expressions {hits} "
                "without source assumption ID + localization token + prerequisites + non-selection tokens."
            )

    for path in scoped_paths:
        text = _read(path)
        for label, pattern in MAXWELL_COMPATIBILITY_MAP_PATTERNS.items():
            if re.search(pattern, text):
                violations.append(
                    f"{label} compatibility-map expression leaked into non-authorized artifact "
                    f"{path.relative_to(REPO_ROOT)}"
                )

    assert not violations, "Cycle-013 compatibility-map localization violation:\n- " + "\n- ".join(violations)


def test_cycle013_is_statement_only_and_blocks_derivation_or_new_physics_selection_language() -> None:
    text = _read(EM_MICRO13_PATH)
    forbidden_patterns = [
        r"\bwe derive\b",
        r"\bwe prove\b",
        r"\btherefore\b",
        r"\bfollows from gauge invariance\b",
        r"\bproves that\b",
        r"\bclosure is proven\b",
        r"\btheorem-level closure\b",
        r"\bT-PROVED\b",
        r"\bDISCHARGED_v0\b",
        r"\bSI units\b",
        r"\bGaussian units\b",
        r"\bHeaviside-?Lorentz\b",
        r"\bLorenz gauge\b",
        r"\bCoulomb gauge\b",
        r"\btemporal gauge\b",
        r"\baxial gauge\b",
        r"\bFeynman gauge\b",
        r"\bD\s*=\s*ε\s*E\b",
        r"\bB\s*=\s*μ\s*H\b",
    ]
    violations = [pattern for pattern in forbidden_patterns if re.search(pattern, text, flags=re.IGNORECASE)]
    assert not violations, (
        "Cycle-013 must remain statement-only/non-derivational with no import-lane selections. "
        "Forbidden pattern(s) found: "
        + ", ".join(violations)
    )

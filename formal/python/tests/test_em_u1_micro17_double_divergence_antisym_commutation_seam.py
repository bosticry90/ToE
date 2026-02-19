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
EM_MICRO14_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_EM_U1_MICRO_14_INDEX_METRIC_CURRENT_DECOMPOSITION_SURFACE_v0.md"
)
EM_MICRO15_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_EM_U1_MICRO_15_CONTINUITY_SURFACE_COMPATIBILITY_SEAM_v0.md"
)
EM_MICRO16_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_EM_U1_MICRO_16_MAXWELL_TO_CONTINUITY_ROUTE_ATTEMPT_PACKAGE_v0.md"
)
EM_MICRO17_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_EM_U1_MICRO_17_DOUBLE_DIVERGENCE_ANTISYM_COMMUTATION_SEAM_v0.md"
)
EM_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
EM_OBJECT_SCAFFOLD_LEAN_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "EM" / "U1" / "ObjectScaffold.lean"

SOURCE_ASSUMPTION_ID = "ASM-EM-U1-PHY-SOURCE-01"
LOCALIZATION_TOKEN = "EM_U1_DOUBLE_DIVERGENCE_LOCALIZATION_GATE_v0: CYCLE17_ARTIFACTS_ONLY"
CYCLE16_LOCALIZATION_TOKEN = "EM_U1_MAXWELL_CONTINUITY_LOCALIZATION_GATE_v0: CYCLE16_ARTIFACTS_ONLY"
PREREQUISITE_TOKENS = [
    "EM_U1_AF_BRIDGE_TENSOR_v0: F_MUNU_FROM_A_SEAM_PINNED",
    "EM_U1_INDEX_METRIC_RAISE_LOWER_SURFACE_v0: F_INDEX_POSITION_CONTRACT_PINNED",
    "EM_U1_MAXWELL_CONTINUITY_ROUTE_v0: DIVERGENCE_OF_INHOM_SURFACE_ROUTE_PINNED",
    "EM_U1_MAXWELL_CONTINUITY_MATH_REGULARITY_SEAM_v0: COMMUTING_PARTIALS_REQUIRED",
]
NON_SELECTION_TOKENS = [
    "EM_U1_IMPORT_LANES_INTERFACE_NO_SELECTION_v0: NO_UNITS_OR_GAUGE_SELECTION",
    "EM_U1_NEW_PHYSICS_ASSUMPTION_ID_GATE_v0: CONSTITUTIVE_UNITS_GAUGE_FIXING_REQUIRE_IDS",
]

SEAM_PATTERNS = {
    "antisymmetry_statement": re.escape("F^{μν} = -F^{νμ}"),
    "commuting_partials_statement": re.escape("∂_μ∂_ν = ∂_ν∂_μ"),
    "double_divergence_statement": re.escape("∂_ν∂_μ F^{μν} = 0"),
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _strip_wrapping_backticks(text: str) -> str:
    s = text.strip()
    if s.startswith("`") and s.endswith("`") and len(s) >= 2:
        return s[1:-1]
    return s


def test_em_cycle017_artifacts_exist() -> None:
    assert STATE_PATH.exists(), "Missing State_of_the_Theory.md."
    assert EM_TARGET_PATH.exists(), "Missing EM U1 target document."
    assert EM_MICRO17_PATH.exists(), "Missing EM U1 Cycle-017 document."
    assert EM_ROADMAP_PATH.exists(), "Missing physics roadmap document."
    assert EM_OBJECT_SCAFFOLD_LEAN_PATH.exists(), "Missing EM U1 object scaffold Lean module."


def test_em_micro17_contains_required_tokens_and_localized_seam_statements() -> None:
    text = _read(EM_MICRO17_PATH)
    required_tokens = [
        "DERIVATION_TARGET_EM_U1_MICRO_17_DOUBLE_DIVERGENCE_ANTISYM_COMMUTATION_SEAM_v0",
        "TARGET-EM-U1-MICRO-17-DOUBLE-DIVERGENCE-ANTISYM-COMMUTATION-SEAM-v0",
        "EM_U1_PROGRESS_CYCLE17_v0: DOUBLE_DIVERGENCE_SEAM_TOKEN_PINNED",
        "EM_U1_DOUBLE_DIVERGENCE_SURFACE_v0: DD_F_ZERO_STATEMENT_PINNED",
        "EM_U1_ANTISYM_SURFACE_v0: F_ANTISYM_STATEMENT_PINNED",
        "EM_U1_COMMUTING_PARTIALS_SURFACE_v0: COMMUTATION_STATEMENT_PINNED",
        LOCALIZATION_TOKEN,
        "EM_U1_DOUBLE_DIVERGENCE_NO_DERIVATION_v0: STATEMENT_ONLY",
        "EM_U1_MICRO17_DOUBLE_DIVERGENCE_ADJUDICATION: NOT_YET_DISCHARGED",
        SOURCE_ASSUMPTION_ID,
        "formal/python/tests/test_em_u1_micro17_double_divergence_antisym_commutation_seam.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM Cycle-017 micro document is missing required token(s): " + ", ".join(missing)

    missing_patterns = [label for label, pattern in SEAM_PATTERNS.items() if re.search(pattern, text) is None]
    assert not missing_patterns, (
        "EM Cycle-017 micro document is missing required seam statement expression(s): "
        + ", ".join(missing_patterns)
    )


def test_em_target_references_cycle017_artifact_and_tokens() -> None:
    text = _read(EM_TARGET_PATH)
    required_tokens = [
        "TARGET-EM-U1-MICRO-17-DOUBLE-DIVERGENCE-ANTISYM-COMMUTATION-SEAM-v0",
        "EM_U1_PROGRESS_CYCLE17_v0: DOUBLE_DIVERGENCE_SEAM_TOKEN_PINNED",
        "EM_U1_DOUBLE_DIVERGENCE_SURFACE_v0: DD_F_ZERO_STATEMENT_PINNED",
        "EM_U1_ANTISYM_SURFACE_v0: F_ANTISYM_STATEMENT_PINNED",
        "EM_U1_COMMUTING_PARTIALS_SURFACE_v0: COMMUTATION_STATEMENT_PINNED",
        LOCALIZATION_TOKEN,
        "EM_U1_DOUBLE_DIVERGENCE_NO_DERIVATION_v0: STATEMENT_ONLY",
        "EM_U1_MICRO17_DOUBLE_DIVERGENCE_ADJUDICATION: NOT_YET_DISCHARGED",
        SOURCE_ASSUMPTION_ID,
        "formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_17_DOUBLE_DIVERGENCE_ANTISYM_COMMUTATION_SEAM_v0.md",
        "formal/python/tests/test_em_u1_micro17_double_divergence_antisym_commutation_seam.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM target document is missing required Cycle-017 token(s): " + ", ".join(missing)


def test_em_roadmap_references_cycle017_target_and_artifact_with_single_row() -> None:
    roadmap_text = _read(EM_ROADMAP_PATH)
    rows = [line.strip() for line in roadmap_text.splitlines() if line.strip().startswith("| `PILLAR-EM` |")]
    assert len(rows) == 1, f"Expected one `PILLAR-EM` roadmap row, found {len(rows)}."
    cells = [cell.strip() for cell in rows[0].split("|")]
    assert len(cells) >= 7, "Malformed `PILLAR-EM` roadmap row."
    targets_raw = _strip_wrapping_backticks(cells[3])
    artifacts_raw = _strip_wrapping_backticks(cells[4])
    targets = {item.strip() for item in targets_raw.split(";") if item.strip()}
    artifacts = {item.strip() for item in artifacts_raw.split(";") if item.strip()}
    assert "TARGET-EM-U1-MICRO-17-DOUBLE-DIVERGENCE-ANTISYM-COMMUTATION-SEAM-v0" in targets
    assert (
        "formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_17_DOUBLE_DIVERGENCE_ANTISYM_COMMUTATION_SEAM_v0.md"
        in artifacts
    )


def test_state_mentions_cycle017_checkpoint_and_tokens() -> None:
    text = _read(STATE_PATH)
    required_tokens = [
        "EM Cycle-017 double-divergence antisymmetry/commutation seam checkpoint",
        "TARGET-EM-U1-MICRO-17-DOUBLE-DIVERGENCE-ANTISYM-COMMUTATION-SEAM-v0",
        "EM_U1_PROGRESS_CYCLE17_v0: DOUBLE_DIVERGENCE_SEAM_TOKEN_PINNED",
        "EM_U1_DOUBLE_DIVERGENCE_SURFACE_v0: DD_F_ZERO_STATEMENT_PINNED",
        "EM_U1_ANTISYM_SURFACE_v0: F_ANTISYM_STATEMENT_PINNED",
        "EM_U1_COMMUTING_PARTIALS_SURFACE_v0: COMMUTATION_STATEMENT_PINNED",
        LOCALIZATION_TOKEN,
        "EM_U1_DOUBLE_DIVERGENCE_NO_DERIVATION_v0: STATEMENT_ONLY",
        "EM_U1_MICRO17_DOUBLE_DIVERGENCE_ADJUDICATION: NOT_YET_DISCHARGED",
        SOURCE_ASSUMPTION_ID,
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "State_of_the_Theory.md is missing required Cycle-017 token(s): " + ", ".join(missing)


def test_em_lean_cycle017_tokens_and_harness_stubs_are_pinned() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    required_tokens = [
        "structure DoubleDivergenceSeam where",
        "def doubleDivergenceSeamHarness",
        "EM_U1_PROGRESS_CYCLE17_v0: DOUBLE_DIVERGENCE_SEAM_TOKEN_PINNED",
        "EM_U1_DOUBLE_DIVERGENCE_SURFACE_v0: DD_F_ZERO_STATEMENT_PINNED",
        "EM_U1_ANTISYM_SURFACE_v0: F_ANTISYM_STATEMENT_PINNED",
        "EM_U1_COMMUTING_PARTIALS_SURFACE_v0: COMMUTATION_STATEMENT_PINNED",
        LOCALIZATION_TOKEN,
        "EM_U1_DOUBLE_DIVERGENCE_NO_DERIVATION_v0: STATEMENT_ONLY",
        "theorem em_u1_cycle017_token_binding_stub_v0",
        "theorem em_u1_cycle017_double_divergence_harness_stub_v0",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM U1 Lean scaffold is missing required Cycle-017 token(s): " + ", ".join(missing)


def test_cycle017_seam_statements_are_localized_to_cycle17_artifact() -> None:
    allowed_paths = [EM_MICRO17_PATH]
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
        EM_MICRO13_PATH,
        EM_MICRO14_PATH,
        EM_MICRO15_PATH,
        EM_MICRO16_PATH,
        EM_ROADMAP_PATH,
        STATE_PATH,
        EM_OBJECT_SCAFFOLD_LEAN_PATH,
    ]

    violations: list[str] = []

    for path in allowed_paths:
        text = _read(path)
        hits = [label for label, pattern in SEAM_PATTERNS.items() if re.search(pattern, text)]
        if not hits:
            violations.append(f"cycle017 artifact {path.relative_to(REPO_ROOT)} is missing localized seam expressions")
            continue
        has_assumption_id = SOURCE_ASSUMPTION_ID in text
        has_localization_gate = LOCALIZATION_TOKEN in text
        has_prereq = all(token in text for token in PREREQUISITE_TOKENS)
        has_non_selection = all(token in text for token in NON_SELECTION_TOKENS)
        if not (has_assumption_id and has_localization_gate and has_prereq and has_non_selection):
            violations.append(
                f"cycle017 artifact {path.relative_to(REPO_ROOT)} contains seam expressions {hits} "
                "without source assumption ID + localization token + prerequisites + non-selection tokens."
            )

    for path in scoped_paths:
        text = _read(path)
        for label, pattern in SEAM_PATTERNS.items():
            if not re.search(pattern, text):
                continue
            if path == EM_MICRO16_PATH and label == "double_divergence_statement":
                has_assumption_id = SOURCE_ASSUMPTION_ID in text
                has_cycle16_localization = CYCLE16_LOCALIZATION_TOKEN in text
                if has_assumption_id and has_cycle16_localization:
                    continue
            violations.append(
                f"{label} seam expression leaked into non-authorized artifact "
                f"{path.relative_to(REPO_ROOT)}"
            )

    assert not violations, "Cycle-017 seam localization violation:\n- " + "\n- ".join(violations)


def test_cycle017_is_statement_only_and_blocks_derivation_or_new_physics_selection_language() -> None:
    text = _read(EM_MICRO17_PATH)
    forbidden_patterns = [
        r"\bwe derive\b",
        r"\bwe prove\b",
        r"\btherefore\b",
        r"\bfollows from Maxwell\b",
        r"\bfollows from Bianchi\b",
        r"\bfollows from gauge invariance\b",
        r"\bderived from Maxwell\b",
        r"\bproves that\b",
        r"\bclosure is proven\b",
        r"\btheorem-level closure\b",
        r"\bT-PROVED\b",
        r"\bDISCHARGED_v0\b",
        r"∇_μ\s*J\^μ\s*=\s*0",
        r"\bcovariant divergence\b",
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
        "Cycle-017 must remain statement-only/non-derivational with no import-lane selections. "
        "Forbidden pattern(s) found: "
        + ", ".join(violations)
    )

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
ASSUMPTION_REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "ASSUMPTION_REGISTRY_v1.md"
EM_MICRO01_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_EM_U1_MICRO_01_OBJECT_SCAFFOLD_v0.md"
EM_MICRO02_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_EM_U1_MICRO_02_GAUGE_CONTRACT_SURFACE_v0.md"
EM_MICRO03_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_EM_U1_MICRO_03_PREDISCHARGE_GATE_BUNDLE_v0.md"
EM_MICRO04_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_EM_U1_MICRO_04_MAXWELL_FORM_ATTEMPT_PACKAGE_v0.md"
EM_MICRO05_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_EM_U1_MICRO_05_MAXWELL_FORM_SEMANTICS_MAPPING_v0.md"
EM_MICRO06_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_EM_U1_MICRO_06_CONVENTION_LOCK_3P1_v0.md"
EM_MICRO07_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_EM_U1_MICRO_07_IMPORT_LANES_PLACEHOLDERS_v0.md"
EM_MICRO08_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_EM_U1_MICRO_08_IMPORT_LANES_INTERFACE_CONTRACTS_v0.md"
EM_MICRO09_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_EM_U1_MICRO_09_DUAL_HODGE_CONVENTION_LOCK_v0.md"
EM_MICRO10_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_EM_U1_MICRO_10_SOURCE_CURRENT_INTERFACE_CONTRACTS_v0.md"
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
EM_MICRO18_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_EM_U1_MICRO_18_MAXWELL_TO_CONTINUITY_THEOREM_ATTEMPT_PACKAGE_v0.md"
)
EM_MICRO19_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_EM_U1_MICRO_19_SMOOTHNESS_WEAKENING_NEGCONTROL_v0.md"
)
EM_MICRO20_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_EM_U1_MICRO_20_DISTRIBUTIONAL_SINGULAR_SOURCE_NEGCONTROL_v0.md"
)
EM_MICRO21_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_EM_U1_MICRO_21_DISTRIBUTIONAL_LANE_AUTHORIZATION_SCAFFOLD_v0.md"
)
EM_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
EM_OBJECT_SCAFFOLD_LEAN_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "EM" / "U1" / "ObjectScaffold.lean"

SOURCE_ASSUMPTION_ID = "ASM-EM-U1-PHY-SOURCE-01"
SMOOTHNESS_ASSUMPTION_ID = "ASM-EM-U1-MATH-SMOOTH-01"
DISTRIB_ASSUMPTION_ID = "ASM-EM-U1-MATH-DISTRIB-01"
LOCALIZATION_TOKEN = "EM_U1_DISTRIBUTIONAL_LANE_AUTHORIZATION_LOCALIZATION_GATE_v0: CYCLE21_ARTIFACTS_ONLY"
PREREQUISITE_TOKENS = [
    "EM_U1_MAXWELL_CONTINUITY_THEOREM_ROUTE_v0: DIVERGENCE_ANTISYM_COMMUTATION_ATTEMPT_PINNED",
    "EM_U1_MAXWELL_CONTINUITY_THEOREM_SMOOTHNESS_SEAM_v0: C2_REGULARITY_REQUIRED",
    "EM_U1_DISTRIBUTIONAL_SINGULAR_SOURCE_NEGCONTROL_ROUTE_v0: SINGULAR_SOURCE_WITHOUT_DISTRIBUTIONAL_LANE_UNLICENSES_ROUTE",
    "EM_U1_MAXWELL_CONTINUITY_ROUTE_v0: DIVERGENCE_OF_INHOM_SURFACE_ROUTE_PINNED",
]
NON_SELECTION_TOKENS = [
    "EM_U1_IMPORT_LANES_INTERFACE_NO_SELECTION_v0: NO_UNITS_OR_GAUGE_SELECTION",
    "EM_U1_NEW_PHYSICS_ASSUMPTION_ID_GATE_v0: CONSTITUTIVE_UNITS_GAUGE_FIXING_REQUIRE_IDS",
]

AUTHORIZATION_PATTERNS = {
    "authz_lane_id": re.escape("AUTHZ_LANE_ID: ASM-EM-U1-MATH-DISTRIB-01"),
    "authz_scope": re.escape("AUTHZ_SCOPE: DISTRIBUTIONAL_FORMALIZATION_IMPORTS_REQUIRE_ID_AND_LOCALIZATION"),
    "authz_outcome": re.escape("AUTHZ_OUTCOME: IMPORTS_NOT_LICENSED_WITHOUT_AUTHORIZATION_LANE"),
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _strip_wrapping_backticks(text: str) -> str:
    s = text.strip()
    if s.startswith("`") and s.endswith("`") and len(s) >= 2:
        return s[1:-1]
    return s


def test_em_cycle021_artifacts_exist() -> None:
    assert STATE_PATH.exists(), "Missing State_of_the_Theory.md."
    assert EM_TARGET_PATH.exists(), "Missing EM U1 target document."
    assert ASSUMPTION_REGISTRY_PATH.exists(), "Missing assumption registry document."
    assert EM_MICRO21_PATH.exists(), "Missing EM U1 Cycle-021 document."
    assert EM_ROADMAP_PATH.exists(), "Missing physics roadmap document."
    assert EM_OBJECT_SCAFFOLD_LEAN_PATH.exists(), "Missing EM U1 object scaffold Lean module."


def test_em_micro21_contains_required_tokens_and_localized_authorization_statements() -> None:
    text = _read(EM_MICRO21_PATH)
    required_tokens = [
        "DERIVATION_TARGET_EM_U1_MICRO_21_DISTRIBUTIONAL_LANE_AUTHORIZATION_SCAFFOLD_v0",
        "TARGET-EM-U1-MICRO-21-DISTRIBUTIONAL-LANE-AUTHORIZATION-SCAFFOLD-v0",
        "EM_U1_PROGRESS_CYCLE21_v0: DISTRIBUTIONAL_LANE_AUTHORIZATION_SCAFFOLD_TOKEN_PINNED",
        "EM_U1_DISTRIBUTIONAL_LANE_AUTHORIZATION_ROUTE_v0: ASSUMPTION_ID_GATED_IMPORT_PERMISSION_PINNED",
        LOCALIZATION_TOKEN,
        "EM_U1_DISTRIBUTIONAL_LANE_AUTHORIZATION_NO_PROMOTION_v0: AUTHORIZATION_ONLY_NO_DISCHARGE",
        "EM_U1_DISTRIBUTIONAL_LANE_AUTHORIZATION_BOUNDARY_v0: NO_DISTRIBUTIONAL_MATH_OR_CURVED_SPACE_IMPORT",
        "EM_U1_MICRO21_DISTRIBUTIONAL_AUTHORIZATION_ADJUDICATION: NOT_YET_DISCHARGED",
        SOURCE_ASSUMPTION_ID,
        SMOOTHNESS_ASSUMPTION_ID,
        DISTRIB_ASSUMPTION_ID,
        "formal/python/tests/test_em_u1_micro21_distributional_lane_authorization_scaffold.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM Cycle-021 micro document is missing required token(s): " + ", ".join(missing)

    missing_patterns = [label for label, pattern in AUTHORIZATION_PATTERNS.items() if re.search(pattern, text) is None]
    assert not missing_patterns, (
        "EM Cycle-021 micro document is missing required authorization seam statement(s): "
        + ", ".join(missing_patterns)
    )


def test_em_target_references_cycle021_artifact_and_tokens() -> None:
    text = _read(EM_TARGET_PATH)
    required_tokens = [
        "TARGET-EM-U1-MICRO-21-DISTRIBUTIONAL-LANE-AUTHORIZATION-SCAFFOLD-v0",
        "EM_U1_PROGRESS_CYCLE21_v0: DISTRIBUTIONAL_LANE_AUTHORIZATION_SCAFFOLD_TOKEN_PINNED",
        "EM_U1_DISTRIBUTIONAL_LANE_AUTHORIZATION_ROUTE_v0: ASSUMPTION_ID_GATED_IMPORT_PERMISSION_PINNED",
        LOCALIZATION_TOKEN,
        "EM_U1_DISTRIBUTIONAL_LANE_AUTHORIZATION_NO_PROMOTION_v0: AUTHORIZATION_ONLY_NO_DISCHARGE",
        "EM_U1_DISTRIBUTIONAL_LANE_AUTHORIZATION_BOUNDARY_v0: NO_DISTRIBUTIONAL_MATH_OR_CURVED_SPACE_IMPORT",
        "EM_U1_MICRO21_DISTRIBUTIONAL_AUTHORIZATION_ADJUDICATION: NOT_YET_DISCHARGED",
        SOURCE_ASSUMPTION_ID,
        SMOOTHNESS_ASSUMPTION_ID,
        DISTRIB_ASSUMPTION_ID,
        "formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_21_DISTRIBUTIONAL_LANE_AUTHORIZATION_SCAFFOLD_v0.md",
        "formal/python/tests/test_em_u1_micro21_distributional_lane_authorization_scaffold.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM target document is missing required Cycle-021 token(s): " + ", ".join(missing)


def test_em_roadmap_references_cycle021_target_and_artifact_with_single_row() -> None:
    roadmap_text = _read(EM_ROADMAP_PATH)
    rows = [line.strip() for line in roadmap_text.splitlines() if line.strip().startswith("| `PILLAR-EM` |")]
    assert len(rows) == 1, f"Expected one `PILLAR-EM` roadmap row, found {len(rows)}."
    cells = [cell.strip() for cell in rows[0].split("|")]
    assert len(cells) >= 7, "Malformed `PILLAR-EM` roadmap row."
    targets_raw = _strip_wrapping_backticks(cells[3])
    artifacts_raw = _strip_wrapping_backticks(cells[4])
    targets = {item.strip() for item in targets_raw.split(";") if item.strip()}
    artifacts = {item.strip() for item in artifacts_raw.split(";") if item.strip()}
    assert "TARGET-EM-U1-MICRO-21-DISTRIBUTIONAL-LANE-AUTHORIZATION-SCAFFOLD-v0" in targets
    assert "formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_21_DISTRIBUTIONAL_LANE_AUTHORIZATION_SCAFFOLD_v0.md" in artifacts


def test_state_mentions_cycle021_checkpoint_and_tokens() -> None:
    text = _read(STATE_PATH)
    required_tokens = [
        "EM Cycle-021 distributional lane authorization scaffold checkpoint",
        "TARGET-EM-U1-MICRO-21-DISTRIBUTIONAL-LANE-AUTHORIZATION-SCAFFOLD-v0",
        "EM_U1_PROGRESS_CYCLE21_v0: DISTRIBUTIONAL_LANE_AUTHORIZATION_SCAFFOLD_TOKEN_PINNED",
        "EM_U1_DISTRIBUTIONAL_LANE_AUTHORIZATION_ROUTE_v0: ASSUMPTION_ID_GATED_IMPORT_PERMISSION_PINNED",
        LOCALIZATION_TOKEN,
        "EM_U1_DISTRIBUTIONAL_LANE_AUTHORIZATION_NO_PROMOTION_v0: AUTHORIZATION_ONLY_NO_DISCHARGE",
        "EM_U1_DISTRIBUTIONAL_LANE_AUTHORIZATION_BOUNDARY_v0: NO_DISTRIBUTIONAL_MATH_OR_CURVED_SPACE_IMPORT",
        "EM_U1_MICRO21_DISTRIBUTIONAL_AUTHORIZATION_ADJUDICATION: NOT_YET_DISCHARGED",
        SOURCE_ASSUMPTION_ID,
        SMOOTHNESS_ASSUMPTION_ID,
        DISTRIB_ASSUMPTION_ID,
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "State_of_the_Theory.md is missing required Cycle-021 token(s): " + ", ".join(missing)


def test_assumption_registry_contains_cycle021_distributional_lane() -> None:
    text = _read(ASSUMPTION_REGISTRY_PATH)
    required_tokens = [
        DISTRIB_ASSUMPTION_ID,
        "em_u1_distributional_lane_authorization_scaffold_v0",
        "distributional/singular-source formalization import requires explicit assumption-ID gating and Cycle-021 localization",
        "formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_21_DISTRIBUTIONAL_LANE_AUTHORIZATION_SCAFFOLD_v0.md",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "Assumption registry is missing Cycle-021 distributional lane sync token(s): " + ", ".join(missing)


def test_em_lean_cycle021_tokens_and_authorization_harness_stubs_are_pinned() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    required_tokens = [
        "structure DistributionalLaneAuthorizationPackage where",
        "def distributionalLaneAuthorizationHarness",
        "EM_U1_PROGRESS_CYCLE21_v0: DISTRIBUTIONAL_LANE_AUTHORIZATION_SCAFFOLD_TOKEN_PINNED",
        "EM_U1_DISTRIBUTIONAL_LANE_AUTHORIZATION_ROUTE_v0: ASSUMPTION_ID_GATED_IMPORT_PERMISSION_PINNED",
        LOCALIZATION_TOKEN,
        "EM_U1_DISTRIBUTIONAL_LANE_AUTHORIZATION_NO_PROMOTION_v0: AUTHORIZATION_ONLY_NO_DISCHARGE",
        "EM_U1_DISTRIBUTIONAL_LANE_AUTHORIZATION_BOUNDARY_v0: NO_DISTRIBUTIONAL_MATH_OR_CURVED_SPACE_IMPORT",
        "theorem em_u1_cycle021_token_binding_stub_v0",
        "theorem em_u1_cycle021_authorization_harness_stub_v0",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM U1 Lean scaffold is missing required Cycle-021 token(s): " + ", ".join(missing)


def test_cycle021_authorization_statements_are_localized_to_cycle21_artifact() -> None:
    allowed_paths = [EM_MICRO21_PATH]
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
        EM_MICRO17_PATH,
        EM_MICRO18_PATH,
        EM_MICRO19_PATH,
        EM_MICRO20_PATH,
        EM_ROADMAP_PATH,
        STATE_PATH,
        ASSUMPTION_REGISTRY_PATH,
        EM_OBJECT_SCAFFOLD_LEAN_PATH,
    ]

    violations: list[str] = []

    for path in allowed_paths:
        text = _read(path)
        hits = [label for label, pattern in AUTHORIZATION_PATTERNS.items() if re.search(pattern, text)]
        if not hits:
            violations.append(f"cycle021 artifact {path.relative_to(REPO_ROOT)} is missing localized authorization statements")
            continue
        has_source_assumption_id = SOURCE_ASSUMPTION_ID in text
        has_smoothness_assumption_id = SMOOTHNESS_ASSUMPTION_ID in text
        has_distrib_assumption_id = DISTRIB_ASSUMPTION_ID in text
        has_localization_gate = LOCALIZATION_TOKEN in text
        has_prereq = all(token in text for token in PREREQUISITE_TOKENS)
        has_non_selection = all(token in text for token in NON_SELECTION_TOKENS)
        if not (
            has_source_assumption_id
            and has_smoothness_assumption_id
            and has_distrib_assumption_id
            and has_localization_gate
            and has_prereq
            and has_non_selection
        ):
            violations.append(
                f"cycle021 artifact {path.relative_to(REPO_ROOT)} contains authorization statements {hits} "
                "without required source/smoothness/distributional assumption IDs + localization token + prerequisites + non-selection tokens."
            )

    for path in scoped_paths:
        text = _read(path)
        for label, pattern in AUTHORIZATION_PATTERNS.items():
            if re.search(pattern, text):
                violations.append(
                    f"{label} authorization statement leaked into non-authorized artifact "
                    f"{path.relative_to(REPO_ROOT)}"
                )

    assert not violations, "Cycle-021 authorization localization violation:\n- " + "\n- ".join(violations)


def test_cycle021_is_authorization_only_and_blocks_distributional_math_or_promotion() -> None:
    text = _read(EM_MICRO21_PATH)
    forbidden_patterns = [
        r"\bwe derive\b",
        r"\bwe prove\b",
        r"\btherefore\b",
        r"\bproves that\b",
        r"\bclosure is proven\b",
        r"\btheorem-level closure\b",
        r"\bT-PROVED\b",
        r"\bDISCHARGED_v0\b",
        r"\bdistributional derivative\b",
        r"\bdistributional equation\b",
        r"\bweak solution\b",
        r"\btempered distribution\b",
        r"\bDirac delta\b",
        r"\bdelta-function\b",
        r"∇_μ\s*J\^μ\s*=\s*0",
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
        "Cycle-021 must remain authorization-only/non-promotional with no distributional-math import. "
        "Forbidden pattern(s) found: "
        + ", ".join(violations)
    )

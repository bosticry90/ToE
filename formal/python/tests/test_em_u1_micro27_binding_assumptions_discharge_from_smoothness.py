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
EM_MICRO27_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_EM_U1_MICRO_27_BINDING_ASSUMPTIONS_DISCHARGE_FROM_SMOOTHNESS_v0.md"
)
EM_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
EM_OBJECT_SCAFFOLD_LEAN_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "EM" / "U1" / "ObjectScaffold.lean"

SOURCE_ASSUMPTION_ID = "ASM-EM-U1-PHY-SOURCE-01"
SMOOTHNESS_ASSUMPTION_ID = "ASM-EM-U1-MATH-SMOOTH-01"
DISTRIB_ASSUMPTION_ID = "ASM-EM-U1-MATH-DISTRIB-01"
LOCALIZATION_TOKEN = "EM_U1_BINDING_ASSUMPTIONS_DISCHARGE_LOCALIZATION_GATE_v0: CYCLE27_ARTIFACTS_ONLY"
PREREQUISITE_TOKENS = [
    "EM_U1_PROGRESS_CYCLE25_v0: DOUBLE_DIVERGENCE_THEOREM_CLOSURE_ATTEMPT_TOKEN_PINNED",
    "EM_U1_DOUBLE_DIVERGENCE_THEOREM_CLOSURE_ROUTE_v0: ANTISYM_COMMUTATION_THEOREM_SURFACE_PINNED",
    "EM_U1_DOUBLE_DIVERGENCE_THEOREM_CLOSURE_LOCALIZATION_GATE_v0: CYCLE25_ARTIFACTS_ONLY",
    "EM_U1_DOUBLE_DIVERGENCE_THEOREM_CLOSURE_NO_PROMOTION_v0: ATTEMPT_ONLY_NO_DISCHARGE",
    "EM_U1_DOUBLE_DIVERGENCE_THEOREM_CLOSURE_BOUNDARY_v0: NO_FULL_DERIVATION_DISCHARGE_OR_INEVITABILITY_PROMOTION",
    "EM_U1_PROGRESS_CYCLE26_v0: DOUBLE_DIVERGENCE_BINDING_THEOREM_CLOSURE_ATTEMPT_TOKEN_PINNED",
    "EM_U1_DOUBLE_DIVERGENCE_BINDING_THEOREM_ROUTE_v0: DD_FROM_FIELD_STRENGTH_BINDING_ROUTE_PINNED",
    "EM_U1_DOUBLE_DIVERGENCE_BINDING_THEOREM_LOCALIZATION_GATE_v0: CYCLE26_ARTIFACTS_ONLY",
    "EM_U1_DOUBLE_DIVERGENCE_BINDING_THEOREM_NO_PROMOTION_v0: ATTEMPT_ONLY_NO_DISCHARGE",
    "EM_U1_DOUBLE_DIVERGENCE_BINDING_THEOREM_BOUNDARY_v0: NO_FULL_DERIVATION_DISCHARGE_OR_INEVITABILITY_PROMOTION",
    "EM_U1_DOUBLE_DIVERGENCE_SURFACE_v0: DD_F_ZERO_STATEMENT_PINNED",
    "EM_U1_ANTISYM_SURFACE_v0: F_ANTISYM_STATEMENT_PINNED",
    "EM_U1_COMMUTING_PARTIALS_SURFACE_v0: COMMUTATION_STATEMENT_PINNED",
    "EM_U1_DISTRIBUTIONAL_LANE_AUTHORIZATION_ROUTE_v0: ASSUMPTION_ID_GATED_IMPORT_PERMISSION_PINNED",
    "EM_U1_DISTRIBUTIONAL_SEMANTICS_MAPPING_ROUTE_v0: CLASSIFICATION_SURFACES_PINNED",
    "EM_U1_DISTRIBUTIONAL_REFERENCE_SURFACE_ROUTE_v0: REFERENCE_ONLY_SEMANTICS_PINNED",
]
NON_SELECTION_TOKENS = [
    "EM_U1_IMPORT_LANES_INTERFACE_NO_SELECTION_v0: NO_UNITS_OR_GAUGE_SELECTION",
    "EM_U1_NEW_PHYSICS_ASSUMPTION_ID_GATE_v0: CONSTITUTIVE_UNITS_GAUGE_FIXING_REQUIRE_IDS",
]

BINDING_DISCHARGE_PATTERNS = {
    "step_commuting_extract": re.escape(
        "BINDING_DISCHARGE_STEP_v0: EXTRACT_DD_COMMUTING_PARTIALS_FROM_SMOOTHNESS_LANE"
    ),
    "step_antisym_extract": re.escape(
        "BINDING_DISCHARGE_STEP_v0: EXTRACT_DD_ANTISYMMETRY_LIFT_FROM_DEFINITION_LANE"
    ),
    "step_build_binding": re.escape("BINDING_DISCHARGE_STEP_v0: BUILD_DD_BINDING_ASSUMPTIONS_OBJECT"),
    "step_apply_cycle26": re.escape(
        "BINDING_DISCHARGE_STEP_v0: APPLY_CYCLE26_THEOREM_WITH_BUILT_BINDING_OBJECT"
    ),
    "rule_attempt_only": re.escape(
        "BINDING_DISCHARGE_RULE_v0: REMAINS_ATTEMPT_ONLY_UNTIL_FULL_DISCHARGE_TARGET"
    ),
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _strip_wrapping_backticks(text: str) -> str:
    s = text.strip()
    if s.startswith("`") and s.endswith("`") and len(s) >= 2:
        return s[1:-1]
    return s


def _em_micro_docs_except_cycle27() -> list[Path]:
    docs = sorted((REPO_ROOT / "formal" / "docs" / "paper").glob("DERIVATION_TARGET_EM_U1_MICRO_*.md"))
    return [path for path in docs if path != EM_MICRO27_PATH]


def test_em_cycle027_artifacts_exist() -> None:
    assert STATE_PATH.exists(), "Missing State_of_the_Theory.md."
    assert EM_TARGET_PATH.exists(), "Missing EM U1 target document."
    assert ASSUMPTION_REGISTRY_PATH.exists(), "Missing assumption registry document."
    assert EM_MICRO27_PATH.exists(), "Missing EM U1 Cycle-027 document."
    assert EM_ROADMAP_PATH.exists(), "Missing physics roadmap document."
    assert EM_OBJECT_SCAFFOLD_LEAN_PATH.exists(), "Missing EM U1 object scaffold Lean module."


def test_em_micro27_contains_required_tokens_and_localized_binding_discharge_statements() -> None:
    text = _read(EM_MICRO27_PATH)
    required_tokens = [
        "DERIVATION_TARGET_EM_U1_MICRO_27_BINDING_ASSUMPTIONS_DISCHARGE_FROM_SMOOTHNESS_v0",
        "TARGET-EM-U1-MICRO-27-BINDING-ASSUMPTIONS-DISCHARGE-FROM-SMOOTHNESS-v0",
        "EM_U1_PROGRESS_CYCLE27_v0: BINDING_ASSUMPTIONS_DISCHARGE_FROM_SMOOTHNESS_TOKEN_PINNED",
        "EM_U1_BINDING_ASSUMPTIONS_DISCHARGE_ROUTE_v0: SMOOTHNESS_TO_BINDING_ASSUMPTIONS_ROUTE_PINNED",
        LOCALIZATION_TOKEN,
        "EM_U1_BINDING_ASSUMPTIONS_DISCHARGE_NO_PROMOTION_v0: ATTEMPT_ONLY_NO_DISCHARGE",
        "EM_U1_BINDING_ASSUMPTIONS_DISCHARGE_BOUNDARY_v0: NO_FULL_DERIVATION_DISCHARGE_OR_INEVITABILITY_PROMOTION",
        "EM_U1_MICRO27_BINDING_ASSUMPTIONS_DISCHARGE_ADJUDICATION: NOT_YET_DISCHARGED",
        SOURCE_ASSUMPTION_ID,
        SMOOTHNESS_ASSUMPTION_ID,
        DISTRIB_ASSUMPTION_ID,
        "formal/python/tests/test_em_u1_micro27_binding_assumptions_discharge_from_smoothness.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM Cycle-027 micro document is missing required token(s): " + ", ".join(missing)

    missing_patterns = [label for label, pattern in BINDING_DISCHARGE_PATTERNS.items() if re.search(pattern, text) is None]
    assert not missing_patterns, (
        "EM Cycle-027 micro document is missing required binding-discharge statement(s): "
        + ", ".join(missing_patterns)
    )


def test_em_target_references_cycle027_artifact_and_tokens() -> None:
    text = _read(EM_TARGET_PATH)
    required_tokens = [
        "TARGET-EM-U1-MICRO-27-BINDING-ASSUMPTIONS-DISCHARGE-FROM-SMOOTHNESS-v0",
        "EM_U1_PROGRESS_CYCLE27_v0: BINDING_ASSUMPTIONS_DISCHARGE_FROM_SMOOTHNESS_TOKEN_PINNED",
        "EM_U1_BINDING_ASSUMPTIONS_DISCHARGE_ROUTE_v0: SMOOTHNESS_TO_BINDING_ASSUMPTIONS_ROUTE_PINNED",
        LOCALIZATION_TOKEN,
        "EM_U1_BINDING_ASSUMPTIONS_DISCHARGE_NO_PROMOTION_v0: ATTEMPT_ONLY_NO_DISCHARGE",
        "EM_U1_BINDING_ASSUMPTIONS_DISCHARGE_BOUNDARY_v0: NO_FULL_DERIVATION_DISCHARGE_OR_INEVITABILITY_PROMOTION",
        "EM_U1_MICRO27_BINDING_ASSUMPTIONS_DISCHARGE_ADJUDICATION: NOT_YET_DISCHARGED",
        SOURCE_ASSUMPTION_ID,
        SMOOTHNESS_ASSUMPTION_ID,
        DISTRIB_ASSUMPTION_ID,
        "formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_27_BINDING_ASSUMPTIONS_DISCHARGE_FROM_SMOOTHNESS_v0.md",
        "formal/python/tests/test_em_u1_micro27_binding_assumptions_discharge_from_smoothness.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM target document is missing required Cycle-027 token(s): " + ", ".join(missing)


def test_em_roadmap_references_cycle027_target_and_artifact_with_single_row() -> None:
    roadmap_text = _read(EM_ROADMAP_PATH)
    rows = [line.strip() for line in roadmap_text.splitlines() if line.strip().startswith("| `PILLAR-EM` |")]
    assert len(rows) == 1, f"Expected one `PILLAR-EM` roadmap row, found {len(rows)}."
    cells = [cell.strip() for cell in rows[0].split("|")]
    assert len(cells) >= 7, "Malformed `PILLAR-EM` roadmap row."
    targets_raw = _strip_wrapping_backticks(cells[3])
    artifacts_raw = _strip_wrapping_backticks(cells[4])
    targets = {item.strip() for item in targets_raw.split(";") if item.strip()}
    artifacts = {item.strip() for item in artifacts_raw.split(";") if item.strip()}
    assert "TARGET-EM-U1-MICRO-27-BINDING-ASSUMPTIONS-DISCHARGE-FROM-SMOOTHNESS-v0" in targets
    assert (
        "formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_27_BINDING_ASSUMPTIONS_DISCHARGE_FROM_SMOOTHNESS_v0.md"
        in artifacts
    )


def test_state_mentions_cycle027_checkpoint_and_tokens() -> None:
    text = _read(STATE_PATH)
    required_tokens = [
        "EM Cycle-027 binding-assumptions discharge-from-smoothness checkpoint",
        "TARGET-EM-U1-MICRO-27-BINDING-ASSUMPTIONS-DISCHARGE-FROM-SMOOTHNESS-v0",
        "EM_U1_PROGRESS_CYCLE27_v0: BINDING_ASSUMPTIONS_DISCHARGE_FROM_SMOOTHNESS_TOKEN_PINNED",
        "EM_U1_BINDING_ASSUMPTIONS_DISCHARGE_ROUTE_v0: SMOOTHNESS_TO_BINDING_ASSUMPTIONS_ROUTE_PINNED",
        LOCALIZATION_TOKEN,
        "EM_U1_BINDING_ASSUMPTIONS_DISCHARGE_NO_PROMOTION_v0: ATTEMPT_ONLY_NO_DISCHARGE",
        "EM_U1_BINDING_ASSUMPTIONS_DISCHARGE_BOUNDARY_v0: NO_FULL_DERIVATION_DISCHARGE_OR_INEVITABILITY_PROMOTION",
        "EM_U1_MICRO27_BINDING_ASSUMPTIONS_DISCHARGE_ADJUDICATION: NOT_YET_DISCHARGED",
        SOURCE_ASSUMPTION_ID,
        SMOOTHNESS_ASSUMPTION_ID,
        DISTRIB_ASSUMPTION_ID,
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "State_of_the_Theory.md is missing required Cycle-027 token(s): " + ", ".join(missing)


def test_assumption_registry_contains_required_source_smoothness_distributional_lanes() -> None:
    text = _read(ASSUMPTION_REGISTRY_PATH)
    required_tokens = [
        SOURCE_ASSUMPTION_ID,
        SMOOTHNESS_ASSUMPTION_ID,
        DISTRIB_ASSUMPTION_ID,
        "em_u1_maxwell_to_continuity_theorem_attempt_v0",
        "em_u1_distributional_lane_authorization_scaffold_v0",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, (
        "Assumption registry is missing required source/smoothness/distributional lane token(s): "
        + ", ".join(missing)
    )


def test_em_lean_cycle027_tokens_theorem_surfaces_and_harness_stubs_are_pinned() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    required_tokens = [
        "structure BindingAssumptionsDischargeFromSmoothnessPackage where",
        "def bindingAssumptionsDischargeFromSmoothnessHarness",
        "structure DoubleDivergenceSmoothnessLaneAssumptions",
        "EM_U1_PROGRESS_CYCLE27_v0: BINDING_ASSUMPTIONS_DISCHARGE_FROM_SMOOTHNESS_TOKEN_PINNED",
        "EM_U1_BINDING_ASSUMPTIONS_DISCHARGE_ROUTE_v0: SMOOTHNESS_TO_BINDING_ASSUMPTIONS_ROUTE_PINNED",
        LOCALIZATION_TOKEN,
        "EM_U1_BINDING_ASSUMPTIONS_DISCHARGE_NO_PROMOTION_v0: ATTEMPT_ONLY_NO_DISCHARGE",
        "EM_U1_BINDING_ASSUMPTIONS_DISCHARGE_BOUNDARY_v0: NO_FULL_DERIVATION_DISCHARGE_OR_INEVITABILITY_PROMOTION",
        "theorem em_u1_cycle027_dd_commuting_partials_from_smoothness_v0",
        "theorem em_u1_cycle027_dd_antisymmetry_lift_from_definition_v0",
        "theorem em_u1_cycle027_build_binding_assumptions_v0",
        "theorem em_u1_cycle027_double_divergence_zero_via_built_binding_v0",
        "theorem em_u1_cycle027_token_binding_stub_v0",
        "theorem em_u1_cycle027_binding_discharge_harness_stub_v0",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM U1 Lean scaffold is missing required Cycle-027 token(s): " + ", ".join(missing)


def test_cycle027_uses_cycle026_theorem_surface() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    assert (
        "em_u1_cycle026_double_divergence_zero_for_field_strength_v0" in text
    ), "Cycle-027 must reference the Cycle-026 theorem surface."


def test_cycle027_binding_discharge_statements_are_localized_to_cycle27_artifact() -> None:
    allowed_paths = [EM_MICRO27_PATH]
    scoped_paths = _em_micro_docs_except_cycle27() + [
        EM_TARGET_PATH,
        EM_ROADMAP_PATH,
        STATE_PATH,
        ASSUMPTION_REGISTRY_PATH,
        EM_OBJECT_SCAFFOLD_LEAN_PATH,
    ]

    violations: list[str] = []

    for path in allowed_paths:
        text = _read(path)
        hits = [label for label, pattern in BINDING_DISCHARGE_PATTERNS.items() if re.search(pattern, text)]
        if not hits:
            violations.append(
                f"cycle027 artifact {path.relative_to(REPO_ROOT)} is missing localized binding-discharge statements"
            )
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
                f"cycle027 artifact {path.relative_to(REPO_ROOT)} contains binding-discharge statements {hits} "
                "without required source/smoothness/distributional assumption IDs + localization token + prerequisites + non-selection tokens."
            )

    for path in scoped_paths:
        text = _read(path)
        for label, pattern in BINDING_DISCHARGE_PATTERNS.items():
            if re.search(pattern, text):
                violations.append(
                    f"{label} binding-discharge statement leaked into non-authorized artifact "
                    f"{path.relative_to(REPO_ROOT)}"
                )

    assert not violations, "Cycle-027 binding-discharge localization violation:\n- " + "\n- ".join(violations)


def test_cycle027_is_attempt_only_and_blocks_promotion_or_new_physics_selection_language() -> None:
    text = _read(EM_MICRO27_PATH)
    forbidden_patterns = [
        r"\bwe derive\b",
        r"\bwe prove\b",
        r"\btherefore\b",
        r"\bproves that\b",
        r"\bclosure is proven\b",
        r"\btheorem-level closure\b",
        r"\bT-PROVED\b",
        r"\bDISCHARGED_v0\b",
        r"\bFULL_DERIVATION_ADJUDICATION\b",
        r"\bTARGET-EM-U1-FULL-DERIVATION-DISCHARGE-v0\b",
        r"\bPILLAR-EM\b.*\bCLOSED\b",
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
        "Cycle-027 must remain theorem-binding-assumption-discharge-attempt-only/non-promotional and non-selecting. "
        "Forbidden pattern(s) found: "
        + ", ".join(violations)
    )

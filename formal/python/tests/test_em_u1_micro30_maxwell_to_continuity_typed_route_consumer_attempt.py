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
EM_MICRO30_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_EM_U1_MICRO_30_MAXWELL_TO_CONTINUITY_TYPED_ROUTE_CONSUMER_ATTEMPT_v0.md"
)
EM_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
EM_OBJECT_SCAFFOLD_LEAN_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "EM" / "U1" / "ObjectScaffold.lean"

SOURCE_ASSUMPTION_ID = "ASM-EM-U1-PHY-SOURCE-01"
SMOOTHNESS_ASSUMPTION_ID = "ASM-EM-U1-MATH-SMOOTH-01"
DISTRIB_ASSUMPTION_ID = "ASM-EM-U1-MATH-DISTRIB-01"
LOCALIZATION_TOKEN = "EM_U1_MAXWELL_CONTINUITY_TYPED_ROUTE_CONSUMER_LOCALIZATION_GATE_v0: CYCLE30_ARTIFACTS_ONLY"
PREREQUISITE_TOKENS = [
    "EM_U1_PROGRESS_CYCLE29_v0: MAXWELL_CONTINUITY_TYPED_DD_SUBROUTE_AUGMENTATION_ATTEMPT_TOKEN_PINNED",
    "EM_U1_MAXWELL_CONTINUITY_TYPED_DD_SUBROUTE_AUGMENTATION_ROUTE_v0: BUILD_TYPED_ROUTE_WITH_DD_SUBSTEP_OBJECT_PINNED",
    "EM_U1_MAXWELL_CONTINUITY_TYPED_DD_SUBROUTE_AUGMENTATION_LOCALIZATION_GATE_v0: CYCLE29_ARTIFACTS_ONLY",
    "EM_U1_MAXWELL_CONTINUITY_TYPED_DD_SUBROUTE_AUGMENTATION_NO_PROMOTION_v0: ATTEMPT_ONLY_NO_DISCHARGE",
    "EM_U1_MAXWELL_CONTINUITY_TYPED_DD_SUBROUTE_AUGMENTATION_BOUNDARY_v0: NO_FULL_DERIVATION_DISCHARGE_OR_INEVITABILITY_PROMOTION",
    "EM_U1_PROGRESS_CYCLE28_v0: MAXWELL_CONTINUITY_DD_SUBROUTE_COMPOSITION_ATTEMPT_TOKEN_PINNED",
    "EM_U1_MAXWELL_CONTINUITY_DD_SUBROUTE_COMPOSITION_ROUTE_v0: CYCLE27_DD_ZERO_SUBROUTE_ROUTE_PINNED",
    "EM_U1_CYCLE029_CYCLE028_THEOREM_SURFACE_USAGE_GUARD_v0: MUST_REFERENCE_em_u1_cycle028_maxwell_continuity_dd_subroute_composition_v0",
    "EM_U1_CYCLE030_CYCLE029_THEOREM_SURFACE_USAGE_GUARD_v0: MUST_REFERENCE_em_u1_cycle029_build_typed_route_with_dd_substep_object_v0",
    "EM_U1_CYCLE030_TYPED_OBJECT_CONSUMPTION_GUARD_v0: MUST_CONSUME_MaxwellToContinuityRouteWithDdSubstepAttempt_ONLY",
    "EM_U1_MAXWELL_CONTINUITY_ROUTE_CLOSURE_ATTEMPT_v0: CANONICAL_ROUTE_CLOSURE_ATTEMPT_PINNED",
    "EM_U1_DOUBLE_DIVERGENCE_SURFACE_v0: DD_F_ZERO_STATEMENT_PINNED",
    "EM_U1_ANTISYM_SURFACE_v0: F_ANTISYM_STATEMENT_PINNED",
    "EM_U1_COMMUTING_PARTIALS_SURFACE_v0: COMMUTATION_STATEMENT_PINNED",
    "EM_U1_CONTINUITY_TENSOR_SURFACE_v0: DIVERGENCE_CURRENT_STATEMENT_PINNED",
    "EM_U1_DISTRIBUTIONAL_LANE_AUTHORIZATION_ROUTE_v0: ASSUMPTION_ID_GATED_IMPORT_PERMISSION_PINNED",
    "EM_U1_DISTRIBUTIONAL_SEMANTICS_MAPPING_ROUTE_v0: CLASSIFICATION_SURFACES_PINNED",
    "EM_U1_DISTRIBUTIONAL_REFERENCE_SURFACE_ROUTE_v0: REFERENCE_ONLY_SEMANTICS_PINNED",
]
NON_SELECTION_TOKENS = [
    "EM_U1_IMPORT_LANES_INTERFACE_NO_SELECTION_v0: NO_UNITS_OR_GAUGE_SELECTION",
    "EM_U1_NEW_PHYSICS_ASSUMPTION_ID_GATE_v0: CONSTITUTIVE_UNITS_GAUGE_FIXING_REQUIRE_IDS",
]

TYPED_ROUTE_CONSUMER_PATTERNS = {
    "step_construct": re.escape("TYPED_ROUTE_CONSUMER_STEP_v0: CONSTRUCT_TYPED_ROUTE_OBJECT_VIA_CYCLE29_CONSTRUCTOR"),
    "step_consume": re.escape("TYPED_ROUTE_CONSUMER_STEP_v0: CONSUME_TYPED_ROUTE_OBJECT_IN_DOWNSTREAM_ROUTE_COMPONENT"),
    "step_expose": re.escape("TYPED_ROUTE_CONSUMER_STEP_v0: EXPOSE_DD_ZERO_FROM_TYPED_ROUTE_OBJECT_ONLY"),
    "rule_attempt_only": re.escape("TYPED_ROUTE_CONSUMER_RULE_v0: REMAINS_ATTEMPT_ONLY_UNTIL_FULL_DISCHARGE_TARGET"),
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    text = path.read_text(encoding="utf-8")
    if path == EM_OBJECT_SCAFFOLD_LEAN_PATH:
        raw_text = text
        wrapped_token = (
            "EM_U1_MAXWELL_CONTINUITY_TYPED_ROUTE_CONSUMER_ROUTE_v0: \\\n"
            "CONSUME_TYPED_ROUTE_WITH_DD_SUBSTEP_OBJECT_PINNED"
        )
        assert wrapped_token in text, (
            "Expected wrapped Cycle-030 route token in ObjectScaffold.lean before normalization."
        )
        while True:
            text, replacements = re.subn(r'"([^"\n]*)\\\n[ \t]*([^"\n]*)"', r'"\1\2"', text)
            if replacements == 0:
                break
        assert text != raw_text, "Cycle-030 string-gap normalization did not perform any replacement."
        assert (
            "EM_U1_MAXWELL_CONTINUITY_TYPED_ROUTE_CONSUMER_ROUTE_v0: "
            "CONSUME_TYPED_ROUTE_WITH_DD_SUBSTEP_OBJECT_PINNED" in text
        ), "Cycle-030 string-gap normalization did not reconstruct the expected unbroken route token."
    return text


def _strip_wrapping_backticks(text: str) -> str:
    s = text.strip()
    if s.startswith("`") and s.endswith("`") and len(s) >= 2:
        return s[1:-1]
    return s


def _em_micro_docs_except_cycle30() -> list[Path]:
    docs = sorted((REPO_ROOT / "formal" / "docs" / "paper").glob("DERIVATION_TARGET_EM_U1_MICRO_*.md"))
    return [path for path in docs if path != EM_MICRO30_PATH]


def test_em_cycle030_artifacts_exist() -> None:
    assert STATE_PATH.exists(), "Missing State_of_the_Theory.md."
    assert EM_TARGET_PATH.exists(), "Missing EM U1 target document."
    assert ASSUMPTION_REGISTRY_PATH.exists(), "Missing assumption registry document."
    assert EM_MICRO30_PATH.exists(), "Missing EM U1 Cycle-030 document."
    assert EM_ROADMAP_PATH.exists(), "Missing physics roadmap document."
    assert EM_OBJECT_SCAFFOLD_LEAN_PATH.exists(), "Missing EM U1 object scaffold Lean module."


def test_em_micro30_contains_required_tokens_and_localized_typed_route_consumer_statements() -> None:
    text = _read(EM_MICRO30_PATH)
    required_tokens = [
        "DERIVATION_TARGET_EM_U1_MICRO_30_MAXWELL_TO_CONTINUITY_TYPED_ROUTE_CONSUMER_ATTEMPT_v0",
        "TARGET-EM-U1-MICRO-30-MAXWELL-TO-CONTINUITY-TYPED-ROUTE-CONSUMER-ATTEMPT-v0",
        "EM_U1_PROGRESS_CYCLE30_v0: MAXWELL_CONTINUITY_TYPED_ROUTE_CONSUMER_ATTEMPT_TOKEN_PINNED",
        "EM_U1_MAXWELL_CONTINUITY_TYPED_ROUTE_CONSUMER_ROUTE_v0: CONSUME_TYPED_ROUTE_WITH_DD_SUBSTEP_OBJECT_PINNED",
        LOCALIZATION_TOKEN,
        "EM_U1_MAXWELL_CONTINUITY_TYPED_ROUTE_CONSUMER_NO_PROMOTION_v0: ATTEMPT_ONLY_NO_DISCHARGE",
        "EM_U1_MAXWELL_CONTINUITY_TYPED_ROUTE_CONSUMER_BOUNDARY_v0: NO_FULL_DERIVATION_DISCHARGE_OR_INEVITABILITY_PROMOTION",
        "EM_U1_MICRO30_MAXWELL_CONTINUITY_TYPED_ROUTE_CONSUMER_ADJUDICATION: NOT_YET_DISCHARGED",
        "EM_U1_CYCLE030_CYCLE029_THEOREM_SURFACE_USAGE_GUARD_v0: MUST_REFERENCE_em_u1_cycle029_build_typed_route_with_dd_substep_object_v0",
        "EM_U1_CYCLE030_TYPED_OBJECT_CONSUMPTION_GUARD_v0: MUST_CONSUME_MaxwellToContinuityRouteWithDdSubstepAttempt_ONLY",
        SOURCE_ASSUMPTION_ID,
        SMOOTHNESS_ASSUMPTION_ID,
        DISTRIB_ASSUMPTION_ID,
        "formal/python/tests/test_em_u1_micro30_maxwell_to_continuity_typed_route_consumer_attempt.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM Cycle-030 micro document is missing required token(s): " + ", ".join(missing)

    missing_patterns = [label for label, pattern in TYPED_ROUTE_CONSUMER_PATTERNS.items() if re.search(pattern, text) is None]
    assert not missing_patterns, (
        "EM Cycle-030 micro document is missing required typed-route consumer statement(s): "
        + ", ".join(missing_patterns)
    )


def test_em_target_references_cycle030_artifact_and_tokens() -> None:
    text = _read(EM_TARGET_PATH)
    required_tokens = [
        "TARGET-EM-U1-MICRO-30-MAXWELL-TO-CONTINUITY-TYPED-ROUTE-CONSUMER-ATTEMPT-v0",
        "EM_U1_PROGRESS_CYCLE30_v0: MAXWELL_CONTINUITY_TYPED_ROUTE_CONSUMER_ATTEMPT_TOKEN_PINNED",
        "EM_U1_MAXWELL_CONTINUITY_TYPED_ROUTE_CONSUMER_ROUTE_v0: CONSUME_TYPED_ROUTE_WITH_DD_SUBSTEP_OBJECT_PINNED",
        LOCALIZATION_TOKEN,
        "EM_U1_MAXWELL_CONTINUITY_TYPED_ROUTE_CONSUMER_NO_PROMOTION_v0: ATTEMPT_ONLY_NO_DISCHARGE",
        "EM_U1_MAXWELL_CONTINUITY_TYPED_ROUTE_CONSUMER_BOUNDARY_v0: NO_FULL_DERIVATION_DISCHARGE_OR_INEVITABILITY_PROMOTION",
        "EM_U1_MICRO30_MAXWELL_CONTINUITY_TYPED_ROUTE_CONSUMER_ADJUDICATION: NOT_YET_DISCHARGED",
        "EM_U1_CYCLE030_CYCLE029_THEOREM_SURFACE_USAGE_GUARD_v0: MUST_REFERENCE_em_u1_cycle029_build_typed_route_with_dd_substep_object_v0",
        "EM_U1_CYCLE030_TYPED_OBJECT_CONSUMPTION_GUARD_v0: MUST_CONSUME_MaxwellToContinuityRouteWithDdSubstepAttempt_ONLY",
        SOURCE_ASSUMPTION_ID,
        SMOOTHNESS_ASSUMPTION_ID,
        DISTRIB_ASSUMPTION_ID,
        "formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_30_MAXWELL_TO_CONTINUITY_TYPED_ROUTE_CONSUMER_ATTEMPT_v0.md",
        "formal/python/tests/test_em_u1_micro30_maxwell_to_continuity_typed_route_consumer_attempt.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM target document is missing required Cycle-030 token(s): " + ", ".join(missing)


def test_em_roadmap_references_cycle030_target_and_artifact_with_single_row() -> None:
    roadmap_text = _read(EM_ROADMAP_PATH)
    rows = [line.strip() for line in roadmap_text.splitlines() if line.strip().startswith("| `PILLAR-EM` |")]
    assert len(rows) == 1, f"Expected one `PILLAR-EM` roadmap row, found {len(rows)}."
    cells = [cell.strip() for cell in rows[0].split("|")]
    assert len(cells) >= 7, "Malformed `PILLAR-EM` roadmap row."
    targets_raw = _strip_wrapping_backticks(cells[3])
    artifacts_raw = _strip_wrapping_backticks(cells[4])
    targets = {item.strip() for item in targets_raw.split(";") if item.strip()}
    artifacts = {item.strip() for item in artifacts_raw.split(";") if item.strip()}
    assert "TARGET-EM-U1-MICRO-30-MAXWELL-TO-CONTINUITY-TYPED-ROUTE-CONSUMER-ATTEMPT-v0" in targets
    assert (
        "formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_30_MAXWELL_TO_CONTINUITY_TYPED_ROUTE_CONSUMER_ATTEMPT_v0.md"
        in artifacts
    )


def test_state_mentions_cycle030_checkpoint_and_tokens() -> None:
    text = _read(STATE_PATH)
    required_tokens = [
        "EM Cycle-030 Maxwell-to-continuity typed-route consumer attempt checkpoint",
        "TARGET-EM-U1-MICRO-30-MAXWELL-TO-CONTINUITY-TYPED-ROUTE-CONSUMER-ATTEMPT-v0",
        "EM_U1_PROGRESS_CYCLE30_v0: MAXWELL_CONTINUITY_TYPED_ROUTE_CONSUMER_ATTEMPT_TOKEN_PINNED",
        "EM_U1_MAXWELL_CONTINUITY_TYPED_ROUTE_CONSUMER_ROUTE_v0: CONSUME_TYPED_ROUTE_WITH_DD_SUBSTEP_OBJECT_PINNED",
        LOCALIZATION_TOKEN,
        "EM_U1_MAXWELL_CONTINUITY_TYPED_ROUTE_CONSUMER_NO_PROMOTION_v0: ATTEMPT_ONLY_NO_DISCHARGE",
        "EM_U1_MAXWELL_CONTINUITY_TYPED_ROUTE_CONSUMER_BOUNDARY_v0: NO_FULL_DERIVATION_DISCHARGE_OR_INEVITABILITY_PROMOTION",
        "EM_U1_MICRO30_MAXWELL_CONTINUITY_TYPED_ROUTE_CONSUMER_ADJUDICATION: NOT_YET_DISCHARGED",
        "EM_U1_CYCLE030_CYCLE029_THEOREM_SURFACE_USAGE_GUARD_v0: MUST_REFERENCE_em_u1_cycle029_build_typed_route_with_dd_substep_object_v0",
        "EM_U1_CYCLE030_TYPED_OBJECT_CONSUMPTION_GUARD_v0: MUST_CONSUME_MaxwellToContinuityRouteWithDdSubstepAttempt_ONLY",
        SOURCE_ASSUMPTION_ID,
        SMOOTHNESS_ASSUMPTION_ID,
        DISTRIB_ASSUMPTION_ID,
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "State_of_the_Theory.md is missing required Cycle-030 token(s): " + ", ".join(missing)


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


def test_em_lean_cycle030_tokens_typed_route_consumer_surfaces_and_harness_stubs_are_pinned() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    required_tokens = [
        "structure MaxwellToContinuityTypedRouteConsumerAttemptPackage where",
        "def maxwellToContinuityTypedRouteConsumerAttemptHarness",
        "EM_U1_PROGRESS_CYCLE30_v0: MAXWELL_CONTINUITY_TYPED_ROUTE_CONSUMER_ATTEMPT_TOKEN_PINNED",
        "EM_U1_MAXWELL_CONTINUITY_TYPED_ROUTE_CONSUMER_ROUTE_v0: CONSUME_TYPED_ROUTE_WITH_DD_SUBSTEP_OBJECT_PINNED",
        LOCALIZATION_TOKEN,
        "EM_U1_MAXWELL_CONTINUITY_TYPED_ROUTE_CONSUMER_NO_PROMOTION_v0: ATTEMPT_ONLY_NO_DISCHARGE",
        "EM_U1_MAXWELL_CONTINUITY_TYPED_ROUTE_CONSUMER_BOUNDARY_v0: NO_FULL_DERIVATION_DISCHARGE_OR_INEVITABILITY_PROMOTION",
        "em_u1_cycle030_build_typed_route_consumer_entrypoint_v0",
        "theorem em_u1_cycle030_consume_typed_route_object_for_dd_zero_v0",
        "theorem em_u1_cycle030_token_binding_stub_v0",
        "theorem em_u1_cycle030_typed_route_consumer_harness_stub_v0",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM U1 Lean scaffold is missing required Cycle-030 token(s): " + ", ".join(missing)


def test_cycle030_uses_cycle029_constructor_surface_without_bypass() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    block_match = re.search(
        r"(?:theorem|def) em_u1_cycle030_build_typed_route_consumer_entrypoint_v0(?P<body>.*?)"
        r"\ntheorem em_u1_cycle030_consume_typed_route_object_for_dd_zero_v0",
        text,
        flags=re.DOTALL,
    )
    assert block_match is not None, "Could not isolate the Cycle-030 consumer-constructor theorem block."
    block = block_match.group("body")
    assert (
        "em_u1_cycle029_build_typed_route_with_dd_substep_object_v0" in block
    ), "Cycle-030 must reference the Cycle-029 constructor theorem surface."
    assert (
        "em_u1_cycle028_maxwell_continuity_dd_subroute_composition_v0" not in block
    ), "Cycle-030 must not bypass Cycle-029 by directly calling Cycle-028 typed composition."
    assert (
        "em_u1_cycle028_dd_zero_substep_for_maxwell_continuity_route_v0" not in block
    ), "Cycle-030 must not bypass canonical layering by directly calling the Cycle-028 DD-substep theorem."
    assert (
        "em_u1_cycle027_double_divergence_zero_via_built_binding_v0" not in block
    ), "Cycle-030 must not bypass canonical layering by directly calling the Cycle-027 theorem."


def test_cycle030_consumes_typed_route_object_only_for_dd_zero() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    block_match = re.search(
        r"theorem em_u1_cycle030_consume_typed_route_object_for_dd_zero_v0(?P<body>.*?)"
        r"\ntheorem em_u1_field_strength_invariance_under_contract_assumptions_v0",
        text,
        flags=re.DOTALL,
    )
    assert block_match is not None, "Could not isolate the Cycle-030 typed-route consumer theorem block."
    block = block_match.group("body")
    assert (
        "MaxwellToContinuityRouteWithDdSubstepAttempt d F" in block
    ), "Cycle-030 typed-route consumer theorem must consume `MaxwellToContinuityRouteWithDdSubstepAttempt d F`."
    assert "routeObj.ddZero" in block, "Cycle-030 typed-route consumer theorem must expose DD=0 via typed object field access."


def test_cycle030_consumer_theorem_signature_is_exact() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    signature_pattern = (
        r"theorem em_u1_cycle030_consume_typed_route_object_for_dd_zero_v0\s*"
        r"\n\s*\(d : DifferentialBundle\)\s*"
        r"\n\s*\(F : FieldStrength\)\s*"
        r"\n\s*\(routeObj : MaxwellToContinuityRouteWithDdSubstepAttempt d F\)\s*"
        r":\s*\n\s*∀ μ ν, ddFromFieldStrength d F μ ν = 0\s*:= by"
    )
    assert re.search(signature_pattern, text, flags=re.DOTALL) is not None, (
        "Cycle-030 typed-route consumer theorem signature must remain exact: "
        "(d, F, routeObj : MaxwellToContinuityRouteWithDdSubstepAttempt d F) -> "
        "∀ μ ν, ddFromFieldStrength d F μ ν = 0."
    )


def test_cycle030_typed_route_consumer_statements_are_localized_to_cycle30_artifact() -> None:
    allowed_paths = [EM_MICRO30_PATH]
    scoped_paths = _em_micro_docs_except_cycle30() + [
        EM_TARGET_PATH,
        EM_ROADMAP_PATH,
        STATE_PATH,
        ASSUMPTION_REGISTRY_PATH,
        EM_OBJECT_SCAFFOLD_LEAN_PATH,
    ]

    violations: list[str] = []

    for path in allowed_paths:
        text = _read(path)
        hits = [label for label, pattern in TYPED_ROUTE_CONSUMER_PATTERNS.items() if re.search(pattern, text)]
        if not hits:
            violations.append(
                f"cycle030 artifact {path.relative_to(REPO_ROOT)} is missing localized typed-route consumer statements"
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
                f"cycle030 artifact {path.relative_to(REPO_ROOT)} contains typed-route consumer statements {hits} "
                "without required source/smoothness/distributional assumption IDs + localization token + prerequisites + non-selection tokens."
            )

    for path in scoped_paths:
        text = _read(path)
        for label, pattern in TYPED_ROUTE_CONSUMER_PATTERNS.items():
            if re.search(pattern, text):
                violations.append(
                    f"{label} typed-route consumer statement leaked into non-authorized artifact "
                    f"{path.relative_to(REPO_ROOT)}"
                )

    assert not violations, "Cycle-030 typed-route consumer localization violation:\n- " + "\n- ".join(violations)


def test_cycle030_is_attempt_only_and_blocks_promotion_or_new_physics_selection_language() -> None:
    text = _read(EM_MICRO30_PATH)
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
        "Cycle-030 must remain typed-route-consumer-attempt-only/non-promotional and non-selecting. "
        "Forbidden pattern(s) found: "
        + ", ".join(violations)
    )


def test_legacy_boundary_phrase_is_absent_across_all_em_micro_docs_and_em_surfaces() -> None:
    legacy_token = "NO_FULL_DERIVATION_DISCHARGE_OR_PROMOTION"
    all_micro_docs = sorted((REPO_ROOT / "formal" / "docs" / "paper").glob("DERIVATION_TARGET_EM_U1_MICRO_*.md"))
    assert all_micro_docs, "Expected EM micro-target documents for legacy-boundary hygiene check."

    scoped_paths = [*all_micro_docs, EM_OBJECT_SCAFFOLD_LEAN_PATH, STATE_PATH, EM_TARGET_PATH]
    violations: list[str] = []
    for path in scoped_paths:
        text = _read(path)
        if legacy_token in text:
            violations.append(f"{path.relative_to(REPO_ROOT)} contains legacy boundary token phrase.")

    assert not violations, "Legacy boundary-token hygiene violation:\n- " + "\n- ".join(violations)

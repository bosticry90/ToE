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
EM_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
EM_OBJECT_SCAFFOLD_LEAN_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "EM" / "U1" / "ObjectScaffold.lean"

SOURCE_ASSUMPTION_ID = "ASM-EM-U1-PHY-SOURCE-01"
LOCALIZATION_TOKEN = "EM_U1_MAXWELL_SURFACE_LOCALIZATION_GATE_v0: CYCLE11_ARTIFACTS_ONLY"
PREREQUISITE_TOKENS = [
    "EM_U1_CONVENTION_LOCK_SIGNATURE_v0: METRIC_SIGNATURE_FIXED",
    "EM_U1_HODGE_STAR_CONVENTION_v0: STARSTAR_SIGN_FIXED_UNDER_SIGNATURE",
    "EM_U1_SOURCE_OBJECT_CONVENTION_v0: CURRENT_OBJECT_DEFINED",
]

MAXWELL_STATEMENT_PATTERNS = {
    "tensor_inhomogeneous": r"∂\s*_\s*μ\s*F\^\{?μν\}?\s*=\s*J\^ν",
    "tensor_homogeneous": re.escape("∂_[α F_{βγ]} = 0"),
    "forms_homogeneous": r"d\s*F\s*=\s*0",
    "forms_inhomogeneous": r"d\s*[⋆*]\s*F\s*=\s*J",
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _strip_wrapping_backticks(text: str) -> str:
    s = text.strip()
    if s.startswith("`") and s.endswith("`") and len(s) >= 2:
        return s[1:-1]
    return s


def test_em_cycle011_artifacts_exist() -> None:
    assert STATE_PATH.exists(), "Missing State_of_the_Theory.md."
    assert EM_TARGET_PATH.exists(), "Missing EM U1 target document."
    assert EM_MICRO11_PATH.exists(), "Missing EM U1 Cycle-011 document."
    assert EM_ROADMAP_PATH.exists(), "Missing physics roadmap document."
    assert EM_OBJECT_SCAFFOLD_LEAN_PATH.exists(), "Missing EM U1 object scaffold Lean module."


def test_em_micro11_contains_required_tokens_and_statement_surfaces() -> None:
    text = _read(EM_MICRO11_PATH)
    required_tokens = [
        "DERIVATION_TARGET_EM_U1_MICRO_11_MAXWELL_EQUATION_SURFACES_STATEMENT_LOCK_v0",
        "TARGET-EM-U1-MICRO-11-MAXWELL-EQUATION-SURFACES-STATEMENT-LOCK-v0",
        "EM_U1_PROGRESS_CYCLE11_v0: MAXWELL_EQUATION_SURFACES_TOKEN_PINNED",
        "EM_U1_MAXWELL_TENSOR_SURFACE_v0: INHOM_HOM_STATEMENTS_PINNED",
        "EM_U1_MAXWELL_FORMS_SURFACE_v0: DUAL_HODGE_DEPENDENT_STATEMENTS_PINNED",
        LOCALIZATION_TOKEN,
        "EM_U1_MAXWELL_SURFACE_NO_DERIVATION_v0: STATEMENT_ONLY",
        "EM_U1_MICRO11_MAXWELL_SURFACES_ADJUDICATION: NOT_YET_DISCHARGED",
        SOURCE_ASSUMPTION_ID,
        "formal/python/tests/test_em_u1_micro11_maxwell_equation_surfaces_statement_lock.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM Cycle-011 micro document is missing required token(s): " + ", ".join(missing)

    missing_patterns = [
        label for label, pattern in MAXWELL_STATEMENT_PATTERNS.items() if re.search(pattern, text) is None
    ]
    assert not missing_patterns, (
        "EM Cycle-011 micro document is missing required Maxwell statement surface(s): "
        + ", ".join(missing_patterns)
    )


def test_em_target_references_cycle011_artifact_and_tokens() -> None:
    text = _read(EM_TARGET_PATH)
    required_tokens = [
        "TARGET-EM-U1-MICRO-11-MAXWELL-EQUATION-SURFACES-STATEMENT-LOCK-v0",
        "EM_U1_PROGRESS_CYCLE11_v0: MAXWELL_EQUATION_SURFACES_TOKEN_PINNED",
        "EM_U1_MAXWELL_TENSOR_SURFACE_v0: INHOM_HOM_STATEMENTS_PINNED",
        "EM_U1_MAXWELL_FORMS_SURFACE_v0: DUAL_HODGE_DEPENDENT_STATEMENTS_PINNED",
        LOCALIZATION_TOKEN,
        "EM_U1_MAXWELL_SURFACE_NO_DERIVATION_v0: STATEMENT_ONLY",
        "EM_U1_MICRO11_MAXWELL_SURFACES_ADJUDICATION: NOT_YET_DISCHARGED",
        SOURCE_ASSUMPTION_ID,
        "formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_11_MAXWELL_EQUATION_SURFACES_STATEMENT_LOCK_v0.md",
        "formal/python/tests/test_em_u1_micro11_maxwell_equation_surfaces_statement_lock.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM target document is missing required Cycle-011 token(s): " + ", ".join(missing)


def test_em_roadmap_references_cycle011_target_and_artifact_with_single_row() -> None:
    roadmap_text = _read(EM_ROADMAP_PATH)
    rows = [line.strip() for line in roadmap_text.splitlines() if line.strip().startswith("| `PILLAR-EM` |")]
    assert len(rows) == 1, f"Expected one `PILLAR-EM` roadmap row, found {len(rows)}."
    cells = [cell.strip() for cell in rows[0].split("|")]
    assert len(cells) >= 7, "Malformed `PILLAR-EM` roadmap row."
    targets_raw = _strip_wrapping_backticks(cells[3])
    artifacts_raw = _strip_wrapping_backticks(cells[4])
    targets = {item.strip() for item in targets_raw.split(";") if item.strip()}
    artifacts = {item.strip() for item in artifacts_raw.split(";") if item.strip()}
    assert "TARGET-EM-U1-MICRO-11-MAXWELL-EQUATION-SURFACES-STATEMENT-LOCK-v0" in targets
    assert (
        "formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_11_MAXWELL_EQUATION_SURFACES_STATEMENT_LOCK_v0.md"
        in artifacts
    )


def test_state_mentions_cycle011_checkpoint_and_tokens() -> None:
    text = _read(STATE_PATH)
    required_tokens = [
        "EM Cycle-011 Maxwell equation statement-surfaces checkpoint",
        "TARGET-EM-U1-MICRO-11-MAXWELL-EQUATION-SURFACES-STATEMENT-LOCK-v0",
        "EM_U1_PROGRESS_CYCLE11_v0: MAXWELL_EQUATION_SURFACES_TOKEN_PINNED",
        "EM_U1_MAXWELL_TENSOR_SURFACE_v0: INHOM_HOM_STATEMENTS_PINNED",
        "EM_U1_MAXWELL_FORMS_SURFACE_v0: DUAL_HODGE_DEPENDENT_STATEMENTS_PINNED",
        LOCALIZATION_TOKEN,
        "EM_U1_MAXWELL_SURFACE_NO_DERIVATION_v0: STATEMENT_ONLY",
        "EM_U1_MICRO11_MAXWELL_SURFACES_ADJUDICATION: NOT_YET_DISCHARGED",
        SOURCE_ASSUMPTION_ID,
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "State_of_the_Theory.md is missing required Cycle-011 token(s): " + ", ".join(missing)


def test_em_lean_cycle011_tokens_and_harness_stubs_are_pinned() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    required_tokens = [
        "structure MaxwellTensorStatementSurface where",
        "structure MaxwellFormsStatementSurface where",
        "def maxwellEquationStatementSurfaceHarness",
        "EM_U1_PROGRESS_CYCLE11_v0: MAXWELL_EQUATION_SURFACES_TOKEN_PINNED",
        "EM_U1_MAXWELL_TENSOR_SURFACE_v0: INHOM_HOM_STATEMENTS_PINNED",
        "EM_U1_MAXWELL_FORMS_SURFACE_v0: DUAL_HODGE_DEPENDENT_STATEMENTS_PINNED",
        LOCALIZATION_TOKEN,
        "EM_U1_MAXWELL_SURFACE_NO_DERIVATION_v0: STATEMENT_ONLY",
        "theorem em_u1_cycle011_token_binding_stub_v0",
        "theorem em_u1_cycle011_statement_surface_harness_stub_v0",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM U1 Lean scaffold is missing required Cycle-011 token(s): " + ", ".join(missing)


def test_cycle011_statement_surfaces_are_localized_to_authorized_artifacts() -> None:
    allowed_paths = [EM_MICRO04_PATH, EM_MICRO11_PATH]
    scoped_paths = [
        EM_TARGET_PATH,
        EM_MICRO01_PATH,
        EM_MICRO02_PATH,
        EM_MICRO03_PATH,
        EM_MICRO05_PATH,
        EM_MICRO06_PATH,
        EM_MICRO07_PATH,
        EM_MICRO08_PATH,
        EM_MICRO09_PATH,
        EM_MICRO10_PATH,
        EM_ROADMAP_PATH,
        STATE_PATH,
        EM_OBJECT_SCAFFOLD_LEAN_PATH,
    ]

    violations: list[str] = []

    for path in allowed_paths:
        text = _read(path)
        hits = [label for label, pattern in MAXWELL_STATEMENT_PATTERNS.items() if re.search(pattern, text)]
        if not hits:
            continue
        if path == EM_MICRO11_PATH:
            has_source_id = SOURCE_ASSUMPTION_ID in text
            has_localization_gate = LOCALIZATION_TOKEN in text
            has_prereq = all(token in text for token in PREREQUISITE_TOKENS)
            if not (has_source_id and has_localization_gate and has_prereq):
                violations.append(
                    f"cycle011 artifact {path.relative_to(REPO_ROOT)} contains statement surfaces {hits} "
                    "without source assumption ID + localization token + prerequisite convention/source tokens."
                )

    for path in scoped_paths:
        text = _read(path)
        for label, pattern in MAXWELL_STATEMENT_PATTERNS.items():
            if re.search(pattern, text):
                violations.append(
                    f"{label} statement surface leaked into non-authorized artifact {path.relative_to(REPO_ROOT)}"
                )

    assert not violations, "Cycle-011 Maxwell statement localization violation:\n- " + "\n- ".join(violations)


def test_cycle011_is_statement_only_and_blocks_derivation_promotion_language() -> None:
    text = _read(EM_MICRO11_PATH)
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
    ]
    violations = [pattern for pattern in forbidden_patterns if re.search(pattern, text, flags=re.IGNORECASE)]
    assert not violations, (
        "Cycle-011 must remain statement-only/non-derivational. "
        "Forbidden derivation/promotion pattern(s) found: "
        + ", ".join(violations)
    )

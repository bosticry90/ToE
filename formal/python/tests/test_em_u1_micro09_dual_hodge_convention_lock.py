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
EM_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
EM_OBJECT_SCAFFOLD_LEAN_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "EM" / "U1" / "ObjectScaffold.lean"

LOCALIZATION_TOKEN = "EM_U1_DUAL_HODGE_LOCALIZATION_GATE_v0: CYCLE6_CYCLE9_ARTIFACTS_ONLY"
CONVENTION_PREREQUISITE_TOKENS = [
    "EM_U1_CONVENTION_LOCK_SIGNATURE_v0: METRIC_SIGNATURE_FIXED",
    "EM_U1_CONVENTION_LOCK_EB_v0: E_B_SIGN_AND_EPSILON_FIXED",
]

DUAL_HODGE_PHRASE_RULES = {
    "dual_convention": {
        "patterns": [
            r"\bSTARF_DEFINITION_FIXED\b",
            r"\bdualFieldStrengthFromConvention\b",
        ]
    },
    "epsilon_convention": {
        "patterns": [
            r"\bLEVI_CIVITA_NORMALIZATION_FIXED\b",
            r"\bepsilon\^0123=\+1\b",
        ]
    },
    "hodge_convention": {
        "patterns": [
            r"\bSTARSTAR_SIGN_FIXED_UNDER_SIGNATURE\b",
            r"\bHodgeStar2FormOperator\b",
            r"\bdualHodgeConventionHarness\b",
        ]
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


def test_em_cycle009_artifacts_exist() -> None:
    assert STATE_PATH.exists(), "Missing State_of_the_Theory.md."
    assert EM_TARGET_PATH.exists(), "Missing EM U1 target document."
    assert EM_MICRO06_PATH.exists(), "Missing EM U1 Cycle-006 document."
    assert EM_MICRO09_PATH.exists(), "Missing EM U1 Cycle-009 document."
    assert EM_ROADMAP_PATH.exists(), "Missing physics roadmap document."
    assert EM_OBJECT_SCAFFOLD_LEAN_PATH.exists(), "Missing EM U1 object scaffold Lean module."


def test_em_micro09_contains_required_tokens_and_pointers() -> None:
    text = _read(EM_MICRO09_PATH)
    required_tokens = [
        "DERIVATION_TARGET_EM_U1_MICRO_09_DUAL_HODGE_CONVENTION_LOCK_v0",
        "TARGET-EM-U1-MICRO-09-DUAL-HODGE-CONVENTION-LOCK-v0",
        "EM_U1_PROGRESS_CYCLE9_v0: DUAL_HODGE_CONVENTION_LOCK_TOKEN_PINNED",
        "EM_U1_DUAL_CONVENTION_v0: STARF_DEFINITION_FIXED",
        "EM_U1_EPSILON_CONVENTION_v0: LEVI_CIVITA_NORMALIZATION_FIXED",
        "EM_U1_HODGE_STAR_CONVENTION_v0: STARSTAR_SIGN_FIXED_UNDER_SIGNATURE",
        "EM_U1_DUAL_HODGE_LOCALIZATION_GATE_v0: CYCLE6_CYCLE9_ARTIFACTS_ONLY",
        "EM_U1_DUAL_HODGE_NO_DYNAMICS_v0: CONVENTION_LOCK_ONLY",
        "EM_U1_MICRO09_DUAL_HODGE_ADJUDICATION: NOT_YET_DISCHARGED",
        "EM_U1_CONVENTION_LOCK_SIGNATURE_v0: METRIC_SIGNATURE_FIXED",
        "EM_U1_CONVENTION_LOCK_EB_v0: E_B_SIGN_AND_EPSILON_FIXED",
        "formal/python/tests/test_em_u1_micro09_dual_hodge_convention_lock.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM Cycle-009 micro document is missing required token(s): " + ", ".join(missing)


def test_em_target_references_cycle009_artifact_and_tokens() -> None:
    text = _read(EM_TARGET_PATH)
    required_tokens = [
        "TARGET-EM-U1-MICRO-09-DUAL-HODGE-CONVENTION-LOCK-v0",
        "EM_U1_PROGRESS_CYCLE9_v0: DUAL_HODGE_CONVENTION_LOCK_TOKEN_PINNED",
        "EM_U1_DUAL_CONVENTION_v0: STARF_DEFINITION_FIXED",
        "EM_U1_EPSILON_CONVENTION_v0: LEVI_CIVITA_NORMALIZATION_FIXED",
        "EM_U1_HODGE_STAR_CONVENTION_v0: STARSTAR_SIGN_FIXED_UNDER_SIGNATURE",
        LOCALIZATION_TOKEN,
        "EM_U1_DUAL_HODGE_NO_DYNAMICS_v0: CONVENTION_LOCK_ONLY",
        "EM_U1_MICRO09_DUAL_HODGE_ADJUDICATION: NOT_YET_DISCHARGED",
        "formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_09_DUAL_HODGE_CONVENTION_LOCK_v0.md",
        "formal/python/tests/test_em_u1_micro09_dual_hodge_convention_lock.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM target document is missing required Cycle-009 token(s): " + ", ".join(missing)


def test_em_roadmap_references_cycle009_target_and_artifact_with_single_row() -> None:
    roadmap_text = _read(EM_ROADMAP_PATH)
    rows = [line.strip() for line in roadmap_text.splitlines() if line.strip().startswith("| `PILLAR-EM` |")]
    assert len(rows) == 1, f"Expected one `PILLAR-EM` roadmap row, found {len(rows)}."
    cells = [cell.strip() for cell in rows[0].split("|")]
    assert len(cells) >= 7, "Malformed `PILLAR-EM` roadmap row."
    targets_raw = _strip_wrapping_backticks(cells[3])
    artifacts_raw = _strip_wrapping_backticks(cells[4])
    targets = {item.strip() for item in targets_raw.split(";") if item.strip()}
    artifacts = {item.strip() for item in artifacts_raw.split(";") if item.strip()}
    assert "TARGET-EM-U1-MICRO-09-DUAL-HODGE-CONVENTION-LOCK-v0" in targets
    assert "formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_09_DUAL_HODGE_CONVENTION_LOCK_v0.md" in artifacts


def test_state_mentions_cycle009_checkpoint_and_tokens() -> None:
    text = _read(STATE_PATH)
    required_tokens = [
        "EM Cycle-009 dual/hodge convention-lock checkpoint",
        "TARGET-EM-U1-MICRO-09-DUAL-HODGE-CONVENTION-LOCK-v0",
        "EM_U1_PROGRESS_CYCLE9_v0: DUAL_HODGE_CONVENTION_LOCK_TOKEN_PINNED",
        "EM_U1_DUAL_CONVENTION_v0: STARF_DEFINITION_FIXED",
        "EM_U1_EPSILON_CONVENTION_v0: LEVI_CIVITA_NORMALIZATION_FIXED",
        "EM_U1_HODGE_STAR_CONVENTION_v0: STARSTAR_SIGN_FIXED_UNDER_SIGNATURE",
        LOCALIZATION_TOKEN,
        "EM_U1_MICRO09_DUAL_HODGE_ADJUDICATION: NOT_YET_DISCHARGED",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "State_of_the_Theory.md is missing required Cycle-009 token(s): " + ", ".join(missing)


def test_em_lean_cycle009_tokens_and_operator_stubs_are_pinned() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    required_tokens = [
        "structure EpsilonConvention where",
        "structure HodgeStar2FormOperator where",
        "def dualFieldStrengthFromConvention",
        "def dualHodgeConventionHarness",
        "EM_U1_PROGRESS_CYCLE9_v0: DUAL_HODGE_CONVENTION_LOCK_TOKEN_PINNED",
        "EM_U1_DUAL_CONVENTION_v0: STARF_DEFINITION_FIXED",
        "EM_U1_EPSILON_CONVENTION_v0: LEVI_CIVITA_NORMALIZATION_FIXED",
        "EM_U1_HODGE_STAR_CONVENTION_v0: STARSTAR_SIGN_FIXED_UNDER_SIGNATURE",
        LOCALIZATION_TOKEN,
        "EM_U1_DUAL_HODGE_NO_DYNAMICS_v0: CONVENTION_LOCK_ONLY",
        "theorem em_u1_cycle009_token_binding_stub_v0",
        "theorem em_u1_cycle009_dual_hodge_harness_stub_v0",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM U1 Lean scaffold is missing required Cycle-009 token(s): " + ", ".join(missing)


def test_cycle009_is_definitional_only_and_blocks_dynamics_equation_forms() -> None:
    text = _read(EM_MICRO09_PATH)
    forbidden_patterns = [
        r"\bd\s*star\s*F\s*=\s*J\b",
        r"\bpartial[_\s-]*mu\s*F\^\{mu\s*nu\}\s*=\s*J\^nu\b",
        r"\bequations of motion\b",
        r"\bwave equation\b",
        r"\bLagrangian density\b",
        r"\bEuler-?Lagrange\b",
        r"\bfull dynamics closure\b",
    ]
    violations = [pattern for pattern in forbidden_patterns if re.search(pattern, text, flags=re.IGNORECASE)]
    assert not violations, (
        "Cycle-009 dual/hodge convention lock must remain definitional-only. "
        "Forbidden dynamics/equation pattern(s) found: "
        + ", ".join(violations)
    )


def test_cycle009_dual_hodge_phrases_are_localized_or_explicitly_gated() -> None:
    allowed_paths = [EM_MICRO06_PATH, EM_MICRO09_PATH, EM_OBJECT_SCAFFOLD_LEAN_PATH]
    scoped_paths = [
        EM_TARGET_PATH,
        EM_MICRO01_PATH,
        EM_MICRO02_PATH,
        EM_MICRO03_PATH,
        EM_MICRO04_PATH,
        EM_MICRO05_PATH,
        EM_MICRO07_PATH,
        EM_MICRO08_PATH,
        EM_ROADMAP_PATH,
        STATE_PATH,
    ]

    violations: list[str] = []
    for lane_name, rule in DUAL_HODGE_PHRASE_RULES.items():
        patterns: list[str] = rule["patterns"]

        for path in allowed_paths:
            text = _read(path)
            lane_hits = [pattern for pattern in patterns if re.search(pattern, text, flags=re.IGNORECASE)]
            if lane_hits:
                missing_prereq = [token for token in CONVENTION_PREREQUISITE_TOKENS if token not in text]
                if missing_prereq:
                    violations.append(
                        f"{lane_name}: allowed artifact {path.relative_to(REPO_ROOT)} contains {lane_hits} "
                        f"but misses convention prerequisite token(s): {', '.join(missing_prereq)}"
                    )

        for path in scoped_paths:
            text = _read(path)
            lane_hits = [pattern for pattern in patterns if re.search(pattern, text, flags=re.IGNORECASE)]
            if not lane_hits:
                continue
            has_prereq = all(token in text for token in CONVENTION_PREREQUISITE_TOKENS)
            has_localization_gate = LOCALIZATION_TOKEN in text
            if not (has_prereq and has_localization_gate):
                violations.append(
                    f"{lane_name}: non-cycle06/09 artifact {path.relative_to(REPO_ROOT)} contains {lane_hits} "
                    "without convention prerequisites + localization token."
                )

    assert not violations, "Cycle-009 localization/convention gate violation:\n- " + "\n- ".join(violations)

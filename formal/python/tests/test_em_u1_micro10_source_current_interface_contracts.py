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
EM_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
ASSUMPTION_REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "ASSUMPTION_REGISTRY_v1.md"
EM_OBJECT_SCAFFOLD_LEAN_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "EM" / "U1" / "ObjectScaffold.lean"

SOURCE_ASSUMPTION_ID = "ASM-EM-U1-PHY-SOURCE-01"
LOCALIZATION_TOKEN = "EM_U1_SOURCE_LOCALIZATION_GATE_v0: CYCLE10_ARTIFACTS_ONLY"
SOURCE_PREREQUISITE_TOKENS = [
    "EM_U1_CONVENTION_LOCK_SIGNATURE_v0: METRIC_SIGNATURE_FIXED",
    "EM_U1_CONVENTION_LOCK_EB_v0: E_B_SIGN_AND_EPSILON_FIXED",
]

SOURCE_INTERFACE_PHRASE_RULES = {
    "source_object": {
        "patterns": [
            r"\bSOURCE_OBJECT_DEFINED\b",
            r"\bCovariantCurrent\b",
        ]
    },
    "source_split": {
        "patterns": [
            r"\bRHO_J_SPLIT_SEAM_DEFINED\b",
            r"\bSourceSplitInterface\b",
        ]
    },
    "continuity_predicate": {
        "patterns": [
            r"\bOPTIONAL_INTERFACE_CONSTRAINT_ONLY\b",
            r"\bcontinuityPredicate\b",
            r"\bsourceInterfaceApplicationHarness\b",
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


def test_em_cycle010_artifacts_exist() -> None:
    assert STATE_PATH.exists(), "Missing State_of_the_Theory.md."
    assert EM_TARGET_PATH.exists(), "Missing EM U1 target document."
    assert EM_MICRO10_PATH.exists(), "Missing EM U1 Cycle-010 document."
    assert EM_ROADMAP_PATH.exists(), "Missing physics roadmap document."
    assert ASSUMPTION_REGISTRY_PATH.exists(), "Missing assumption registry."
    assert EM_OBJECT_SCAFFOLD_LEAN_PATH.exists(), "Missing EM U1 object scaffold Lean module."


def test_em_micro10_contains_required_tokens_and_pointers() -> None:
    text = _read(EM_MICRO10_PATH)
    required_tokens = [
        "DERIVATION_TARGET_EM_U1_MICRO_10_SOURCE_CURRENT_INTERFACE_CONTRACTS_v0",
        "TARGET-EM-U1-MICRO-10-SOURCE-CURRENT-INTERFACE-CONTRACTS-v0",
        "EM_U1_PROGRESS_CYCLE10_v0: SOURCE_CURRENT_INTERFACE_TOKEN_PINNED",
        "EM_U1_SOURCE_OBJECT_CONVENTION_v0: CURRENT_OBJECT_DEFINED",
        "EM_U1_SOURCE_SPLIT_CONVENTION_v0: RHO_J_SPLIT_SEAM_DEFINED",
        "EM_U1_SOURCE_CONTINUITY_PREDICATE_v0: OPTIONAL_INTERFACE_CONSTRAINT_ONLY",
        LOCALIZATION_TOKEN,
        "EM_U1_SOURCE_NO_DYNAMICS_v0: INTERFACE_ONLY",
        "EM_U1_MICRO10_SOURCE_CURRENT_ADJUDICATION: NOT_YET_DISCHARGED",
        SOURCE_ASSUMPTION_ID,
        "formal/python/tests/test_em_u1_micro10_source_current_interface_contracts.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM Cycle-010 micro document is missing required token(s): " + ", ".join(missing)


def test_assumption_registry_contains_cycle010_source_assumption_and_index() -> None:
    text = _read(ASSUMPTION_REGISTRY_PATH)
    required_tokens = [
        f"| `{SOURCE_ASSUMPTION_ID}` |",
        "`em_u1_source_current_interface_contracts_v0`",
        f"- `{SOURCE_ASSUMPTION_ID}`",
        "formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_10_SOURCE_CURRENT_INTERFACE_CONTRACTS_v0.md",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "Assumption registry is missing required Cycle-010 token(s): " + ", ".join(missing)


def test_em_target_references_cycle010_artifact_and_tokens() -> None:
    text = _read(EM_TARGET_PATH)
    required_tokens = [
        "TARGET-EM-U1-MICRO-10-SOURCE-CURRENT-INTERFACE-CONTRACTS-v0",
        "EM_U1_PROGRESS_CYCLE10_v0: SOURCE_CURRENT_INTERFACE_TOKEN_PINNED",
        "EM_U1_SOURCE_OBJECT_CONVENTION_v0: CURRENT_OBJECT_DEFINED",
        "EM_U1_SOURCE_SPLIT_CONVENTION_v0: RHO_J_SPLIT_SEAM_DEFINED",
        "EM_U1_SOURCE_CONTINUITY_PREDICATE_v0: OPTIONAL_INTERFACE_CONSTRAINT_ONLY",
        LOCALIZATION_TOKEN,
        "EM_U1_SOURCE_NO_DYNAMICS_v0: INTERFACE_ONLY",
        "EM_U1_MICRO10_SOURCE_CURRENT_ADJUDICATION: NOT_YET_DISCHARGED",
        SOURCE_ASSUMPTION_ID,
        "formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_10_SOURCE_CURRENT_INTERFACE_CONTRACTS_v0.md",
        "formal/python/tests/test_em_u1_micro10_source_current_interface_contracts.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM target document is missing required Cycle-010 token(s): " + ", ".join(missing)


def test_em_roadmap_references_cycle010_target_and_artifact_with_single_row() -> None:
    roadmap_text = _read(EM_ROADMAP_PATH)
    rows = [line.strip() for line in roadmap_text.splitlines() if line.strip().startswith("| `PILLAR-EM` |")]
    assert len(rows) == 1, f"Expected one `PILLAR-EM` roadmap row, found {len(rows)}."
    cells = [cell.strip() for cell in rows[0].split("|")]
    assert len(cells) >= 7, "Malformed `PILLAR-EM` roadmap row."
    targets_raw = _strip_wrapping_backticks(cells[3])
    artifacts_raw = _strip_wrapping_backticks(cells[4])
    targets = {item.strip() for item in targets_raw.split(";") if item.strip()}
    artifacts = {item.strip() for item in artifacts_raw.split(";") if item.strip()}
    assert "TARGET-EM-U1-MICRO-10-SOURCE-CURRENT-INTERFACE-CONTRACTS-v0" in targets
    assert "formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_10_SOURCE_CURRENT_INTERFACE_CONTRACTS_v0.md" in artifacts


def test_state_mentions_cycle010_checkpoint_and_tokens() -> None:
    text = _read(STATE_PATH)
    required_tokens = [
        "EM Cycle-010 source/current interface-contracts checkpoint",
        "TARGET-EM-U1-MICRO-10-SOURCE-CURRENT-INTERFACE-CONTRACTS-v0",
        "EM_U1_PROGRESS_CYCLE10_v0: SOURCE_CURRENT_INTERFACE_TOKEN_PINNED",
        "EM_U1_SOURCE_OBJECT_CONVENTION_v0: CURRENT_OBJECT_DEFINED",
        "EM_U1_SOURCE_SPLIT_CONVENTION_v0: RHO_J_SPLIT_SEAM_DEFINED",
        "EM_U1_SOURCE_CONTINUITY_PREDICATE_v0: OPTIONAL_INTERFACE_CONSTRAINT_ONLY",
        LOCALIZATION_TOKEN,
        "EM_U1_MICRO10_SOURCE_CURRENT_ADJUDICATION: NOT_YET_DISCHARGED",
        SOURCE_ASSUMPTION_ID,
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "State_of_the_Theory.md is missing required Cycle-010 token(s): " + ", ".join(missing)


def test_em_lean_cycle010_tokens_and_source_stubs_are_pinned() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    required_tokens = [
        "structure CovariantCurrent where",
        "structure SourceSplitInterface where",
        "def continuityPredicate",
        "def sourceInterfaceApplicationHarness",
        "EM_U1_PROGRESS_CYCLE10_v0: SOURCE_CURRENT_INTERFACE_TOKEN_PINNED",
        "EM_U1_SOURCE_OBJECT_CONVENTION_v0: CURRENT_OBJECT_DEFINED",
        "EM_U1_SOURCE_SPLIT_CONVENTION_v0: RHO_J_SPLIT_SEAM_DEFINED",
        "EM_U1_SOURCE_CONTINUITY_PREDICATE_v0: OPTIONAL_INTERFACE_CONSTRAINT_ONLY",
        LOCALIZATION_TOKEN,
        "EM_U1_SOURCE_NO_DYNAMICS_v0: INTERFACE_ONLY",
        "theorem em_u1_cycle010_token_binding_stub_v0",
        "theorem em_u1_cycle010_source_interface_harness_stub_v0",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM U1 Lean scaffold is missing required Cycle-010 token(s): " + ", ".join(missing)


def test_cycle010_is_definitional_only_and_blocks_dynamics_equation_forms() -> None:
    text = _read(EM_MICRO10_PATH)
    forbidden_patterns = [
        r"\bpartial[_\s-]*mu\s*J\^mu\s*=\s*0\b",
        r"∂_μ\s*J\^μ\s*=\s*0",
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
        "Cycle-010 source/current interface lock must remain non-dynamics. "
        "Forbidden dynamics/equation pattern(s) found: "
        + ", ".join(violations)
    )


def test_cycle010_source_phrases_are_localized_or_explicitly_gated() -> None:
    allowed_paths = [EM_MICRO10_PATH, EM_OBJECT_SCAFFOLD_LEAN_PATH]
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
        EM_ROADMAP_PATH,
        STATE_PATH,
    ]

    violations: list[str] = []
    for lane_name, rule in SOURCE_INTERFACE_PHRASE_RULES.items():
        patterns: list[str] = rule["patterns"]

        for path in allowed_paths:
            text = _read(path)
            lane_hits = [pattern for pattern in patterns if re.search(pattern, text, flags=re.IGNORECASE)]
            if lane_hits and SOURCE_ASSUMPTION_ID not in text:
                violations.append(
                    f"{lane_name}: allowed artifact {path.relative_to(REPO_ROOT)} contains {lane_hits} "
                    f"but misses source assumption ID {SOURCE_ASSUMPTION_ID}"
                )

        for path in scoped_paths:
            text = _read(path)
            lane_hits = [pattern for pattern in patterns if re.search(pattern, text, flags=re.IGNORECASE)]
            if not lane_hits:
                continue
            has_source_id = SOURCE_ASSUMPTION_ID in text
            has_localization_gate = LOCALIZATION_TOKEN in text
            has_prereq = all(token in text for token in SOURCE_PREREQUISITE_TOKENS)
            if not (has_source_id and has_localization_gate and has_prereq):
                violations.append(
                    f"{lane_name}: non-cycle10 artifact {path.relative_to(REPO_ROOT)} contains {lane_hits} "
                    "without source assumption ID + localization token + prerequisite convention tokens."
                )

    assert not violations, "Cycle-010 localization/source gate violation:\n- " + "\n- ".join(violations)

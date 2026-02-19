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
EM_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
ASSUMPTION_REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "ASSUMPTION_REGISTRY_v1.md"
EM_OBJECT_SCAFFOLD_LEAN_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "EM" / "U1" / "ObjectScaffold.lean"

LOCALIZATION_TOKEN = "EM_U1_IMPORT_LANES_INTERFACE_LOCALIZATION_GATE_v0: CYCLE7_CYCLE8_ARTIFACTS_ONLY"

INTERFACE_PHRASE_RULES = {
    "constitutive_interface": {
        "patterns": [
            r"\bconstitutive interface contract\b",
            r"\bplaceholderConstitutiveLane\b",
        ],
        "required_ids": ["ASM-EM-U1-PHY-CONSTITUTIVE-01"],
    },
    "units_interface": {
        "patterns": [
            r"\bunits interface contract\b",
            r"\bplaceholderUnitsLane\b",
        ],
        "required_ids": ["ASM-EM-U1-PHY-UNITS-01"],
    },
    "gauge_fixing_interface": {
        "patterns": [
            r"\bgauge-?fixing interface contract\b",
            r"\bplaceholderGaugeFixingLane\b",
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


def test_em_cycle008_artifacts_exist() -> None:
    assert STATE_PATH.exists(), "Missing State_of_the_Theory.md."
    assert EM_TARGET_PATH.exists(), "Missing EM U1 target document."
    assert EM_MICRO07_PATH.exists(), "Missing EM U1 Cycle-007 document."
    assert EM_MICRO08_PATH.exists(), "Missing EM U1 Cycle-008 document."
    assert EM_ROADMAP_PATH.exists(), "Missing physics roadmap document."
    assert ASSUMPTION_REGISTRY_PATH.exists(), "Missing assumption registry."
    assert EM_OBJECT_SCAFFOLD_LEAN_PATH.exists(), "Missing EM U1 object scaffold Lean module."


def test_em_micro08_contains_required_interface_tokens_ids_and_pointers() -> None:
    text = _read(EM_MICRO08_PATH)
    required_tokens = [
        "DERIVATION_TARGET_EM_U1_MICRO_08_IMPORT_LANES_INTERFACE_CONTRACTS_v0",
        "TARGET-EM-U1-MICRO-08-IMPORT-LANES-INTERFACE-CONTRACTS-v0",
        "EM_U1_PROGRESS_CYCLE8_v0: IMPORT_LANES_INTERFACE_CONTRACTS_TOKEN_PINNED",
        "EM_U1_IMPORT_LANES_INTERFACE_CONTRACTS_v0: THREE_LANE_INTERFACES_DEFINED",
        "EM_U1_IMPORT_LANES_INTERFACE_NO_SELECTION_v0: NO_UNITS_OR_GAUGE_SELECTION",
        "EM_U1_IMPORT_LANES_INTERFACE_LOCALIZATION_GATE_v0: CYCLE7_CYCLE8_ARTIFACTS_ONLY",
        "EM_U1_IMPORT_LANES_INTERFACE_APPLICATION_HARNESS_v0: REFERENCE_ONLY_IMPORT_APPLICATION",
        "EM_U1_IMPORT_LANES_NO_DYNAMICS_v0: PLACEHOLDER_ONLY",
        "EM_U1_MICRO08_IMPORT_LANES_INTERFACE_ADJUDICATION: NOT_YET_DISCHARGED",
        "EM_U1_NEW_PHYSICS_ASSUMPTION_ID_GATE_v0: CONSTITUTIVE_UNITS_GAUGE_FIXING_REQUIRE_IDS",
        "ASM-EM-U1-PHY-CONSTITUTIVE-01",
        "ASM-EM-U1-PHY-UNITS-01",
        "ASM-EM-U1-PHY-GFIX-01",
        "formal/python/tests/test_em_u1_micro08_import_lanes_interface_contracts.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM Cycle-008 micro document is missing required token(s): " + ", ".join(missing)


def test_em_target_references_cycle008_artifact_and_tokens() -> None:
    text = _read(EM_TARGET_PATH)
    required_tokens = [
        "TARGET-EM-U1-MICRO-08-IMPORT-LANES-INTERFACE-CONTRACTS-v0",
        "EM_U1_PROGRESS_CYCLE8_v0: IMPORT_LANES_INTERFACE_CONTRACTS_TOKEN_PINNED",
        "EM_U1_IMPORT_LANES_INTERFACE_CONTRACTS_v0: THREE_LANE_INTERFACES_DEFINED",
        "EM_U1_IMPORT_LANES_INTERFACE_NO_SELECTION_v0: NO_UNITS_OR_GAUGE_SELECTION",
        "EM_U1_IMPORT_LANES_INTERFACE_LOCALIZATION_GATE_v0: CYCLE7_CYCLE8_ARTIFACTS_ONLY",
        "EM_U1_IMPORT_LANES_INTERFACE_APPLICATION_HARNESS_v0: REFERENCE_ONLY_IMPORT_APPLICATION",
        "EM_U1_MICRO08_IMPORT_LANES_INTERFACE_ADJUDICATION: NOT_YET_DISCHARGED",
        "formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_08_IMPORT_LANES_INTERFACE_CONTRACTS_v0.md",
        "formal/python/tests/test_em_u1_micro08_import_lanes_interface_contracts.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM target document is missing required Cycle-008 token(s): " + ", ".join(missing)


def test_em_roadmap_references_cycle008_target_and_artifact_with_single_row() -> None:
    roadmap_text = _read(EM_ROADMAP_PATH)
    rows = [line.strip() for line in roadmap_text.splitlines() if line.strip().startswith("| `PILLAR-EM` |")]
    assert len(rows) == 1, f"Expected one `PILLAR-EM` roadmap row, found {len(rows)}."
    cells = [cell.strip() for cell in rows[0].split("|")]
    assert len(cells) >= 7, "Malformed `PILLAR-EM` roadmap row."
    targets_raw = _strip_wrapping_backticks(cells[3])
    artifacts_raw = _strip_wrapping_backticks(cells[4])
    targets = {item.strip() for item in targets_raw.split(";") if item.strip()}
    artifacts = {item.strip() for item in artifacts_raw.split(";") if item.strip()}
    assert "TARGET-EM-U1-MICRO-08-IMPORT-LANES-INTERFACE-CONTRACTS-v0" in targets
    assert "formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_08_IMPORT_LANES_INTERFACE_CONTRACTS_v0.md" in artifacts


def test_state_mentions_cycle008_checkpoint_and_tokens() -> None:
    text = _read(STATE_PATH)
    required_tokens = [
        "EM Cycle-008 import-lanes interface-contracts checkpoint",
        "TARGET-EM-U1-MICRO-08-IMPORT-LANES-INTERFACE-CONTRACTS-v0",
        "EM_U1_PROGRESS_CYCLE8_v0: IMPORT_LANES_INTERFACE_CONTRACTS_TOKEN_PINNED",
        "EM_U1_IMPORT_LANES_INTERFACE_CONTRACTS_v0: THREE_LANE_INTERFACES_DEFINED",
        "EM_U1_IMPORT_LANES_INTERFACE_NO_SELECTION_v0: NO_UNITS_OR_GAUGE_SELECTION",
        "EM_U1_IMPORT_LANES_INTERFACE_LOCALIZATION_GATE_v0: CYCLE7_CYCLE8_ARTIFACTS_ONLY",
        "EM_U1_MICRO08_IMPORT_LANES_INTERFACE_ADJUDICATION: NOT_YET_DISCHARGED",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "State_of_the_Theory.md is missing required Cycle-008 token(s): " + ", ".join(missing)


def test_em_lean_cycle008_tokens_and_interface_stubs_are_pinned() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    required_tokens = [
        "structure ConstitutiveImportInterface where",
        "structure UnitsImportInterface where",
        "structure GaugeFixingImportInterface where",
        "def importLaneInterfaceApplicationHarness",
        "EM_U1_PROGRESS_CYCLE8_v0: IMPORT_LANES_INTERFACE_CONTRACTS_TOKEN_PINNED",
        "EM_U1_IMPORT_LANES_INTERFACE_CONTRACTS_v0: THREE_LANE_INTERFACES_DEFINED",
        "EM_U1_IMPORT_LANES_INTERFACE_NO_SELECTION_v0: NO_UNITS_OR_GAUGE_SELECTION",
        "EM_U1_IMPORT_LANES_INTERFACE_LOCALIZATION_GATE_v0: CYCLE7_CYCLE8_ARTIFACTS_ONLY",
        "EM_U1_IMPORT_LANES_INTERFACE_APPLICATION_HARNESS_v0: REFERENCE_ONLY_IMPORT_APPLICATION",
        "theorem em_u1_cycle008_token_binding_stub_v0",
        "theorem em_u1_cycle008_import_lane_interface_harness_stub_v0",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM U1 Lean scaffold is missing required Cycle-008 token(s): " + ", ".join(missing)


def test_cycle008_is_definitional_only_and_avoids_dynamics_claim_language() -> None:
    text = _read(EM_MICRO08_PATH)
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
        "Cycle-008 import-lane interface contracts must remain definitional/structural only. "
        "Forbidden dynamics-claim pattern(s) found: "
        + ", ".join(violations)
    )


def test_cycle008_interface_phrases_are_localized_or_explicitly_gated() -> None:
    allowed_paths = [EM_MICRO07_PATH, EM_MICRO08_PATH]
    scoped_paths = [
        EM_TARGET_PATH,
        EM_MICRO01_PATH,
        EM_MICRO02_PATH,
        EM_MICRO03_PATH,
        EM_MICRO04_PATH,
        EM_MICRO05_PATH,
        EM_MICRO06_PATH,
        EM_ROADMAP_PATH,
        STATE_PATH,
    ]

    violations: list[str] = []
    for lane_name, rule in INTERFACE_PHRASE_RULES.items():
        patterns: list[str] = rule["patterns"]
        required_ids: list[str] = rule["required_ids"]

        for path in allowed_paths:
            text = _read(path)
            lane_hits = [pattern for pattern in patterns if re.search(pattern, text, flags=re.IGNORECASE)]
            if lane_hits:
                missing_ids = [assumption_id for assumption_id in required_ids if assumption_id not in text]
                if missing_ids:
                    violations.append(
                        f"{lane_name}: allowed artifact {path.relative_to(REPO_ROOT)} contains {lane_hits} "
                        f"but misses required assumption ID(s): {', '.join(missing_ids)}"
                    )

        for path in scoped_paths:
            text = _read(path)
            lane_hits = [pattern for pattern in patterns if re.search(pattern, text, flags=re.IGNORECASE)]
            if not lane_hits:
                continue
            has_required_ids = all(assumption_id in text for assumption_id in required_ids)
            has_localization_gate = LOCALIZATION_TOKEN in text
            if not (has_required_ids and has_localization_gate):
                violations.append(
                    f"{lane_name}: non-cycle07/08 artifact {path.relative_to(REPO_ROOT)} contains {lane_hits} "
                    "without required IDs + localization token."
                )

    assert not violations, "Cycle-008 interface localization/assumption gate violation:\n- " + "\n- ".join(violations)

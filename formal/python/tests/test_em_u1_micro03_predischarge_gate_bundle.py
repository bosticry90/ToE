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
EM_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
ASSUMPTION_REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "ASSUMPTION_REGISTRY_v1.md"
EM_OBJECT_SCAFFOLD_LEAN_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "EM" / "U1" / "ObjectScaffold.lean"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _strip_wrapping_backticks(text: str) -> str:
    s = text.strip()
    if s.startswith("`") and s.endswith("`") and len(s) >= 2:
        return s[1:-1]
    return s


def _em_roadmap_row_cells(roadmap_text: str) -> list[str]:
    rows = [
        line.strip()
        for line in roadmap_text.splitlines()
        if line.strip().startswith("| `PILLAR-EM` |")
    ]
    assert len(rows) == 1, (
        "EM roadmap row uniqueness gate violated: expected exactly one `PILLAR-EM` row, "
        f"found {len(rows)}."
    )
    cells = [cell.strip() for cell in rows[0].split("|")]
    assert len(cells) >= 7, "Malformed `PILLAR-EM` roadmap row."
    return cells


def _extract_cycle3_adjudication_value(text: str) -> str:
    m = re.search(
        r"EM_U1_MICRO03_PREDISCHARGE_GATE_BUNDLE_ADJUDICATION:\s*`?([A-Za-z0-9_<>\-_]+)`?",
        text,
    )
    assert m is not None, "Cycle-003 adjudication token is missing."
    return m.group(1)


def test_em_cycle003_artifacts_exist() -> None:
    assert EM_TARGET_PATH.exists(), "Missing EM U1 target document."
    assert EM_MICRO03_PATH.exists(), "Missing EM U1 Cycle-003 pre-discharge gate-bundle document."
    assert ASSUMPTION_REGISTRY_PATH.exists(), "Missing assumption registry."
    assert EM_ROADMAP_PATH.exists(), "Missing physics roadmap document."
    assert EM_OBJECT_SCAFFOLD_LEAN_PATH.exists(), "Missing EM U1 object scaffold Lean module."


def test_em_micro03_contains_required_predischarge_gate_tokens() -> None:
    text = _read(EM_MICRO03_PATH)
    required_tokens = [
        "DERIVATION_TARGET_EM_U1_MICRO_03_PREDISCHARGE_GATE_BUNDLE_v0",
        "TARGET-EM-U1-MICRO-03-PREDISCHARGE-GATE-BUNDLE-v0",
        "EM_U1_MICRO03_PREDISCHARGE_GATE_BUNDLE_ADJUDICATION:",
        "EM_U1_PROGRESS_CYCLE3_v0: PREDISCHARGE_GATE_BUNDLE_TOKEN_PINNED",
        "EM_U1_OBJECT_ROUTE_ARTIFACT_UNIQUENESS_GATE_v0: SINGLE_AUTHORITATIVE_ARTIFACT_SET_REQUIRED",
        "EM_U1_ROADMAP_ROW_UNIQUENESS_GATE_v0: SINGLE_ACTIVE_ROW_REQUIRED",
        "EM_U1_ASSUMPTION_REGISTRY_SYNC_GATE_v0: DIFFERENTIAL_BUNDLE_IDS_REQUIRED",
        "EM_U1_MAXWELL_FORM_AUTHORIZATION_GATE_v0: LOCKED_UNTIL_CYCLE3_ADJUDICATION_FLIP",
        "ASM-EM-U1-STR-01",
        "ASM-EM-U1-SYM-01",
        "formal/python/tests/test_em_u1_micro03_predischarge_gate_bundle.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM Cycle-003 micro document is missing required token(s): " + ", ".join(missing)
    adjudication_value = _extract_cycle3_adjudication_value(text)
    assert adjudication_value in {"NOT_YET_DISCHARGED", "DISCHARGED_CONDITIONAL_v0"}, (
        "Cycle-003 adjudication value is outside allowed transition values: " + adjudication_value
    )


def test_em_target_references_cycle003_artifact_and_gate_tokens() -> None:
    text = _read(EM_TARGET_PATH)
    required_tokens = [
        "TARGET-EM-U1-MICRO-03-PREDISCHARGE-GATE-BUNDLE-v0",
        "EM_U1_PROGRESS_CYCLE3_v0: PREDISCHARGE_GATE_BUNDLE_TOKEN_PINNED",
        "EM_U1_MICRO03_PREDISCHARGE_GATE_BUNDLE_ADJUDICATION:",
        "EM_U1_OBJECT_ROUTE_ARTIFACT_UNIQUENESS_GATE_v0: SINGLE_AUTHORITATIVE_ARTIFACT_SET_REQUIRED",
        "EM_U1_ROADMAP_ROW_UNIQUENESS_GATE_v0: SINGLE_ACTIVE_ROW_REQUIRED",
        "EM_U1_ASSUMPTION_REGISTRY_SYNC_GATE_v0: DIFFERENTIAL_BUNDLE_IDS_REQUIRED",
        "EM_U1_MAXWELL_FORM_AUTHORIZATION_GATE_v0: LOCKED_UNTIL_CYCLE3_ADJUDICATION_FLIP",
        "formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_03_PREDISCHARGE_GATE_BUNDLE_v0.md",
        "formal/python/tests/test_em_u1_micro03_predischarge_gate_bundle.py",
        "ASM-EM-U1-STR-01",
        "ASM-EM-U1-SYM-01",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM target document is missing required Cycle-003 token(s): " + ", ".join(missing)
    adjudication_value = _extract_cycle3_adjudication_value(text)
    assert adjudication_value in {"NOT_YET_DISCHARGED", "DISCHARGED_CONDITIONAL_v0"}, (
        "EM target Cycle-003 adjudication value is outside allowed transition values: " + adjudication_value
    )


def test_em_roadmap_row_and_artifact_lists_are_unique_and_authoritative() -> None:
    roadmap_text = _read(EM_ROADMAP_PATH)
    cells = _em_roadmap_row_cells(roadmap_text)

    targets_raw = _strip_wrapping_backticks(cells[3])
    artifacts_raw = _strip_wrapping_backticks(cells[4])

    targets = [item.strip() for item in targets_raw.split(";") if item.strip()]
    artifacts = [item.strip() for item in artifacts_raw.split(";") if item.strip()]

    assert len(targets) == len(set(targets)), "EM roadmap target list contains duplicate entries."
    assert len(artifacts) == len(set(artifacts)), "EM roadmap artifact list contains duplicate entries."

    required_targets = {
        "TARGET-EM-U1-MICRO-01-OBJECT-SCAFFOLD-v0",
        "TARGET-EM-U1-MICRO-02-GAUGE-CONTRACT-SURFACE-v0",
        "TARGET-EM-U1-MICRO-03-PREDISCHARGE-GATE-BUNDLE-v0",
    }
    missing_targets = sorted(required_targets.difference(targets))
    assert not missing_targets, "EM roadmap row is missing required micro-target(s): " + ", ".join(missing_targets)

    required_artifacts = {
        "formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_01_OBJECT_SCAFFOLD_v0.md",
        "formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_02_GAUGE_CONTRACT_SURFACE_v0.md",
        "formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_03_PREDISCHARGE_GATE_BUNDLE_v0.md",
        "formal/toe_formal/ToeFormal/EM/U1/ObjectScaffold.lean",
    }
    missing_artifacts = sorted(required_artifacts.difference(artifacts))
    assert not missing_artifacts, (
        "EM roadmap row is missing required object-route artifact(s): " + ", ".join(missing_artifacts)
    )


def test_em_differential_bundle_assumptions_are_registry_explicit() -> None:
    text = _read(ASSUMPTION_REGISTRY_PATH)
    required_tokens = [
        "| `ASM-EM-U1-STR-01` |",
        "| `ASM-EM-U1-SYM-01` |",
        "em_u1_field_strength_invariance_under_contract_assumptions_v0",
        "- `ASM-EM-U1-STR-01`",
        "- `ASM-EM-U1-SYM-01`",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "Assumption registry is missing required EM differential-bundle linkage token(s): " + ", ".join(
        missing
    )


def test_maxwell_form_expressions_remain_locked_before_cycle003_adjudication_flip() -> None:
    micro03_text = _read(EM_MICRO03_PATH)
    adjudication_value = _extract_cycle3_adjudication_value(micro03_text)

    if adjudication_value.startswith("DISCHARGED"):
        return

    forbidden_equation_patterns = [
        r"∇\s*·\s*E\s*=",
        r"∇\s*×\s*B\s*=",
        r"∂\s*_\s*μ\s*F\s*\^?\s*μ\s*ν\s*=",
        r"dF\s*=\s*0",
        r"d\*F\s*=\s*J",
    ]
    guarded_paths = [EM_TARGET_PATH, EM_MICRO01_PATH, EM_MICRO02_PATH, EM_MICRO03_PATH]

    violations: list[str] = []
    for path in guarded_paths:
        text = _read(path)
        for pattern in forbidden_equation_patterns:
            if re.search(pattern, text):
                violations.append(f"{path.relative_to(REPO_ROOT)} -> {pattern}")

    assert not violations, (
        "Maxwell-form authorization gate is locked (Cycle-003 adjudication not discharged), "
        "but Maxwell-equation-form expressions were detected:\n- " + "\n- ".join(violations)
    )


def test_em_lean_cycle003_gate_tokens_are_pinned() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    required_tokens = [
        "EM_U1_OBJECT_ROUTE_ARTIFACT_UNIQUENESS_GATE_v0: SINGLE_AUTHORITATIVE_ARTIFACT_SET_REQUIRED",
        "EM_U1_ROADMAP_ROW_UNIQUENESS_GATE_v0: SINGLE_ACTIVE_ROW_REQUIRED",
        "EM_U1_ASSUMPTION_REGISTRY_SYNC_GATE_v0: DIFFERENTIAL_BUNDLE_IDS_REQUIRED",
        "EM_U1_MAXWELL_FORM_AUTHORIZATION_GATE_v0: LOCKED_UNTIL_CYCLE3_ADJUDICATION_FLIP",
        "theorem em_u1_cycle003_token_binding_stub_v0",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM U1 Lean scaffold is missing required Cycle-003 gate token(s): " + ", ".join(missing)

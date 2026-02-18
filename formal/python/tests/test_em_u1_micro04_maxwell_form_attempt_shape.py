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
EM_MICRO04_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_EM_U1_MICRO_04_MAXWELL_FORM_ATTEMPT_PACKAGE_v0.md"
)
EM_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
EM_OBJECT_SCAFFOLD_LEAN_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "EM" / "U1" / "ObjectScaffold.lean"

MAXWELL_SHAPE_PATTERNS = {
    "gauss_e": r"∇\s*·\s*E\s*=\s*ρ",
    "ampere_maxwell": r"∇\s*×\s*B\s*=\s*J\s*\+\s*∂E/∂t",
    "gauss_b": r"∇\s*·\s*B\s*=\s*0",
    "faraday": r"∇\s*×\s*E\s*=\s*-\s*∂B/∂t",
    "covariant": r"∂\s*_\s*μ\s*F\^μν\s*=\s*J\^ν",
    "bianchi": r"dF\s*=\s*0",
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _extract_cycle3_adjudication_value() -> str:
    text = _read(EM_MICRO03_PATH)
    m = re.search(
        r"EM_U1_MICRO03_PREDISCHARGE_GATE_BUNDLE_ADJUDICATION:\s*`?([A-Za-z0-9_<>\-_]+)`?",
        text,
    )
    assert m is not None, "Cycle-003 adjudication token is missing from the micro-03 artifact."
    return m.group(1)


def _is_cycle3_authorized(adjudication_value: str) -> bool:
    return adjudication_value.startswith("DISCHARGED")


def _strip_wrapping_backticks(text: str) -> str:
    s = text.strip()
    if s.startswith("`") and s.endswith("`") and len(s) >= 2:
        return s[1:-1]
    return s


def test_em_cycle004_artifacts_exist() -> None:
    assert EM_MICRO04_PATH.exists(), "Missing EM U1 Cycle-004 Maxwell-form attempt package document."
    assert EM_TARGET_PATH.exists(), "Missing EM U1 target document."
    assert EM_MICRO03_PATH.exists(), "Missing EM U1 Cycle-003 gate-bundle document."
    assert EM_ROADMAP_PATH.exists(), "Missing physics roadmap document."
    assert EM_OBJECT_SCAFFOLD_LEAN_PATH.exists(), "Missing EM U1 object scaffold Lean module."


def test_em_micro04_contains_required_tokens() -> None:
    text = _read(EM_MICRO04_PATH)
    required_tokens = [
        "DERIVATION_TARGET_EM_U1_MICRO_04_MAXWELL_FORM_ATTEMPT_PACKAGE_v0",
        "TARGET-EM-U1-MICRO-04-MAXWELL-FORM-ATTEMPT-v0",
        "EM_U1_PROGRESS_CYCLE4_v0: MAXWELL_FORM_ATTEMPT_PACKAGE_TOKEN_PINNED",
        "EM_U1_MAXWELL_FORM_SHAPE_GATE_v0: AUTHORIZED_PRESENCE_ONLY",
        "EM_U1_MAXWELL_FORM_LOCALIZATION_GATE_v0: CYCLE4_ARTIFACT_ONLY",
        "EM_U1_MICRO04_MAXWELL_FORM_ATTEMPT_ADJUDICATION: NOT_YET_DISCHARGED",
        "EM_U1_MICRO03_PREDISCHARGE_GATE_BUNDLE_ADJUDICATION: DISCHARGED_CONDITIONAL_v0",
        "formal/python/tests/test_em_u1_micro04_maxwell_form_attempt_shape.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM Cycle-004 micro document is missing required token(s): " + ", ".join(missing)


def test_em_target_references_cycle004_package_and_authorization_tokens() -> None:
    text = _read(EM_TARGET_PATH)
    required_tokens = [
        "TARGET-EM-U1-MICRO-04-MAXWELL-FORM-ATTEMPT-v0",
        "EM_U1_PROGRESS_CYCLE4_v0: MAXWELL_FORM_ATTEMPT_PACKAGE_TOKEN_PINNED",
        "EM_U1_MAXWELL_FORM_SHAPE_GATE_v0: AUTHORIZED_PRESENCE_ONLY",
        "EM_U1_MAXWELL_FORM_LOCALIZATION_GATE_v0: CYCLE4_ARTIFACT_ONLY",
        "EM_U1_MICRO03_PREDISCHARGE_GATE_BUNDLE_ADJUDICATION: DISCHARGED_CONDITIONAL_v0",
        "formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_04_MAXWELL_FORM_ATTEMPT_PACKAGE_v0.md",
        "formal/python/tests/test_em_u1_micro04_maxwell_form_attempt_shape.py",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM target document is missing required Cycle-004 token(s): " + ", ".join(missing)


def test_em_roadmap_references_cycle004_target_and_artifact() -> None:
    roadmap_text = _read(EM_ROADMAP_PATH)
    rows = [line.strip() for line in roadmap_text.splitlines() if line.strip().startswith("| `PILLAR-EM` |")]
    assert len(rows) == 1, f"Expected one `PILLAR-EM` roadmap row, found {len(rows)}."
    cells = [cell.strip() for cell in rows[0].split("|")]
    assert len(cells) >= 7, "Malformed `PILLAR-EM` roadmap row."
    targets_raw = _strip_wrapping_backticks(cells[3])
    artifacts_raw = _strip_wrapping_backticks(cells[4])
    targets = {item.strip() for item in targets_raw.split(";") if item.strip()}
    artifacts = {item.strip() for item in artifacts_raw.split(";") if item.strip()}
    assert "TARGET-EM-U1-MICRO-04-MAXWELL-FORM-ATTEMPT-v0" in targets
    assert "formal/docs/paper/DERIVATION_TARGET_EM_U1_MICRO_04_MAXWELL_FORM_ATTEMPT_PACKAGE_v0.md" in artifacts


def test_maxwell_form_shapes_are_authorization_gated_and_localized() -> None:
    cycle3_adjudication = _extract_cycle3_adjudication_value()
    authorized = _is_cycle3_authorized(cycle3_adjudication)

    micro04_text = _read(EM_MICRO04_PATH)
    non_cycle4_paths = [EM_TARGET_PATH, EM_MICRO01_PATH, EM_MICRO02_PATH, EM_MICRO03_PATH]

    if authorized:
        missing_shapes = [
            label for label, pattern in MAXWELL_SHAPE_PATTERNS.items() if re.search(pattern, micro04_text) is None
        ]
        assert not missing_shapes, (
            "Cycle-003 authorization is discharged, but Cycle-004 Maxwell-form shapes are missing: "
            + ", ".join(sorted(missing_shapes))
        )

        leakage: list[str] = []
        for path in non_cycle4_paths:
            text = _read(path)
            for label, pattern in MAXWELL_SHAPE_PATTERNS.items():
                if re.search(pattern, text) is not None:
                    leakage.append(f"{label} in {path.relative_to(REPO_ROOT)}")
        assert not leakage, (
            "Maxwell-form shapes must remain localized to the Cycle-004 artifact. Leakage detected:\n- "
            + "\n- ".join(leakage)
        )
        return

    present_shapes = [label for label, pattern in MAXWELL_SHAPE_PATTERNS.items() if re.search(pattern, micro04_text)]
    assert not present_shapes, (
        "Cycle-003 authorization is not discharged, so Cycle-004 Maxwell-form shapes must be absent. Found: "
        + ", ".join(sorted(present_shapes))
    )


def test_em_lean_cycle004_tokens_are_pinned() -> None:
    text = _read(EM_OBJECT_SCAFFOLD_LEAN_PATH)
    required_tokens = [
        "EM_U1_PROGRESS_CYCLE4_v0: MAXWELL_FORM_ATTEMPT_PACKAGE_TOKEN_PINNED",
        "EM_U1_MAXWELL_FORM_SHAPE_GATE_v0: AUTHORIZED_PRESENCE_ONLY",
        "EM_U1_MAXWELL_FORM_LOCALIZATION_GATE_v0: CYCLE4_ARTIFACT_ONLY",
        "theorem em_u1_cycle004_token_binding_stub_v0",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "EM U1 Lean scaffold is missing required Cycle-004 token(s): " + ", ".join(missing)

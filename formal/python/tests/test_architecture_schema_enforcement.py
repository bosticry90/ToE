from __future__ import annotations

import json
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
ARCHITECTURE_SCHEMA_PATH = REPO_ROOT / "ARCHITECTURE_SCHEMA_v1.json"
DERIVATION_TARGET_DIR = REPO_ROOT / "formal" / "docs" / "paper"

EXPECTED_REQUIRED_PHASES = [
    "TARGET_DEFINITION",
    "ASSUMPTION_FREEZE",
    "CANONICAL_ROUTE",
    "ANTI_SHORTCUT",
    "COUNTERFACTUAL",
    "INDEPENDENT_NECESSITY",
    "HARDENING",
    "BOUNDED_SCOPE",
    "DRIFT_GATES",
    "ADJUDICATION_SYNC",
]
EXPECTED_ALLOWED_TOKEN_CLASSES = [
    "STRUCTURAL",
    "REGIME",
    "APPROXIMATION",
    "DERIVATION",
    "INEVITABILITY",
]
EXPECTED_ALLOWED_ADJUDICATION_PREFIXES = [
    "DISCHARGED_v0",
    "T-PROVED",
    "T-CONDITIONAL",
    "LOCKED",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _derivation_target_paths() -> list[Path]:
    return sorted(DERIVATION_TARGET_DIR.glob("DERIVATION_TARGET*.md"))


def _extract_architecture_phase_tokens(text: str) -> list[str]:
    heading = re.search(r"^##\s+Architecture phase coverage \(v1\)\s*$", text, flags=re.MULTILINE)
    if heading is None:
        return []
    tail = text[heading.end() :]
    phases: list[str] = []
    for line in tail.splitlines():
        if re.match(r"^\s*##\s+", line):
            break
        m = re.match(r"^\s*-\s*`?([A-Z_]+)`?\s*$", line)
        if m:
            phases.append(m.group(1))
            continue
        if phases and line.strip():
            break
    return phases


def _iter_adjudication_values(text: str) -> list[str]:
    values: list[str] = []
    for m in re.finditer(r"\b[A-Z0-9_]+_ADJUDICATION\s*:\s*([^\n\r]+)", text):
        raw = m.group(1).strip()
        token_match = re.match(r"`?([A-Za-z0-9_<>\-_]+)`?", raw)
        if token_match is None:
            continue
        values.append(token_match.group(1))
    return values


def test_architecture_schema_shape_is_frozen() -> None:
    schema = _read_json(ARCHITECTURE_SCHEMA_PATH)

    assert schema.get("schema_id") == "ARCHITECTURE_SCHEMA_v1"
    assert schema.get("schema_version") == 1
    assert schema.get("pillar_required_phases") == EXPECTED_REQUIRED_PHASES
    assert schema.get("allowed_token_classes") == EXPECTED_ALLOWED_TOKEN_CLASSES
    assert schema.get("allowed_adjudication_prefixes") == EXPECTED_ALLOWED_ADJUDICATION_PREFIXES


def test_known_derivation_target_files_exist() -> None:
    schema = _read_json(ARCHITECTURE_SCHEMA_PATH)
    known_files = schema.get("known_derivation_target_files", [])
    assert known_files, "ARCHITECTURE_SCHEMA_v1.json must declare known_derivation_target_files."
    assert len(known_files) == len(set(known_files)), "known_derivation_target_files contains duplicates."

    missing = [
        name
        for name in known_files
        if not (DERIVATION_TARGET_DIR / name).exists()
    ]
    assert not missing, "Known derivation target file(s) missing from repo: " + ", ".join(sorted(missing))


def test_phase_coverage_is_valid_for_pillars_and_new_targets() -> None:
    schema = _read_json(ARCHITECTURE_SCHEMA_PATH)
    required = schema["pillar_required_phases"]
    known = set(schema.get("known_derivation_target_files", []))
    pillars = set(schema.get("pillar_target_files", []))

    phase_violations: list[str] = []
    for path in _derivation_target_paths():
        text = _read(path)
        phases = _extract_architecture_phase_tokens(text)
        name = path.name

        if name in pillars and phases != required:
            phase_violations.append(
                f"{name}: pillar target must declare the exact required phase sequence {required}; found {phases or '<missing>'}."
            )
            continue

        if name not in known and phases != required:
            phase_violations.append(
                f"{name}: new derivation target must declare the exact required phase sequence {required}; found {phases or '<missing>'}."
            )
            continue

        if phases and phases != required:
            phase_violations.append(
                f"{name}: architecture phase coverage contains unknown/missing phase tokens; expected {required}, found {phases}."
            )

    assert not phase_violations, "Architecture phase coverage violations:\n- " + "\n- ".join(phase_violations)


def test_adjudication_prefixes_are_frozen_for_derivation_targets() -> None:
    schema = _read_json(ARCHITECTURE_SCHEMA_PATH)
    allowed_prefixes = list(schema.get("allowed_adjudication_prefixes", []))
    allowed_prefixes.extend(schema.get("legacy_allowed_adjudication_prefixes", []))

    violations: list[str] = []
    for path in _derivation_target_paths():
        text = _read(path)
        for value in _iter_adjudication_values(text):
            if value.startswith("<"):
                continue
            if not any(value.startswith(prefix) for prefix in allowed_prefixes):
                violations.append(f"{path.name}: disallowed adjudication value '{value}'")

    assert not violations, (
        "New adjudication prefix/value detected. Add explicit governance update before introducing it:\n- "
        + "\n- ".join(violations)
    )

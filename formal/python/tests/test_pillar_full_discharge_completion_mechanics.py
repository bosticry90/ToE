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
PAPER_DIR = REPO_ROOT / "formal" / "docs" / "paper"
REGISTRY_PATH = PAPER_DIR / "PILLAR_DISCHARGE_REGISTRY_v0.json"
ROADMAP_PATH = PAPER_DIR / "PHYSICS_ROADMAP_v0.md"
RESULTS_PATH = PAPER_DIR / "RESULTS_TABLE_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _extract_token_value(token: str, text: str) -> str:
    m = re.search(rf"{re.escape(token)}:\s*([A-Za-z0-9_\-,]+)", text)
    assert m is not None, f"Missing token: {token}"
    return m.group(1)


def _results_row_status(row_id: str, results_text: str) -> str:
    m = re.search(rf"^\|\s*{re.escape(row_id)}\s*\|\s*`([^`]+)`\s*\|", results_text, flags=re.MULTILINE)
    assert m is not None, f"Missing result row: {row_id}"
    return m.group(1)


def _results_row_occurrences(row_id: str, results_text: str) -> int:
    return len(re.findall(rf"^\|\s*{re.escape(row_id)}\s*\|", results_text, flags=re.MULTILINE))


def _matrix_status_for_pillar(pillar_name: str, roadmap_text: str) -> str:
    m = re.search(
        rf"^\|\s*`{re.escape(pillar_name)}`\s*\|\s*`([^`]+)`\s*\|",
        roadmap_text,
        flags=re.MULTILINE,
    )
    assert m is not None, f"Missing roadmap row for {pillar_name}."
    return m.group(1)


def test_registry_entries_provide_generic_completion_mechanics_fields() -> None:
    registry = _read_json(REGISTRY_PATH)
    pillars = registry.get("pillars", [])
    assert isinstance(pillars, list) and pillars, "Registry must declare at least one pillar entry."

    required_fields = [
        "pillar_key",
        "pillar_name",
        "discharge_doc_path",
        "discharge_adjudication_token",
        "required_results_rows",
        "required_theorem_surfaces",
        "lean_paths",
    ]
    violations: list[str] = []

    for entry in pillars:
        missing = [field for field in required_fields if field not in entry]
        if missing:
            violations.append(
                f"Registry pillar entry {entry.get('pillar_name', '<unknown>')} missing field(s): " + ", ".join(missing)
            )
            continue
        if not entry["required_results_rows"]:
            violations.append(f"{entry['pillar_name']}: required_results_rows must be non-empty.")
        if not entry["required_theorem_surfaces"]:
            violations.append(f"{entry['pillar_name']}: required_theorem_surfaces must be non-empty.")
        elif len(entry["required_theorem_surfaces"]) != len(set(entry["required_theorem_surfaces"])):
            violations.append(f"{entry['pillar_name']}: required_theorem_surfaces must be unique.")
        if not entry["lean_paths"]:
            violations.append(f"{entry['pillar_name']}: lean_paths must be non-empty.")

    assert not violations, "Registry completion-mechanics field violation(s):\n- " + "\n- ".join(violations)


def test_registry_driven_pillar_completion_mechanics_coupling() -> None:
    registry = _read_json(REGISTRY_PATH)
    pillars = list(registry.get("pillars", []))
    roadmap_text = _read(ROADMAP_PATH)
    results_text = _read(RESULTS_PATH)

    violations: list[str] = []

    for entry in pillars:
        pillar_key = entry["pillar_key"]
        pillar_name = entry["pillar_name"]
        discharge_doc_rel = entry["discharge_doc_path"]
        discharge_doc = REPO_ROOT / Path(discharge_doc_rel)
        discharge_text = _read(discharge_doc)

        adjudication_token = entry["discharge_adjudication_token"]
        try:
            adjudication = _extract_token_value(adjudication_token, discharge_text)
        except AssertionError as err:
            violations.append(f"{pillar_name}: {err}")
            continue

        if not (adjudication == "NOT_YET_DISCHARGED" or adjudication.startswith("DISCHARGED")):
            violations.append(
                f"{pillar_name}: adjudication `{adjudication}` must be NOT_YET_DISCHARGED or DISCHARGED_*."
            )
            continue

        required_rows = list(entry["required_results_rows"])
        try:
            required_rows_raw = _extract_token_value(f"REQUIRED_{pillar_key}_CLOSURE_ROWS", roadmap_text)
        except AssertionError as err:
            violations.append(f"{pillar_name}: {err}")
            continue
        required_rows_roadmap = {x.strip() for x in required_rows_raw.split(",") if x.strip()}
        if required_rows_roadmap != set(required_rows):
            violations.append(
                f"{pillar_name}: REQUIRED_{pillar_key}_CLOSURE_ROWS mismatch "
                f"(roadmap={sorted(required_rows_roadmap)}, registry={sorted(required_rows)})."
            )

        for row_id in required_rows:
            occurrences = _results_row_occurrences(row_id, results_text)
            if occurrences != 1:
                violations.append(f"{pillar_name}: result row `{row_id}` must appear exactly once (found {occurrences}).")
                continue

            if not row_id.startswith(f"TOE-{pillar_key}-"):
                violations.append(f"{pillar_name}: result row `{row_id}` must use prefix TOE-{pillar_key}-.")

        matrix_status = _matrix_status_for_pillar(pillar_name, roadmap_text)
        physics_status = _extract_token_value(f"PILLAR-{pillar_key}_PHYSICS_STATUS", roadmap_text)
        governance_status = _extract_token_value(f"PILLAR-{pillar_key}_GOVERNANCE_STATUS", roadmap_text)
        proceed_gate = _extract_token_value(f"PROCEED_GATE_{pillar_key}", roadmap_text)
        matrix_gate = _extract_token_value(f"MATRIX_CLOSURE_GATE_{pillar_key}", roadmap_text)

        row_statuses = {row_id: _results_row_status(row_id, results_text) for row_id in required_rows}

        if adjudication == "NOT_YET_DISCHARGED":
            if matrix_status == "CLOSED":
                violations.append(f"{pillar_name}: matrix status cannot be CLOSED while adjudication is NOT_YET_DISCHARGED.")
            if not all(status.startswith("B-") for status in row_statuses.values()):
                violations.append(
                    f"{pillar_name}: required closure rows must remain blocked while adjudication is NOT_YET_DISCHARGED."
                )
            if not physics_status.startswith("OPEN_"):
                violations.append(f"{pillar_name}: PILLAR-{pillar_key}_PHYSICS_STATUS must be OPEN_* while not discharged.")
            if not governance_status.startswith("OPEN_"):
                violations.append(f"{pillar_name}: PILLAR-{pillar_key}_GOVERNANCE_STATUS must be OPEN_* while not discharged.")
            if not proceed_gate.startswith("BLOCKED_"):
                violations.append(f"{pillar_name}: PROCEED_GATE_{pillar_key} must be BLOCKED_* while not discharged.")
            if not matrix_gate.startswith("BLOCKED_"):
                violations.append(f"{pillar_name}: MATRIX_CLOSURE_GATE_{pillar_key} must be BLOCKED_* while not discharged.")
        else:
            if matrix_status != "CLOSED":
                violations.append(f"{pillar_name}: matrix status must be CLOSED when adjudication is DISCHARGED_*.")
            if any(status.startswith("B-") for status in row_statuses.values()):
                violations.append(f"{pillar_name}: required closure rows must be non-blocked when adjudication is DISCHARGED_*.")
            if not physics_status.startswith("CLOSED_"):
                violations.append(f"{pillar_name}: PILLAR-{pillar_key}_PHYSICS_STATUS must be CLOSED_* when discharged.")
            if not governance_status.startswith("CLOSED_"):
                violations.append(f"{pillar_name}: PILLAR-{pillar_key}_GOVERNANCE_STATUS must be CLOSED_* when discharged.")
            if not proceed_gate.startswith("ALLOWED_"):
                violations.append(f"{pillar_name}: PROCEED_GATE_{pillar_key} must be ALLOWED_* when discharged.")
            if not matrix_gate.startswith("ALLOWED_"):
                violations.append(f"{pillar_name}: MATRIX_CLOSURE_GATE_{pillar_key} must be ALLOWED_* when discharged.")

        theorem_surfaces = list(entry["required_theorem_surfaces"])
        missing_target_theorems = [surface for surface in theorem_surfaces if surface not in discharge_text]
        if missing_target_theorems:
            violations.append(
                f"{pillar_name}: discharge doc missing required theorem surface token(s): "
                + ", ".join(missing_target_theorems)
            )

        lean_paths = [REPO_ROOT / Path(path) for path in entry["lean_paths"]]
        missing_lean_paths = [str(path.relative_to(REPO_ROOT)) for path in lean_paths if not path.exists()]
        if missing_lean_paths:
            violations.append(f"{pillar_name}: missing Lean path(s): " + ", ".join(missing_lean_paths))
            continue

        lean_texts = [_read(path) for path in lean_paths]
        for surface in theorem_surfaces:
            found = any(re.search(rf"\b(?:theorem|def)\s+{re.escape(surface)}\b", text) for text in lean_texts)
            if not found:
                violations.append(
                    f"{pillar_name}: required theorem surface `{surface}` is not declared as theorem/def "
                    "in registry Lean paths."
                )

    assert not violations, "Registry-driven pillar completion-mechanics violation(s):\n- " + "\n- ".join(violations)

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
EM_TARGET_PATH = PAPER_DIR / "DERIVATION_TARGET_EM_U1_MAXWELL_OBJECT_v0.md"
ROADMAP_PATH = PAPER_DIR / "PHYSICS_ROADMAP_v0.md"
RESULTS_PATH = PAPER_DIR / "RESULTS_TABLE_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "em_pillar_full_discharge_adjudication_criteria_cycle46_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _extract_token_value(token: str, text: str) -> str:
    m = re.search(rf"{re.escape(token)}:\s*([A-Za-z0-9_\-,./]+)", text)
    assert m is not None, f"Missing token: {token}"
    return m.group(1)


def _results_row_status(row_id: str, results_text: str) -> str:
    m = re.search(rf"^\|\s*{re.escape(row_id)}\s*\|\s*`([^`]+)`\s*\|", results_text, flags=re.MULTILINE)
    assert m is not None, f"Missing result row: {row_id}"
    return m.group(1)


def _em_registry_entry() -> dict:
    registry = _read_json(REGISTRY_PATH)
    matches = [entry for entry in registry.get("pillars", []) if entry.get("pillar_key") == "EM"]
    assert len(matches) == 1, "Registry must contain exactly one EM pillar entry."
    return matches[0]


def _em_discharge_required_theorem_surfaces() -> set[str]:
    text = _read(EM_TARGET_PATH)
    block_match = re.search(
        r"EM full-discharge completion mechanics \(v0\):(?P<body>.*?)"
        r"- `EM_PILLAR_FULL_DISCHARGE_CRITERIA_ROW_02_v0",
        text,
        flags=re.DOTALL,
    )
    assert block_match is not None, "Could not isolate EM full-discharge completion mechanics theorem-surface block."
    return set(re.findall(r"`(em_u1_[^`]+)`", block_match.group("body")))


def test_em_adjudication_criteria_artifact_pointers_are_pinned_across_governance_surfaces() -> None:
    required_tokens = [
        "EM_PILLAR_FULL_DISCHARGE_ADJUDICATION_CRITERIA_ARTIFACT_v0: "
        "em_pillar_full_discharge_adjudication_criteria_cycle46_v0",
        "EM_PILLAR_FULL_DISCHARGE_ADJUDICATION_FLIP_GATE_v0: "
        "CRITERIA_ARTIFACT_AND_NON_BLOCKED_ROWS_REQUIRED",
        "formal/output/em_pillar_full_discharge_adjudication_criteria_cycle46_v0.json",
        "formal/python/tests/test_em_u1_full_discharge_adjudication_criteria_artifact.py",
    ]
    governance_surfaces = [EM_TARGET_PATH, STATE_PATH, ROADMAP_PATH, RESULTS_PATH]
    for path in governance_surfaces:
        text = _read(path)
        missing = [token for token in required_tokens if token not in text]
        assert not missing, f"{path} missing EM adjudication-criteria artifact token(s): " + ", ".join(missing)


def test_em_adjudication_criteria_artifact_payload_is_well_formed_and_synced() -> None:
    payload = _read_json(ARTIFACT_PATH)
    em_entry = _em_registry_entry()
    em_target_text = _read(EM_TARGET_PATH)

    assert payload.get("record_id") == "EM_PILLAR_FULL_DISCHARGE_ADJUDICATION_CRITERIA_CYCLE46_v0"
    assert payload.get("artifact_id") == "em_pillar_full_discharge_adjudication_criteria_cycle46_v0"
    assert payload.get("scope") == "em_pillar_full_discharge_adjudication_criteria_v0"
    assert payload.get("adjudication_token") == "PILLAR_EM_FULL_DERIVATION_DISCHARGE_ADJUDICATION"
    assert payload.get("adjudication_posture") == _extract_token_value(
        "PILLAR_EM_FULL_DERIVATION_DISCHARGE_ADJUDICATION", em_target_text
    )

    expected_rows = list(em_entry["required_results_rows"])
    assert payload.get("required_results_rows") == expected_rows

    artifact_required_surfaces = set(payload.get("required_theorem_surfaces", []))
    registry_required_surfaces = set(em_entry["required_theorem_surfaces"])
    discharge_required_surfaces = _em_discharge_required_theorem_surfaces()
    assert artifact_required_surfaces == registry_required_surfaces, (
        "EM adjudication-criteria artifact required theorem surfaces must match EM registry."
    )
    assert artifact_required_surfaces == discharge_required_surfaces, (
        "EM adjudication-criteria artifact required theorem surfaces must match EM discharge doc."
    )

    criteria_rows = payload.get("criteria_rows")
    assert isinstance(criteria_rows, list) and len(criteria_rows) == 2
    assert [row.get("row_id") for row in criteria_rows] == [
        "EM_PILLAR_FULL_DISCHARGE_CRITERIA_ROW_01_v0",
        "EM_PILLAR_FULL_DISCHARGE_CRITERIA_ROW_02_v0",
    ]
    assert all(row.get("status") == "PINNED" for row in criteria_rows)

    results_text = _read(RESULTS_PATH)
    expected_row_statuses = {row_id: _results_row_status(row_id, results_text) for row_id in expected_rows}
    assert payload.get("current_row_statuses") == expected_row_statuses

    roadmap_text = _read(ROADMAP_PATH)
    expected_gate_tokens = {
        "PILLAR-EM_PHYSICS_STATUS": _extract_token_value("PILLAR-EM_PHYSICS_STATUS", roadmap_text),
        "PILLAR-EM_GOVERNANCE_STATUS": _extract_token_value("PILLAR-EM_GOVERNANCE_STATUS", roadmap_text),
        "PROCEED_GATE_EM": _extract_token_value("PROCEED_GATE_EM", roadmap_text),
        "MATRIX_CLOSURE_GATE_EM": _extract_token_value("MATRIX_CLOSURE_GATE_EM", roadmap_text),
    }
    assert payload.get("current_roadmap_gate_tokens") == expected_gate_tokens


def test_em_adjudication_criteria_artifact_encodes_no_premature_flip() -> None:
    payload = _read_json(ARTIFACT_PATH)

    flip_preconditions = payload.get("flip_preconditions")
    assert isinstance(flip_preconditions, dict)
    assert flip_preconditions.get("adjudication_must_start_with") == "DISCHARGED_"
    assert flip_preconditions.get("required_rows_must_be_non_blocked") is True
    assert flip_preconditions.get("physics_status_must_start_with") == "CLOSED_"
    assert flip_preconditions.get("governance_status_must_start_with") == "CLOSED_"
    assert flip_preconditions.get("proceed_gate_must_start_with") == "ALLOWED_"
    assert flip_preconditions.get("matrix_gate_must_start_with") == "ALLOWED_"

    flip_readiness = payload.get("flip_readiness")
    assert isinstance(flip_readiness, dict)
    adjudication_posture = payload.get("adjudication_posture", "")
    if isinstance(adjudication_posture, str) and adjudication_posture.startswith("DISCHARGED"):
        assert flip_readiness.get("adjudication_flip_allowed_now") is True
        assert flip_readiness.get("reason") == "required_rows_non_blocked_and_roadmap_gates_closed"
    else:
        assert flip_readiness.get("adjudication_flip_allowed_now") is False
        assert flip_readiness.get("reason") == "required_rows_blocked_and_roadmap_gates_not_closed"

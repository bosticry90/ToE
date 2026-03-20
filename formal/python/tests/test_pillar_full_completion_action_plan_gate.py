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
PLAN_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PILLAR_FULL_COMPLETION_ACTION_PLAN_v0.md"
RESULTS_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "RESULTS_TABLE_v0.md"
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PILLAR_PHASE_ADVANCEMENT_REGISTRY_v0.json"
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PILLAR_STATUS_MATRIX_v1.json"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
SUITE_PATH = REPO_ROOT / "governance_suite.ps1"

GATE_REL = "formal/python/tests/test_pillar_full_completion_action_plan_gate.py"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _pillar_roadmap_statuses(roadmap_text: str) -> dict[str, str]:
    pattern = re.compile(r"^\|\s*`(PILLAR-[A-Z0-9-]+)`\s*\|\s*`([^`]+)`\s*\|", flags=re.MULTILINE)
    return {pillar_id: status for pillar_id, status in pattern.findall(roadmap_text)}


def _blocked_pillar_rows(results_text: str) -> list[str]:
    pattern = re.compile(r"^\|\s*(TOE-(?:GR|QM|EM|SR|QFT|STAT|COSMO)-[^|]+)\s*\|\s*`B-BLOCKED`\s*\|", flags=re.MULTILINE)
    return pattern.findall(results_text)


def _conditional_derivation_rows(results_text: str) -> list[str]:
    pattern = re.compile(r"^\|\s*(TOE-(?:GR|QM|EM|SR|QFT|STAT|COSMO)-DER-[0-9]+)\s*\|\s*`T-CONDITIONAL`\s*\|", flags=re.MULTILINE)
    return pattern.findall(results_text)


def _policy_derivation_rows(results_text: str) -> list[str]:
    pattern = re.compile(r"^\|\s*(TOE-(?:GR|QM|EM|SR|QFT|STAT|COSMO)-DER-[0-9]+)\s*\|\s*`P-POLICY`\s*\|", flags=re.MULTILINE)
    return pattern.findall(results_text)


def test_full_completion_plan_contract_and_gate_wiring() -> None:
    plan_text = _read(PLAN_PATH)
    suite_text = _read(SUITE_PATH)

    required_plan_tokens = [
        "PILLAR_FULL_COMPLETION_ACTION_PLAN_v0",
        "## Full-Completion Definition",
        "## Program Phases",
        "### Phase 1: Normalize Completion Contract",
        "### Phase 2: Resolve Non-Terminal Modes",
        "### Phase 3: Clear Blocked and Conditional Derivation Debt",
        "### Phase 4: Cross-Pillar Unification and Residual-Risk Closure",
        "## Recommended Execution Order",
        "./governance_suite.ps1",
    ]
    missing = [token for token in required_plan_tokens if token not in plan_text]
    assert not missing, "Full-completion plan is missing required token(s): " + ", ".join(missing)

    assert GATE_REL in suite_text, "governance_suite.ps1 must include the full-completion action-plan gate."


def test_full_completion_gap_visibility_and_attestation_rule() -> None:
    registry = _read_json(REGISTRY_PATH)
    matrix = _read_json(MATRIX_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    results_text = _read(RESULTS_PATH)
    state_text = _read(STATE_PATH)

    matrix_pillars = matrix.get("pillars", {})
    assert isinstance(matrix_pillars, dict) and matrix_pillars, "Pillar matrix must define pillars."

    roadmap_statuses = _pillar_roadmap_statuses(roadmap_text)
    pillar_ids = [
        "PILLAR-GR",
        "PILLAR-QM",
        "PILLAR-EM",
        "PILLAR-SR",
        "PILLAR-QFT",
        "PILLAR-STAT",
        "PILLAR-COSMO",
    ]

    for pillar_id in pillar_ids:
        matrix_row = matrix_pillars.get(pillar_id)
        assert isinstance(matrix_row, dict), f"{pillar_id} must exist in matrix."
        assert matrix_row.get("matrix_status") == "CLOSED", f"{pillar_id} matrix status must be CLOSED."
        if pillar_id == "PILLAR-STAT":
            assert roadmap_statuses.get(pillar_id) in {"ACTIVE", "CLOSED"}, (
                "PILLAR-STAT roadmap status may remain ACTIVE during staged handoff."
            )
        else:
            assert roadmap_statuses.get(pillar_id) == "CLOSED", f"{pillar_id} roadmap status must be CLOSED."

    non_terminal_modes = sorted(
        row.get("mode")
        for row in registry.get("pillars", [])
        if row.get("mode") in {"ACTIVE_EXECUTION", "LOCKED_QUEUE", "PHASE_ORDERED"}
    )
    blocked_rows = _blocked_pillar_rows(results_text)
    conditional_der_rows = _conditional_derivation_rows(results_text)
    policy_der_rows = _policy_derivation_rows(results_text)

    # Until completion debt is gone, the project remains in planning/execution posture.
    if non_terminal_modes or blocked_rows or conditional_der_rows or policy_der_rows:
        assert "Status: Active Planning" in _read(PLAN_PATH)
        return

    # If no detectable debt remains, require an explicit state attestation token.
    assert "PILLAR_FULL_COMPLETION_ATTESTATION_v0: COMPLETE" in state_text, (
        "Full-completion attestation token is required once non-terminal modes, blocked rows, and conditional DER rows are cleared."
    )
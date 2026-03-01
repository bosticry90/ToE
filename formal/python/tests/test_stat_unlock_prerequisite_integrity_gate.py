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
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PILLAR_STATUS_MATRIX_v1.json"
RESULTS_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "RESULTS_TABLE_v0.md"
THERMO_TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_THERMO_ENTROPY_OBJECT_v0.md"
STAT_PLAN_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_STAT_ENTROPY_PLAN_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
STAT_CONTRACT_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PILLAR_STAT_PHASE_ADVANCEMENT_CONTRACT_v0.md"
PHASE_REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PILLAR_PHASE_ADVANCEMENT_REGISTRY_v0.json"
CHECKLIST_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PILLAR_STAT_UNLOCK_READINESS_CHECKLIST_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _extract_single_token_value(text: str, token_name: str) -> str:
    matches = re.findall(rf"\b{re.escape(token_name)}\s*:\s*([^\n]+)", text)
    assert len(matches) == 1, f"Expected exactly one `{token_name}` definition, found {len(matches)}."
    return matches[0].strip().strip("`")


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def _pillar_table_row(text: str, pillar_id: str) -> str:
    rows = [line for line in text.splitlines() if line.strip().startswith(f"| `{pillar_id}` |")]
    assert len(rows) == 1, f"Expected exactly one `{pillar_id}` row in roadmap table, found {len(rows)}."
    return rows[0]


def _extract_status_from_row(row: str) -> str:
    cols = [c.strip() for c in row.split("|") if c.strip()]
    assert len(cols) >= 2, f"Malformed pillar row: {row}"
    return cols[1].strip("`")


def _extract_prereqs_from_row(row: str) -> str:
    cols = [c.strip() for c in row.split("|") if c.strip()]
    assert len(cols) >= 5, f"Malformed pillar row: {row}"
    return cols[4].strip("`")


def _results_labels_by_claim(text: str) -> dict[str, str]:
    claim_to_label: dict[str, str] = {}
    pattern = re.compile(r"^\|\s*([^|]+?)\s*\|\s*`([^`]+)`\s*\|", re.MULTILINE)
    for claim, label in pattern.findall(text):
        claim_to_label[claim.strip()] = label.strip()
    return claim_to_label


def _roadmap_active_pillars(text: str) -> list[str]:
    pattern = re.compile(r"^\|\s*`(PILLAR-[^`]+)`\s*\|\s*`([A-Z]+)`\s*\|", re.MULTILINE)
    return [pillar for pillar, status in pattern.findall(text) if status == "ACTIVE"]


def test_stat_unlock_prerequisite_integrity_gate() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    matrix = _read_json(MATRIX_PATH)
    results_text = _read(RESULTS_PATH)
    thermo_target_text = _read(THERMO_TARGET_PATH)
    stat_plan_text = _read(STAT_PLAN_PATH)
    state_text = _read(STATE_PATH)
    contract_text = _read(STAT_CONTRACT_PATH)
    phase_registry = _read_json(PHASE_REGISTRY_PATH)
    checklist_text = _read(CHECKLIST_PATH)

    stat_row = _pillar_table_row(roadmap_text, "PILLAR-STAT")
    stat_status = _extract_status_from_row(stat_row)
    assert stat_status in {"LOCKED", "ACTIVE", "CLOSED"}, (
        "PILLAR-STAT prerequisite integrity gate expects LOCKED, ACTIVE, or CLOSED posture."
    )
    assert "`TARGET-TH-ENTROPY-PLAN`" in stat_row
    assert "`TARGET-GR01-DERIV-CHECKLIST-PLAN`" in stat_row

    stat_matrix = matrix.get("pillars", {}).get("PILLAR-STAT")
    if stat_status == "ACTIVE":
        assert isinstance(stat_matrix, dict), "PILLAR-STAT matrix row must exist after activation."
        assert stat_matrix.get("matrix_status") in {"ACTIVE", "CLOSED"}, "PILLAR-STAT matrix status must be ACTIVE or CLOSED."
        assert stat_matrix.get("matrix_status") == stat_status, "PILLAR-STAT matrix status must mirror roadmap posture."
    elif stat_status == "CLOSED":
        assert isinstance(stat_matrix, dict), "PILLAR-STAT matrix row must exist in CLOSED posture."
        assert stat_matrix.get("matrix_status") in {"ACTIVE", "CLOSED"}, "PILLAR-STAT matrix status must be ACTIVE or CLOSED."
        assert stat_matrix.get("matrix_status") == stat_status, "PILLAR-STAT matrix status must mirror roadmap posture."

    assert "`TOE-STAT-*` -> `TARGET-TH-ENTROPY-PLAN`" in roadmap_text

    gr_matrix = matrix.get("pillars", {}).get("PILLAR-GR")
    assert isinstance(gr_matrix, dict), "PILLAR-GR matrix row is missing."
    assert gr_matrix.get("matrix_status") == "CLOSED", "PILLAR-GR must remain CLOSED for STAT unlock readiness."

    active_matrix_pillars = [
        pillar_id for pillar_id, entry in matrix.get("pillars", {}).items() if entry.get("matrix_status") == "ACTIVE"
    ]
    active_roadmap_pillars = _roadmap_active_pillars(roadmap_text)
    assert len(active_matrix_pillars) <= 1, "Pillar status matrix may admit at most one ACTIVE pillar."
    assert len(active_roadmap_pillars) <= 1, "Roadmap pillar table may admit at most one ACTIVE pillar."
    if stat_status == "ACTIVE":
        assert active_matrix_pillars == ["PILLAR-STAT"], "ACTIVE matrix posture must be solely owned by PILLAR-STAT."
        assert active_roadmap_pillars == ["PILLAR-STAT"], "ACTIVE roadmap posture must be solely owned by PILLAR-STAT."

    required_rows_raw = _extract_single_token_value(roadmap_text, "REQUIRED_GR_CLOSURE_ROWS")
    required_rows = [token.strip().strip("`") for token in required_rows_raw.split(",") if token.strip()]
    assert required_rows, "REQUIRED_GR_CLOSURE_ROWS must not be empty."

    claim_labels = _results_labels_by_claim(results_text)
    for claim in required_rows:
        assert claim in claim_labels, f"Required prerequisite row `{claim}` missing in RESULTS_TABLE_v0.md."
        assert not claim_labels[claim].startswith("B-"), (
            f"Required prerequisite row `{claim}` is still blocker-labeled: `{claim_labels[claim]}`."
        )

    qft_row = _pillar_table_row(roadmap_text, "PILLAR-QFT")
    qft_prereqs = _extract_prereqs_from_row(qft_row)
    assert "TARGET-TH-ENTROPY-PLAN" not in qft_prereqs, (
        "QFT prerequisite set must not depend on STAT target during readiness lane."
    )

    assert "Target ID:\n- `TARGET-TH-ENTROPY-PLAN`" in thermo_target_text
    assert "Target ID:\n- `TARGET-TH-ENTROPY-PLAN`" in stat_plan_text

    assert "ASM-QM-" not in thermo_target_text
    assert "ASM-QFT-" not in thermo_target_text
    assert "ASM-QM-" not in stat_plan_text
    assert "ASM-QFT-" not in stat_plan_text

    registry_entries = phase_registry.get("pillars", [])
    assert isinstance(registry_entries, list), "Phase advancement registry must expose a `pillars` list."
    stat_registry_entry = next((entry for entry in registry_entries if entry.get("pillar_id") == "PILLAR-STAT"), None)
    assert isinstance(stat_registry_entry, dict), "Phase advancement registry must include a PILLAR-STAT entry."
    assert stat_registry_entry.get("mode") == "ACTIVE_EXECUTION", "PILLAR-STAT must remain in ACTIVE_EXECUTION mode."
    assert stat_registry_entry.get("contract_doc_path") == "formal/docs/release/PILLAR_STAT_PHASE_ADVANCEMENT_CONTRACT_v0.md"
    assert stat_registry_entry.get("expected_matrix_status") in {"ACTIVE", "CLOSED"}
    assert stat_registry_entry.get("expected_roadmap_status") in {"ACTIVE", "CLOSED"}
    if stat_status in {"ACTIVE", "CLOSED"}:
        assert stat_registry_entry.get("expected_matrix_status") == stat_status
        assert stat_registry_entry.get("expected_roadmap_status") == stat_status

    required_tokens = stat_registry_entry.get("required_tokens")
    assert isinstance(required_tokens, dict), "PILLAR-STAT registry entry must pin required phase-advancement tokens."
    expected_tokens = {
        "STAT_NEXT_EXECUTION_PHASE_v0": "SCAFFOLD_PHASE_REOPEN_ENTRY",
        "STAT_NEXT_EXECUTION_OBJECTIVE_v0": "FLIP_STAT_SCAFFOLD_PHASE_REOPEN_TOKEN_BEFORE_COMPONENT_GATE_EXPANSION",
        "STAT_NEXT_EXECUTION_TOKEN_v0": "STAT_SCAFFOLD_PHASE_REOPEN_TOKEN_v0",
        "STAT_NEXT_EXECUTION_TOKEN_STATE_v0": "NOT_PRESENT_v0",
        "STAT_FAILURE_TRIGGER_DISCHARGE_OBJECT_SURFACE_STATUS_v0": "OBJECT_SURFACE_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_FAILURE_TRIGGER_DISCHARGE_COHERENCE_STATUS_v0": "COHERENCE_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_DISCHARGE_COMPLETION_TRANSITION_STATUS_v0": "DISCHARGE_COMPLETION_TRANSITION_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_ADJUDICATION_TRANSITION_STATUS_v0": "ADJUDICATION_TRANSITION_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_INEVITABILITY_TRANSITION_STATUS_v0": "INEVITABILITY_TRANSITION_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_NONFLIP_EXECUTION_BOUNDARY_STATUS_v0": "NONFLIP_EXECUTION_BOUNDARY_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_NONFLIP_EXECUTION_CUSTODY_STATUS_v0": "NONFLIP_EXECUTION_CUSTODY_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_STATUS_v0": "NONFLIP_EXECUTION_CUSTODY_ATTESTATION_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_STATUS_v0": "NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_STATUS_v0": "NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_STATUS_v0": "NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_STATUS_v0": "NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_STATUS_v0": "NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_STATUS_v0": "NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_STATUS_v0": "NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_STATUS_v0": "NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_STATUS_v0": "NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_STATUS_v0": "NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_SCAFFOLD_PINNED_NONCLAIM",
    }
    for token_name, expected in expected_tokens.items():
        assert required_tokens.get(token_name) == expected, f"Phase registry drift detected for `{token_name}`."
        for surface_text, surface_label in (
            (stat_plan_text, "STAT plan"),
            (roadmap_text, "roadmap"),
            (state_text, "state"),
            (contract_text, "phase-advancement contract"),
        ):
            assert _extract_token(surface_text, token_name) == expected, (
                f"{surface_label} must pin `{token_name}` as `{expected}`."
            )

    assert "formal/python/tests/test_stat_failure_trigger_discharge_object_surface_status_cycle01_gate.py" in checklist_text
    assert "formal/python/tests/test_stat_failure_trigger_discharge_coherence_status_cycle01_gate.py" in checklist_text
    assert "formal/python/tests/test_stat_discharge_completion_transition_status_cycle01_gate.py" in checklist_text
    assert "formal/python/tests/test_stat_adjudication_transition_status_cycle01_gate.py" in checklist_text
    assert "formal/python/tests/test_stat_inevitability_transition_status_cycle01_gate.py" in checklist_text
    assert "formal/python/tests/test_stat_nonflip_execution_boundary_status_cycle01_gate.py" in checklist_text
    assert "formal/python/tests/test_stat_nonflip_execution_custody_status_cycle01_gate.py" in checklist_text
    assert "formal/python/tests/test_stat_nonflip_execution_custody_attestation_status_cycle01_gate.py" in checklist_text
    assert "formal/python/tests/test_stat_nonflip_execution_custody_attestation_confirmation_status_cycle01_gate.py" in checklist_text
    assert "formal/python/tests/test_stat_nonflip_execution_custody_attestation_confirmation_attestation_status_cycle01_gate.py" in checklist_text
    assert "formal/python/tests/test_stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_status_cycle01_gate.py" in checklist_text
    assert "formal/python/tests/test_stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_status_cycle01_gate.py" in checklist_text
    assert "formal/python/tests/test_stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_status_cycle01_gate.py" in checklist_text
    assert "formal/python/tests/test_stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_status_cycle01_gate.py" in checklist_text
    assert "formal/python/tests/test_stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_cycle01_gate.py" in checklist_text
    assert "formal/python/tests/test_stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_cycle01_gate.py" in checklist_text
    assert "formal/python/tests/test_stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_status_cycle01_gate.py" in checklist_text
    assert "formal/python/tests/test_stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_status_cycle01_gate.py" in checklist_text
    assert "formal/python/tests/test_stat_unlock_prerequisite_integrity_gate.py" in checklist_text
    assert "formal/python/tests/test_pillar_phase_advancement_gate.py" in checklist_text
    for required_surface in (
        "formal/docs/paper/DERIVATION_TARGET_STAT_ENTROPY_PLAN_v0.md",
        "formal/docs/paper/PHYSICS_ROADMAP_v0.md",
        "State_of_the_Theory.md",
        "formal/docs/release/PILLAR_STAT_PHASE_ADVANCEMENT_CONTRACT_v0.md",
        "formal/docs/release/PILLAR_PHASE_ADVANCEMENT_REGISTRY_v0.json",
    ):
        assert required_surface in checklist_text, f"Unlock readiness checklist must pin `{required_surface}`."

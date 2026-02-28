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
STAT_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_STAT_ENTROPY_PLAN_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PILLAR_STATUS_MATRIX_v1.json"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "stat_evidence_checkpoint_cycle01_v0.json"

EXPECTED_ACCEPTANCE_GATE_TOKEN = "PAYLOAD_SCHEMA_SCOPE_POINTERS_ROWS_REQUIRED"
EXPECTED_ACCEPTANCE_GATE_REL = "formal/python/tests/test_stat_evidence_checkpoint_cycle01_acceptance_gate.py"
EXPECTED_COUPLING_GATE_REL = "formal/python/tests/test_stat_evidence_checkpoint_coupling_cycle01_gate.py"
EXPECTED_ARTIFACT_REL = "formal/output/stat_evidence_checkpoint_cycle01_v0.json"

EXPECTED_SCOPE_BOUNDARY = [
    "classical_entropy_balance_scaffold_only",
    "no_cosmology_claims",
    "no_qft_statistical_ensemble_claims",
    "no_black_hole_entropy_claims",
    "no_holographic_principle_claims",
    "no_emergent_gravity_claims",
    "no_derivation_discharge_claim",
]
EXPECTED_RESULTS_ROWS = ["TOE-STAT-DER-01", "TOE-STAT-DER-02"]
EXPECTED_CROSS_SURFACE_POINTERS = [
    "formal/docs/paper/DERIVATION_TARGET_STAT_ENTROPY_PLAN_v0.md",
    "formal/docs/paper/PHYSICS_ROADMAP_v0.md",
    "State_of_the_Theory.md",
    EXPECTED_COUPLING_GATE_REL,
    EXPECTED_ACCEPTANCE_GATE_REL,
]
EXPECTED_ACCEPTANCE_CRITERIA = {
    "schema_version": "v0",
    "placeholder_posture_required": {
        "placeholder_template": True,
        "payload_status": "structural_activation_checkpoint_placeholder",
    },
    "required_payload_keys": [
        "artifact_id",
        "cycle_id",
        "target_id",
        "status",
        "scope_boundary",
        "assumption_freeze_refs",
        "required_results_rows_refs",
        "acceptance_criteria_v0",
        "cross_surface_pointers",
        "artifact_sha256",
        "generated_on",
    ],
    "required_results_rows_refs": EXPECTED_RESULTS_ROWS,
    "scope_boundary_required": EXPECTED_SCOPE_BOUNDARY,
    "cross_surface_pointers_required": EXPECTED_CROSS_SURFACE_POINTERS,
    "non_claim_constraints": [
        "no_toe_stat_der_label_promotion",
        "no_discharge_adjudication_change",
        "no_adequacy_completion_claim",
        "no_external_truth_claim",
    ],
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def test_stat_evidence_checkpoint_cycle01_acceptance_gate() -> None:
    stat_text = _read(STAT_DOC_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    matrix = _read_json(MATRIX_PATH)
    artifact = _read_json(ARTIFACT_PATH)

    assert "| `PILLAR-STAT` | `ACTIVE` |" in roadmap_text, (
        "STAT cycle01 acceptance gate applies only after `PILLAR-STAT` activation."
    )
    stat_matrix = matrix.get("pillars", {}).get("PILLAR-STAT")
    assert isinstance(stat_matrix, dict), "PILLAR-STAT matrix row must exist for STAT cycle01 acceptance gate."
    assert stat_matrix.get("matrix_status") == "ACTIVE", "PILLAR-STAT matrix row must be `ACTIVE`."

    stat_gate_token = _extract_token(stat_text, "STAT_EVIDENCE_CHECKPOINT_CYCLE01_ACCEPTANCE_GATE_v0")
    state_gate_token = _extract_token(state_text, "STAT_EVIDENCE_CHECKPOINT_CYCLE01_ACCEPTANCE_GATE_v0")
    roadmap_gate_token = _extract_token(roadmap_text, "STAT_EVIDENCE_CHECKPOINT_CYCLE01_ACCEPTANCE_GATE_v0")
    assert stat_gate_token == state_gate_token == roadmap_gate_token == EXPECTED_ACCEPTANCE_GATE_TOKEN

    for doc_text, doc_label in (
        (stat_text, "STAT plan"),
        (state_text, "state"),
        (roadmap_text, "roadmap"),
    ):
        assert EXPECTED_ARTIFACT_REL in doc_text, f"{doc_label} must pin STAT cycle01 artifact path."
        assert EXPECTED_ACCEPTANCE_GATE_REL in doc_text, f"{doc_label} must pin STAT cycle01 acceptance gate path."
        assert "STAT_EVIDENCE_CHECKPOINT_CYCLE01_ACCEPTANCE_GATE_v0" in doc_text, (
            f"{doc_label} must mirror the STAT cycle01 acceptance gate token."
        )

    assert artifact.get("artifact_id") == "stat_evidence_checkpoint_cycle01_v0"
    assert artifact.get("artifact_version") == "v0"
    assert artifact.get("placeholder_template") is True

    payload = artifact.get("payload")
    assert isinstance(payload, dict), "STAT cycle01 artifact must include an object payload."
    assert payload.get("artifact_id") == "stat_evidence_checkpoint_cycle01_v0"
    assert payload.get("cycle_id") == "CYCLE01"
    assert payload.get("target_id") == "TARGET-TH-ENTROPY-PLAN"
    assert payload.get("status") == "structural_activation_checkpoint_placeholder"
    assert payload.get("artifact_sha256") == "TOP_LEVEL_payload_sha256"

    for required_key in EXPECTED_ACCEPTANCE_CRITERIA["required_payload_keys"]:
        assert required_key in payload, f"STAT cycle01 payload missing required key `{required_key}`."

    assert payload.get("required_results_rows_refs") == EXPECTED_RESULTS_ROWS
    assert payload.get("scope_boundary") == EXPECTED_SCOPE_BOUNDARY
    assert payload.get("cross_surface_pointers") == EXPECTED_CROSS_SURFACE_POINTERS
    assert payload.get("acceptance_criteria_v0") == EXPECTED_ACCEPTANCE_CRITERIA

    acceptance = payload["acceptance_criteria_v0"]
    assert acceptance["required_results_rows_refs"] == payload["required_results_rows_refs"]
    assert acceptance["scope_boundary_required"] == payload["scope_boundary"]
    assert acceptance["cross_surface_pointers_required"] == payload["cross_surface_pointers"]
    assert acceptance["placeholder_posture_required"]["placeholder_template"] is artifact["placeholder_template"]
    assert acceptance["placeholder_posture_required"]["payload_status"] == payload["status"]

    assert "no entropy derivation discharge claim" in stat_text
    assert "no adequacy completion claim" in stat_text
    assert "do not authorize `TOE-STAT-DER-*` label promotion" in stat_text

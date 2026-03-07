from __future__ import annotations

import hashlib
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
RESULTS_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "RESULTS_TABLE_v0.md"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "stat_der02_regime_closure_coupling_scaffold_cycle01_v0.json"

EXPECTED_ARTIFACT_ID = "stat_der02_regime_closure_coupling_scaffold_cycle01_v0"
EXPECTED_GATE = "ARTIFACT_HASH_ROW_LABEL_AND_CROSS_SURFACE_POINTERS_REQUIRED"
EXPECTED_ROW_BINDING = "TOE_STAT_DER_02_T_PROVED_REGIME_VALIDITY_CLOSURE_COUPLING_SCAFFOLD_PINNED_NONCLAIM"
EXPECTED_ROW_ID = "TOE-STAT-DER-02"
EXPECTED_ROW_LABEL = "T-PROVED"
EXPECTED_ARTIFACT_REL = "formal/output/stat_der02_regime_closure_coupling_scaffold_cycle01_v0.json"
EXPECTED_GATE_REL = "formal/python/tests/test_stat_der02_regime_closure_coupling_scaffold_coupling_cycle01_gate.py"
EXPECTED_DER01_ARTIFACT_ID = "stat_der01_entropy_balance_theorem_surface_scaffold_cycle01_v0"
EXPECTED_DER01_ARTIFACT_REL = "formal/output/stat_der01_entropy_balance_theorem_surface_scaffold_cycle01_v0.json"
EXPECTED_DER01_GATE_REL = "formal/python/tests/test_stat_der01_theorem_surface_scaffold_coupling_cycle01_gate.py"
EXPECTED_DER01_DISCHARGE_ARTIFACT_ID = "stat_der01_entropy_balance_discharge_scaffold_cycle01_v0"
EXPECTED_DER01_DISCHARGE_ARTIFACT_REL = "formal/output/stat_der01_entropy_balance_discharge_scaffold_cycle01_v0.json"
EXPECTED_DER01_DISCHARGE_GATE_REL = "formal/python/tests/test_stat_der01_discharge_scaffold_coupling_cycle01_gate.py"
EXPECTED_DER01_SCOPE_BOUNDARY_ARTIFACT_ID = "stat_der01_theorem_body_scope_boundary_cycle01_v0"
EXPECTED_DER01_SCOPE_BOUNDARY_ARTIFACT_REL = "formal/output/stat_der01_theorem_body_scope_boundary_cycle01_v0.json"
EXPECTED_DER01_SCOPE_BOUNDARY_GATE_REL = "formal/python/tests/test_stat_der01_theorem_body_scope_boundary_cycle01_gate.py"
EXPECTED_DER02_SCOPE_BOUNDARY_ARTIFACT_ID = "stat_der02_theorem_body_scope_boundary_cycle01_v0"
EXPECTED_DER02_SCOPE_BOUNDARY_ARTIFACT_REL = "formal/output/stat_der02_theorem_body_scope_boundary_cycle01_v0.json"
EXPECTED_DER02_SCOPE_BOUNDARY_GATE_REL = "formal/python/tests/test_stat_der02_theorem_body_scope_boundary_cycle01_gate.py"
EXPECTED_POINTERS = [
    "formal/docs/paper/DERIVATION_TARGET_STAT_ENTROPY_PLAN_v0.md",
    "formal/docs/paper/PHYSICS_ROADMAP_v0.md",
    "State_of_the_Theory.md",
    "formal/docs/paper/RESULTS_TABLE_v0.md",
    EXPECTED_GATE_REL,
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def _payload_hash(payload: dict) -> str:
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def _results_row_line(text: str, row_id: str) -> str:
    m = re.search(rf"(?m)^\| {re.escape(row_id)} \| .*?$", text)
    assert m is not None, f"Missing results row `{row_id}`."
    return m.group(0)


def test_stat_der02_regime_closure_coupling_scaffold_coupling_cycle01_gate() -> None:
    stat_text = _read(STAT_DOC_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    results_text = _read(RESULTS_PATH)
    matrix = _read_json(MATRIX_PATH)
    artifact_json = _read_json(ARTIFACT_PATH)

    assert "| `PILLAR-STAT` | `ACTIVE` |" in roadmap_text, (
        "STAT DER02 regime-closure scaffold coupling gate applies only after `PILLAR-STAT` activation."
    )
    stat_matrix = matrix.get("pillars", {}).get("PILLAR-STAT")
    assert isinstance(stat_matrix, dict), "PILLAR-STAT matrix row must exist for DER02 regime-closure scaffold gate."
    assert stat_matrix.get("matrix_status") in {"ACTIVE", "CLOSED"}, "PILLAR-STAT matrix row must be `ACTIVE` or `CLOSED`."

    assert artifact_json.get("artifact_id") == EXPECTED_ARTIFACT_ID
    assert artifact_json.get("artifact_version") == "v0"
    assert artifact_json.get("placeholder_template") is True
    assert isinstance(artifact_json.get("payload"), dict)

    computed_payload_sha = _payload_hash(artifact_json["payload"])
    assert artifact_json.get("payload_sha256") == computed_payload_sha, (
        "STAT DER02 regime-closure scaffold payload_sha256 does not match canonical payload hash."
    )

    for token_name, expected in (
        ("STAT_DER02_REGIME_CLOSURE_COUPLING_SCAFFOLD_CYCLE01_ARTIFACT_v0", EXPECTED_ARTIFACT_ID),
        ("STAT_DER02_REGIME_CLOSURE_COUPLING_SCAFFOLD_CYCLE01_GATE_v0", EXPECTED_GATE),
        ("STAT_DER02_REGIME_CLOSURE_COUPLING_ROW_BINDING_v0", EXPECTED_ROW_BINDING),
    ):
        assert _extract_token(stat_text, token_name) == expected
        assert _extract_token(state_text, token_name) == expected
        assert _extract_token(roadmap_text, token_name) == expected

    stat_sha = _extract_token(stat_text, "STAT_DER02_REGIME_CLOSURE_COUPLING_SCAFFOLD_CYCLE01_ARTIFACT_SHA256_v0")
    state_sha = _extract_token(state_text, "STAT_DER02_REGIME_CLOSURE_COUPLING_SCAFFOLD_CYCLE01_ARTIFACT_SHA256_v0")
    roadmap_sha = _extract_token(roadmap_text, "STAT_DER02_REGIME_CLOSURE_COUPLING_SCAFFOLD_CYCLE01_ARTIFACT_SHA256_v0")
    assert stat_sha == state_sha == roadmap_sha == artifact_json["payload_sha256"]

    for doc_text, doc_label in (
        (stat_text, "STAT plan"),
        (state_text, "state"),
        (roadmap_text, "roadmap"),
    ):
        assert EXPECTED_ARTIFACT_REL in doc_text, f"{doc_label} must pin DER02 regime-closure scaffold artifact path."
        assert EXPECTED_GATE_REL in doc_text, f"{doc_label} must pin DER02 regime-closure scaffold gate path."

    row_line = _results_row_line(results_text, EXPECTED_ROW_ID)
    assert f"| {EXPECTED_ROW_ID} | `{EXPECTED_ROW_LABEL}` |" in row_line, "TOE-STAT-DER-02 row label must remain `T-PROVED`."
    assert "STAT_DER02_REGIME_CLOSURE_COUPLING_SCAFFOLD_CYCLE01_GATE_v0" in row_line
    assert "STAT_DER02_REGIME_CLOSURE_COUPLING_ROW_BINDING_v0" in row_line
    assert EXPECTED_ARTIFACT_REL in row_line
    assert EXPECTED_GATE_REL in row_line
    assert "label promotion" in row_line

    payload = artifact_json["payload"]
    assert payload.get("artifact_id") == EXPECTED_ARTIFACT_ID
    assert payload.get("cycle_id") == "CYCLE01"
    assert payload.get("pillar_id") == "PILLAR-STAT"
    assert payload.get("target_id") == "TARGET-TH-ENTROPY-PLAN"
    assert payload.get("results_row_id") == EXPECTED_ROW_ID
    assert payload.get("results_row_expected_label") == "T-PROVED"
    assert payload.get("status") == "regime_validity_closure_coupling_scaffold_placeholder_nonclaim"
    assert payload.get("artifact_sha256") == "TOP_LEVEL_payload_sha256"
    assert payload.get("cross_surface_pointers") == EXPECTED_POINTERS
    assert payload.get("prerequisite_structural_checkpoint_artifact_id") == "stat_evidence_checkpoint_cycle01_v0"
    assert payload.get("prerequisite_structural_checkpoint_gates") == [
        "formal/python/tests/test_stat_evidence_checkpoint_coupling_cycle01_gate.py",
        "formal/python/tests/test_stat_evidence_checkpoint_cycle01_acceptance_gate.py",
    ]
    assert payload.get("sibling_row_scaffold_dependency_artifact_id") == EXPECTED_DER01_ARTIFACT_ID
    assert payload.get("sibling_row_scaffold_dependency_artifact_path") == EXPECTED_DER01_ARTIFACT_REL
    assert payload.get("sibling_row_scaffold_dependency_gate") == EXPECTED_DER01_GATE_REL
    assert payload.get("sibling_der01_discharge_scaffold_dependency_artifact_id") == EXPECTED_DER01_DISCHARGE_ARTIFACT_ID
    assert payload.get("sibling_der01_discharge_scaffold_dependency_artifact_path") == EXPECTED_DER01_DISCHARGE_ARTIFACT_REL
    assert payload.get("sibling_der01_discharge_scaffold_dependency_gate") == EXPECTED_DER01_DISCHARGE_GATE_REL
    assert payload.get("sibling_der01_theorem_body_scope_boundary_dependency_artifact_id") == (
        EXPECTED_DER01_SCOPE_BOUNDARY_ARTIFACT_ID
    )
    assert payload.get("sibling_der01_theorem_body_scope_boundary_dependency_artifact_path") == (
        EXPECTED_DER01_SCOPE_BOUNDARY_ARTIFACT_REL
    )
    assert payload.get("sibling_der01_theorem_body_scope_boundary_dependency_gate") == EXPECTED_DER01_SCOPE_BOUNDARY_GATE_REL
    assert payload.get("sibling_der02_theorem_body_scope_boundary_dependency_artifact_id") == (
        EXPECTED_DER02_SCOPE_BOUNDARY_ARTIFACT_ID
    )
    assert payload.get("sibling_der02_theorem_body_scope_boundary_dependency_artifact_path") == (
        EXPECTED_DER02_SCOPE_BOUNDARY_ARTIFACT_REL
    )
    assert payload.get("sibling_der02_theorem_body_scope_boundary_dependency_gate") == EXPECTED_DER02_SCOPE_BOUNDARY_GATE_REL

    assert payload.get("regime_validity_scope") == [
        "classical_entropy_balance_regime_validity_scaffold_only",
        "bounded_equilibrium_or_near_equilibrium_placeholder",
        "no_qm_qft_statistical_ensemble_coupling_claims",
        "no_cosmology_coupling_claims",
        "no_closure_discharge_claim",
    ]
    assert payload.get("closure_coupling_requirements") == [
        "toe_stat_der_01_theorem_surface_scaffold_pointer",
        "toe_stat_der_01_discharge_scaffold_pointer",
        "toe_stat_der_01_theorem_body_scope_boundary_pointer",
        "toe_stat_der_02_theorem_body_scope_boundary_pointer",
        "assumption_freeze_pointer_surface",
        "results_row_label_persistence_pointer",
        "future_adequacy_placeholder_pointer",
        "future_coupling_gate_expansion_slot",
    ]
    assert payload.get("non_claim_boundary") == [
        "placeholder_regime_validity_closure_coupling_surface_only",
        "no_toe_stat_der_02_label_promotion",
        "no_derivation_discharge_claim",
        "no_inevitability_claim",
        "no_adequacy_completion_claim",
        "no_external_truth_claim",
    ]

    assert "does not authorize `TOE-STAT-DER-02` label promotion" in stat_text
    assert "no regime-validity discharge claim" in stat_text
    assert "no closure-coupling discharge claim" in stat_text

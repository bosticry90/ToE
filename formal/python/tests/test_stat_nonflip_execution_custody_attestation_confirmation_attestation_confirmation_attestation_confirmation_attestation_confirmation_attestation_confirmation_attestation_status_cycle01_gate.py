from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
STAT_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_STAT_ENTROPY_PLAN_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PILLAR_STATUS_MATRIX_v1.json"
CONTRACT_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PILLAR_STAT_PHASE_ADVANCEMENT_CONTRACT_v0.md"
PHASE_REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PILLAR_PHASE_ADVANCEMENT_REGISTRY_v0.json"
ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_status_cycle01_v0.json"
)
PREDECESSOR_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_status_cycle01_v0.json"
)
CURRENT_ARTIFACT_ID = (
    "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_status_cycle01_v0"
)
PREDECESSOR_ARTIFACT_ID = (
    "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_status_cycle01_v0"
)
CURRENT_ARTIFACT_TOKEN = (
    "STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_STATUS_CYCLE01_ARTIFACT_v0"
)
CURRENT_SHA_TOKEN = (
    "STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_STATUS_CYCLE01_SHA256_v0"
)
CURRENT_GATE_TOKEN = (
    "STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_STATUS_CYCLE01_GATE_v0"
)
CURRENT_STATUS_TOKEN = (
    "STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_STATUS_v0"
)
CURRENT_STATUS_VALUE = (
    "NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_SCAFFOLD_PINNED_NONCLAIM"
)
NEXT_PHASE_TOKEN = "STAT_NEXT_EXECUTION_PHASE_v0"
NEXT_PHASE_VALUE = "SCAFFOLD_PHASE_REOPEN_ENTRY"
NEXT_OBJECTIVE_TOKEN = "STAT_NEXT_EXECUTION_OBJECTIVE_v0"
NEXT_OBJECTIVE_VALUE = "FLIP_STAT_SCAFFOLD_PHASE_REOPEN_TOKEN_BEFORE_COMPONENT_GATE_EXPANSION"
NEXT_TOKEN_TOKEN = "STAT_NEXT_EXECUTION_TOKEN_v0"
NEXT_TOKEN_VALUE = "STAT_SCAFFOLD_PHASE_REOPEN_TOKEN_v0"
NEXT_TOKEN_STATE_TOKEN = "STAT_NEXT_EXECUTION_TOKEN_STATE_v0"
NEXT_TOKEN_STATE_VALUE = "NOT_PRESENT_v0"
PREDECESSOR_ARTIFACT_TOKEN = (
    "STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_STATUS_CYCLE01_ARTIFACT_v0"
)
CURRENT_SCOPE_BOUNDARY_TOKEN = (
    "STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_SCOPE_BOUNDARY_CYCLE01_ARTIFACT_v0"
)
ATTESTATION_SCOPE_BOUNDARY_TOKEN = (
    "STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_SCOPE_BOUNDARY_CYCLE01_ARTIFACT_v0"
)
EXPECTED_GATE = "ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED"
EXPECTED_ARTIFACT_REL = (
    "formal/output/stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_status_cycle01_v0.json"
)
EXPECTED_GATE_REL = (
    "formal/python/tests/test_stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_status_cycle01_gate.py"
)


def _read(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _extract_token(text: str, token_name: str) -> str:
    match = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert match is not None, f"Missing token `{token_name}`."
    return match.group(1)


def _payload_hash(payload: dict) -> str:
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def test_stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_status_cycle01_gate() -> None:
    stat_text = _read(STAT_DOC_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    contract_text = _read(CONTRACT_PATH)
    matrix = _read_json(MATRIX_PATH)
    phase_registry = _read_json(PHASE_REGISTRY_PATH)
    artifact = _read_json(ARTIFACT_PATH)
    predecessor = _read_json(PREDECESSOR_ARTIFACT_PATH)

    assert "| `PILLAR-STAT` | `ACTIVE` |" in roadmap_text
    stat_matrix = matrix.get("pillars", {}).get("PILLAR-STAT")
    assert isinstance(stat_matrix, dict)
    assert stat_matrix.get("matrix_status") in {"ACTIVE", "CLOSED"}

    assert artifact.get("artifact_id") == CURRENT_ARTIFACT_ID
    assert artifact.get("artifact_version") == "v0"
    assert artifact.get("placeholder_template") is True
    assert predecessor.get("artifact_id") == PREDECESSOR_ARTIFACT_ID
    assert artifact.get("payload_sha256") == _payload_hash(artifact["payload"])

    for doc_text in (stat_text, state_text, roadmap_text):
        assert _extract_token(doc_text, CURRENT_ARTIFACT_TOKEN) == CURRENT_ARTIFACT_ID
        assert _extract_token(doc_text, CURRENT_GATE_TOKEN) == EXPECTED_GATE
        assert _extract_token(doc_text, CURRENT_STATUS_TOKEN) == CURRENT_STATUS_VALUE
        assert _extract_token(doc_text, PREDECESSOR_ARTIFACT_TOKEN) == PREDECESSOR_ARTIFACT_ID
        assert _extract_token(doc_text, CURRENT_SCOPE_BOUNDARY_TOKEN) == (
            "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_cycle01_v0"
        )
        assert _extract_token(doc_text, ATTESTATION_SCOPE_BOUNDARY_TOKEN) == (
            "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_cycle01_v0"
        )
        assert _extract_token(doc_text, CURRENT_SHA_TOKEN) == artifact["payload_sha256"]
        assert EXPECTED_ARTIFACT_REL in doc_text
        assert EXPECTED_GATE_REL in doc_text

    for doc_text in (stat_text, state_text, roadmap_text, contract_text):
        assert _extract_token(doc_text, CURRENT_STATUS_TOKEN) == CURRENT_STATUS_VALUE
        assert _extract_token(doc_text, NEXT_PHASE_TOKEN) == NEXT_PHASE_VALUE
        assert _extract_token(doc_text, NEXT_OBJECTIVE_TOKEN) == NEXT_OBJECTIVE_VALUE
        assert _extract_token(doc_text, NEXT_TOKEN_TOKEN) == NEXT_TOKEN_VALUE
        assert _extract_token(doc_text, NEXT_TOKEN_STATE_TOKEN) == NEXT_TOKEN_STATE_VALUE
        assert _extract_token(doc_text, "STAT_SCAFFOLD_PHASE_REOPEN_TOKEN_v0") == "NOT_PRESENT_v0"

    registry_entries = phase_registry.get("pillars", [])
    assert isinstance(registry_entries, list)
    stat_entry = next((entry for entry in registry_entries if entry.get("pillar_id") == "PILLAR-STAT"), None)
    assert isinstance(stat_entry, dict)
    required_tokens = stat_entry.get("required_tokens")
    assert isinstance(required_tokens, dict)
    assert required_tokens.get(CURRENT_STATUS_TOKEN) == CURRENT_STATUS_VALUE
    assert required_tokens.get(NEXT_PHASE_TOKEN) == NEXT_PHASE_VALUE
    assert required_tokens.get(NEXT_OBJECTIVE_TOKEN) == NEXT_OBJECTIVE_VALUE
    assert required_tokens.get(NEXT_TOKEN_TOKEN) == NEXT_TOKEN_VALUE
    assert required_tokens.get(NEXT_TOKEN_STATE_TOKEN) == NEXT_TOKEN_STATE_VALUE
    assert required_tokens.get("STAT_SCAFFOLD_PHASE_REOPEN_TOKEN_v0") == "NOT_PRESENT_v0"

    payload = artifact["payload"]
    assert payload.get("checkpoint") == (
        "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_status_cycle01"
    )
    assert payload.get("status") == (
        "nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_status_non_promotional"
    )
    assert payload.get(
        "confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_entry_scope"
    ) == [
        "nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_status_placeholder_only",
        "nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_status_verified_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_status",
        "nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_status",
        "nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_status",
        "no_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_claim",
        "no_external_truth_claim",
    ]
    assert payload.get(
        "required_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_status_inputs"
    ) == [
        "evidence_adequacy_5x5_justification_present",
        "derivation_completeness_gate_readiness_packet_present",
        "failure_trigger_discharge_surface_status_pinned",
        "failure_trigger_discharge_theorem_surface_status_pinned",
        "failure_trigger_discharge_object_surface_status_pinned",
        "failure_trigger_discharge_coherence_status_pinned",
        "discharge_completion_transition_status_pinned",
        "adjudication_transition_status_pinned",
        "inevitability_transition_status_pinned",
        "nonflip_execution_boundary_status_pinned",
        "nonflip_execution_custody_status_pinned",
        "nonflip_execution_custody_attestation_status_pinned",
        "nonflip_execution_custody_attestation_confirmation_status_pinned",
        "nonflip_execution_custody_attestation_confirmation_attestation_status_pinned",
        "nonflip_execution_custody_attestation_confirmation_attestation_confirmation_status_pinned",
        "nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_status_pinned",
        "nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_status_pinned",
        "nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_status_pinned",
        "nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_status_pinned",
        "nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_status_pinned",
        "nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_status_pinned",
        "nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_pinned",
        "nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_pinned",
        "failure_trigger_audit_scope_boundary_pinned",
        "promotion_readiness_scope_boundary_pinned",
    ]
    assert payload.get("dependency_ladder") == [
        "stat_failure_trigger_discharge_surface_status_cycle01_v0",
        "stat_failure_trigger_discharge_theorem_surface_status_cycle01_v0",
        "stat_failure_trigger_discharge_object_surface_status_cycle01_v0",
        "stat_failure_trigger_discharge_coherence_status_cycle01_v0",
        "stat_discharge_completion_transition_status_cycle01_v0",
        "stat_adjudication_transition_status_cycle01_v0",
        "stat_inevitability_transition_status_cycle01_v0",
        "stat_nonflip_execution_boundary_status_cycle01_v0",
        "stat_nonflip_execution_custody_status_cycle01_v0",
        "stat_nonflip_execution_custody_attestation_status_cycle01_v0",
        "stat_nonflip_execution_custody_attestation_confirmation_status_cycle01_v0",
        "stat_nonflip_execution_custody_attestation_confirmation_attestation_status_cycle01_v0",
        "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_status_cycle01_v0",
        "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_status_cycle01_v0",
        "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_status_cycle01_v0",
        "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_status_cycle01_v0",
        "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_status_cycle01_v0",
        "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_status_cycle01_v0",
        "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_status_cycle01_v0",
        "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_cycle01_v0",
        "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_cycle01_v0",
    ]
    assert payload.get("emitted_status_tokens") == [
        f"{CURRENT_STATUS_TOKEN}: {CURRENT_STATUS_VALUE}",
        "STAT_SCAFFOLD_PHASE_REOPEN_TOKEN_v0: NOT_PRESENT_v0",
    ]
    assert payload.get("required_token_bindings") == [
        "EVIDENCE_ADEQUACY_STAT_5X5_JUSTIFICATION_v0: PRESENT",
        "STAT_DERIVATION_COMPLETENESS_GATE_READINESS_PACKET_v0: PRESENT",
        "STAT_DERIVATION_COMPLETENESS_GATE_ENTRY_STATUS_v0: DERIVATION_COMPLETENESS_GATE_ENTRY_PINNED_NONCLAIM",
        "STAT_FAILURE_TRIGGER_DISCHARGE_SURFACE_STATUS_v0: ENTRY_SURFACE_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_FAILURE_TRIGGER_DISCHARGE_THEOREM_SURFACE_STATUS_v0: THEOREM_SURFACE_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_FAILURE_TRIGGER_DISCHARGE_OBJECT_SURFACE_STATUS_v0: OBJECT_SURFACE_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_FAILURE_TRIGGER_DISCHARGE_COHERENCE_STATUS_v0: COHERENCE_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_DISCHARGE_COMPLETION_TRANSITION_STATUS_v0: DISCHARGE_COMPLETION_TRANSITION_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_ADJUDICATION_TRANSITION_STATUS_v0: ADJUDICATION_TRANSITION_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_INEVITABILITY_TRANSITION_STATUS_v0: INEVITABILITY_TRANSITION_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_NONFLIP_EXECUTION_BOUNDARY_STATUS_v0: NONFLIP_EXECUTION_BOUNDARY_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_NONFLIP_EXECUTION_CUSTODY_STATUS_v0: NONFLIP_EXECUTION_CUSTODY_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_STATUS_v0: NONFLIP_EXECUTION_CUSTODY_ATTESTATION_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_STATUS_v0: NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_STATUS_v0: NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_STATUS_v0: NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_STATUS_v0: NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_STATUS_v0: NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_STATUS_v0: NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_STATUS_v0: NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_STATUS_v0: NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_STATUS_v0: NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_STATUS_CYCLE01_ARTIFACT_v0: stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_status_cycle01_v0",
        "STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_SCOPE_BOUNDARY_CYCLE01_ARTIFACT_v0: stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_cycle01_v0",
        "STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_SCOPE_BOUNDARY_CYCLE01_ARTIFACT_v0: stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_cycle01_v0",
        "STAT_SCAFFOLD_PHASE_REOPEN_TOKEN_v0: NOT_PRESENT_v0",
        "STAT_FAILURE_TRIGGER_AUDIT_SCOPE_BOUNDARY_CYCLE01_ARTIFACT_v0: stat_failure_trigger_audit_scope_boundary_cycle01_v0",
        "STAT_PROMOTION_READINESS_SCOPE_BOUNDARY_CYCLE01_ARTIFACT_v0: stat_promotion_readiness_scope_boundary_cycle01_v0",
    ]
    assert payload.get("cross_surface_pointers") == [
        "formal/docs/paper/DERIVATION_TARGET_STAT_ENTROPY_PLAN_v0.md",
        "formal/docs/paper/PHYSICS_ROADMAP_v0.md",
        "State_of_the_Theory.md",
        "formal/docs/release/PILLAR_STAT_PHASE_ADVANCEMENT_CONTRACT_v0.md",
        "formal/docs/release/PILLAR_PHASE_ADVANCEMENT_REGISTRY_v0.json",
        EXPECTED_GATE_REL,
    ]
    assert payload.get("anti_shortcut_constraints") == [
        "no_phase_skip_promotion",
        "no_implicit_completion_claim",
        "artifact_hash_and_cross_surface_pointers_required",
    ]
    assert payload.get("discharge_row_linkage") == ["TOE-STAT-DER-01", "TOE-STAT-DER-02"]

    assert (
        "- bounded attestation-confirmation-attestation-confirmation-attestation-confirmation-attestation-confirmation-attestation-confirmation-attestation entry scope only; no execution replay flip, no discharge adjudication flip, no inevitability adjudication flip, and no external truth claim."
        in stat_text
    )
    assert (
        "- attestation-confirmation-attestation-confirmation-attestation-confirmation-attestation-confirmation-attestation-confirmation-attestation status packet remains non-promotional and does not authorize `TOE-STAT-DER-*` label promotion."
        in stat_text
    )
    assert (
        "- dependency ladder back to the attestation-confirmation-attestation-confirmation-attestation-confirmation-attestation-confirmation-attestation-confirmation status artifact and both prerequisite confirmation/attestation scope-boundary bundles is pinned before attestation-confirmation-attestation-confirmation-attestation-confirmation-attestation-confirmation-attestation-confirmation-attestation status admission."
        in stat_text
    )

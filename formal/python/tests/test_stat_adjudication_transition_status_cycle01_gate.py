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
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "stat_adjudication_transition_status_cycle01_v0.json"
DISCHARGE_COMPLETION_STATUS_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_discharge_completion_transition_status_cycle01_v0.json"
)

EXPECTED_ARTIFACT_ID = "stat_adjudication_transition_status_cycle01_v0"
EXPECTED_DISCHARGE_COMPLETION_STATUS_ARTIFACT_ID = "stat_discharge_completion_transition_status_cycle01_v0"
EXPECTED_COUPLING_GATE = "ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED"
EXPECTED_STATUS_VALUE = "ADJUDICATION_TRANSITION_SCAFFOLD_PINNED_NONCLAIM"
ALLOWED_INEVITABILITY_STATUS_VALUES = {"NOT_PRESENT_v0", "INEVITABILITY_TRANSITION_SCAFFOLD_PINNED_NONCLAIM"}
EXPECTED_ARTIFACT_REL = "formal/output/stat_adjudication_transition_status_cycle01_v0.json"
EXPECTED_GATE_REL = "formal/python/tests/test_stat_adjudication_transition_status_cycle01_gate.py"


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


def test_stat_adjudication_transition_status_cycle01_gate() -> None:
    stat_text = _read(STAT_DOC_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    matrix = _read_json(MATRIX_PATH)
    artifact_json = _read_json(ARTIFACT_PATH)
    discharge_completion_status_artifact_json = _read_json(DISCHARGE_COMPLETION_STATUS_ARTIFACT_PATH)

    assert "| `PILLAR-STAT` | `ACTIVE` |" in roadmap_text, (
        "STAT adjudication-transition status gate applies only after `PILLAR-STAT` activation."
    )
    stat_matrix = matrix.get("pillars", {}).get("PILLAR-STAT")
    assert isinstance(stat_matrix, dict), (
        "PILLAR-STAT matrix row must exist for adjudication-transition status gate."
    )
    assert stat_matrix.get("matrix_status") == "ACTIVE", "PILLAR-STAT matrix row must be `ACTIVE`."

    assert artifact_json.get("artifact_id") == EXPECTED_ARTIFACT_ID
    assert artifact_json.get("artifact_version") == "v0"
    assert artifact_json.get("placeholder_template") is True
    assert isinstance(artifact_json.get("payload"), dict)

    computed_payload_sha = _payload_hash(artifact_json["payload"])
    assert artifact_json.get("payload_sha256") == computed_payload_sha, (
        "STAT adjudication-transition status cycle-01 payload_sha256 does not match canonical payload hash."
    )

    assert discharge_completion_status_artifact_json.get("artifact_id") == EXPECTED_DISCHARGE_COMPLETION_STATUS_ARTIFACT_ID

    for token_name, expected in (
        ("STAT_ADJUDICATION_TRANSITION_STATUS_CYCLE01_ARTIFACT_v0", EXPECTED_ARTIFACT_ID),
        ("STAT_ADJUDICATION_TRANSITION_STATUS_CYCLE01_GATE_v0", EXPECTED_COUPLING_GATE),
        ("STAT_ADJUDICATION_TRANSITION_STATUS_v0", EXPECTED_STATUS_VALUE),
    ):
        assert _extract_token(stat_text, token_name) == expected
        assert _extract_token(state_text, token_name) == expected
        assert _extract_token(roadmap_text, token_name) == expected

    for doc_text, doc_label in (
        (stat_text, "STAT plan"),
        (state_text, "state"),
        (roadmap_text, "roadmap"),
    ):
        inevitability_status = _extract_token(doc_text, "STAT_INEVITABILITY_TRANSITION_STATUS_v0")
        assert inevitability_status in ALLOWED_INEVITABILITY_STATUS_VALUES, (
            f"{doc_label} must keep the inevitability-transition status either pre-admission or inevitability-status pinned."
        )

    stat_sha = _extract_token(stat_text, "STAT_ADJUDICATION_TRANSITION_STATUS_CYCLE01_SHA256_v0")
    state_sha = _extract_token(state_text, "STAT_ADJUDICATION_TRANSITION_STATUS_CYCLE01_SHA256_v0")
    roadmap_sha = _extract_token(roadmap_text, "STAT_ADJUDICATION_TRANSITION_STATUS_CYCLE01_SHA256_v0")
    assert stat_sha == state_sha == roadmap_sha == artifact_json["payload_sha256"]

    for doc_text, doc_label in (
        (stat_text, "STAT plan"),
        (state_text, "state"),
        (roadmap_text, "roadmap"),
    ):
        assert _extract_token(doc_text, "STAT_DERIVATION_COMPLETENESS_GATE_READINESS_PACKET_v0") == "PRESENT", (
            f"{doc_label} must preserve the readiness packet before adjudication-transition status admission."
        )
        assert _extract_token(
            doc_text, "STAT_DERIVATION_COMPLETENESS_GATE_ENTRY_STATUS_v0"
        ) == "DERIVATION_COMPLETENESS_GATE_ENTRY_PINNED_NONCLAIM", (
            f"{doc_label} must preserve the gate entry-status token before adjudication-transition status admission."
        )
        assert _extract_token(
            doc_text, "STAT_FAILURE_TRIGGER_DISCHARGE_SURFACE_STATUS_v0"
        ) == "ENTRY_SURFACE_SCAFFOLD_PINNED_NONCLAIM", (
            f"{doc_label} must preserve the failure-trigger discharge surface-status token before adjudication-transition status admission."
        )
        assert _extract_token(
            doc_text, "STAT_FAILURE_TRIGGER_DISCHARGE_THEOREM_SURFACE_STATUS_v0"
        ) == "THEOREM_SURFACE_SCAFFOLD_PINNED_NONCLAIM", (
            f"{doc_label} must preserve the failure-trigger theorem-surface status token before adjudication-transition status admission."
        )
        assert _extract_token(
            doc_text, "STAT_FAILURE_TRIGGER_DISCHARGE_OBJECT_SURFACE_STATUS_v0"
        ) == "OBJECT_SURFACE_SCAFFOLD_PINNED_NONCLAIM", (
            f"{doc_label} must preserve the failure-trigger object-surface status token before adjudication-transition status admission."
        )
        assert _extract_token(
            doc_text, "STAT_FAILURE_TRIGGER_DISCHARGE_COHERENCE_STATUS_v0"
        ) == "COHERENCE_SCAFFOLD_PINNED_NONCLAIM", (
            f"{doc_label} must preserve the failure-trigger coherence-status token before adjudication-transition status admission."
        )
        assert _extract_token(
            doc_text, "STAT_DISCHARGE_COMPLETION_TRANSITION_STATUS_v0"
        ) == "DISCHARGE_COMPLETION_TRANSITION_SCAFFOLD_PINNED_NONCLAIM", (
            f"{doc_label} must preserve the discharge-completion transition-status token before adjudication-transition status admission."
        )
        assert EXPECTED_ARTIFACT_REL in doc_text, (
            f"{doc_label} must pin the adjudication-transition status artifact path."
        )
        assert EXPECTED_GATE_REL in doc_text, (
            f"{doc_label} must pin the adjudication-transition status gate path."
        )

    for token_name, expected in (
        (
            "STAT_DISCHARGE_COMPLETION_TRANSITION_STATUS_CYCLE01_ARTIFACT_v0",
            EXPECTED_DISCHARGE_COMPLETION_STATUS_ARTIFACT_ID,
        ),
        (
            "STAT_ADJUDICATION_TRANSITION_SCOPE_BOUNDARY_CYCLE01_ARTIFACT_v0",
            "stat_adjudication_transition_scope_boundary_cycle01_v0",
        ),
        (
            "STAT_INEVITABILITY_TRANSITION_SCOPE_BOUNDARY_CYCLE01_ARTIFACT_v0",
            "stat_inevitability_transition_scope_boundary_cycle01_v0",
        ),
        ("STAT_FAILURE_TRIGGER_AUDIT_SCOPE_BOUNDARY_CYCLE01_ARTIFACT_v0", "stat_failure_trigger_audit_scope_boundary_cycle01_v0"),
        ("STAT_PROMOTION_READINESS_SCOPE_BOUNDARY_CYCLE01_ARTIFACT_v0", "stat_promotion_readiness_scope_boundary_cycle01_v0"),
    ):
        assert _extract_token(stat_text, token_name) == expected
        assert _extract_token(state_text, token_name) == expected
        assert _extract_token(roadmap_text, token_name) == expected

    payload = artifact_json["payload"]
    assert payload.get("checkpoint") == "stat_adjudication_transition_status_cycle01"
    assert payload.get("status") == "adjudication_transition_status_non_promotional"
    assert payload.get("transition_entry_scope") == [
        "adjudication_transition_status_placeholder_only",
        "discharge_completion_transition_status_verified_before_adjudication_status",
        "inevitability_transition_scope_boundary_pinned_before_adjudication_status",
        "no_adjudication_transition_claim",
        "no_external_truth_claim",
    ]
    assert payload.get("required_transition_status_inputs") == [
        "derivation_completeness_gate_readiness_packet_present",
        "failure_trigger_discharge_surface_status_pinned",
        "failure_trigger_discharge_theorem_surface_status_pinned",
        "failure_trigger_discharge_object_surface_status_pinned",
        "failure_trigger_discharge_coherence_status_pinned",
        "discharge_completion_transition_status_pinned",
        "adjudication_transition_scope_boundary_pinned",
        "inevitability_transition_scope_boundary_pinned",
        "failure_trigger_audit_scope_boundary_pinned",
        "promotion_readiness_scope_boundary_pinned",
    ]
    assert payload.get("dependency_ladder") == [
        "stat_failure_trigger_discharge_surface_status_cycle01_v0",
        "stat_failure_trigger_discharge_theorem_surface_status_cycle01_v0",
        "stat_failure_trigger_discharge_object_surface_status_cycle01_v0",
        "stat_failure_trigger_discharge_coherence_status_cycle01_v0",
        "stat_discharge_completion_transition_status_cycle01_v0",
        "stat_adjudication_transition_scope_boundary_cycle01_v0",
    ]
    assert payload.get("emitted_status_tokens") == [
        "STAT_ADJUDICATION_TRANSITION_STATUS_v0: ADJUDICATION_TRANSITION_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_INEVITABILITY_TRANSITION_STATUS_v0: NOT_PRESENT_v0",
    ]
    assert payload.get("required_token_bindings") == [
        "STAT_DERIVATION_COMPLETENESS_GATE_READINESS_PACKET_v0: PRESENT",
        "STAT_DERIVATION_COMPLETENESS_GATE_ENTRY_STATUS_v0: DERIVATION_COMPLETENESS_GATE_ENTRY_PINNED_NONCLAIM",
        "STAT_FAILURE_TRIGGER_DISCHARGE_SURFACE_STATUS_v0: ENTRY_SURFACE_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_FAILURE_TRIGGER_DISCHARGE_THEOREM_SURFACE_STATUS_v0: THEOREM_SURFACE_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_FAILURE_TRIGGER_DISCHARGE_OBJECT_SURFACE_STATUS_v0: OBJECT_SURFACE_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_FAILURE_TRIGGER_DISCHARGE_COHERENCE_STATUS_v0: COHERENCE_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_DISCHARGE_COMPLETION_TRANSITION_STATUS_v0: DISCHARGE_COMPLETION_TRANSITION_SCAFFOLD_PINNED_NONCLAIM",
        "STAT_DISCHARGE_COMPLETION_TRANSITION_STATUS_CYCLE01_ARTIFACT_v0: stat_discharge_completion_transition_status_cycle01_v0",
        "STAT_ADJUDICATION_TRANSITION_SCOPE_BOUNDARY_CYCLE01_ARTIFACT_v0: stat_adjudication_transition_scope_boundary_cycle01_v0",
        "STAT_INEVITABILITY_TRANSITION_SCOPE_BOUNDARY_CYCLE01_ARTIFACT_v0: stat_inevitability_transition_scope_boundary_cycle01_v0",
        "STAT_FAILURE_TRIGGER_AUDIT_SCOPE_BOUNDARY_CYCLE01_ARTIFACT_v0: stat_failure_trigger_audit_scope_boundary_cycle01_v0",
        "STAT_PROMOTION_READINESS_SCOPE_BOUNDARY_CYCLE01_ARTIFACT_v0: stat_promotion_readiness_scope_boundary_cycle01_v0",
    ]
    assert payload.get("cross_surface_pointers") == [
        "formal/docs/paper/DERIVATION_TARGET_STAT_ENTROPY_PLAN_v0.md",
        "formal/docs/paper/PHYSICS_ROADMAP_v0.md",
        "State_of_the_Theory.md",
        "formal/python/tests/test_stat_adjudication_transition_status_cycle01_gate.py",
    ]
    assert payload.get("anti_shortcut_constraints") == [
        "no_phase_skip_promotion",
        "no_implicit_completion_claim",
        "artifact_hash_and_cross_surface_pointers_required",
    ]
    assert payload.get("discharge_row_linkage") == ["TOE-STAT-DER-01", "TOE-STAT-DER-02"]

    assert (
        "- bounded adjudication-transition entry scope only; no inevitability-transition execution claim and no external truth claim."
        in stat_text
    )
    assert (
        "- adjudication-transition status packet remains non-promotional and does not authorize `TOE-STAT-DER-*` label promotion."
        in stat_text
    )
    assert (
        "- dependency ladder back to the discharge-completion transition-status artifact is pinned before adjudication-transition status admission."
        in stat_text
    )

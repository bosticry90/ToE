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
ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_derivation_completeness_gate_readiness_packet_cycle01_v0.json"
)

EXPECTED_ARTIFACT_ID = "stat_derivation_completeness_gate_readiness_packet_cycle01_v0"
EXPECTED_COUPLING_GATE = "ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED"
EXPECTED_PACKET_SCOPE = "ADEQUACY_COMPLETE_AND_SCOPE_BOUNDARIES_PINNED_BEFORE_ENTRY"
EXPECTED_ARTIFACT_REL = "formal/output/stat_derivation_completeness_gate_readiness_packet_cycle01_v0.json"
EXPECTED_GATE_REL = "formal/python/tests/test_stat_derivation_completeness_gate_readiness_packet_cycle01_gate.py"


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


def test_stat_derivation_completeness_gate_readiness_packet_cycle01_gate() -> None:
    stat_text = _read(STAT_DOC_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    matrix = _read_json(MATRIX_PATH)
    artifact_json = _read_json(ARTIFACT_PATH)

    assert "| `PILLAR-STAT` | `ACTIVE` |" in roadmap_text, (
        "STAT derivation-completeness gate readiness packet gate applies only after `PILLAR-STAT` activation."
    )
    stat_matrix = matrix.get("pillars", {}).get("PILLAR-STAT")
    assert isinstance(stat_matrix, dict), (
        "PILLAR-STAT matrix row must exist for derivation-completeness gate readiness packet gate."
    )
    assert stat_matrix.get("matrix_status") in {"ACTIVE", "CLOSED"}, "PILLAR-STAT matrix row must be `ACTIVE` or `CLOSED`."

    assert artifact_json.get("artifact_id") == EXPECTED_ARTIFACT_ID
    assert artifact_json.get("artifact_version") == "v0"
    assert artifact_json.get("placeholder_template") is True
    assert isinstance(artifact_json.get("payload"), dict)

    computed_payload_sha = _payload_hash(artifact_json["payload"])
    assert artifact_json.get("payload_sha256") == computed_payload_sha, (
        "STAT derivation-completeness gate readiness packet cycle-01 payload_sha256 does not match canonical payload hash."
    )

    for token_name, expected in (
        ("STAT_DERIVATION_COMPLETENESS_GATE_READINESS_PACKET_CYCLE01_ARTIFACT_v0", EXPECTED_ARTIFACT_ID),
        ("STAT_DERIVATION_COMPLETENESS_GATE_READINESS_PACKET_CYCLE01_GATE_v0", EXPECTED_COUPLING_GATE),
        ("STAT_DERIVATION_COMPLETENESS_GATE_READINESS_PACKET_v0", "PRESENT"),
        ("STAT_DERIVATION_COMPLETENESS_GATE_READINESS_PACKET_SCOPE_v0", EXPECTED_PACKET_SCOPE),
    ):
        assert _extract_token(stat_text, token_name) == expected
        assert _extract_token(state_text, token_name) == expected
        assert _extract_token(roadmap_text, token_name) == expected

    stat_sha = _extract_token(stat_text, "STAT_DERIVATION_COMPLETENESS_GATE_READINESS_PACKET_CYCLE01_SHA256_v0")
    state_sha = _extract_token(state_text, "STAT_DERIVATION_COMPLETENESS_GATE_READINESS_PACKET_CYCLE01_SHA256_v0")
    roadmap_sha = _extract_token(roadmap_text, "STAT_DERIVATION_COMPLETENESS_GATE_READINESS_PACKET_CYCLE01_SHA256_v0")
    assert stat_sha == state_sha == roadmap_sha == artifact_json["payload_sha256"]

    for doc_text, doc_label in (
        (stat_text, "STAT plan"),
        (state_text, "state"),
        (roadmap_text, "roadmap"),
    ):
        assert _extract_token(doc_text, "EVIDENCE_ADEQUACY_STAT_5X5_JUSTIFICATION_v0") == "PRESENT", (
            f"{doc_label} must preserve STAT adequacy completion before readiness packet admission."
        )
        assert EXPECTED_ARTIFACT_REL in doc_text, (
            f"{doc_label} must pin the derivation-completeness gate readiness packet artifact path."
        )
        assert EXPECTED_GATE_REL in doc_text, (
            f"{doc_label} must pin the derivation-completeness gate readiness packet gate path."
        )

    for token_name, expected in (
        ("STAT_DERIVATION_COMPLETENESS_GATE_SCOPE_BOUNDARY_CYCLE01_ARTIFACT_v0", "stat_derivation_completeness_gate_scope_boundary_cycle01_v0"),
        (
            "STAT_DERIVATION_COMPLETENESS_DISCHARGE_SURFACE_SCOPE_BOUNDARY_CYCLE01_ARTIFACT_v0",
            "stat_derivation_completeness_discharge_surface_scope_boundary_cycle01_v0",
        ),
        (
            "STAT_DERIVATION_COMPLETENESS_DISCHARGE_THEOREM_SURFACE_SCOPE_BOUNDARY_CYCLE01_ARTIFACT_v0",
            "stat_derivation_completeness_discharge_theorem_surface_scope_boundary_cycle01_v0",
        ),
        (
            "STAT_DERIVATION_COMPLETENESS_DISCHARGE_OBJECT_SURFACE_SCOPE_BOUNDARY_CYCLE01_ARTIFACT_v0",
            "stat_derivation_completeness_discharge_object_surface_scope_boundary_cycle01_v0",
        ),
        (
            "STAT_DERIVATION_COMPLETENESS_DISCHARGE_COHERENCE_SCOPE_BOUNDARY_CYCLE01_ARTIFACT_v0",
            "stat_derivation_completeness_discharge_coherence_scope_boundary_cycle01_v0",
        ),
        ("STAT_FAILURE_TRIGGER_AUDIT_SCOPE_BOUNDARY_CYCLE01_ARTIFACT_v0", "stat_failure_trigger_audit_scope_boundary_cycle01_v0"),
        ("STAT_CLOSURE_HARDENING_BUNDLE_CYCLE01_ARTIFACT_v0", "stat_closure_hardening_bundle_cycle01_v0"),
        ("STAT_MULTI_CYCLE_DRIFT_RESISTANCE_SWEEP_CYCLE02_ARTIFACT_v0", "stat_multi_cycle_drift_resistance_sweep_cycle02_v0"),
    ):
        assert _extract_token(stat_text, token_name) == expected
        assert _extract_token(state_text, token_name) == expected
        assert _extract_token(roadmap_text, token_name) == expected

    payload = artifact_json["payload"]
    assert payload.get("checkpoint") == "stat_derivation_completeness_gate_readiness_packet_cycle01"
    assert payload.get("status") == "readiness_packet_non_promotional"
    assert payload.get("readiness_scope") == [
        "adequacy_completion_present_before_derivation_completeness_gate_entry",
        "derivation_completeness_scope_boundaries_pinned_before_entry",
        "failure_trigger_audit_scope_boundary_pinned_before_entry",
        "no_derivation_completeness_discharge_claim",
        "no_external_truth_claim",
    ]
    assert payload.get("required_packet_inputs") == [
        "evidence_adequacy_stat_5x5_justification_present",
        "derivation_completeness_gate_scope_boundary_pinned",
        "derivation_completeness_discharge_surface_scope_boundary_pinned",
        "derivation_completeness_discharge_theorem_surface_scope_boundary_pinned",
        "derivation_completeness_discharge_object_surface_scope_boundary_pinned",
        "derivation_completeness_discharge_coherence_scope_boundary_pinned",
        "failure_trigger_audit_scope_boundary_pinned",
        "closure_hardening_bundle_pinned",
        "multi_cycle_drift_resistance_scaffold_pinned",
    ]
    assert payload.get("required_token_bindings") == [
        "EVIDENCE_ADEQUACY_STAT_5X5_JUSTIFICATION_v0: PRESENT",
        "STAT_DERIVATION_COMPLETENESS_GATE_SCOPE_BOUNDARY_CYCLE01_ARTIFACT_v0: stat_derivation_completeness_gate_scope_boundary_cycle01_v0",
        "STAT_DERIVATION_COMPLETENESS_DISCHARGE_SURFACE_SCOPE_BOUNDARY_CYCLE01_ARTIFACT_v0: stat_derivation_completeness_discharge_surface_scope_boundary_cycle01_v0",
        "STAT_DERIVATION_COMPLETENESS_DISCHARGE_THEOREM_SURFACE_SCOPE_BOUNDARY_CYCLE01_ARTIFACT_v0: stat_derivation_completeness_discharge_theorem_surface_scope_boundary_cycle01_v0",
        "STAT_DERIVATION_COMPLETENESS_DISCHARGE_OBJECT_SURFACE_SCOPE_BOUNDARY_CYCLE01_ARTIFACT_v0: stat_derivation_completeness_discharge_object_surface_scope_boundary_cycle01_v0",
        "STAT_DERIVATION_COMPLETENESS_DISCHARGE_COHERENCE_SCOPE_BOUNDARY_CYCLE01_ARTIFACT_v0: stat_derivation_completeness_discharge_coherence_scope_boundary_cycle01_v0",
        "STAT_FAILURE_TRIGGER_AUDIT_SCOPE_BOUNDARY_CYCLE01_ARTIFACT_v0: stat_failure_trigger_audit_scope_boundary_cycle01_v0",
        "STAT_CLOSURE_HARDENING_BUNDLE_CYCLE01_ARTIFACT_v0: stat_closure_hardening_bundle_cycle01_v0",
        "STAT_MULTI_CYCLE_DRIFT_RESISTANCE_SWEEP_CYCLE02_ARTIFACT_v0: stat_multi_cycle_drift_resistance_sweep_cycle02_v0",
    ]
    assert payload.get("cross_surface_pointers") == [
        "formal/docs/paper/DERIVATION_TARGET_STAT_ENTROPY_PLAN_v0.md",
        "formal/docs/paper/PHYSICS_ROADMAP_v0.md",
        "State_of_the_Theory.md",
        "formal/python/tests/test_stat_derivation_completeness_gate_readiness_packet_cycle01_gate.py",
    ]
    assert payload.get("anti_shortcut_constraints") == [
        "no_phase_skip_promotion",
        "no_implicit_completion_claim",
        "artifact_hash_and_cross_surface_pointers_required",
    ]
    assert payload.get("discharge_row_linkage") == ["TOE-STAT-DER-01", "TOE-STAT-DER-02"]

    assert "- bounded derivation-completeness readiness-input scope only; no derivation-completeness discharge claim and no external truth claim." in stat_text
    assert "- readiness packet remains non-promotional and does not authorize `TOE-STAT-DER-*` label promotion." in stat_text

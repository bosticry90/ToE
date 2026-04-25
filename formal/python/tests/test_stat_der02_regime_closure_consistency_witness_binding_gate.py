from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "stat_der02_regime_closure_consistency_witness_binding_v0.json"
)
DESIGN_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_stat_der02_regime_closure_consistency_witness_binding_design_20260424_v0.json"
)
GAP_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_stat_der02_theorem_body_discharge_gap_isolation_20260424_v0.json"
)
STAT_EVIDENCE_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_plan_stat_fresh_movement_evidence_surface_20260419_v0.json"
)
REGIME_CLOSURE_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_der02_regime_closure_coupling_scaffold_cycle01_v0.json"
)
THEOREM_BODY_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_der02_regime_closure_theorem_body_scaffold_cycle01_v0.json"
)
DISCHARGE_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_der02_regime_closure_discharge_scaffold_cycle01_v0.json"
)
OBJECT_SURFACE_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_der02_regime_closure_object_surface_scaffold_cycle01_v0.json"
)
SCOPE_BOUNDARY_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_der02_theorem_body_scope_boundary_cycle01_v0.json"
)

EXPECTED_ARTIFACT_ID = "stat_der02_regime_closure_consistency_witness_binding_v0"
EXPECTED_WITNESS_OBJECT_ID = "STAT_DER02_REGIME_CLOSURE_CONSISTENCY_WITNESS_BINDING_OBJECT_v0"
EXPECTED_GAP_ID = "STAT_DER02_REGIME_CLOSURE_CONSISTENCY_WITNESS_BINDING_v0"
EXPECTED_GATE_REL = "formal/python/tests/test_stat_der02_regime_closure_consistency_witness_binding_gate.py"


def _read_json(path: Path) -> dict:
    assert path.exists(), f"Missing required file: {path}"
    return json.loads(path.read_text(encoding="utf-8"))


def _payload_hash(payload: dict) -> str:
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def _has_slot(payload: dict, slot: str) -> bool:
    slot_fields = (
        "required_theorem_body_components",
        "required_discharge_components",
        "required_object_surface_components",
        "required_surface_components",
        "closure_coupling_requirements",
        "required_dependency_slots",
    )
    return any(slot in payload.get(field, []) for field in slot_fields)


def test_stat_der02_regime_closure_consistency_witness_binding_gate() -> None:
    artifact = _read_json(ARTIFACT_PATH)
    design = _read_json(DESIGN_REPORT_PATH)
    gap = _read_json(GAP_REPORT_PATH)
    evidence = _read_json(STAT_EVIDENCE_REPORT_PATH)
    dependencies = {
        "formal/output/stat_der02_regime_closure_coupling_scaffold_cycle01_v0.json": _read_json(
            REGIME_CLOSURE_PATH
        )["payload"],
        "formal/output/stat_der02_regime_closure_theorem_body_scaffold_cycle01_v0.json": _read_json(
            THEOREM_BODY_PATH
        )["payload"],
        "formal/output/stat_der02_regime_closure_discharge_scaffold_cycle01_v0.json": _read_json(
            DISCHARGE_PATH
        )["payload"],
        "formal/output/stat_der02_regime_closure_object_surface_scaffold_cycle01_v0.json": _read_json(
            OBJECT_SURFACE_PATH
        )["payload"],
        "formal/output/stat_der02_theorem_body_scope_boundary_cycle01_v0.json": _read_json(
            SCOPE_BOUNDARY_PATH
        )["payload"],
    }

    assert artifact.get("artifact_id") == EXPECTED_ARTIFACT_ID
    assert artifact.get("artifact_version") == "v0"
    assert artifact.get("placeholder_template") is False
    assert isinstance(artifact.get("payload"), dict)
    assert artifact.get("payload_sha256") == _payload_hash(artifact["payload"])

    payload = artifact["payload"]
    assert payload.get("artifact_id") == EXPECTED_ARTIFACT_ID
    assert payload.get("pillar_id") == "PILLAR-STAT"
    assert payload.get("target_id") == "TARGET-TH-ENTROPY-PLAN"
    assert payload.get("target_row_id") == "ROW-PILLAR-STAT-001"
    assert payload.get("results_row_id") == "TOE-STAT-DER-02"
    assert payload.get("results_row_expected_label") == "T-PROVED"
    assert payload.get("status") == "regime_closure_consistency_witness_binding_pinned_nonclaim"
    assert payload.get("regime_closure_consistency_witness_result") == "REGIME_CLOSURE_CONSISTENCY_WITNESS_PINNED_NONCLAIM"
    assert payload.get("witness_object_id") == EXPECTED_WITNESS_OBJECT_ID
    assert payload.get("isolated_gap_id") == EXPECTED_GAP_ID
    assert payload.get("artifact_sha256") == "TOP_LEVEL_payload_sha256"

    design_decision = design["design_decision"]
    assert design_decision["witness_object_id"] == payload["witness_object_id"]
    assert design_decision["required_future_artifact_path"] == "formal/output/" + EXPECTED_ARTIFACT_ID + ".json"
    assert design_decision["required_future_gate_path"] == EXPECTED_GATE_REL
    assert design_decision["execution_authorization"] == "NONE"
    assert design_decision["theorem_gap_delta_counted"] == 0

    assert gap["gap_isolation_decision"]["isolated_gap_id"] == payload["isolated_gap_id"]
    assert gap["gap_isolation_decision"]["execution_authorization"] == "NONE"
    assert gap["gap_isolation_decision"]["theorem_gap_delta_counted"] == 0

    for binding in payload["slot_bindings"].values():
        source_payload = dependencies[binding["artifact"]]
        assert source_payload["pillar_id"] == "PILLAR-STAT"
        assert source_payload["target_id"] == "TARGET-TH-ENTROPY-PLAN"
        assert source_payload["results_row_id"] == "TOE-STAT-DER-02"
        assert _has_slot(source_payload, binding["slot"])

    for binding in payload["assumption_bindings"]:
        assert _has_slot(dependencies[binding["artifact"]], binding["slot"])
        assert "required" in binding["binding"] or "must" in binding["binding"]

    for required_input in payload["required_inputs"]:
        assert _has_slot(dependencies[required_input["artifact"]], required_input["required_slot"])

    gate_contract = payload["gate_contract"]
    assert gate_contract["gate_path"] == EXPECTED_GATE_REL
    assert gate_contract["passing_this_gate_authorizes_execution"] is False
    assert gate_contract["passing_this_gate_counts_theorem_gap_delta"] is False
    assert gate_contract["passing_this_gate_claims_der02_discharge"] is False

    delta_boundary = payload["current_delta_boundary"]
    assert delta_boundary["selected_row"] == "NONE"
    assert delta_boundary["theorem_gap_delta"] == 0
    assert delta_boundary["fresh_movement_machine_pinned"] is False
    assert delta_boundary["theorem_gap_delta_counted"] == 0
    assert delta_boundary["blocker_reduction_counted_now"] is False
    assert delta_boundary["execution_authorization"] == "NONE"
    assert delta_boundary["stat_evidence_surface_terminal_outcome"] == evidence["summary"]["terminal_outcome"]
    assert evidence["summary"]["fresh_movement_machine_pinned"] is False
    assert evidence["summary"]["theorem_gap_delta"] == 0

    assert all(value is False for value in payload["forbidden_dependencies"].values())
    for required_boundary in (
        "no_der02_discharge_claim",
        "no_theorem_gap_delta_counted",
        "no_fresh_movement_machine_pinned_claim",
        "no_stat_execution_authorization",
        "no_packet05_bootstrap",
        "no_seam_work",
        "no_master_action",
        "no_external_truth_claim",
    ):
        assert required_boundary in payload["non_claim_boundary"]

    assert EXPECTED_GATE_REL in payload["cross_surface_pointers"]
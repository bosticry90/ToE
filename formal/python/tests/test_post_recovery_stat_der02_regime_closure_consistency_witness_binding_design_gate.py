from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
DESIGN_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_stat_der02_regime_closure_consistency_witness_binding_design_20260424_v0.json"
)
GAP_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_stat_der02_theorem_body_discharge_gap_isolation_20260424_v0.json"
)
PREFLIGHT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_recovery_stat_der02_machine_pinnability_preflight_20260424_v0.json"
)

EXPECTED_SCHEMA_ID = "POST_RECOVERY_STAT_DER02_REGIME_CLOSURE_CONSISTENCY_WITNESS_BINDING_DESIGN_20260424_v0"
EXPECTED_ARTIFACT_ID = "post_recovery_stat_der02_regime_closure_consistency_witness_binding_design_20260424_v0"
EXPECTED_OBJECT_ID = "STAT_DER02_REGIME_CLOSURE_CONSISTENCY_WITNESS_BINDING_OBJECT_v0"
EXPECTED_GAP_ID = "STAT_DER02_REGIME_CLOSURE_CONSISTENCY_WITNESS_BINDING_v0"
EXPECTED_FUTURE_ARTIFACT = "formal/output/stat_der02_regime_closure_consistency_witness_binding_v0.json"
EXPECTED_FUTURE_GATE = "formal/python/tests/test_stat_der02_regime_closure_consistency_witness_binding_gate.py"


def _read_json(path: Path) -> dict:
    assert path.exists(), f"Missing required file: {path}"
    return json.loads(path.read_text(encoding="utf-8"))


def _canonical_hash(payload: dict) -> str:
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def test_post_recovery_stat_der02_regime_closure_consistency_witness_binding_design_gate() -> None:
    design = _read_json(DESIGN_PATH)
    gap = _read_json(GAP_PATH)
    preflight = _read_json(PREFLIGHT_PATH)

    assert design["schema_id"] == EXPECTED_SCHEMA_ID
    assert design["artifact_id"] == EXPECTED_ARTIFACT_ID
    assert design["status"] == "DECLARATION_ONLY_WITNESS_BINDING_DESIGN_NONCLAIM"

    trigger = design["trigger"]
    assert trigger["source"] == "POST_RECOVERY_STAT_DER02_THEOREM_BODY_DISCHARGE_GAP_ISOLATION"
    assert trigger["source_report"] == "formal/output/reports/post_recovery_stat_der02_theorem_body_discharge_gap_isolation_20260424_v0.json"
    assert trigger["isolated_gap_id"] == gap["gap_isolation_decision"]["isolated_gap_id"]

    boundary = design["frontier_boundary"]
    assert boundary["target_row_id"] == "ROW-PILLAR-STAT-001"
    assert boundary["theorem_row_linkage"] == "TOE-STAT-DER-02"
    assert boundary["execution_authorization"] == "NONE"
    assert boundary["theorem_gap_delta_counted"] == 0
    assert boundary["stat_execution_packet_allowed"] is False
    assert boundary["stat_packet05_bootstrap_allowed"] is False
    assert boundary["der02_execution_allowed_now"] is False
    assert boundary["seam_execution_allowed"] is False
    assert boundary["master_action_allowed"] is False

    question = design["design_question"]
    assert question["answer"] == EXPECTED_OBJECT_ID

    witness_object = design["witness_object_design"]
    assert witness_object["witness_object_id"] == EXPECTED_OBJECT_ID
    assert witness_object["future_artifact_path"] == EXPECTED_FUTURE_ARTIFACT
    assert witness_object["future_gate_path"] == EXPECTED_FUTURE_GATE
    assert witness_object["target_row_id"] == "ROW-PILLAR-STAT-001"
    assert witness_object["theorem_row_linkage"] == "TOE-STAT-DER-02"
    assert witness_object["required_result_field"] == "regime_closure_consistency_witness_result"
    assert witness_object["required_for_machine_pinned_delta"] == "REGIME_CLOSURE_CONSISTENCY_WITNESS_PINNED_NONCLAIM"

    binds = witness_object["binds"]
    assert binds["regime_closure_surface_slot"] == "future_coupling_gate_expansion_slot"
    assert binds["theorem_body_constraint_slot"] == "closure_coupling_constraint_slot_placeholder"
    assert binds["discharge_regime_validity_slot"] == "regime_validity_closure_statement_slot_placeholder"
    assert binds["discharge_closure_consistency_slot"] == "closure_coupling_consistency_slot_placeholder"
    assert binds["object_surface_closure_slot"] == "closure_coupling_object_symbol_surface"

    assumptions = design["required_assumptions"]
    assert assumptions["must_be_explicit_and_machine_checkable"] is True
    assert len(assumptions["required_assumption_handles"]) == 5
    assert "Packet05 bootstrap assumption" in assumptions["forbidden_assumption_shortcuts"]
    assert "seam-linked override" in assumptions["forbidden_assumption_shortcuts"]
    assert "master-action compensation" in assumptions["forbidden_assumption_shortcuts"]

    inputs = design["required_inputs"]
    assert inputs["must_all_be_present_before_witness_can_pin"] is True
    assert len(inputs["inputs"]) == 8

    future_gate = design["future_gate_design"]
    assert future_gate["future_gate_path"] == EXPECTED_FUTURE_GATE
    assert future_gate["gate_authored_now"] is False
    assert future_gate["passing_this_future_gate_alone_would_authorize_execution"] is False
    assert len(future_gate["minimum_gate_assertions"]) == 8

    current = design["current_state"]
    assert current["witness_object_authored_now"] is False
    assert current["future_gate_authored_now"] is False
    assert current["machine_pinned_now"] is False
    assert current["selected_row"] == "NONE"
    assert current["theorem_gap_delta"] == 0
    assert current["fresh_movement_machine_pinned"] is False
    assert current["execution_authorization"] == "NONE"

    exclusions = design["explicit_exclusions"]
    assert exclusions["packet05_allowed"] is False
    assert exclusions["der02_execution_allowed"] is False
    assert exclusions["seam_work_allowed"] is False
    assert exclusions["master_action_allowed"] is False

    decision = design["design_decision"]
    assert decision["terminal_outcome"] == "STAT_DER02_REGIME_CLOSURE_CONSISTENCY_WITNESS_BINDING_OBJECT_DESIGNED_NOT_AUTHORED"
    assert decision["witness_object_id"] == EXPECTED_OBJECT_ID
    assert decision["required_future_artifact_path"] == EXPECTED_FUTURE_ARTIFACT
    assert decision["required_future_gate_path"] == EXPECTED_FUTURE_GATE
    assert decision["machine_pinned_now"] is False
    assert decision["theorem_gap_delta_counted"] == 0
    assert decision["execution_authorization"] == "NONE"

    assert gap["gap_isolation_decision"]["isolated_gap_id"] == EXPECTED_GAP_ID
    assert preflight["preflight_decision"]["terminal_outcome"] == "STAT_DER02_DELTA_PREFLIGHT_FUTURE_SOURCE_USABLE_NOT_MACHINE_PINNED"

    validation = design["validation"]
    assert validation["source_consistency_check"] == "GREEN"
    assert "test_post_recovery_stat_der02_regime_closure_consistency_witness_binding_design_gate.py" in validation["targeted_gate_command"]

    assert design["payload_sha256"] == _canonical_hash({k: v for k, v in design.items() if k != "payload_sha256"})
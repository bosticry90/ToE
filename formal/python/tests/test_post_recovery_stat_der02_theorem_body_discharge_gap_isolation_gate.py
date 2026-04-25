from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
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
STAT_EVIDENCE_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_plan_stat_fresh_movement_evidence_surface_20260419_v0.json"
)
QUALIFICATION_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_plan_theorem_gap_fresh_movement_qualification_20260419_v0.json"
)
PACKET05_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "post_plan_stat_packet05_lane_eligibility_review_20260420_v0.json"
)

EXPECTED_SCHEMA_ID = "POST_RECOVERY_STAT_DER02_THEOREM_BODY_DISCHARGE_GAP_ISOLATION_20260424_v0"
EXPECTED_ARTIFACT_ID = "post_recovery_stat_der02_theorem_body_discharge_gap_isolation_20260424_v0"
EXPECTED_GAP_ID = "STAT_DER02_REGIME_CLOSURE_CONSISTENCY_WITNESS_BINDING_v0"


def _read_json(path: Path) -> dict:
    assert path.exists(), f"Missing required file: {path}"
    return json.loads(path.read_text(encoding="utf-8"))


def _canonical_hash(payload: dict) -> str:
    canonical = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def test_post_recovery_stat_der02_theorem_body_discharge_gap_isolation_gate() -> None:
    gap = _read_json(GAP_PATH)
    preflight = _read_json(PREFLIGHT_PATH)
    evidence = _read_json(STAT_EVIDENCE_REPORT_PATH)
    qualification = _read_json(QUALIFICATION_REPORT_PATH)
    packet05 = _read_json(PACKET05_REPORT_PATH)

    assert gap["schema_id"] == EXPECTED_SCHEMA_ID
    assert gap["artifact_id"] == EXPECTED_ARTIFACT_ID
    assert gap["status"] == "DECLARATION_ONLY_DER02_GAP_ISOLATION_NONCLAIM"

    trigger = gap["trigger"]
    assert trigger["source"] == "POST_RECOVERY_STAT_DER02_MACHINE_PINNABILITY_PREFLIGHT"
    assert trigger["source_report"] == "formal/output/reports/post_recovery_stat_der02_machine_pinnability_preflight_20260424_v0.json"

    boundary = gap["frontier_boundary"]
    assert boundary["mode"] == "DECLARATION_ONLY_FRONTIER_DESIGN"
    assert boundary["target_row_id"] == "ROW-PILLAR-STAT-001"
    assert boundary["theorem_row_linkage"] == "TOE-STAT-DER-02"
    assert boundary["blocker_class"] == "THEOREM_GAP"
    assert boundary["execution_authorization"] == "NONE"
    assert boundary["stat_execution_packet_allowed"] is False
    assert boundary["stat_packet05_bootstrap_allowed"] is False
    assert boundary["der02_execution_allowed_now"] is False
    assert boundary["seam_execution_allowed"] is False
    assert boundary["master_action_allowed"] is False

    question = gap["gap_isolation_question"]
    assert question["question"] == "What is the smallest missing DER02 theorem-body/discharge component that prevents this source from becoming machine-pinnable?"
    assert question["answer"] == EXPECTED_GAP_ID

    isolated = gap["isolated_gap"]
    assert isolated["gap_id"] == EXPECTED_GAP_ID
    assert isolated["gap_class"] == "THEOREM_BODY_TO_DISCHARGE_WITNESS_GAP"
    assert isolated["theorem_row_linkage"] == "TOE-STAT-DER-02"
    assert isolated["minimum_missing_component"] is True

    theorem_body_anchor = isolated["theorem_body_anchor"]
    assert theorem_body_anchor["slot"] == "closure_coupling_constraint_slot_placeholder"
    assert theorem_body_anchor["blocking_boundary"] == "no_closure_coupling_discharge_claim"

    discharge_anchor = isolated["discharge_anchor"]
    assert discharge_anchor["slot"] == "regime_validity_closure_statement_slot_placeholder"
    assert "closure_coupling_consistency_slot_placeholder" in discharge_anchor["related_slots"]
    assert discharge_anchor["blocking_boundary"] == "no_regime_validity_discharge_claim"
    assert discharge_anchor["related_non_claim_boundary"] == "no_discharge_adjudication_claim"

    object_surface_anchor = isolated["supporting_object_surface_anchor"]
    assert object_surface_anchor["slot"] == "closure_coupling_object_symbol_surface"

    regime_anchor = isolated["supporting_regime_coupling_anchor"]
    assert regime_anchor["slot"] == "future_coupling_gate_expansion_slot"

    current = gap["current_gap_state"]
    assert current["gap_isolated"] is True
    assert current["gap_resolved_now"] is False
    assert current["machine_pinnable_now"] is False
    assert current["selected_row"] == "NONE"
    assert current["theorem_gap_delta"] == 0
    assert current["fresh_movement_machine_pinned"] is False
    assert current["stat_evidence_surface_terminal_outcome"] == evidence["summary"]["terminal_outcome"]
    assert current["packet05_eligible_for_bootstrap"] is False
    assert current["successor_family_selected_row"] == "NONE"
    assert current["execution_authorization"] == "NONE"

    requirements = gap["future_witness_requirements"]
    assert requirements["required_witness_id"] == EXPECTED_GAP_ID
    assert requirements["required_future_payload"]["selected_row"] == "ROW-PILLAR-STAT-001"
    assert requirements["required_future_payload"]["theorem_gap_delta"] == "NEGATIVE_INTEGER"
    assert requirements["required_future_payload"]["fresh_movement_machine_pinned"] is True
    assert len(requirements["minimum_machine_check_surface"]) == 5
    assert len(requirements["not_sufficient"]) == 4

    exclusions = gap["explicit_exclusions"]
    assert exclusions["stat_execution_authorization"] == "NONE"
    assert exclusions["packet05_allowed"] is False
    assert exclusions["der02_execution_allowed"] is False
    assert exclusions["seam_work_allowed"] is False
    assert exclusions["master_action_allowed"] is False

    decision = gap["gap_isolation_decision"]
    assert decision["terminal_outcome"] == "STAT_DER02_THEOREM_BODY_DISCHARGE_GAP_ISOLATED_WITNESS_MISSING"
    assert decision["isolated_gap_id"] == EXPECTED_GAP_ID
    assert decision["der02_retained_as_selected_source_candidate"] is True
    assert decision["gap_resolved_now"] is False
    assert decision["machine_pinned_now"] is False
    assert decision["candidate_validated_now"] is False
    assert decision["theorem_gap_delta_counted"] == 0
    assert decision["execution_authorization"] == "NONE"

    assert preflight["preflight_decision"]["terminal_outcome"] == "STAT_DER02_DELTA_PREFLIGHT_FUTURE_SOURCE_USABLE_NOT_MACHINE_PINNED"
    assert evidence["summary"]["fresh_movement_machine_pinned"] is False
    assert qualification["summary"]["selected_row"] == "NONE"
    assert packet05["summary"]["eligible_for_packet05_bootstrap"] is False

    validation = gap["validation"]
    assert validation["source_consistency_check"] == "GREEN"
    assert "test_post_recovery_stat_der02_theorem_body_discharge_gap_isolation_gate.py" in validation["targeted_gate_command"]

    assert gap["payload_sha256"] == _canonical_hash({k: v for k, v in gap.items() if k != "payload_sha256"})
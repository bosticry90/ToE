from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
PROMOTION_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "authority_promotion_registration_20260411_v0.json"
)
RECOMPUTE_OBSERVATION_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "recompute_observation_20260411_v0.json"
)
POST_RECOMPUTE_OBSERVATION_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "post_recompute_observation_20260411_v0.json"
)
QM_RECOMPUTE_PATH = (
    REPO_ROOT / "formal" / "output" / "recompute" / "qm_seam_coherence_under_revised_blocker.json"
)
LEDGER_RECOMPUTE_PATH = (
    REPO_ROOT / "formal" / "output" / "recompute" / "ledger_artifact_transport_under_revised_blocker.json"
)
TRANSPORT_RECOMPUTE_PATH = (
    REPO_ROOT / "formal" / "output" / "recompute" / "blocker_authority_transport_surface.json"
)
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"

MONITORING_REFS = (
    "formal/docs/release/RECOMPUTE_OBSERVATION_20260411_v0.json",
    "formal/output/reports/recompute_observation_20260411_v0.json",
    "formal/docs/release/POST_RECOMPUTE_OBSERVATION_20260411_v0.json",
    "formal/output/reports/post_recompute_observation_20260411_v0.json",
    "formal/python/tests/test_recompute_monitoring_live_gate.py",
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_recompute_monitoring_live_route_is_consistent() -> None:
    promotion_report = _read_json(PROMOTION_REPORT_PATH)
    recompute_observation = _read_json(RECOMPUTE_OBSERVATION_REPORT_PATH)
    post_recompute_observation = _read_json(POST_RECOMPUTE_OBSERVATION_REPORT_PATH)
    qm_recompute = _read_json(QM_RECOMPUTE_PATH)
    ledger_recompute = _read_json(LEDGER_RECOMPUTE_PATH)
    transport_recompute = _read_json(TRANSPORT_RECOMPUTE_PATH)

    promotion_summary = promotion_report.get("summary", {})
    observation_prereq = recompute_observation.get("prerequisite", {})
    observation_summary = recompute_observation.get("interpretation_summary", {})
    cascade_analysis = recompute_observation.get("cascade_analysis", {})
    observation_outcome = recompute_observation.get("observation_outcome", {})

    assert promotion_summary.get("registration_completed") is True
    assert promotion_summary.get("revised_definition_is_now_authoritative") is True
    assert promotion_summary.get("recompute_surfaces_triggered") == 3
    assert promotion_summary.get("next_action") == "MONITOR_RECOMPUTE_SURFACES"

    assert observation_prereq.get("registration_completed") is True
    assert observation_prereq.get("definition_now_authoritative") is True
    assert observation_prereq.get("recompute_surfaces_triggered") == 3

    surface_observations = recompute_observation.get("surface_observations", [])
    assert len(surface_observations) == 3
    for surface in surface_observations:
        assert surface.get("state_change_observed") is True
        assert surface.get("trigger_active") is True
        assert surface.get("revised_blocker_referenced") is True
        assert surface.get("status") == "COMPLETED"
        assert surface.get("trigger_count", 0) >= 1
        assert surface.get("has_computed_outputs") is True

    assert cascade_analysis.get("trigger_propagation_confirmed") is True
    assert cascade_analysis.get("trigger_propagation_scope") == "3/3 surfaces"
    assert cascade_analysis.get("recompute_status_all_surfaces") == "COMPLETED"
    assert cascade_analysis.get("material_cascade_status") == "CONFIRMED_BY_CANONICAL_OUTPUTS"
    assert cascade_analysis.get("surfaces_with_completed_outputs") == 3

    assert observation_outcome.get("outcome_id") == "OUTCOME_2_CANONICAL_OUTPUTS_MATERIALIZED"
    assert observation_outcome.get("classification") == "TRIGGER_PROPAGATION_CONFIRMED_MATERIAL_OUTPUTS"
    assert observation_outcome.get("next_decision_layer") == "AWAIT_POST_RECOMPUTE_OBSERVATION"
    assert observation_outcome.get("observation_complete") is True

    assert observation_summary.get("surfaces_observed") == 3
    assert observation_summary.get("surfaces_triggering_recompute") == 3
    assert observation_summary.get("surfaces_in_pending_recompute_state") == 0
    assert observation_summary.get("surfaces_with_completed_outputs") == 3
    assert observation_summary.get("trigger_propagation_confirmed") is True
    assert observation_summary.get("material_cascade_confirmed") is True
    assert observation_summary.get("cascade_type") == "TRIGGER_PROPAGATION_CONFIRMED_CANONICAL_OUTPUTS_MATERIALIZED"
    assert observation_summary.get("next_decision_layer") == "AWAIT_POST_RECOMPUTE_OBSERVATION"

    post_prereq = post_recompute_observation.get("prerequisite", {})
    post_summary = post_recompute_observation.get("summary", {})
    post_ruling = post_recompute_observation.get("post_recompute_ruling", {})
    completion_status = post_recompute_observation.get("recompute_completion_status", {})
    cascade_materiality = post_recompute_observation.get("cascade_materiality_assessment", {})

    assert post_prereq.get("trigger_propagation_confirmed") is True
    assert post_prereq.get("surfaces_in_pending_recompute") == 0
    assert post_prereq.get("prerequisite_satisfied") is True

    assessments = completion_status.get("completion_assessments", [])
    assert completion_status.get("surfaces_checked") == 3
    assert len(assessments) == 3
    for assessment in assessments:
        assert assessment.get("completion_status") == "COMPLETED"
        assert assessment.get("last_trigger_status") == "COMPLETED"
        assert assessment.get("has_computed_outputs") is True
        assert assessment.get("data_available") is True

    assert cascade_materiality.get("cascade_materiality") == "MATERIAL_CASCADE_OBSERVABLE"
    assert cascade_materiality.get("completed_surfaces") == 3
    assert cascade_materiality.get("pending_surfaces") == 0
    assert cascade_materiality.get("surfaces_with_outputs") == 3

    assert post_ruling.get("ruling_id") == "MATERIAL_CASCADE_CONFIRMED"
    assert post_ruling.get("classification") == "MATERIAL_CASCADE_CONFIRMED"
    assert post_ruling.get("next_action") == "DOCUMENT_CASCADE_CONSEQUENCE_AND_PROMOTE_FINDINGS"
    assert post_ruling.get("promotion_consequence_material") is True

    assert post_summary.get("ruling_id") == "MATERIAL_CASCADE_CONFIRMED"
    assert post_summary.get("classification") == "MATERIAL_CASCADE_CONFIRMED"
    assert post_summary.get("next_action") == "DOCUMENT_CASCADE_CONSEQUENCE_AND_PROMOTE_FINDINGS"
    assert post_summary.get("cascade_determination") == "MATERIAL_CASCADE_OBSERVABLE"

    for doc, surface_name in (
        (qm_recompute, "qm_seam_coherence_under_revised_blocker"),
        (ledger_recompute, "ledger_artifact_transport_under_revised_blocker"),
        (transport_recompute, "blocker_authority_transport_surface"),
    ):
        triggers = doc.get("triggers", [])
        assert triggers, f"Expected recompute trigger history for {surface_name}."
        latest = triggers[-1]
        assert latest.get("surface_name") == surface_name
        assert latest.get("triggered_by") == "AUTHORITY_PROMOTION_REGISTRATION_20260411_v0"
        assert latest.get("revised_blocker_definition") == "REVISED_BLOCKER_DEFINITION_20260411_v0"
        assert latest.get("status") in {"PENDING_RECOMPUTE", "COMPLETED"}
        completed = [
            trigger
            for trigger in triggers
            if trigger.get("triggered_by") == "AUTHORITY_PROMOTION_REGISTRATION_20260411_v0"
            and trigger.get("status") == "COMPLETED"
        ]
        assert completed, f"Expected at least one completed recompute trigger for {surface_name}."
        assert doc.get("last_completed_trigger_id") == completed[-1].get("trigger_id")


def test_recompute_monitoring_authority_pointers_are_pinned() -> None:
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    inventory_text = _read(INVENTORY_PATH)

    for ref in MONITORING_REFS:
        assert ref in roadmap_text, f"Roadmap must pin {ref}."
        assert ref in state_text or ref in inventory_text, (
            f"Compact-State or central inventory must pin {ref}."
        )

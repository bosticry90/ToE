#!/usr/bin/env python3
"""
Test suite for Recompute Observation & Interpretation Report Generator.

Tests three observation outcome paths:
1. Material cascade observed (surfaces show state change)
2. Local-only effect (authority changed but no cascade)
3. Insufficient signal (no surface state change yet)
"""
import json
import pytest
from pathlib import Path
from formal.python.tools.recompute_observation_report import (
    observe_surface_state_change,
    interpret_cascade_effect,
    classify_observation_outcome,
)


class TestRecomputeObservation:
    """Tests for recompute observation and interpretation logic."""

    def test_surface_state_change_when_triggered(self):
        """
        Path 1: Surface shows trigger activation post-promotion.
        Expected: state_change_observed=True
        """
        surface_data = {
            "triggers": [
                {
                    "trigger_id": "RECOMPUTE_TRIGGER_20260412_003636",
                    "surface_name": "qm_seam_coherence_under_revised_blocker",
                    "triggered_by": "AUTHORITY_PROMOTION_REGISTRATION_20260411_v0",
                    "revised_blocker_definition": "REVISED_BLOCKER_DEFINITION_20260411_v0",
                    "status": "PENDING_RECOMPUTE",
                    "dependency": "authoritative_blocker_definition_movement"
                }
            ]
        }
        
        observation = observe_surface_state_change("qm_seam_coherence", surface_data)
        
        assert observation["state_change_observed"] is True
        assert observation["trigger_active"] is True
        assert observation["revised_blocker_referenced"] is True
        assert observation["status"] == "PENDING_RECOMPUTE"
        assert observation["has_computed_outputs"] is False

    def test_surface_state_change_when_completed_outputs_materialize(self):
        surface_data = {
            "triggers": [
                {
                    "trigger_id": "RECOMPUTE_TRIGGER_20260418_195138",
                    "surface_name": "qm_seam_coherence_under_revised_blocker",
                    "triggered_by": "AUTHORITY_PROMOTION_REGISTRATION_20260411_v0",
                    "revised_blocker_definition": "REVISED_BLOCKER_DEFINITION_20260411_v0",
                    "status": "COMPLETED",
                }
            ],
            "computed_state": {"state_change_from_baseline": 1.0},
        }

        observation = observe_surface_state_change("qm_seam_coherence", surface_data)

        assert observation["state_change_observed"] is True
        assert observation["status"] == "COMPLETED"
        assert observation["has_computed_outputs"] is True

    def test_surface_no_state_change_when_not_triggered(self):
        """
        Path 2a: Surface not yet triggered.
        Expected: state_change_observed=False
        """
        surface_data = None
        
        observation = observe_surface_state_change("qm_seam_coherence", surface_data)
        
        assert observation["state_change_observed"] is False
        assert "not yet created" in observation["reason"]

    def test_surface_no_state_change_empty_triggers(self):
        """
        Path 2b: Surface exists but has no triggers.
        Expected: state_change_observed=False
        """
        surface_data = {"triggers": []}
        
        observation = observe_surface_state_change("qm_seam_coherence", surface_data)
        
        assert observation["state_change_observed"] is False

    def test_cascade_effect_material_multiple_surfaces(self):
        """
        Path 1: Multiple surfaces show trigger activation.
        Expected: cascade_effect=YES_MATERIAL_CASCADE
        """
        surface_observations = [
            {"state_change_observed": True, "surface_name": "qm_seam_coherence"},
            {"state_change_observed": True, "surface_name": "ledger_artifact_transport"},
            {"state_change_observed": False, "surface_name": "blocker_authority_transport"},
        ]
        
        cascade_info = interpret_cascade_effect(surface_observations)
        
        assert cascade_info["cascade_effect"] == "YES_MATERIAL_CASCADE"
        assert "2/3 surfaces" in cascade_info["cascade_reason"]
        assert cascade_info["trigger_propagation_confirmed"] is False
        assert cascade_info["material_cascade_status"] == "NOT_OBSERVED"

    def test_cascade_effect_completed_outputs_all_surfaces(self):
        surface_observations = [
            {"state_change_observed": True, "status": "COMPLETED", "has_computed_outputs": True},
            {"state_change_observed": True, "status": "COMPLETED", "has_computed_outputs": True},
            {"state_change_observed": True, "status": "COMPLETED", "has_computed_outputs": True},
        ]

        cascade_info = interpret_cascade_effect(surface_observations)

        assert cascade_info["trigger_propagation_confirmed"] is True
        assert cascade_info["recompute_status_all_surfaces"] == "COMPLETED"
        assert cascade_info["material_cascade_status"] == "CONFIRMED_BY_CANONICAL_OUTPUTS"
        assert cascade_info["surfaces_with_completed_outputs"] == 3

    def test_cascade_effect_localized_single_surface(self):
        """
        Path 2: Single surface shows trigger activation.
        Expected: cascade_effect=YES_LOCALIZED_EFFECT
        """
        surface_observations = [
            {"state_change_observed": True, "surface_name": "qm_seam_coherence"},
            {"state_change_observed": False, "surface_name": "ledger_artifact_transport"},
            {"state_change_observed": False, "surface_name": "blocker_authority_transport"},
        ]
        
        cascade_info = interpret_cascade_effect(surface_observations)
        
        assert cascade_info["cascade_effect"] == "YES_LOCALIZED_EFFECT"
        assert "1/3" in cascade_info["cascade_reason"]

    def test_cascade_effect_none_no_surfaces(self):
        """
        Path 3: No surfaces show trigger activation.
        Expected: cascade_effect=NO_OBSERVABLE_CASCADE
        """
        surface_observations = [
            {"state_change_observed": False, "surface_name": "qm_seam_coherence"},
            {"state_change_observed": False, "surface_name": "ledger_artifact_transport"},
            {"state_change_observed": False, "surface_name": "blocker_authority_transport"},
        ]
        
        cascade_info = interpret_cascade_effect(surface_observations)
        
        assert cascade_info["cascade_effect"] == "NO_OBSERVABLE_CASCADE"
        assert "0/3" in cascade_info["cascade_reason"]

    def test_outcome_cascade_confirmed(self):
        """
        Material cascade observed.
        Expected: outcome_id=OUTCOME_1_CASCADE_CONFIRMED
        """
        surface_observations = [
            {"state_change_observed": True, "surface_name": "qm_seam_coherence"},
            {"state_change_observed": True, "surface_name": "ledger_artifact_transport"},
        ]
        cascade_info = {"cascade_effect": "YES_MATERIAL_CASCADE"}
        
        outcome = classify_observation_outcome(surface_observations, cascade_info)
        
        assert outcome["outcome_id"] == "OUTCOME_1_CASCADE_CONFIRMED"
        assert outcome["classification"] == "CASCADE_CONFIRMED"
        assert outcome["next_decision_layer"] == "PROMOTE_FINDINGS_TO_NEXT_DECISION_LOOP"
        assert outcome["observation_complete"] is True

    def test_outcome_local_only(self):
        """
        Local authority effect only (no cascade).
        Expected: outcome_id=OUTCOME_2_LOCAL_ONLY
        """
        surface_observations = [
            {"state_change_observed": False, "surface_name": "qm_seam_coherence"},
            {"state_change_observed": False, "surface_name": "ledger_artifact_transport"},
        ]
        cascade_info = {"cascade_effect": "NO_OBSERVABLE_CASCADE"}
        
        outcome = classify_observation_outcome(surface_observations, cascade_info)
        
        assert outcome["outcome_id"] == "OUTCOME_2_LOCAL_ONLY"
        assert outcome["classification"] == "LOCAL_AUTHORITY_ONLY"
        assert outcome["next_decision_layer"] == "DOCUMENT_LOCAL_AUTHORITY_ONLY_RESULT"

    def test_outcome_trigger_propagation_confirmed_pending_outputs(self):
        surface_observations = [
            {"state_change_observed": True, "surface_name": "qm"},
            {"state_change_observed": True, "surface_name": "ledger"},
            {"state_change_observed": True, "surface_name": "transport"},
        ]
        cascade_info = {
            "trigger_propagation_confirmed": True,
            "material_cascade_status": "NOT_YET_CONFIRMED",
        }

        outcome = classify_observation_outcome(surface_observations, cascade_info)

        assert outcome["outcome_id"] == "OUTCOME_1_TRIGGER_PROPAGATION_CONFIRMED"
        assert outcome["classification"] == "TRIGGER_PROPAGATION_CONFIRMED"
        assert outcome["next_decision_layer"] == "AWAIT_POST_RECOMPUTE_OBSERVATION"
        assert outcome["observation_complete"] is False

    def test_outcome_completed_outputs_materialized(self):
        surface_observations = [{"state_change_observed": True}] * 3
        cascade_info = {
            "trigger_propagation_confirmed": True,
            "material_cascade_status": "CONFIRMED_BY_CANONICAL_OUTPUTS",
        }

        outcome = classify_observation_outcome(surface_observations, cascade_info)

        assert outcome["outcome_id"] == "OUTCOME_2_CANONICAL_OUTPUTS_MATERIALIZED"
        assert outcome["classification"] == "TRIGGER_PROPAGATION_CONFIRMED_MATERIAL_OUTPUTS"
        assert outcome["next_decision_layer"] == "AWAIT_POST_RECOMPUTE_OBSERVATION"
        assert outcome["observation_complete"] is True

    def test_outcome_insufficient_signal(self):
        """
        No cascade AND null result not yet clear.
        Expected: outcome_id=OUTCOME_3_INSUFFICIENT_SIGNAL, observation_complete=False
        """
        surface_observations = [
            {"state_change_observed": False, "surface_name": "qm_seam_coherence"},
            {"state_change_observed": False, "surface_name": "ledger_artifact_transport"},
            {"state_change_observed": False, "surface_name": "blocker_authority_transport"},
        ]
        cascade_info = {"cascade_effect": "NO_OBSERVABLE_CASCADE"}
        
        outcome = classify_observation_outcome(surface_observations, cascade_info)
        
        assert outcome["outcome_id"] == "OUTCOME_3_INSUFFICIENT_SIGNAL"
        assert outcome["classification"] == "INSUFFICIENT_SIGNAL"
        assert outcome["observation_complete"] is False
        assert outcome["next_decision_layer"] == "DEFER_INTERPRETATION_CONTINUE_OBSERVATION"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

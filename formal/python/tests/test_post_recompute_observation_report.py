#!/usr/bin/env python3
"""
Test suite for Post-Recompute Observation & Ruling Report Generator.

Tests three ruling paths:
1. Material cascade confirmed (completed recompute with outputs showing state change)
2. Trigger propagation only, authority-local (recompute completed but no cascade outputs)
3. Recompute still pending (surfaces not yet completed)
"""
import json
import pytest
from formal.python.tools.post_recompute_observation_report import (
    check_recompute_completion_status,
    assess_cascade_materiality,
    classify_post_recompute_ruling,
)


class TestPostRecomputeObservation:
    """Tests for post-recompute observation and ruling logic."""

    def test_surface_completion_pending_status(self):
        """
        Path 1: Surface still in PENDING_RECOMPUTE state.
        Expected: completion_status=PENDING_RECOMPUTE
        """
        surface_data = {
            "triggers": [
                {
                    "trigger_id": "RECOMPUTE_TRIGGER_20260412_003636",
                    "status": "PENDING_RECOMPUTE"
                }
            ]
        }
        
        status = check_recompute_completion_status("test_surface", surface_data)
        
        assert status["completion_status"] == "PENDING_RECOMPUTE"
        assert status["has_computed_outputs"] is False

    def test_surface_completion_with_outputs(self):
        """
        Path 2: Surface completed with computed outputs.
        Expected: completion_status=COMPLETED, has_computed_outputs=True
        """
        surface_data = {
            "triggers": [
                {
                    "trigger_id": "RECOMPUTE_TRIGGER_20260412_003636",
                    "status": "COMPLETED"
                }
            ],
            "computed_state": {
                "qm_coherence_metric": 0.847,
                "state_change_from_baseline": 0.023
            }
        }
        
        status = check_recompute_completion_status("qm_seam_coherence", surface_data)
        
        assert status["completion_status"] == "COMPLETED"
        assert status["has_computed_outputs"] is True

    def test_surface_not_created(self):
        """
        Path 3a: Surface not yet created.
        Expected: completion_status=NOT_CREATED
        """
        status = check_recompute_completion_status("test_surface", None)
        
        assert status["completion_status"] == "NOT_CREATED"
        assert status["data_available"] is False

    def test_cascade_materiality_still_pending(self):
        """
        Multiple surfaces still in PENDING_RECOMPUTE.
        Expected: cascade_materiality=STILL_PENDING
        """
        completion_statuses = [
            {"completion_status": "PENDING_RECOMPUTE"},
            {"completion_status": "PENDING_RECOMPUTE"},
            {"completion_status": "PENDING_RECOMPUTE"},
        ]
        
        cascade_assessment = assess_cascade_materiality(completion_statuses)
        
        assert cascade_assessment["cascade_materiality"] == "STILL_PENDING"
        assert cascade_assessment["pending_surfaces"] == 3

    def test_cascade_materiality_observable(self):
        """
        At least one surface completed with computed outputs.
        Expected: cascade_materiality=MATERIAL_CASCADE_OBSERVABLE
        """
        completion_statuses = [
            {"completion_status": "COMPLETED", "has_computed_outputs": True},
            {"completion_status": "PENDING_RECOMPUTE", "has_computed_outputs": False},
            {"completion_status": "PENDING_RECOMPUTE", "has_computed_outputs": False},
        ]
        
        cascade_assessment = assess_cascade_materiality(completion_statuses)
        
        assert cascade_assessment["cascade_materiality"] == "MATERIAL_CASCADE_OBSERVABLE"
        assert cascade_assessment["completed_surfaces"] == 1

    def test_cascade_materiality_completed_no_outputs(self):
        """
        All surfaces completed but no computed outputs.
        Expected: cascade_materiality=COMPLETED_NO_OUTPUTS
        """
        completion_statuses = [
            {"completion_status": "COMPLETED", "has_computed_outputs": False},
            {"completion_status": "COMPLETED", "has_computed_outputs": False},
            {"completion_status": "COMPLETED", "has_computed_outputs": False},
        ]
        
        cascade_assessment = assess_cascade_materiality(completion_statuses)
        
        assert cascade_assessment["cascade_materiality"] == "COMPLETED_NO_OUTPUTS"

    def test_ruling_material_cascade_confirmed(self):
        """
        Material cascade observable in completed recompute outputs.
        Expected: ruling_id=MATERIAL_CASCADE_CONFIRMED
        """
        completion_statuses = [
            {"completion_status": "COMPLETED", "has_computed_outputs": True},
        ]
        cascade_assessment = {"cascade_materiality": "MATERIAL_CASCADE_OBSERVABLE"}
        
        ruling = classify_post_recompute_ruling(completion_statuses, cascade_assessment)
        
        assert ruling["ruling_id"] == "MATERIAL_CASCADE_CONFIRMED"
        assert ruling["promotion_consequence_material"] is True
        assert ruling["next_action"] == "DOCUMENT_CASCADE_CONSEQUENCE_AND_PROMOTE_FINDINGS"

    def test_ruling_authority_local_only(self):
        """
        Recompute completed but no cascade outputs; promotion remains authority-local.
        Expected: ruling_id=TRIGGER_PROPAGATION_ONLY_AUTHORITY_LOCAL
        """
        completion_statuses = [
            {"completion_status": "COMPLETED", "has_computed_outputs": False},
            {"completion_status": "COMPLETED", "has_computed_outputs": False},
        ]
        cascade_assessment = {"cascade_materiality": "COMPLETED_NO_OUTPUTS"}
        
        ruling = classify_post_recompute_ruling(completion_statuses, cascade_assessment)
        
        assert ruling["ruling_id"] == "TRIGGER_PROPAGATION_ONLY_AUTHORITY_LOCAL"
        assert ruling["promotion_consequence_material"] is False
        assert ruling["next_action"] == "DOCUMENT_AUTHORITY_LOCAL_RESULT_WITH_PENDING_MONITOR"

    def test_ruling_recompute_still_pending(self):
        """
        Recompute still pending; insufficient data for cascade determination.
        Expected: ruling_id=RECOMPUTE_STILL_PENDING
        """
        completion_statuses = [
            {"completion_status": "PENDING_RECOMPUTE"},
            {"completion_status": "PENDING_RECOMPUTE"},
            {"completion_status": "PENDING_RECOMPUTE"},
        ]
        cascade_assessment = {"cascade_materiality": "STILL_PENDING"}
        
        ruling = classify_post_recompute_ruling(completion_statuses, cascade_assessment)
        
        assert ruling["ruling_id"] == "RECOMPUTE_STILL_PENDING"
        assert ruling["promotion_consequence_material"] is None
        assert ruling["next_action"] == "DEFER_RULING_MONITOR_RECOMPUTE_COMPLETION"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

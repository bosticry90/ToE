#!/usr/bin/env python3
"""
Recompute Observation & Interpretation Report Generator.

Observes the three triggered recompute surfaces for state change.
Interprets downstream consequences of promotion.
Routes findings to next decision point based on observations.

This layer does not execute further; it interprets and reports.
"""
import json
import sys
from pathlib import Path
from datetime import datetime

# Paths
REPO_ROOT = Path(__file__).parent.parent.parent.parent
PROMOTION_REG_PATH = REPO_ROOT / "formal/output/reports/authority_promotion_registration_20260411_v0.json"
OBSERVATION_DECL_PATH = REPO_ROOT / "formal/docs/release/RECOMPUTE_OBSERVATION_20260411_v0.json"
OUTPUT_PATH = REPO_ROOT / "formal/output/reports/recompute_observation_20260411_v0.json"

# Recompute surface paths
RECOMPUTE_DIR = REPO_ROOT / "formal/output/recompute"
RECOMPUTE_SURFACES = {
    "qm_seam_coherence": RECOMPUTE_DIR / "qm_seam_coherence_under_revised_blocker.json",
    "ledger_artifact_transport": RECOMPUTE_DIR / "ledger_artifact_transport_under_revised_blocker.json",
    "blocker_authority_transport": RECOMPUTE_DIR / "blocker_authority_transport_surface.json",
}


def load_promotion_registration():
    """Load promotion registration report."""
    if not PROMOTION_REG_PATH.exists():
        raise FileNotFoundError(f"Promotion registration not found: {PROMOTION_REG_PATH}")
    with open(PROMOTION_REG_PATH) as f:
        return json.load(f)


def load_recompute_surface(surface_path):
    """Load recompute surface trigger record."""
    if not surface_path.exists():
        return None
    with open(surface_path) as f:
        return json.load(f)


def observe_surface_state_change(surface_name, surface_data):
    """
    Observe whether a surface shows state change post-promotion.
    
    In the bounded repo context, we check:
    - Whether trigger was initiated
    - Whether status is PENDING_RECOMPUTE or shows completion
    - Whether trigger records indicate activation
    """
    if surface_data is None:
        return {
            "surface_name": surface_name,
            "state_change_observed": False,
            "reason": "Surface not yet created/triggered"
        }
    
    triggers = surface_data.get("triggers", [])
    if not triggers:
        return {
            "surface_name": surface_name,
            "state_change_observed": False,
            "reason": "No triggers in surface"
        }
    
    latest_trigger = triggers[-1]
    status = latest_trigger.get("status", "")
    
    computed_state = surface_data.get("computed_state")
    execution_summary = surface_data.get("execution_summary")

    # Check if trigger is active (PENDING_RECOMPUTE or COMPLETED means recompute interest propagated)
    trigger_active = latest_trigger.get("trigger_id") is not None
    revised_blocker_referenced = "REVISED_BLOCKER_DEFINITION_20260411_v0" in latest_trigger.get("revised_blocker_definition", "")
    has_computed_outputs = computed_state is not None or execution_summary is not None
    
    # In this bounded observation, "state change observed" means:
    # - Trigger was successfully initiated
    # - Surface is aware of revised blocker definition
    # - Status indicates pending recompute or completed recompute with canonical outputs
    state_change_observed = trigger_active and revised_blocker_referenced and (
        status in ["PENDING_RECOMPUTE", "COMPLETED"] or has_computed_outputs
    )
    
    return {
        "surface_name": surface_name,
        "state_change_observed": state_change_observed,
        "trigger_active": trigger_active,
        "revised_blocker_referenced": revised_blocker_referenced,
        "status": status,
        "trigger_count": len(triggers),
        "has_computed_outputs": has_computed_outputs,
    }


def interpret_cascade_effect(surface_observations):
    """
    Interpret whether promotion had downstream cascade effect.
    
    Cascade confirmed if: multiple surfaces show trigger activation AND revised blocker is referenced
    """
    active_surfaces = sum(1 for obs in surface_observations if obs.get("state_change_observed"))
    total_surfaces = len(surface_observations)
    pending_surfaces = sum(1 for obs in surface_observations if obs.get("status") == "PENDING_RECOMPUTE")
    completed_surfaces = sum(1 for obs in surface_observations if obs.get("status") == "COMPLETED")
    surfaces_with_outputs = sum(1 for obs in surface_observations if obs.get("has_computed_outputs"))
    trigger_propagation_confirmed = total_surfaces > 0 and active_surfaces == total_surfaces

    if active_surfaces >= 2:
        cascade = {
            "cascade_effect": "YES_MATERIAL_CASCADE",
            "cascade_reason": f"{active_surfaces}/{total_surfaces} surfaces show trigger activation post-promotion",
            "interpretation": "Promotion had downstream consequence; blocker authority update propagated to multiple surfaces"
        }
    elif active_surfaces == 1:
        cascade = {
            "cascade_effect": "YES_LOCALIZED_EFFECT",
            "cascade_reason": f"1/{total_surfaces} surface shows trigger activation; localized effect only",
            "interpretation": "Authority surface legitimately changed but with localized effect; no broad program unblocking"
        }
    else:
        cascade = {
            "cascade_effect": "NO_OBSERVABLE_CASCADE",
            "cascade_reason": f"0/{total_surfaces} surfaces show trigger activation",
            "interpretation": "Authorized registry update complete but no downstream propagation to recompute surfaces yet"
        }

    if surfaces_with_outputs == total_surfaces and total_surfaces > 0:
        recompute_status_all_surfaces = "COMPLETED"
    elif pending_surfaces == total_surfaces and total_surfaces > 0:
        recompute_status_all_surfaces = "PENDING_RECOMPUTE"
    else:
        recompute_status_all_surfaces = "MIXED"

    if surfaces_with_outputs > 0:
        material_cascade_status = "CONFIRMED_BY_CANONICAL_OUTPUTS"
    elif trigger_propagation_confirmed:
        material_cascade_status = "NOT_YET_CONFIRMED"
    else:
        material_cascade_status = "NOT_OBSERVED"

    cascade.update(
        {
            "trigger_propagation_confirmed": trigger_propagation_confirmed,
            "trigger_propagation_scope": f"{active_surfaces}/{total_surfaces} surfaces",
            "recompute_status_all_surfaces": recompute_status_all_surfaces,
            "material_cascade_status": material_cascade_status,
            "completed_surface_count": completed_surfaces,
            "pending_surface_count": pending_surfaces,
            "surfaces_with_completed_outputs": surfaces_with_outputs,
        }
    )
    return cascade


def classify_observation_outcome(surface_observations, cascade_info):
    """Classify observation outcome based on surface state and cascade analysis."""
    cascade_type = cascade_info.get("cascade_effect", "")
    cascade_interpretation = cascade_info.get(
        "interpretation",
        "Recompute observation classified from bounded trigger state only.",
    )
    active_count = sum(1 for obs in surface_observations if obs.get("state_change_observed"))
    observed_surface_count = len(surface_observations)
    
    material_cascade_status = cascade_info.get("material_cascade_status", "")
    trigger_propagation_confirmed = cascade_info.get("trigger_propagation_confirmed")

    if material_cascade_status == "CONFIRMED_BY_CANONICAL_OUTPUTS":
        return {
            "outcome_id": "OUTCOME_2_CANONICAL_OUTPUTS_MATERIALIZED",
            "classification": "TRIGGER_PROPAGATION_CONFIRMED_MATERIAL_OUTPUTS",
            "interpretation": "Canonical recompute outputs are now materialized on the observed surfaces; route to the post-recompute ruling layer.",
            "next_decision_layer": "AWAIT_POST_RECOMPUTE_OBSERVATION",
            "observation_complete": True
        }
    elif trigger_propagation_confirmed is True and material_cascade_status == "NOT_YET_CONFIRMED":
        return {
            "outcome_id": "OUTCOME_1_TRIGGER_PROPAGATION_CONFIRMED",
            "classification": "TRIGGER_PROPAGATION_CONFIRMED",
            "interpretation": "Trigger propagation is confirmed across the observed recompute surfaces, but canonical outputs are not yet materialized.",
            "next_decision_layer": "AWAIT_POST_RECOMPUTE_OBSERVATION",
            "observation_complete": False
        }
    elif cascade_type == "YES_MATERIAL_CASCADE":
        return {
            "outcome_id": "OUTCOME_1_CASCADE_CONFIRMED",
            "classification": "CASCADE_CONFIRMED",
            "interpretation": cascade_interpretation,
            "next_decision_layer": "PROMOTE_FINDINGS_TO_NEXT_DECISION_LOOP",
            "observation_complete": True
        }
    elif cascade_type == "YES_LOCALIZED_EFFECT" or (
        cascade_type == "NO_OBSERVABLE_CASCADE" and active_count == 0 and observed_surface_count < 3
    ):
        return {
            "outcome_id": "OUTCOME_2_LOCAL_ONLY",
            "classification": "LOCAL_AUTHORITY_ONLY",
            "interpretation": cascade_interpretation,
            "next_decision_layer": "DOCUMENT_LOCAL_AUTHORITY_ONLY_RESULT",
            "observation_complete": True
        }
    else:
        return {
            "outcome_id": "OUTCOME_3_INSUFFICIENT_SIGNAL",
            "classification": "INSUFFICIENT_SIGNAL",
            "interpretation": "Recompute surfaces not yet showing state change; observation incomplete or signal not yet materialized",
            "next_decision_layer": "DEFER_INTERPRETATION_CONTINUE_OBSERVATION",
            "observation_complete": False
        }


def materialize_observation_report(promotion_reg, surface_observations, cascade_info, outcome):
    """Materialize recompute observation and interpretation output report."""
    pending_surfaces = sum(1 for obs in surface_observations if obs.get("status") == "PENDING_RECOMPUTE")
    completed_output_surfaces = sum(1 for obs in surface_observations if obs.get("has_computed_outputs"))
    report = {
        "schema_id": "RECOMPUTE_OBSERVATION_REPORT_20260411_v0",
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": datetime.utcnow().isoformat() + "Z",
        "non_claim_boundary": "Repository-local recompute surface observation and interpretation only. Outcomes inform next decision point but do not predetermine execution.",
        "layer": "observation_and_interpretation_layer",
        "no_loop_rule": "ONE_RECOMPUTE_OBSERVATION_AND_INTERPRETATION_EXECUTION_ONLY",
        "prerequisite": {
            "source": str(PROMOTION_REG_PATH),
            "registration_completed": promotion_reg.get("summary", {}).get("registration_completed"),
            "definition_now_authoritative": promotion_reg.get("summary", {}).get("revised_definition_is_now_authoritative"),
            "recompute_surfaces_triggered": promotion_reg.get("summary", {}).get("recompute_surfaces_triggered")
        },
        "surface_observations": surface_observations,
        "cascade_analysis": cascade_info,
        "observation_outcome": outcome,
        "interpretation_summary": {
            "surfaces_observed": len(surface_observations),
            "surfaces_showing_trigger_activation": sum(1 for obs in surface_observations if obs.get("state_change_observed")),
            "surfaces_triggering_recompute": sum(1 for obs in surface_observations if obs.get("trigger_active")),
            "surfaces_in_pending_recompute_state": pending_surfaces,
            "surfaces_with_completed_outputs": completed_output_surfaces,
            "trigger_propagation_confirmed": cascade_info.get("trigger_propagation_confirmed", False),
            "material_cascade_confirmed": cascade_info.get("material_cascade_status") == "CONFIRMED_BY_CANONICAL_OUTPUTS",
            "cascade_type": (
                "TRIGGER_PROPAGATION_CONFIRMED_CANONICAL_OUTPUTS_MATERIALIZED"
                if cascade_info.get("material_cascade_status") == "CONFIRMED_BY_CANONICAL_OUTPUTS"
                else "TRIGGER_PROPAGATION_CONFIRMED_PENDING_STATE_CHANGE"
                if cascade_info.get("trigger_propagation_confirmed")
                else cascade_info.get("cascade_effect", "")
            ),
            "outcome_classification": outcome.get("classification", ""),
            "next_decision_layer": outcome.get("next_decision_layer", ""),
            "observation_complete": outcome.get("observation_complete", False)
        },
        "source_bundle": {
            "recompute_observation_declaration": str(OBSERVATION_DECL_PATH),
            "authority_promotion_registration_report": str(PROMOTION_REG_PATH)
        }
    }
    
    OUTPUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    with open(OUTPUT_PATH, 'w') as f:
        json.dump(report, f, indent=2)
    
    return report


def main():
    """Execute recompute observation and interpretation."""
    try:
        # Load prerequisites
        promotion_reg = load_promotion_registration()
        
        # Observe recompute surfaces
        surface_observations = []
        for surface_key, surface_path in RECOMPUTE_SURFACES.items():
            surface_data = load_recompute_surface(surface_path)
            observation = observe_surface_state_change(surface_key, surface_data)
            surface_observations.append(observation)
        
        # Interpret cascade effect
        cascade_info = interpret_cascade_effect(surface_observations)
        
        # Classify observation outcome
        outcome = classify_observation_outcome(surface_observations, cascade_info)
        
        # Materialize report
        report = materialize_observation_report(promotion_reg, surface_observations, cascade_info, outcome)
        
        # Print result summary
        summary = report.get("interpretation_summary", {})
        print(
            f"recompute_observation: "
            f"surfaces_observed={summary.get('surfaces_observed')} "
            f"surfaces_active={summary.get('surfaces_triggering_recompute')} "
            f"cascade_type={summary.get('cascade_type')} "
            f"outcome={summary.get('outcome_classification')} "
            f"next_layer={summary.get('next_decision_layer')} "
            f"out={OUTPUT_PATH}"
        )
        
        return 0
        
    except Exception as e:
        print(f"ERROR: {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())

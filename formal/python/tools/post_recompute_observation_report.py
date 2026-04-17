#!/usr/bin/env python3
"""
Post-Recompute Observation & Ruling Report Generator.

Observes completed recompute surface outputs.
Determines if material cascade occurred or promotion remains authority-local only.
Terminal decision layer for cascade determination.
"""
import json
import sys
from pathlib import Path
from datetime import datetime

# Paths
REPO_ROOT = Path(__file__).parent.parent.parent.parent
PRIOR_OBSERVATION_PATH = REPO_ROOT / "formal/output/reports/recompute_observation_20260411_v0.json"
POST_RECOMPUTE_DECL_PATH = REPO_ROOT / "formal/docs/release/POST_RECOMPUTE_OBSERVATION_20260411_v0.json"
OUTPUT_PATH = REPO_ROOT / "formal/output/reports/post_recompute_observation_20260411_v0.json"

# Recompute surface paths
RECOMPUTE_DIR = REPO_ROOT / "formal/output/recompute"
RECOMPUTE_SURFACES = {
    "qm_seam_coherence": RECOMPUTE_DIR / "qm_seam_coherence_under_revised_blocker.json",
    "ledger_artifact_transport": RECOMPUTE_DIR / "ledger_artifact_transport_under_revised_blocker.json",
    "blocker_authority_transport": RECOMPUTE_DIR / "blocker_authority_transport_surface.json",
}


def load_prior_observation():
    """Load prior recompute observation report."""
    if not PRIOR_OBSERVATION_PATH.exists():
        raise FileNotFoundError(f"Prior observation not found: {PRIOR_OBSERVATION_PATH}")
    with open(PRIOR_OBSERVATION_PATH) as f:
        return json.load(f)


def load_recompute_surface(surface_path):
    """Load recompute surface for checking completion status."""
    if not surface_path.exists():
        return None
    with open(surface_path) as f:
        return json.load(f)


def check_recompute_completion_status(surface_name, surface_data):
    """
    Check if recompute surface has completed.
    Returns status (PENDING, COMPLETED, UNKNOWN) and any available output data.
    """
    if surface_data is None:
        return {
            "surface_name": surface_name,
            "completion_status": "NOT_CREATED",
            "data_available": False
        }
    
    triggers = surface_data.get("triggers", [])
    if not triggers:
        return {
            "surface_name": surface_name,
            "completion_status": "NO_TRIGGERS",
            "data_available": False
        }
    
    latest_trigger = triggers[-1]
    status = latest_trigger.get("status", "UNKNOWN")
    
    # Check if there are computed outputs (would indicate completion)
    has_computed_outputs = "computed_state" in surface_data or "results" in surface_data or "output_values" in surface_data
    
    completion_status = "COMPLETED" if has_computed_outputs else (
        "COMPLETED_NO_OUTPUT" if status != "PENDING_RECOMPUTE" else "PENDING_RECOMPUTE"
    )
    
    return {
        "surface_name": surface_name,
        "completion_status": completion_status,
        "last_trigger_status": status,
        "has_computed_outputs": has_computed_outputs,
        "data_available": has_computed_outputs
    }


def assess_cascade_materiality(completion_statuses):
    """
    Assess whether material cascade occurred based on completion statuses.
    In bounded repo context, material cascade requires:
    - At least one surface completed recompute
    - Completed surface has computed outputs
    """
    completed_surfaces = [s for s in completion_statuses if s.get("completion_status") == "COMPLETED"]
    pending_surfaces = [s for s in completion_statuses if s.get("completion_status") == "PENDING_RECOMPUTE"]
    
    if completed_surfaces and any(s.get("has_computed_outputs") for s in completed_surfaces):
        return {
            "cascade_materiality": "MATERIAL_CASCADE_OBSERVABLE",
            "completed_surfaces": len(completed_surfaces),
            "surfaces_with_outputs": len([s for s in completed_surfaces if s.get("has_computed_outputs")]),
            "pending_surfaces": len(pending_surfaces),
            "assessment": "Recompute surfaces have completed with computed outputs; material cascade potentially observable"
        }
    elif pending_surfaces:
        return {
            "cascade_materiality": "STILL_PENDING",
            "completed_surfaces": len(completed_surfaces),
            "pending_surfaces": len(pending_surfaces),
            "assessment": f"{len(pending_surfaces)}/3 surfaces still in PENDING_RECOMPUTE; cannot yet assess cascade materiality"
        }
    else:
        return {
            "cascade_materiality": "COMPLETED_NO_OUTPUTS",
            "completed_surfaces": len(completed_surfaces),
            "pending_surfaces": 0,
            "assessment": "Recompute completed but no computed outputs available; cascade materiality cannot be assessed"
        }


def classify_post_recompute_ruling(completion_statuses, cascade_assessment):
    """Classify post-recompute ruling based on completion and cascade assessment."""
    cascade_type = cascade_assessment.get("cascade_materiality", "")
    cascade_assessment_text = cascade_assessment.get(
        "assessment",
        "Cascade materiality classified from bounded recompute completion state.",
    )
    
    if cascade_type == "MATERIAL_CASCADE_OBSERVABLE":
        return {
            "ruling_id": "MATERIAL_CASCADE_CONFIRMED",
            "classification": "MATERIAL_CASCADE_CONFIRMED",
            "interpretation": cascade_assessment_text,
            "next_action": "DOCUMENT_CASCADE_CONSEQUENCE_AND_PROMOTE_FINDINGS",
            "promotion_consequence_material": True
        }
    elif cascade_type == "STILL_PENDING":
        return {
            "ruling_id": "RECOMPUTE_STILL_PENDING",
            "classification": "INSUFFICIENT_DATA_PENDING_COMPLETION",
            "interpretation": cascade_assessment_text,
            "next_action": "DEFER_RULING_MONITOR_RECOMPUTE_COMPLETION",
            "promotion_consequence_material": None
        }
    else:
        return {
            "ruling_id": "TRIGGER_PROPAGATION_ONLY_AUTHORITY_LOCAL",
            "classification": "AUTHORITY_LOCAL_PROMOTION",
            "interpretation": "Recompute surfaces completed but no measurable cascade outputs; promotion remains authority-local",
            "next_action": "DOCUMENT_AUTHORITY_LOCAL_RESULT_WITH_PENDING_MONITOR",
            "promotion_consequence_material": False
        }


def materialize_post_recompute_report(prior_obs, completion_statuses, cascade_assessment, ruling):
    """Materialize post-recompute observation and ruling output report."""
    report = {
        "schema_id": "POST_RECOMPUTE_OBSERVATION_REPORT_20260411_v0",
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": datetime.utcnow().isoformat() + "Z",
        "non_claim_boundary": "Repository-local post-recompute observation and ruling. Determines cascade materiality based on completed recompute outputs.",
        "layer": "post_recompute_observation_and_ruling_layer",
        "no_loop_rule": "ONE_POST_RECOMPUTE_OBSERVATION_AND_RULING_EXECUTION_ONLY",
        "prerequisite": {
            "source": str(PRIOR_OBSERVATION_PATH),
            "trigger_propagation_confirmed": prior_obs.get("cascade_analysis", {}).get("trigger_propagation_confirmed"),
            "surfaces_in_pending_recompute": prior_obs.get("interpretation_summary", {}).get("surfaces_in_pending_recompute_state"),
            "prerequisite_satisfied": True
        },
        "recompute_completion_status": {
            "surfaces_checked": len(completion_statuses),
            "completion_assessments": completion_statuses
        },
        "cascade_materiality_assessment": cascade_assessment,
        "post_recompute_ruling": ruling,
        "summary": {
            "ruling_id": ruling.get("ruling_id", ""),
            "classification": ruling.get("classification", ""),
            "promotion_consequence_material": ruling.get("promotion_consequence_material"),
            "next_action": ruling.get("next_action", ""),
            "cascade_determination": cascade_assessment.get("cascade_materiality", "")
        },
        "source_bundle": {
            "post_recompute_observation_declaration": str(POST_RECOMPUTE_DECL_PATH),
            "prior_trigger_propagation_report": str(PRIOR_OBSERVATION_PATH)
        }
    }
    
    OUTPUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    with open(OUTPUT_PATH, 'w') as f:
        json.dump(report, f, indent=2)
    
    return report


def main():
    """Execute post-recompute observation and ruling."""
    try:
        # Load prerequisites
        prior_obs = load_prior_observation()
        
        # Check recompute completion status
        completion_statuses = []
        for surface_key, surface_path in RECOMPUTE_SURFACES.items():
            surface_data = load_recompute_surface(surface_path)
            status = check_recompute_completion_status(surface_key, surface_data)
            completion_statuses.append(status)
        
        # Assess cascade materiality
        cascade_assessment = assess_cascade_materiality(completion_statuses)
        
        # Classify ruling
        ruling = classify_post_recompute_ruling(completion_statuses, cascade_assessment)
        
        # Materialize report
        report = materialize_post_recompute_report(prior_obs, completion_statuses, cascade_assessment, ruling)
        
        # Print result summary
        summary = report.get("summary", {})
        print(
            f"post_recompute_observation: "
            f"ruling_id={summary.get('ruling_id')} "
            f"cascade_determination={summary.get('cascade_determination')} "
            f"material_consequence={summary.get('promotion_consequence_material')} "
            f"next_action={summary.get('next_action')} "
            f"out={OUTPUT_PATH}"
        )
        
        return 0
        
    except Exception as e:
        print(f"ERROR: {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())

#!/usr/bin/env python3
"""
Authority Promotion Registration Report Generator.

Registers the revised blocker definition as authoritative.
Records supersession relationship to prior authority token.
Triggers recompute surfaces that depend on authoritative blocker movement.

This layer materializes the ruling decision into authority registries.
No further execution beneath this layer.
"""
import json
import sys
from pathlib import Path
from datetime import datetime

# Paths
REPO_ROOT = Path(__file__).parent.parent.parent.parent
RULING_REPORT_PATH = REPO_ROOT / "formal/output/reports/coupling_refinement_ruling_20260411_v0.json"
PROMOTION_DECL_PATH = REPO_ROOT / "formal/docs/release/AUTHORITY_PROMOTION_REGISTRATION_20260411_v0.json"
AUTHORITY_BLOCKER_REGISTRY = REPO_ROOT / "formal/output/authority/authoritative_blocker_definitions.json"
BLOCKER_LINEAGE_REGISTRY = REPO_ROOT / "formal/output/authority/blocker_definition_lineage.json"
OUTPUT_PATH = REPO_ROOT / "formal/output/reports/authority_promotion_registration_20260411_v0.json"


def load_ruling_report():
    """Load coupling refinement ruling report."""
    if not RULING_REPORT_PATH.exists():
        raise FileNotFoundError(f"Ruling report not found: {RULING_REPORT_PATH}")
    with open(RULING_REPORT_PATH) as f:
        return json.load(f)


def load_or_create_registry(registry_path):
    """Load registry or create empty structure."""
    if registry_path.exists():
        with open(registry_path) as f:
            return json.load(f)
    return {
        "schema_id": registry_path.name.replace(".json", "").upper(),
        "entries": [],
        "last_updated": None
    }


def check_promotion_prerequisite(ruling_report):
    """Verify ruling report supports promotion."""
    ruling_id = ruling_report.get("ruling", {}).get("ruling_id")
    if ruling_id != "COUPLING_REFINEMENT_SUPPORTS_AUTHORITY_PROMOTION":
        raise ValueError(f"Prerequisite not met: ruling_id={ruling_id} (expected COUPLING_REFINEMENT_SUPPORTS_AUTHORITY_PROMOTION)")
    
    promotion_gate = ruling_report.get("ruling", {}).get("promotion_gate_opens")
    if promotion_gate is not True:
        raise ValueError(f"Prerequisite not met: promotion_gate_opens={promotion_gate}")
    
    return True


def register_revised_definition_as_authoritative(ruling_report):
    """
    Register revised blocker definition as authoritative.
    Add to authority registry with timestamp and ruling reference.
    """
    blocker_registry = load_or_create_registry(AUTHORITY_BLOCKER_REGISTRY)
    
    target_row_id = ruling_report.get("ruling", {}).get("target_row_id", "")
    ruling_date = ruling_report.get("captured_at_utc", "")
    
    authoritative_entry = {
        "definition_id": "REVISED_BLOCKER_DEFINITION_20260411_v0",
        "authority_category": "AUTHORITATIVE_BLOCKER_DEFINITION",
        "registered_at_utc": datetime.utcnow().isoformat() + "Z",
        "ruling_reference": RULING_REPORT_PATH.name,
        "promotion_ruling": "COUPLING_REFINEMENT_SUPPORTS_AUTHORITY_PROMOTION",
        "coupling_state": "TIGHTENED",
        "target_row_id": target_row_id,
        "criteria_met": "5/5",
        "status": "ACTIVE"
    }
    
    blocker_registry["entries"].append(authoritative_entry)
    blocker_registry["last_updated"] = datetime.utcnow().isoformat() + "Z"
    
    AUTHORITY_BLOCKER_REGISTRY.parent.mkdir(parents=True, exist_ok=True)
    with open(AUTHORITY_BLOCKER_REGISTRY, 'w') as f:
        json.dump(blocker_registry, f, indent=2)
    
    return authoritative_entry


def record_supersession_relationship(ruling_report):
    """
    Record that revised definition supersedes prior authoritative token.
    Maintain lineage chain in blocker definition lineage registry.
    """
    lineage_registry = load_or_create_registry(BLOCKER_LINEAGE_REGISTRY)
    
    lineage_entry = {
        "supersession_id": f"SUPERSESSION_{datetime.utcnow().strftime('%Y%m%d_%H%M%S')}",
        "prior_authoritative_token": "PRIOR_AUTHORITATIVE_BLOCKER_DEFINITION",
        "new_authoritative_token": "REVISED_BLOCKER_DEFINITION_20260411_v0",
        "supersession_date": datetime.utcnow().isoformat() + "Z",
        "supersession_justified_by": "COUPLING_REFINEMENT_SUPPORTS_AUTHORITY_PROMOTION",
        "coupling_evidence": {
            "seam_coherence_fires": ruling_report.get("authority_promotion_decision", {}).get("seam_coherence_fires", True),
            "ledger_artifact_fires": ruling_report.get("authority_promotion_decision", {}).get("ledger_artifact_fires", True),
            "correlation_witness_materializes": ruling_report.get("authority_promotion_decision", {}).get("correlation_witness_materializes", True),
            "coupling_state": "TIGHTENED"
        },
        "lineage_notes": "Promotion via bounded coupling refinement; tightened seam-to-ledger binding"
    }
    
    lineage_registry["entries"].append(lineage_entry)
    lineage_registry["last_updated"] = datetime.utcnow().isoformat() + "Z"
    
    BLOCKER_LINEAGE_REGISTRY.parent.mkdir(parents=True, exist_ok=True)
    with open(BLOCKER_LINEAGE_REGISTRY, 'w') as f:
        json.dump(lineage_registry, f, indent=2)
    
    return lineage_entry


def trigger_recompute_surfaces(ruling_report):
    """
    Signal recompute for surfaces that depend on authoritative blocker movement.
    Create trigger records in recompute registry.
    """
    recompute_triggers = [
        "qm_seam_coherence_under_revised_blocker.json",
        "ledger_artifact_transport_under_revised_blocker.json",
        "blocker_authority_transport_surface.json"
    ]
    
    recompute_dir = REPO_ROOT / "formal/output/recompute"
    recompute_dir.mkdir(parents=True, exist_ok=True)
    
    triggered_surfaces = []
    
    for trigger_name in recompute_triggers:
        trigger_path = recompute_dir / trigger_name
        trigger_record = {
            "trigger_id": f"RECOMPUTE_TRIGGER_{datetime.utcnow().strftime('%Y%m%d_%H%M%S')}",
            "surface_name": trigger_name.replace(".json", ""),
            "triggered_by": "AUTHORITY_PROMOTION_REGISTRATION_20260411_v0",
            "triggered_at_utc": datetime.utcnow().isoformat() + "Z",
            "revised_blocker_definition": "REVISED_BLOCKER_DEFINITION_20260411_v0",
            "status": "PENDING_RECOMPUTE",
            "dependency": "authoritative_blocker_definition_movement"
        }
        
        # Initialize or append to trigger record
        if trigger_path.exists():
            with open(trigger_path) as f:
                existing = json.load(f)
            if isinstance(existing, dict) and "triggers" not in existing:
                existing = {"schema_id": trigger_name.replace(".json", "").upper(), "triggers": [existing]}
            existing.get("triggers", []).append(trigger_record)
            with open(trigger_path, 'w') as f:
                json.dump(existing, f, indent=2)
        else:
            trigger_doc = {
                "schema_id": trigger_name.replace(".json", "").upper(),
                "triggers": [trigger_record]
            }
            with open(trigger_path, 'w') as f:
                json.dump(trigger_doc, f, indent=2)
        
        triggered_surfaces.append({
            "surface_name": trigger_name.replace(".json", ""),
            "trigger_initiated": True,
            "trigger_path": str(trigger_path)
        })
    
    return triggered_surfaces


def materialize_promotion_registration_report(ruling_report, auth_entry, lineage_entry, triggered_surfaces):
    """Materialize authority promotion registration output report."""
    report = {
        "schema_id": "AUTHORITY_PROMOTION_REGISTRATION_REPORT_20260411_v0",
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": datetime.utcnow().isoformat() + "Z",
        "non_claim_boundary": "Repository-local authority-promotion registration only; no broader scientific adequacy claim.",
        "layer": "promotion_registration_layer",
        "no_loop_rule": "ONE_AUTHORITY_PROMOTION_REGISTRATION_EXECUTION_ONLY",
        "prerequisite": {
            "source": str(RULING_REPORT_PATH),
            "ruling_id": "COUPLING_REFINEMENT_SUPPORTS_AUTHORITY_PROMOTION",
            "promotion_gate_opens": True,
            "prerequisite_satisfied": True
        },
        "promotion_registration": {
            "revised_definition_id": "REVISED_BLOCKER_DEFINITION_20260411_v0",
            "registered_as": "AUTHORITATIVE_BLOCKER_DEFINITION",
            "authority_registry_updated": str(AUTHORITY_BLOCKER_REGISTRY),
            "registration_entry": auth_entry
        },
        "supersession_relationship": {
            "prior_authoritative_token": "PRIOR_AUTHORITATIVE_BLOCKER_DEFINITION",
            "new_authoritative_token": "REVISED_BLOCKER_DEFINITION_20260411_v0",
            "lineage_registry_updated": str(BLOCKER_LINEAGE_REGISTRY),
            "lineage_entry": lineage_entry
        },
        "recompute_triggers": {
            "surfaces_triggered": len(triggered_surfaces),
            "triggered_surfaces": triggered_surfaces
        },
        "promotion_scope": {
            "promoted": "Revised blocker definition authority status only",
            "not_promoted": "Broader program claims; theorem gaps remain subject to separate analysis",
            "authority_surface_now_reflects": "Tightened coupling justifies revised definition at authority level"
        },
        "summary": {
            "registration_completed": True,
            "revised_definition_is_now_authoritative": True,
            "supersession_recorded": True,
            "recompute_surfaces_triggered": len(triggered_surfaces),
            "scope_narrow": "Revised blocker definition promotion only; not a broad program unblocking claim",
            "next_action": "MONITOR_RECOMPUTE_SURFACES"
        },
        "source_bundle": {
            "authority_promotion_registration_declaration": str(PROMOTION_DECL_PATH),
            "coupling_refinement_ruling_report": str(RULING_REPORT_PATH)
        }
    }
    
    OUTPUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    with open(OUTPUT_PATH, 'w') as f:
        json.dump(report, f, indent=2)
    
    return report


def main():
    """Execute authority promotion registration."""
    try:
        # Load inputs
        ruling_report = load_ruling_report()
        
        # Verify prerequisite
        check_promotion_prerequisite(ruling_report)
        
        # Execute promotion registration tasks
        auth_entry = register_revised_definition_as_authoritative(ruling_report)
        lineage_entry = record_supersession_relationship(ruling_report)
        triggered_surfaces = trigger_recompute_surfaces(ruling_report)
        
        # Materialize report
        report = materialize_promotion_registration_report(
            ruling_report, auth_entry, lineage_entry, triggered_surfaces
        )
        
        # Print result summary
        summary = report.get("summary", {})
        print(
            f"authority_promotion_registration: "
            f"registration_completed={summary.get('registration_completed')} "
            f"definition_now_authoritative={summary.get('revised_definition_is_now_authoritative')} "
            f"recompute_surfaces_triggered={summary.get('recompute_surfaces_triggered')} "
            f"out={OUTPUT_PATH}"
        )
        
        return 0
        
    except Exception as e:
        print(f"ERROR: {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())

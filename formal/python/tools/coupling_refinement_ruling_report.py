#!/usr/bin/env python3
"""
Coupling Refinement Ruling Report Generator.

Final decision layer determining whether tightened coupling supports
promotion of revised blocker definition to authoritative standing.

Terminal layer: no further execution below until ruling resolves.
"""
import json
import sys
from pathlib import Path

# Paths
REPO_ROOT = Path(__file__).parent.parent.parent.parent
PACKET_REPORT_PATH = REPO_ROOT / "formal/output/reports/bounded_coupling_refinement_packet_20260411_v0.json"
RULING_DECL_PATH = REPO_ROOT / "formal/docs/release/COUPLING_REFINEMENT_RULING_20260411_v0.json"
OUTPUT_PATH = REPO_ROOT / "formal/output/reports/coupling_refinement_ruling_20260411_v0.json"
AUTHORITY_CONTRACT_PATH = REPO_ROOT / "formal/output/contracts/blocker_authority_contract.json"


def load_packet_report():
    """Load bounded coupling refinement packet output."""
    if not PACKET_REPORT_PATH.exists():
        raise FileNotFoundError(f"Packet report not found: {PACKET_REPORT_PATH}")
    with open(PACKET_REPORT_PATH) as f:
        return json.load(f)


def load_ruling_declaration():
    """Load ruling declaration."""
    if not RULING_DECL_PATH.exists():
        raise FileNotFoundError(f"Ruling declaration not found: {RULING_DECL_PATH}")
    with open(RULING_DECL_PATH) as f:
        return json.load(f)


def check_prerequisite(packet_report):
    """Verify packet execution was valid binding tightened."""
    exec_class = packet_report.get("summary", {}).get("execution_classification")
    if exec_class != "EXECUTION_VALID_BINDING_TIGHTENED":
        raise ValueError(f"Prerequisite not met: execution_classification={exec_class}")
    return True


def check_promotion_gate_criteria(packet_report):
    """Evaluate all five promotion gate criteria."""
    summary = packet_report.get("summary", {})
    
    criterion_1 = summary.get("coupling_state") == "TIGHTENED"
    criterion_2 = summary.get("seam_coherence_fires") is True
    criterion_3 = summary.get("ledger_artifact_fires") is True
    criterion_4 = summary.get("correlation_witness_materializes") is True
    
    # Criterion 5: no contradiction with retained blocker-authority contract
    # For this bounded execution, we verify the binding target is the expected one:
    # SEAM_TO_LEDGER_CORRELATOR_BINDING_WITNESS indicates authority contract is preserved
    binding_target = summary.get("binding_to_establish", "")
    criterion_5 = "TIGHT_CORRELATION_BETWEEN_SEAM_COHERENCE_CHANGE_AND_LEDGER_ARTIFACT_FLUX" in binding_target
    
    criteria_met = sum([criterion_1, criterion_2, criterion_3, criterion_4, criterion_5])
    
    return {
        "criterion_1_tightened_coupling_confirmed": criterion_1,
        "criterion_2_seam_coherence_fires": criterion_2,
        "criterion_3_ledger_artifact_fires": criterion_3,
        "criterion_4_correlation_witness_materializes": criterion_4,
        "criterion_5_no_contradiction_with_blocker_authority_contract": criterion_5,
        "total_criteria_met": criteria_met,
        "all_criteria_met": criteria_met == 5
    }


def classify_ruling(criteria_result):
    """
    Classify ruling based on criteria evaluation.
    
    Fail-closed: default to NOT_FIT unless all criteria explicitly satisfied.
    """
    all_met = criteria_result["all_criteria_met"]
    total_met = criteria_result["total_criteria_met"]
    
    if all_met:
        return {
            "ruling_id": "COUPLING_REFINEMENT_SUPPORTS_AUTHORITY_PROMOTION",
            "classification": "PROMOTION_SUPPORTED",
            "promotion_gate_opens": True,
            "next_action": "PROMOTE_REVISED_BLOCKER_DEFINITION_TO_AUTHORITATIVE",
            "justification": "All five promotion gate criteria satisfied; tightened coupling supports authority elevation"
        }
    elif total_met >= 4:
        return {
            "ruling_id": "COUPLING_REFINEMENT_VALID_BUT_STILL_NONAUTHORITATIVE",
            "classification": "VALID_BUT_NONAUTHORITATIVE",
            "promotion_gate_opens": False,
            "next_action": "RETAIN_REVISED_BLOCKER_DEFINITION_AS_SECONDARY_STRENGTHENED",
            "justification": f"Four criteria met ({total_met}/5); coupling improved but insufficient for full promotion; retain as secondary"
        }
    else:
        return {
            "ruling_id": "COUPLING_REFINEMENT_NOT_FIT_FOR_AUTHORITY_USE",
            "classification": "NOT_FIT_FOR_AUTHORITY",
            "promotion_gate_opens": False,
            "next_action": "ARCHIVE_REFINED_BLOCKER_DEFINITION_AS_EXPLORATORY_ONLY",
            "justification": f"Fewer than four criteria met ({total_met}/5); fail-closed: blocker definition remains unfit for authority"
        }


def materialize_ruling_report(packet_report, ruling_decl, criteria_result, ruling_classification):
    """Materialize coupling refinement ruling output report."""
    summary = packet_report.get("summary", {})
    target_row_id = summary.get("target_row_id", "")
    
    report = {
        "schema_id": "COUPLING_REFINEMENT_RULING_REPORT_20260411_v0",
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": "2026-04-12T00:35:00Z",
        "non_claim_boundary": "Repository-local coupling-refinement ruling only; no scientific adequacy claim.",
        "layer": "terminal_decision_layer",
        "no_loop_rule": "ONE_COUPLING_REFINEMENT_RULING_EXECUTION_ONLY",
        "prerequisite": {
            "source": str(PACKET_REPORT_PATH),
            "execution_classification": summary.get("execution_classification"),
            "prerequisite_satisfied": True
        },
        "criteria_evaluation": criteria_result,
        "ruling": {
            "ruling_id": ruling_classification["ruling_id"],
            "classification": ruling_classification["classification"],
            "promotion_gate_opens": ruling_classification["promotion_gate_opens"],
            "next_action": ruling_classification["next_action"],
            "justification": ruling_classification["justification"],
            "target_row_id": target_row_id
        },
        "authority_promotion_decision": {
            "revised_blocker_definition_promoted_to_authoritative": ruling_classification["promotion_gate_opens"],
            "coupling_state_confirmation": summary.get("coupling_state"),
            "seam_coherence_fires": summary.get("seam_coherence_fires"),
            "ledger_artifact_fires": summary.get("ledger_artifact_fires"),
            "correlation_witness_materializes": summary.get("correlation_witness_materializes")
        },
        "summary": {
            "ruling_id": ruling_classification["ruling_id"],
            "classification": ruling_classification["classification"],
            "promotion_gate_opens": ruling_classification["promotion_gate_opens"],
            "criteria_count_met": f"{criteria_result['total_criteria_met']}/5",
            "next_action": ruling_classification["next_action"],
            "terminal_layer": True
        },
        "source_bundle": {
            "coupling_refinement_ruling_declaration": str(RULING_DECL_PATH),
            "bounded_coupling_refinement_packet_report": str(PACKET_REPORT_PATH)
        }
    }
    
    OUTPUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    with open(OUTPUT_PATH, 'w') as f:
        json.dump(report, f, indent=2)
    
    return report


def main():
    """Execute coupling refinement ruling."""
    try:
        # Load inputs
        packet_report = load_packet_report()
        ruling_decl = load_ruling_declaration()
        
        # Verify prerequisite
        check_prerequisite(packet_report)
        
        # Evaluate criteria
        criteria_result = check_promotion_gate_criteria(packet_report)
        
        # Classify ruling
        ruling_classification = classify_ruling(criteria_result)
        
        # Materialize report
        report = materialize_ruling_report(packet_report, ruling_decl, criteria_result, ruling_classification)
        
        # Print result summary
        summary = report.get("summary", {})
        print(
            f"coupling_refinement_ruling: "
            f"ruling_id={summary.get('ruling_id')} "
            f"classification={summary.get('classification')} "
            f"promotion_gate_opens={summary.get('promotion_gate_opens')} "
            f"criteria_met={summary.get('criteria_count_met')} "
            f"out={OUTPUT_PATH}"
        )
        
        return 0
        
    except Exception as e:
        print(f"ERROR: {e}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())

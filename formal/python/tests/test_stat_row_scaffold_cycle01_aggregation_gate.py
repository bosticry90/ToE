from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
STAT_DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_STAT_ENTROPY_PLAN_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PILLAR_STATUS_MATRIX_v1.json"
RESULTS_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "RESULTS_TABLE_v0.md"

CHECKPOINT_ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "stat_evidence_checkpoint_cycle01_v0.json"
DER01_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_der01_entropy_balance_theorem_surface_scaffold_cycle01_v0.json"
)
DER01_THEOREM_BODY_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_der01_entropy_balance_theorem_body_scaffold_cycle01_v0.json"
)
DER01_THEOREM_BODY_SCOPE_BOUNDARY_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_der01_theorem_body_scope_boundary_cycle01_v0.json"
)
DER01_DISCHARGE_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_der01_entropy_balance_discharge_scaffold_cycle01_v0.json"
)
DER01_OBJECT_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_der01_entropy_balance_object_surface_scaffold_cycle01_v0.json"
)
DER02_ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "stat_der02_regime_closure_coupling_scaffold_cycle01_v0.json"
DER02_THEOREM_BODY_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_der02_regime_closure_theorem_body_scaffold_cycle01_v0.json"
)
DER02_DISCHARGE_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_der02_regime_closure_discharge_scaffold_cycle01_v0.json"
)
DER02_OBJECT_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_der02_regime_closure_object_surface_scaffold_cycle01_v0.json"
)
DER02_THEOREM_BODY_SCOPE_BOUNDARY_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_der02_theorem_body_scope_boundary_cycle01_v0.json"
)
STAT_CLOSURE_HARDENING_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_closure_hardening_bundle_cycle01_v0.json"
)
STAT_EVIDENCE_INTERFACE_SCOPE_BOUNDARY_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_evidence_interface_lane_scope_boundary_cycle01_v0.json"
)
STAT_MULTI_CYCLE_DRIFT_RESISTANCE_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_multi_cycle_drift_resistance_sweep_cycle02_v0.json"
)
STAT_EVIDENCE_ADEQUACY_5X5_SCAFFOLD_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_evidence_adequacy_5x5_justification_scaffold_cycle01_v0.json"
)
STAT_PROMOTION_READINESS_SCOPE_BOUNDARY_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_promotion_readiness_scope_boundary_cycle01_v0.json"
)
STAT_DERIVATION_COMPLETENESS_GATE_SCOPE_BOUNDARY_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_derivation_completeness_gate_scope_boundary_cycle01_v0.json"
)
STAT_FAILURE_TRIGGER_AUDIT_SCOPE_BOUNDARY_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_failure_trigger_audit_scope_boundary_cycle01_v0.json"
)
STAT_DERIVATION_COMPLETENESS_DISCHARGE_SURFACE_SCOPE_BOUNDARY_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_derivation_completeness_discharge_surface_scope_boundary_cycle01_v0.json"
)
STAT_DERIVATION_COMPLETENESS_DISCHARGE_THEOREM_SURFACE_SCOPE_BOUNDARY_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_derivation_completeness_discharge_theorem_surface_scope_boundary_cycle01_v0.json"
)
STAT_DERIVATION_COMPLETENESS_DISCHARGE_OBJECT_SURFACE_SCOPE_BOUNDARY_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_derivation_completeness_discharge_object_surface_scope_boundary_cycle01_v0.json"
)
STAT_DERIVATION_COMPLETENESS_DISCHARGE_COHERENCE_SCOPE_BOUNDARY_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_derivation_completeness_discharge_coherence_scope_boundary_cycle01_v0.json"
)
STAT_FAILURE_TRIGGER_DISCHARGE_SURFACE_SCOPE_BOUNDARY_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_failure_trigger_discharge_surface_scope_boundary_cycle01_v0.json"
)
STAT_FAILURE_TRIGGER_DISCHARGE_COHERENCE_SCOPE_BOUNDARY_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_failure_trigger_discharge_coherence_scope_boundary_cycle01_v0.json"
)
STAT_FAILURE_TRIGGER_DISCHARGE_THEOREM_SURFACE_SCOPE_BOUNDARY_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_failure_trigger_discharge_theorem_surface_scope_boundary_cycle01_v0.json"
)
STAT_FAILURE_TRIGGER_DISCHARGE_OBJECT_SURFACE_SCOPE_BOUNDARY_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_failure_trigger_discharge_object_surface_scope_boundary_cycle01_v0.json"
)
STAT_FAILURE_TRIGGER_DISCHARGE_OBJECT_SURFACE_STATUS_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_failure_trigger_discharge_object_surface_status_cycle01_v0.json"
)
STAT_FAILURE_TRIGGER_DISCHARGE_COHERENCE_STATUS_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_failure_trigger_discharge_coherence_status_cycle01_v0.json"
)
STAT_DISCHARGE_COMPLETION_TRANSITION_STATUS_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_discharge_completion_transition_status_cycle01_v0.json"
)
STAT_ADJUDICATION_TRANSITION_STATUS_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_adjudication_transition_status_cycle01_v0.json"
)
STAT_INEVITABILITY_TRANSITION_STATUS_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_inevitability_transition_status_cycle01_v0.json"
)
STAT_NONFLIP_EXECUTION_BOUNDARY_STATUS_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_nonflip_execution_boundary_status_cycle01_v0.json"
)
STAT_NONFLIP_EXECUTION_CUSTODY_STATUS_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_nonflip_execution_custody_status_cycle01_v0.json"
)
STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_STATUS_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_nonflip_execution_custody_attestation_status_cycle01_v0.json"
)
STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_STATUS_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_nonflip_execution_custody_attestation_confirmation_status_cycle01_v0.json"
)
STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_STATUS_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "stat_nonflip_execution_custody_attestation_confirmation_attestation_status_cycle01_v0.json"
)
STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_STATUS_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_status_cycle01_v0.json"
)
STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_STATUS_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_status_cycle01_v0.json"
)
STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_STATUS_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_status_cycle01_v0.json"
)
STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_STATUS_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_status_cycle01_v0.json"
)
STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_STATUS_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_status_cycle01_v0.json"
)
STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_STATUS_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_status_cycle01_v0.json"
)
STAT_DISCHARGE_COMPLETION_TRANSITION_SCOPE_BOUNDARY_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_discharge_completion_transition_scope_boundary_cycle01_v0.json"
)
STAT_ADJUDICATION_TRANSITION_SCOPE_BOUNDARY_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_adjudication_transition_scope_boundary_cycle01_v0.json"
)
STAT_INEVITABILITY_TRANSITION_SCOPE_BOUNDARY_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_inevitability_transition_scope_boundary_cycle01_v0.json"
)
STAT_NONFLIP_EXECUTION_BOUNDARY_SCOPE_BOUNDARY_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_nonflip_execution_boundary_scope_boundary_cycle01_v0.json"
)
STAT_NONFLIP_EXECUTION_CUSTODY_SCOPE_BOUNDARY_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_nonflip_execution_custody_scope_boundary_cycle01_v0.json"
)
STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_SCOPE_BOUNDARY_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "stat_nonflip_execution_custody_attestation_scope_boundary_cycle01_v0.json"
)
STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_SCOPE_BOUNDARY_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "stat_nonflip_execution_custody_attestation_confirmation_scope_boundary_cycle01_v0.json"
)
STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_SCOPE_BOUNDARY_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "stat_nonflip_execution_custody_attestation_confirmation_attestation_scope_boundary_cycle01_v0.json"
)
STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_SCOPE_BOUNDARY_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_scope_boundary_cycle01_v0.json"
)
STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_SCOPE_BOUNDARY_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_cycle01_v0.json"
)
STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_SCOPE_BOUNDARY_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_cycle01_v0.json"
)
STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_SCOPE_BOUNDARY_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_cycle01_v0.json"
)
STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_SCOPE_BOUNDARY_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_cycle01_v0.json"
)
STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_SCOPE_BOUNDARY_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_cycle01_v0.json"
)

# Do not include this aggregation gate itself to avoid recursive re-entry.
STAT_ROW_SCAFFOLD_COMPONENT_GATES = [
    "formal/python/tests/test_stat_evidence_checkpoint_coupling_cycle01_gate.py",
    "formal/python/tests/test_stat_evidence_checkpoint_cycle01_acceptance_gate.py",
    "formal/python/tests/test_stat_der01_theorem_surface_scaffold_coupling_cycle01_gate.py",
    "formal/python/tests/test_stat_der01_theorem_body_scope_boundary_cycle01_gate.py",
    "formal/python/tests/test_stat_der01_theorem_body_scaffold_coupling_cycle01_gate.py",
    "formal/python/tests/test_stat_der01_discharge_scaffold_coupling_cycle01_gate.py",
    "formal/python/tests/test_stat_der01_object_surface_scaffold_coupling_cycle01_gate.py",
    "formal/python/tests/test_stat_der02_regime_closure_coupling_scaffold_coupling_cycle01_gate.py",
    "formal/python/tests/test_stat_der02_theorem_body_scaffold_coupling_cycle01_gate.py",
    "formal/python/tests/test_stat_der02_discharge_scaffold_coupling_cycle01_gate.py",
    "formal/python/tests/test_stat_der02_object_surface_scaffold_coupling_cycle01_gate.py",
    "formal/python/tests/test_stat_der02_theorem_body_scope_boundary_cycle01_gate.py",
    "formal/python/tests/test_stat_closure_hardening_bundle_coupling_cycle01_gate.py",
    "formal/python/tests/test_stat_evidence_interface_lane_scope_boundary_cycle01_gate.py",
    "formal/python/tests/test_stat_multi_cycle_drift_resistance_sweep_cycle02_gate.py",
    "formal/python/tests/test_stat_evidence_adequacy_5x5_justification_scaffold_cycle01_gate.py",
    "formal/python/tests/test_stat_promotion_readiness_scope_boundary_cycle01_gate.py",
    "formal/python/tests/test_stat_derivation_completeness_gate_scope_boundary_cycle01_gate.py",
    "formal/python/tests/test_stat_failure_trigger_audit_scope_boundary_cycle01_gate.py",
    "formal/python/tests/test_stat_derivation_completeness_discharge_surface_scope_boundary_cycle01_gate.py",
    "formal/python/tests/test_stat_derivation_completeness_discharge_theorem_surface_scope_boundary_cycle01_gate.py",
    "formal/python/tests/test_stat_derivation_completeness_discharge_object_surface_scope_boundary_cycle01_gate.py",
    "formal/python/tests/test_stat_derivation_completeness_discharge_coherence_scope_boundary_cycle01_gate.py",
    "formal/python/tests/test_stat_failure_trigger_discharge_surface_scope_boundary_cycle01_gate.py",
    "formal/python/tests/test_stat_failure_trigger_discharge_coherence_scope_boundary_cycle01_gate.py",
    "formal/python/tests/test_stat_failure_trigger_discharge_theorem_surface_scope_boundary_cycle01_gate.py",
    "formal/python/tests/test_stat_failure_trigger_discharge_object_surface_scope_boundary_cycle01_gate.py",
    "formal/python/tests/test_stat_discharge_completion_transition_scope_boundary_cycle01_gate.py",
    "formal/python/tests/test_stat_adjudication_transition_scope_boundary_cycle01_gate.py",
    "formal/python/tests/test_stat_inevitability_transition_scope_boundary_cycle01_gate.py",
    "formal/python/tests/test_stat_nonflip_execution_boundary_scope_boundary_cycle01_gate.py",
    "formal/python/tests/test_stat_nonflip_execution_custody_scope_boundary_cycle01_gate.py",
    "formal/python/tests/test_stat_nonflip_execution_custody_attestation_scope_boundary_cycle01_gate.py",
    "formal/python/tests/test_stat_nonflip_execution_custody_attestation_confirmation_scope_boundary_cycle01_gate.py",
    "formal/python/tests/test_stat_nonflip_execution_custody_attestation_confirmation_attestation_scope_boundary_cycle01_gate.py",
    "formal/python/tests/test_stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_scope_boundary_cycle01_gate.py",
    "formal/python/tests/test_stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_cycle01_gate.py",
    "formal/python/tests/test_stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_cycle01_gate.py",
    "formal/python/tests/test_stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_cycle01_gate.py",
    "formal/python/tests/test_stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_cycle01_gate.py",
    "formal/python/tests/test_stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_cycle01_gate.py",
    "formal/python/tests/test_pillar_phase_advancement_gate.py",
    "formal/python/tests/test_results_table_integrity.py",
]

EXPECTED_CHECKPOINT_ARTIFACT_ID = "stat_evidence_checkpoint_cycle01_v0"
EXPECTED_CHECKPOINT_GATES = [
    "formal/python/tests/test_stat_evidence_checkpoint_coupling_cycle01_gate.py",
    "formal/python/tests/test_stat_evidence_checkpoint_cycle01_acceptance_gate.py",
]
EXPECTED_ROW_IDS = ["TOE-STAT-DER-01", "TOE-STAT-DER-02"]
EXPECTED_ROW_LABEL = "P-POLICY"

EXPECTED_DER01_ARTIFACT_ID = "stat_der01_entropy_balance_theorem_surface_scaffold_cycle01_v0"
EXPECTED_DER01_GATE_REL = "formal/python/tests/test_stat_der01_theorem_surface_scaffold_coupling_cycle01_gate.py"
EXPECTED_DER01_THEOREM_BODY_SCOPE_BOUNDARY_ARTIFACT_ID = "stat_der01_theorem_body_scope_boundary_cycle01_v0"
EXPECTED_DER01_THEOREM_BODY_SCOPE_BOUNDARY_GATE_REL = (
    "formal/python/tests/test_stat_der01_theorem_body_scope_boundary_cycle01_gate.py"
)
EXPECTED_DER01_THEOREM_BODY_ARTIFACT_ID = "stat_der01_entropy_balance_theorem_body_scaffold_cycle01_v0"
EXPECTED_DER01_THEOREM_BODY_GATE_REL = "formal/python/tests/test_stat_der01_theorem_body_scaffold_coupling_cycle01_gate.py"
EXPECTED_DER01_DISCHARGE_ARTIFACT_ID = "stat_der01_entropy_balance_discharge_scaffold_cycle01_v0"
EXPECTED_DER01_DISCHARGE_GATE_REL = "formal/python/tests/test_stat_der01_discharge_scaffold_coupling_cycle01_gate.py"
EXPECTED_DER01_OBJECT_ARTIFACT_ID = "stat_der01_entropy_balance_object_surface_scaffold_cycle01_v0"
EXPECTED_DER01_OBJECT_GATE_REL = "formal/python/tests/test_stat_der01_object_surface_scaffold_coupling_cycle01_gate.py"
EXPECTED_DER02_ARTIFACT_ID = "stat_der02_regime_closure_coupling_scaffold_cycle01_v0"
EXPECTED_DER02_GATE_REL = "formal/python/tests/test_stat_der02_regime_closure_coupling_scaffold_coupling_cycle01_gate.py"
EXPECTED_DER02_THEOREM_BODY_ARTIFACT_ID = "stat_der02_regime_closure_theorem_body_scaffold_cycle01_v0"
EXPECTED_DER02_THEOREM_BODY_GATE_REL = (
    "formal/python/tests/test_stat_der02_theorem_body_scaffold_coupling_cycle01_gate.py"
)
EXPECTED_DER02_DISCHARGE_ARTIFACT_ID = "stat_der02_regime_closure_discharge_scaffold_cycle01_v0"
EXPECTED_DER02_DISCHARGE_GATE_REL = "formal/python/tests/test_stat_der02_discharge_scaffold_coupling_cycle01_gate.py"
EXPECTED_DER02_OBJECT_ARTIFACT_ID = "stat_der02_regime_closure_object_surface_scaffold_cycle01_v0"
EXPECTED_DER02_OBJECT_GATE_REL = "formal/python/tests/test_stat_der02_object_surface_scaffold_coupling_cycle01_gate.py"
EXPECTED_DER02_THEOREM_BODY_SCOPE_BOUNDARY_ARTIFACT_ID = "stat_der02_theorem_body_scope_boundary_cycle01_v0"
EXPECTED_DER02_THEOREM_BODY_SCOPE_BOUNDARY_GATE_REL = (
    "formal/python/tests/test_stat_der02_theorem_body_scope_boundary_cycle01_gate.py"
)
EXPECTED_STAT_CLOSURE_HARDENING_ARTIFACT_ID = "stat_closure_hardening_bundle_cycle01_v0"
EXPECTED_STAT_CLOSURE_HARDENING_GATE_REL = (
    "formal/python/tests/test_stat_closure_hardening_bundle_coupling_cycle01_gate.py"
)
EXPECTED_STAT_EVIDENCE_INTERFACE_SCOPE_BOUNDARY_ARTIFACT_ID = (
    "stat_evidence_interface_lane_scope_boundary_cycle01_v0"
)
EXPECTED_STAT_EVIDENCE_INTERFACE_SCOPE_BOUNDARY_GATE_REL = (
    "formal/python/tests/test_stat_evidence_interface_lane_scope_boundary_cycle01_gate.py"
)
EXPECTED_STAT_MULTI_CYCLE_DRIFT_RESISTANCE_ARTIFACT_ID = (
    "stat_multi_cycle_drift_resistance_sweep_cycle02_v0"
)
EXPECTED_STAT_MULTI_CYCLE_DRIFT_RESISTANCE_GATE_REL = (
    "formal/python/tests/test_stat_multi_cycle_drift_resistance_sweep_cycle02_gate.py"
)
EXPECTED_STAT_EVIDENCE_ADEQUACY_5X5_SCAFFOLD_ARTIFACT_ID = (
    "stat_evidence_adequacy_5x5_justification_scaffold_cycle01_v0"
)
EXPECTED_STAT_EVIDENCE_ADEQUACY_5X5_SCAFFOLD_GATE_REL = (
    "formal/python/tests/test_stat_evidence_adequacy_5x5_justification_scaffold_cycle01_gate.py"
)
EXPECTED_STAT_PROMOTION_READINESS_SCOPE_BOUNDARY_ARTIFACT_ID = (
    "stat_promotion_readiness_scope_boundary_cycle01_v0"
)
EXPECTED_STAT_PROMOTION_READINESS_SCOPE_BOUNDARY_GATE_REL = (
    "formal/python/tests/test_stat_promotion_readiness_scope_boundary_cycle01_gate.py"
)
EXPECTED_STAT_DERIVATION_COMPLETENESS_GATE_SCOPE_BOUNDARY_ARTIFACT_ID = (
    "stat_derivation_completeness_gate_scope_boundary_cycle01_v0"
)
EXPECTED_STAT_DERIVATION_COMPLETENESS_GATE_SCOPE_BOUNDARY_GATE_REL = (
    "formal/python/tests/test_stat_derivation_completeness_gate_scope_boundary_cycle01_gate.py"
)
EXPECTED_STAT_FAILURE_TRIGGER_AUDIT_SCOPE_BOUNDARY_ARTIFACT_ID = (
    "stat_failure_trigger_audit_scope_boundary_cycle01_v0"
)
EXPECTED_STAT_FAILURE_TRIGGER_AUDIT_SCOPE_BOUNDARY_GATE_REL = (
    "formal/python/tests/test_stat_failure_trigger_audit_scope_boundary_cycle01_gate.py"
)
EXPECTED_STAT_DERIVATION_COMPLETENESS_DISCHARGE_SURFACE_SCOPE_BOUNDARY_ARTIFACT_ID = (
    "stat_derivation_completeness_discharge_surface_scope_boundary_cycle01_v0"
)
EXPECTED_STAT_DERIVATION_COMPLETENESS_DISCHARGE_SURFACE_SCOPE_BOUNDARY_GATE_REL = (
    "formal/python/tests/test_stat_derivation_completeness_discharge_surface_scope_boundary_cycle01_gate.py"
)
EXPECTED_STAT_DERIVATION_COMPLETENESS_DISCHARGE_THEOREM_SURFACE_SCOPE_BOUNDARY_ARTIFACT_ID = (
    "stat_derivation_completeness_discharge_theorem_surface_scope_boundary_cycle01_v0"
)
EXPECTED_STAT_DERIVATION_COMPLETENESS_DISCHARGE_THEOREM_SURFACE_SCOPE_BOUNDARY_GATE_REL = (
    "formal/python/tests/test_stat_derivation_completeness_discharge_theorem_surface_scope_boundary_cycle01_gate.py"
)
EXPECTED_STAT_DERIVATION_COMPLETENESS_DISCHARGE_OBJECT_SURFACE_SCOPE_BOUNDARY_ARTIFACT_ID = (
    "stat_derivation_completeness_discharge_object_surface_scope_boundary_cycle01_v0"
)
EXPECTED_STAT_DERIVATION_COMPLETENESS_DISCHARGE_OBJECT_SURFACE_SCOPE_BOUNDARY_GATE_REL = (
    "formal/python/tests/test_stat_derivation_completeness_discharge_object_surface_scope_boundary_cycle01_gate.py"
)
EXPECTED_STAT_DERIVATION_COMPLETENESS_DISCHARGE_COHERENCE_SCOPE_BOUNDARY_ARTIFACT_ID = (
    "stat_derivation_completeness_discharge_coherence_scope_boundary_cycle01_v0"
)
EXPECTED_STAT_DERIVATION_COMPLETENESS_DISCHARGE_COHERENCE_SCOPE_BOUNDARY_GATE_REL = (
    "formal/python/tests/test_stat_derivation_completeness_discharge_coherence_scope_boundary_cycle01_gate.py"
)
EXPECTED_STAT_FAILURE_TRIGGER_DISCHARGE_SURFACE_SCOPE_BOUNDARY_ARTIFACT_ID = (
    "stat_failure_trigger_discharge_surface_scope_boundary_cycle01_v0"
)
EXPECTED_STAT_FAILURE_TRIGGER_DISCHARGE_SURFACE_SCOPE_BOUNDARY_GATE_REL = (
    "formal/python/tests/test_stat_failure_trigger_discharge_surface_scope_boundary_cycle01_gate.py"
)
EXPECTED_STAT_FAILURE_TRIGGER_DISCHARGE_COHERENCE_SCOPE_BOUNDARY_ARTIFACT_ID = (
    "stat_failure_trigger_discharge_coherence_scope_boundary_cycle01_v0"
)
EXPECTED_STAT_FAILURE_TRIGGER_DISCHARGE_COHERENCE_SCOPE_BOUNDARY_GATE_REL = (
    "formal/python/tests/test_stat_failure_trigger_discharge_coherence_scope_boundary_cycle01_gate.py"
)
EXPECTED_STAT_FAILURE_TRIGGER_DISCHARGE_THEOREM_SURFACE_SCOPE_BOUNDARY_ARTIFACT_ID = (
    "stat_failure_trigger_discharge_theorem_surface_scope_boundary_cycle01_v0"
)
EXPECTED_STAT_FAILURE_TRIGGER_DISCHARGE_THEOREM_SURFACE_SCOPE_BOUNDARY_GATE_REL = (
    "formal/python/tests/test_stat_failure_trigger_discharge_theorem_surface_scope_boundary_cycle01_gate.py"
)
EXPECTED_STAT_FAILURE_TRIGGER_DISCHARGE_OBJECT_SURFACE_SCOPE_BOUNDARY_ARTIFACT_ID = (
    "stat_failure_trigger_discharge_object_surface_scope_boundary_cycle01_v0"
)
EXPECTED_STAT_FAILURE_TRIGGER_DISCHARGE_OBJECT_SURFACE_SCOPE_BOUNDARY_GATE_REL = (
    "formal/python/tests/test_stat_failure_trigger_discharge_object_surface_scope_boundary_cycle01_gate.py"
)
EXPECTED_STAT_DISCHARGE_COMPLETION_TRANSITION_SCOPE_BOUNDARY_ARTIFACT_ID = (
    "stat_discharge_completion_transition_scope_boundary_cycle01_v0"
)
EXPECTED_STAT_DISCHARGE_COMPLETION_TRANSITION_SCOPE_BOUNDARY_GATE_REL = (
    "formal/python/tests/test_stat_discharge_completion_transition_scope_boundary_cycle01_gate.py"
)
EXPECTED_STAT_ADJUDICATION_TRANSITION_SCOPE_BOUNDARY_ARTIFACT_ID = (
    "stat_adjudication_transition_scope_boundary_cycle01_v0"
)
EXPECTED_STAT_ADJUDICATION_TRANSITION_SCOPE_BOUNDARY_GATE_REL = (
    "formal/python/tests/test_stat_adjudication_transition_scope_boundary_cycle01_gate.py"
)
EXPECTED_STAT_INEVITABILITY_TRANSITION_SCOPE_BOUNDARY_ARTIFACT_ID = (
    "stat_inevitability_transition_scope_boundary_cycle01_v0"
)
EXPECTED_STAT_INEVITABILITY_TRANSITION_SCOPE_BOUNDARY_GATE_REL = (
    "formal/python/tests/test_stat_inevitability_transition_scope_boundary_cycle01_gate.py"
)
EXPECTED_STAT_NONFLIP_EXECUTION_BOUNDARY_SCOPE_BOUNDARY_ARTIFACT_ID = (
    "stat_nonflip_execution_boundary_scope_boundary_cycle01_v0"
)
EXPECTED_STAT_NONFLIP_EXECUTION_BOUNDARY_SCOPE_BOUNDARY_GATE_REL = (
    "formal/python/tests/test_stat_nonflip_execution_boundary_scope_boundary_cycle01_gate.py"
)
EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_SCOPE_BOUNDARY_ARTIFACT_ID = (
    "stat_nonflip_execution_custody_scope_boundary_cycle01_v0"
)
EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_SCOPE_BOUNDARY_GATE_REL = (
    "formal/python/tests/test_stat_nonflip_execution_custody_scope_boundary_cycle01_gate.py"
)
EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_SCOPE_BOUNDARY_ARTIFACT_ID = (
    "stat_nonflip_execution_custody_attestation_scope_boundary_cycle01_v0"
)
EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_SCOPE_BOUNDARY_GATE_REL = (
    "formal/python/tests/test_stat_nonflip_execution_custody_attestation_scope_boundary_cycle01_gate.py"
)
EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_SCOPE_BOUNDARY_ARTIFACT_ID = (
    "stat_nonflip_execution_custody_attestation_confirmation_scope_boundary_cycle01_v0"
)
EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_SCOPE_BOUNDARY_GATE_REL = (
    "formal/python/tests/test_stat_nonflip_execution_custody_attestation_confirmation_scope_boundary_cycle01_gate.py"
)
EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_SCOPE_BOUNDARY_ARTIFACT_ID = (
    "stat_nonflip_execution_custody_attestation_confirmation_attestation_scope_boundary_cycle01_v0"
)
EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_SCOPE_BOUNDARY_GATE_REL = (
    "formal/python/tests/test_stat_nonflip_execution_custody_attestation_confirmation_attestation_scope_boundary_cycle01_gate.py"
)
EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_SCOPE_BOUNDARY_ARTIFACT_ID = (
    "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_scope_boundary_cycle01_v0"
)
EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_SCOPE_BOUNDARY_GATE_REL = (
    "formal/python/tests/test_stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_scope_boundary_cycle01_gate.py"
)
EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_SCOPE_BOUNDARY_ARTIFACT_ID = (
    "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_cycle01_v0"
)
EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_SCOPE_BOUNDARY_GATE_REL = (
    "formal/python/tests/test_stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_cycle01_gate.py"
)
EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_SCOPE_BOUNDARY_ARTIFACT_ID = (
    "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_cycle01_v0"
)
EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_SCOPE_BOUNDARY_GATE_REL = (
    "formal/python/tests/test_stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_cycle01_gate.py"
)
EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_SCOPE_BOUNDARY_ARTIFACT_ID = (
    "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_cycle01_v0"
)
EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_SCOPE_BOUNDARY_GATE_REL = (
    "formal/python/tests/test_stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_cycle01_gate.py"
)
EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_SCOPE_BOUNDARY_ARTIFACT_ID = (
    "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_cycle01_v0"
)
EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_SCOPE_BOUNDARY_GATE_REL = (
    "formal/python/tests/test_stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_cycle01_gate.py"
)
EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_SCOPE_BOUNDARY_ARTIFACT_ID = (
    "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_cycle01_v0"
)
EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_SCOPE_BOUNDARY_GATE_REL = (
    "formal/python/tests/test_stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_cycle01_gate.py"
)

DISALLOWED_STAT_TOKEN_PATTERNS: list[str] = []
DISALLOWED_OUTPUT_GLOBS: list[str] = []


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _results_row_line(text: str, row_id: str) -> str:
    m = re.search(rf"(?m)^\| {re.escape(row_id)} \| .*?$", text)
    assert m is not None, f"Missing results row `{row_id}`."
    return m.group(0)


def test_stat_row_scaffold_cycle01_aggregation_gate() -> None:
    stat_text = _read(STAT_DOC_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    results_text = _read(RESULTS_PATH)
    matrix = _read_json(MATRIX_PATH)

    assert "| `PILLAR-STAT` | `ACTIVE` |" in roadmap_text, (
        "STAT row-scaffold aggregation gate applies only after `PILLAR-STAT` activation."
    )
    stat_matrix = matrix.get("pillars", {}).get("PILLAR-STAT")
    assert isinstance(stat_matrix, dict), "PILLAR-STAT matrix row must exist for row-scaffold aggregation gate."
    assert stat_matrix.get("matrix_status") == "ACTIVE", "PILLAR-STAT matrix row must be `ACTIVE`."

    for gate_rel in STAT_ROW_SCAFFOLD_COMPONENT_GATES:
        gate_path = REPO_ROOT / gate_rel
        assert gate_path.exists(), f"Missing STAT row-scaffold component gate `{gate_rel}`."

    cmd = [sys.executable, "-m", "pytest", *STAT_ROW_SCAFFOLD_COMPONENT_GATES]
    result = subprocess.run(
        cmd,
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        encoding="utf-8",
    )
    assert result.returncode == 0, (
        "STAT row-scaffold component gates are not green.\n"
        f"Command: {' '.join(cmd)}\n"
        f"stdout:\n{result.stdout}\n"
        f"stderr:\n{result.stderr}"
    )

    checkpoint = _read_json(CHECKPOINT_ARTIFACT_PATH)
    der01 = _read_json(DER01_ARTIFACT_PATH)
    der01_theorem_body_scope_boundary = _read_json(DER01_THEOREM_BODY_SCOPE_BOUNDARY_ARTIFACT_PATH)
    der01_theorem_body = _read_json(DER01_THEOREM_BODY_ARTIFACT_PATH)
    der01_discharge = _read_json(DER01_DISCHARGE_ARTIFACT_PATH)
    der01_object = _read_json(DER01_OBJECT_ARTIFACT_PATH)
    der02 = _read_json(DER02_ARTIFACT_PATH)
    der02_theorem_body = _read_json(DER02_THEOREM_BODY_ARTIFACT_PATH)
    der02_discharge = _read_json(DER02_DISCHARGE_ARTIFACT_PATH)
    der02_object = _read_json(DER02_OBJECT_ARTIFACT_PATH)
    der02_theorem_body_scope_boundary = _read_json(DER02_THEOREM_BODY_SCOPE_BOUNDARY_ARTIFACT_PATH)
    stat_closure_hardening = _read_json(STAT_CLOSURE_HARDENING_ARTIFACT_PATH)
    stat_evidence_interface_scope_boundary = _read_json(STAT_EVIDENCE_INTERFACE_SCOPE_BOUNDARY_ARTIFACT_PATH)
    stat_multi_cycle_drift_resistance = _read_json(STAT_MULTI_CYCLE_DRIFT_RESISTANCE_ARTIFACT_PATH)
    stat_evidence_adequacy_5x5_scaffold = _read_json(STAT_EVIDENCE_ADEQUACY_5X5_SCAFFOLD_ARTIFACT_PATH)
    stat_promotion_readiness_scope_boundary = _read_json(STAT_PROMOTION_READINESS_SCOPE_BOUNDARY_ARTIFACT_PATH)
    stat_derivation_completeness_gate_scope_boundary = _read_json(
        STAT_DERIVATION_COMPLETENESS_GATE_SCOPE_BOUNDARY_ARTIFACT_PATH
    )
    stat_failure_trigger_audit_scope_boundary = _read_json(
        STAT_FAILURE_TRIGGER_AUDIT_SCOPE_BOUNDARY_ARTIFACT_PATH
    )
    stat_derivation_completeness_discharge_surface_scope_boundary = _read_json(
        STAT_DERIVATION_COMPLETENESS_DISCHARGE_SURFACE_SCOPE_BOUNDARY_ARTIFACT_PATH
    )
    stat_derivation_completeness_discharge_theorem_surface_scope_boundary = _read_json(
        STAT_DERIVATION_COMPLETENESS_DISCHARGE_THEOREM_SURFACE_SCOPE_BOUNDARY_ARTIFACT_PATH
    )
    stat_derivation_completeness_discharge_object_surface_scope_boundary = _read_json(
        STAT_DERIVATION_COMPLETENESS_DISCHARGE_OBJECT_SURFACE_SCOPE_BOUNDARY_ARTIFACT_PATH
    )
    stat_derivation_completeness_discharge_coherence_scope_boundary = _read_json(
        STAT_DERIVATION_COMPLETENESS_DISCHARGE_COHERENCE_SCOPE_BOUNDARY_ARTIFACT_PATH
    )
    stat_failure_trigger_discharge_surface_scope_boundary = _read_json(
        STAT_FAILURE_TRIGGER_DISCHARGE_SURFACE_SCOPE_BOUNDARY_ARTIFACT_PATH
    )
    stat_failure_trigger_discharge_coherence_scope_boundary = _read_json(
        STAT_FAILURE_TRIGGER_DISCHARGE_COHERENCE_SCOPE_BOUNDARY_ARTIFACT_PATH
    )
    stat_failure_trigger_discharge_theorem_surface_scope_boundary = _read_json(
        STAT_FAILURE_TRIGGER_DISCHARGE_THEOREM_SURFACE_SCOPE_BOUNDARY_ARTIFACT_PATH
    )
    stat_failure_trigger_discharge_object_surface_scope_boundary = _read_json(
        STAT_FAILURE_TRIGGER_DISCHARGE_OBJECT_SURFACE_SCOPE_BOUNDARY_ARTIFACT_PATH
    )
    stat_discharge_completion_transition_scope_boundary = _read_json(
        STAT_DISCHARGE_COMPLETION_TRANSITION_SCOPE_BOUNDARY_ARTIFACT_PATH
    )
    stat_adjudication_transition_scope_boundary = _read_json(
        STAT_ADJUDICATION_TRANSITION_SCOPE_BOUNDARY_ARTIFACT_PATH
    )
    stat_inevitability_transition_scope_boundary = _read_json(
        STAT_INEVITABILITY_TRANSITION_SCOPE_BOUNDARY_ARTIFACT_PATH
    )
    stat_nonflip_execution_boundary_scope_boundary = _read_json(
        STAT_NONFLIP_EXECUTION_BOUNDARY_SCOPE_BOUNDARY_ARTIFACT_PATH
    )
    stat_nonflip_execution_custody_scope_boundary = _read_json(
        STAT_NONFLIP_EXECUTION_CUSTODY_SCOPE_BOUNDARY_ARTIFACT_PATH
    )
    stat_nonflip_execution_custody_attestation_scope_boundary = _read_json(
        STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_SCOPE_BOUNDARY_ARTIFACT_PATH
    )
    stat_nonflip_execution_custody_attestation_confirmation_scope_boundary = _read_json(
        STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_SCOPE_BOUNDARY_ARTIFACT_PATH
    )
    stat_nonflip_execution_custody_attestation_confirmation_attestation_scope_boundary = _read_json(
        STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_SCOPE_BOUNDARY_ARTIFACT_PATH
    )
    stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_scope_boundary = _read_json(
        STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_SCOPE_BOUNDARY_ARTIFACT_PATH
    )
    stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_scope_boundary = (
        _read_json(
            STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_SCOPE_BOUNDARY_ARTIFACT_PATH
        )
    )
    stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary = (
        _read_json(
            STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_SCOPE_BOUNDARY_ARTIFACT_PATH
        )
    )
    stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary = (
        _read_json(
            STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_SCOPE_BOUNDARY_ARTIFACT_PATH
        )
    )
    stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary = (
        _read_json(
            STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_SCOPE_BOUNDARY_ARTIFACT_PATH
        )
    )
    stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary = (
        _read_json(
            STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_SCOPE_BOUNDARY_ARTIFACT_PATH
        )
    )

    assert checkpoint.get("artifact_id") == EXPECTED_CHECKPOINT_ARTIFACT_ID
    assert checkpoint.get("placeholder_template") is True
    checkpoint_payload = checkpoint.get("payload")
    assert isinstance(checkpoint_payload, dict)
    assert checkpoint_payload.get("target_id") == "TARGET-TH-ENTROPY-PLAN"
    assert checkpoint_payload.get("status") == "structural_activation_checkpoint_placeholder"
    assert checkpoint_payload.get("required_results_rows_refs") == EXPECTED_ROW_IDS
    assert checkpoint_payload.get("artifact_sha256") == "TOP_LEVEL_payload_sha256"

    checkpoint_acceptance = checkpoint_payload.get("acceptance_criteria_v0")
    assert isinstance(checkpoint_acceptance, dict)
    assert checkpoint_acceptance.get("required_results_rows_refs") == EXPECTED_ROW_IDS
    assert checkpoint_acceptance.get("cross_surface_pointers_required") == checkpoint_payload.get("cross_surface_pointers")
    assert set(EXPECTED_CHECKPOINT_GATES).issubset(set(checkpoint_payload.get("cross_surface_pointers", [])))

    for artifact_json, expected_artifact_id, expected_row_id in (
        (der01, EXPECTED_DER01_ARTIFACT_ID, "TOE-STAT-DER-01"),
        (der01_theorem_body_scope_boundary, EXPECTED_DER01_THEOREM_BODY_SCOPE_BOUNDARY_ARTIFACT_ID, "TOE-STAT-DER-01"),
        (der01_theorem_body, EXPECTED_DER01_THEOREM_BODY_ARTIFACT_ID, "TOE-STAT-DER-01"),
        (der01_discharge, EXPECTED_DER01_DISCHARGE_ARTIFACT_ID, "TOE-STAT-DER-01"),
        (der01_object, EXPECTED_DER01_OBJECT_ARTIFACT_ID, "TOE-STAT-DER-01"),
        (der02, EXPECTED_DER02_ARTIFACT_ID, "TOE-STAT-DER-02"),
        (der02_theorem_body, EXPECTED_DER02_THEOREM_BODY_ARTIFACT_ID, "TOE-STAT-DER-02"),
        (der02_discharge, EXPECTED_DER02_DISCHARGE_ARTIFACT_ID, "TOE-STAT-DER-02"),
        (der02_object, EXPECTED_DER02_OBJECT_ARTIFACT_ID, "TOE-STAT-DER-02"),
        (der02_theorem_body_scope_boundary, EXPECTED_DER02_THEOREM_BODY_SCOPE_BOUNDARY_ARTIFACT_ID, "TOE-STAT-DER-02"),
    ):
        assert artifact_json.get("artifact_id") == expected_artifact_id
        assert artifact_json.get("placeholder_template") is True
        payload = artifact_json.get("payload")
        assert isinstance(payload, dict)
        assert payload.get("artifact_id") == expected_artifact_id
        assert payload.get("cycle_id") == "CYCLE01"
        assert payload.get("pillar_id") == "PILLAR-STAT"
        assert payload.get("target_id") == "TARGET-TH-ENTROPY-PLAN"
        assert payload.get("results_row_id") == expected_row_id
        assert payload.get("results_row_expected_label") == EXPECTED_ROW_LABEL
        assert payload.get("artifact_sha256") == "TOP_LEVEL_payload_sha256"
        assert payload.get("prerequisite_structural_checkpoint_artifact_id") == EXPECTED_CHECKPOINT_ARTIFACT_ID
        assert payload.get("prerequisite_structural_checkpoint_gates") == EXPECTED_CHECKPOINT_GATES

    der01_payload = der01["payload"]
    der01_theorem_body_scope_boundary_payload = der01_theorem_body_scope_boundary["payload"]
    der01_theorem_body_payload = der01_theorem_body["payload"]
    der01_discharge_payload = der01_discharge["payload"]
    der01_object_payload = der01_object["payload"]
    der02_payload = der02["payload"]
    der02_theorem_body_payload = der02_theorem_body["payload"]
    der02_discharge_payload = der02_discharge["payload"]
    der02_object_payload = der02_object["payload"]
    der02_theorem_body_scope_boundary_payload = der02_theorem_body_scope_boundary["payload"]
    stat_closure_hardening_payload = stat_closure_hardening.get("payload")
    stat_evidence_interface_scope_boundary_payload = stat_evidence_interface_scope_boundary.get("payload")
    stat_multi_cycle_drift_resistance_payload = stat_multi_cycle_drift_resistance.get("payload")
    stat_evidence_adequacy_5x5_scaffold_payload = stat_evidence_adequacy_5x5_scaffold.get("payload")
    stat_promotion_readiness_scope_boundary_payload = stat_promotion_readiness_scope_boundary.get("payload")
    stat_derivation_completeness_gate_scope_boundary_payload = (
        stat_derivation_completeness_gate_scope_boundary.get("payload")
    )
    stat_failure_trigger_audit_scope_boundary_payload = stat_failure_trigger_audit_scope_boundary.get("payload")
    stat_derivation_completeness_discharge_surface_scope_boundary_payload = (
        stat_derivation_completeness_discharge_surface_scope_boundary.get("payload")
    )
    stat_derivation_completeness_discharge_theorem_surface_scope_boundary_payload = (
        stat_derivation_completeness_discharge_theorem_surface_scope_boundary.get("payload")
    )
    stat_derivation_completeness_discharge_object_surface_scope_boundary_payload = (
        stat_derivation_completeness_discharge_object_surface_scope_boundary.get("payload")
    )
    stat_derivation_completeness_discharge_coherence_scope_boundary_payload = (
        stat_derivation_completeness_discharge_coherence_scope_boundary.get("payload")
    )
    stat_failure_trigger_discharge_surface_scope_boundary_payload = (
        stat_failure_trigger_discharge_surface_scope_boundary.get("payload")
    )
    stat_failure_trigger_discharge_coherence_scope_boundary_payload = (
        stat_failure_trigger_discharge_coherence_scope_boundary.get("payload")
    )
    stat_failure_trigger_discharge_theorem_surface_scope_boundary_payload = (
        stat_failure_trigger_discharge_theorem_surface_scope_boundary.get("payload")
    )
    stat_failure_trigger_discharge_object_surface_scope_boundary_payload = (
        stat_failure_trigger_discharge_object_surface_scope_boundary.get("payload")
    )
    stat_discharge_completion_transition_scope_boundary_payload = (
        stat_discharge_completion_transition_scope_boundary.get("payload")
    )
    stat_adjudication_transition_scope_boundary_payload = (
        stat_adjudication_transition_scope_boundary.get("payload")
    )
    stat_inevitability_transition_scope_boundary_payload = (
        stat_inevitability_transition_scope_boundary.get("payload")
    )
    stat_nonflip_execution_boundary_scope_boundary_payload = (
        stat_nonflip_execution_boundary_scope_boundary.get("payload")
    )
    stat_nonflip_execution_custody_scope_boundary_payload = (
        stat_nonflip_execution_custody_scope_boundary.get("payload")
    )
    stat_nonflip_execution_custody_attestation_scope_boundary_payload = (
        stat_nonflip_execution_custody_attestation_scope_boundary.get("payload")
    )
    stat_nonflip_execution_custody_attestation_confirmation_scope_boundary_payload = (
        stat_nonflip_execution_custody_attestation_confirmation_scope_boundary.get("payload")
    )
    stat_nonflip_execution_custody_attestation_confirmation_attestation_scope_boundary_payload = (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_scope_boundary.get("payload")
    )
    stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_scope_boundary_payload = (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_scope_boundary.get("payload")
    )
    stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_payload = (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_scope_boundary.get(
            "payload"
        )
    )
    stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_payload = (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary.get(
            "payload"
        )
    )
    stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_payload = (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary.get(
            "payload"
        )
    )
    stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_payload = (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary.get(
            "payload"
        )
    )
    stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_payload = (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary.get(
            "payload"
        )
    )
    assert der01_payload.get("status") == "theorem_surface_scaffold_placeholder_nonclaim"
    assert der01_theorem_body_scope_boundary_payload.get("status") == "theorem_body_scope_boundary_placeholder_nonclaim"
    assert der01_theorem_body_payload.get("status") == "theorem_body_scaffold_placeholder_nonclaim"
    assert der01_discharge_payload.get("status") == "discharge_scaffold_placeholder_nonclaim"
    assert der01_object_payload.get("status") == "object_surface_scaffold_placeholder_nonclaim"
    assert der02_payload.get("status") == "regime_validity_closure_coupling_scaffold_placeholder_nonclaim"
    assert der02_theorem_body_payload.get("status") == "regime_closure_theorem_body_scaffold_placeholder_nonclaim"
    assert der02_discharge_payload.get("status") == "regime_closure_discharge_scaffold_placeholder_nonclaim"
    assert der02_object_payload.get("status") == "regime_closure_object_surface_scaffold_placeholder_nonclaim"
    assert der02_theorem_body_scope_boundary_payload.get("status") == "theorem_body_scope_boundary_placeholder_nonclaim"
    assert stat_closure_hardening.get("artifact_id") == EXPECTED_STAT_CLOSURE_HARDENING_ARTIFACT_ID
    assert stat_closure_hardening.get("placeholder_template") is True
    assert isinstance(stat_closure_hardening_payload, dict)
    assert stat_closure_hardening_payload.get("checkpoint") == "stat_closure_hardening_cycle01"
    assert stat_closure_hardening_payload.get("status") == "placeholder_non_promotional"
    assert stat_closure_hardening_payload.get("boundedness_restatement") == [
        "active_stage_pre_discharge_scope_only",
        "no_toe_stat_der_discharge_claim",
        "no_inevitability_or_adequacy_completion_claim",
        "no_external_truth_claim",
    ]
    assert stat_closure_hardening_payload.get("anti_shortcut_constraints") == [
        "no_phase_skip_promotion",
        "no_implicit_status_promotion",
        "artifact_hash_and_cross_surface_pointers_required",
    ]
    assert stat_closure_hardening_payload.get("discharge_row_linkage") == EXPECTED_ROW_IDS
    assert (
        stat_evidence_interface_scope_boundary.get("artifact_id")
        == EXPECTED_STAT_EVIDENCE_INTERFACE_SCOPE_BOUNDARY_ARTIFACT_ID
    )
    assert stat_evidence_interface_scope_boundary.get("placeholder_template") is True
    assert isinstance(stat_evidence_interface_scope_boundary_payload, dict)
    assert (
        stat_evidence_interface_scope_boundary_payload.get("checkpoint")
        == "stat_evidence_interface_lane_scope_boundary_cycle01"
    )
    assert stat_evidence_interface_scope_boundary_payload.get("status") == "placeholder_non_promotional"
    assert stat_evidence_interface_scope_boundary_payload.get("interface_scope_boundary") == [
        "evidence_interface_schema_placeholder_only",
        "no_external_dataset_admission_claim",
        "no_stat_adequacy_adjudication_claim",
        "no_label_promotion_claim",
        "no_external_truth_claim",
    ]
    assert stat_evidence_interface_scope_boundary_payload.get("anti_shortcut_constraints") == [
        "no_phase_skip_promotion",
        "no_implicit_status_promotion",
        "artifact_hash_and_cross_surface_pointers_required",
    ]
    assert stat_evidence_interface_scope_boundary_payload.get("discharge_row_linkage") == EXPECTED_ROW_IDS
    assert (
        stat_multi_cycle_drift_resistance.get("artifact_id")
        == EXPECTED_STAT_MULTI_CYCLE_DRIFT_RESISTANCE_ARTIFACT_ID
    )
    assert stat_multi_cycle_drift_resistance.get("placeholder_template") is True
    assert isinstance(stat_multi_cycle_drift_resistance_payload, dict)
    assert (
        stat_multi_cycle_drift_resistance_payload.get("checkpoint")
        == "stat_multi_cycle_drift_resistance_sweep_cycle02"
    )
    assert stat_multi_cycle_drift_resistance_payload.get("status") == "placeholder_non_promotional"
    assert stat_multi_cycle_drift_resistance_payload.get("cycle_window") == ["cycle01", "cycle02"]
    assert stat_multi_cycle_drift_resistance_payload.get("drift_resistance_scope") == [
        "multi_cycle_token_stability_placeholder_only",
        "cross_surface_pointer_stability_placeholder_only",
        "no_adjudication_or_label_promotion_claim",
        "no_external_truth_claim",
    ]
    assert stat_multi_cycle_drift_resistance_payload.get("anti_shortcut_constraints") == [
        "no_phase_skip_promotion",
        "no_implicit_status_promotion",
        "artifact_hash_and_cross_surface_pointers_required",
    ]
    assert stat_multi_cycle_drift_resistance_payload.get("discharge_row_linkage") == EXPECTED_ROW_IDS
    assert (
        stat_evidence_adequacy_5x5_scaffold.get("artifact_id")
        == EXPECTED_STAT_EVIDENCE_ADEQUACY_5X5_SCAFFOLD_ARTIFACT_ID
    )
    assert stat_evidence_adequacy_5x5_scaffold.get("placeholder_template") is True
    assert isinstance(stat_evidence_adequacy_5x5_scaffold_payload, dict)
    assert (
        stat_evidence_adequacy_5x5_scaffold_payload.get("checkpoint")
        == "stat_evidence_adequacy_5x5_justification_scaffold_cycle01"
    )
    assert stat_evidence_adequacy_5x5_scaffold_payload.get("status") == "placeholder_non_promotional"
    assert stat_evidence_adequacy_5x5_scaffold_payload.get("adequacy_scope_boundary") == [
        "five_by_five_justification_structure_placeholder_only",
        "entry_threshold_binding_without_completion_claim",
        "no_stat_adequacy_completion_claim",
        "no_label_promotion_claim",
        "no_external_truth_claim",
    ]
    assert (
        stat_evidence_adequacy_5x5_scaffold_payload.get("entry_threshold_token")
        == "EVIDENCE_ADEQUACY_STAT_5X5_JUSTIFICATION_ENTRY_THRESHOLD_v0: MIN_5_ENTRIES_REQUIRED"
    )
    assert stat_evidence_adequacy_5x5_scaffold_payload.get("entry_placeholders") == [
        "STAT_ADEQUACY_ENTRY_01_v0_PLACEHOLDER",
        "STAT_ADEQUACY_ENTRY_02_v0_PLACEHOLDER",
        "STAT_ADEQUACY_ENTRY_03_v0_PLACEHOLDER",
        "STAT_ADEQUACY_ENTRY_04_v0_PLACEHOLDER",
        "STAT_ADEQUACY_ENTRY_05_v0_PLACEHOLDER",
    ]
    assert stat_evidence_adequacy_5x5_scaffold_payload.get("anti_shortcut_constraints") == [
        "no_phase_skip_promotion",
        "no_implicit_status_promotion",
        "artifact_hash_and_cross_surface_pointers_required",
    ]
    assert stat_evidence_adequacy_5x5_scaffold_payload.get("discharge_row_linkage") == EXPECTED_ROW_IDS
    assert (
        stat_promotion_readiness_scope_boundary.get("artifact_id")
        == EXPECTED_STAT_PROMOTION_READINESS_SCOPE_BOUNDARY_ARTIFACT_ID
    )
    assert stat_promotion_readiness_scope_boundary.get("placeholder_template") is True
    assert isinstance(stat_promotion_readiness_scope_boundary_payload, dict)
    assert (
        stat_promotion_readiness_scope_boundary_payload.get("checkpoint")
        == "stat_promotion_readiness_scope_boundary_cycle01"
    )
    assert stat_promotion_readiness_scope_boundary_payload.get("status") == "placeholder_non_promotional"
    assert stat_promotion_readiness_scope_boundary_payload.get("promotion_readiness_scope_boundary") == [
        "promotion_input_contract_placeholder_only",
        "requires_derivation_completeness_gate_before_execution",
        "requires_adequacy_completion_before_execution",
        "no_claim_promotion_execution",
        "no_external_truth_claim",
    ]
    assert stat_promotion_readiness_scope_boundary_payload.get("required_readiness_inputs") == [
        "derivation_completeness_gate_placeholder_required_before_execution",
        "evidence_adequacy_5x5_completion_token_required_before_execution",
        "results_rows_must_remain_p_policy_until_dedicated_promotion_gate",
    ]
    assert stat_promotion_readiness_scope_boundary_payload.get("anti_shortcut_constraints") == [
        "no_phase_skip_promotion",
        "no_implicit_status_promotion",
        "artifact_hash_and_cross_surface_pointers_required",
    ]
    assert stat_promotion_readiness_scope_boundary_payload.get("discharge_row_linkage") == EXPECTED_ROW_IDS
    assert (
        stat_derivation_completeness_gate_scope_boundary.get("artifact_id")
        == EXPECTED_STAT_DERIVATION_COMPLETENESS_GATE_SCOPE_BOUNDARY_ARTIFACT_ID
    )
    assert stat_derivation_completeness_gate_scope_boundary.get("placeholder_template") is True
    assert isinstance(stat_derivation_completeness_gate_scope_boundary_payload, dict)
    assert (
        stat_derivation_completeness_gate_scope_boundary_payload.get("checkpoint")
        == "stat_derivation_completeness_gate_scope_boundary_cycle01"
    )
    assert stat_derivation_completeness_gate_scope_boundary_payload.get("status") == "placeholder_non_promotional"
    assert stat_derivation_completeness_gate_scope_boundary_payload.get("derivation_completeness_scope_boundary") == [
        "derivation_completeness_gate_structure_placeholder_only",
        "failure_trigger_audit_structure_placeholder_only",
        "no_derivation_completeness_discharge_claim",
        "no_label_promotion_claim",
        "no_external_truth_claim",
    ]
    assert stat_derivation_completeness_gate_scope_boundary_payload.get("required_gate_inputs") == [
        "der01_der02_row_scaffolds_pinned_before_completion_gate_execution",
        "closure_hardening_bundle_pinned_before_completion_gate_execution",
        "multi_cycle_drift_resistance_scaffold_pinned_before_completion_gate_execution",
        "evidence_adequacy_completion_token_required_before_completion_gate_execution",
    ]
    assert stat_derivation_completeness_gate_scope_boundary_payload.get("anti_shortcut_constraints") == [
        "no_phase_skip_promotion",
        "no_implicit_status_promotion",
        "artifact_hash_and_cross_surface_pointers_required",
    ]
    assert stat_derivation_completeness_gate_scope_boundary_payload.get("discharge_row_linkage") == EXPECTED_ROW_IDS
    assert (
        stat_failure_trigger_audit_scope_boundary.get("artifact_id")
        == EXPECTED_STAT_FAILURE_TRIGGER_AUDIT_SCOPE_BOUNDARY_ARTIFACT_ID
    )
    assert stat_failure_trigger_audit_scope_boundary.get("placeholder_template") is True
    assert isinstance(stat_failure_trigger_audit_scope_boundary_payload, dict)
    assert (
        stat_failure_trigger_audit_scope_boundary_payload.get("checkpoint")
        == "stat_failure_trigger_audit_scope_boundary_cycle01"
    )
    assert stat_failure_trigger_audit_scope_boundary_payload.get("status") == "placeholder_non_promotional"
    assert stat_failure_trigger_audit_scope_boundary_payload.get("failure_trigger_audit_scope_boundary") == [
        "failure_trigger_set_structure_placeholder_only",
        "failure_informative_audit_structure_placeholder_only",
        "no_failure_trigger_discharge_claim",
        "no_label_promotion_claim",
        "no_external_truth_claim",
    ]
    assert stat_failure_trigger_audit_scope_boundary_payload.get("required_audit_inputs") == [
        "derivation_completeness_gate_scope_boundary_pinned_before_audit_execution",
        "multi_cycle_drift_resistance_scaffold_pinned_before_audit_execution",
        "evidence_adequacy_completion_token_required_before_audit_execution",
        "promotion_readiness_scope_boundary_pinned_before_audit_execution",
    ]
    assert stat_failure_trigger_audit_scope_boundary_payload.get("anti_shortcut_constraints") == [
        "no_phase_skip_promotion",
        "no_implicit_status_promotion",
        "artifact_hash_and_cross_surface_pointers_required",
    ]
    assert stat_failure_trigger_audit_scope_boundary_payload.get("discharge_row_linkage") == EXPECTED_ROW_IDS
    assert (
        stat_derivation_completeness_discharge_surface_scope_boundary.get("artifact_id")
        == EXPECTED_STAT_DERIVATION_COMPLETENESS_DISCHARGE_SURFACE_SCOPE_BOUNDARY_ARTIFACT_ID
    )
    assert stat_derivation_completeness_discharge_surface_scope_boundary.get("placeholder_template") is True
    assert isinstance(stat_derivation_completeness_discharge_surface_scope_boundary_payload, dict)
    assert (
        stat_derivation_completeness_discharge_surface_scope_boundary_payload.get("checkpoint")
        == "stat_derivation_completeness_discharge_surface_scope_boundary_cycle01"
    )
    assert stat_derivation_completeness_discharge_surface_scope_boundary_payload.get("status") == "placeholder_non_promotional"
    assert stat_derivation_completeness_discharge_surface_scope_boundary_payload.get("discharge_surface_scope_boundary") == [
        "derivation_completeness_discharge_surface_structure_placeholder_only",
        "derivation_completeness_theorem_surface_structure_placeholder_only",
        "no_derivation_completeness_discharge_claim",
        "no_label_promotion_claim",
        "no_external_truth_claim",
    ]
    assert stat_derivation_completeness_discharge_surface_scope_boundary_payload.get("required_surface_inputs") == [
        "derivation_completeness_gate_scope_boundary_pinned_before_surface_execution",
        "failure_trigger_audit_scope_boundary_pinned_before_surface_execution",
        "evidence_adequacy_completion_token_required_before_surface_execution",
        "promotion_readiness_scope_boundary_pinned_before_surface_execution",
    ]
    assert stat_derivation_completeness_discharge_surface_scope_boundary_payload.get("anti_shortcut_constraints") == [
        "no_phase_skip_promotion",
        "no_implicit_status_promotion",
        "artifact_hash_and_cross_surface_pointers_required",
    ]
    assert stat_derivation_completeness_discharge_surface_scope_boundary_payload.get("discharge_row_linkage") == EXPECTED_ROW_IDS
    assert (
        stat_derivation_completeness_discharge_theorem_surface_scope_boundary.get("artifact_id")
        == EXPECTED_STAT_DERIVATION_COMPLETENESS_DISCHARGE_THEOREM_SURFACE_SCOPE_BOUNDARY_ARTIFACT_ID
    )
    assert stat_derivation_completeness_discharge_theorem_surface_scope_boundary.get("placeholder_template") is True
    assert isinstance(stat_derivation_completeness_discharge_theorem_surface_scope_boundary_payload, dict)
    assert (
        stat_derivation_completeness_discharge_theorem_surface_scope_boundary_payload.get("checkpoint")
        == "stat_derivation_completeness_discharge_theorem_surface_scope_boundary_cycle01"
    )
    assert (
        stat_derivation_completeness_discharge_theorem_surface_scope_boundary_payload.get("status")
        == "placeholder_non_promotional"
    )
    assert stat_derivation_completeness_discharge_theorem_surface_scope_boundary_payload.get("theorem_surface_scope_boundary") == [
        "derivation_completeness_discharge_theorem_surface_structure_placeholder_only",
        "derivation_completeness_discharge_assumption_surface_placeholder_only",
        "no_derivation_completeness_theorem_discharge_claim",
        "no_label_promotion_claim",
        "no_external_truth_claim",
    ]
    assert (
        stat_derivation_completeness_discharge_theorem_surface_scope_boundary_payload.get("required_theorem_surface_inputs")
        == [
            "derivation_completeness_gate_scope_boundary_pinned_before_theorem_surface_execution",
            "derivation_completeness_discharge_surface_scope_boundary_pinned_before_theorem_surface_execution",
            "failure_trigger_audit_scope_boundary_pinned_before_theorem_surface_execution",
            "evidence_adequacy_completion_token_required_before_theorem_surface_execution",
            "promotion_readiness_scope_boundary_pinned_before_theorem_surface_execution",
        ]
    )
    assert stat_derivation_completeness_discharge_theorem_surface_scope_boundary_payload.get("anti_shortcut_constraints") == [
        "no_phase_skip_promotion",
        "no_implicit_status_promotion",
        "artifact_hash_and_cross_surface_pointers_required",
    ]
    assert stat_derivation_completeness_discharge_theorem_surface_scope_boundary_payload.get("discharge_row_linkage") == (
        EXPECTED_ROW_IDS
    )
    assert (
        stat_derivation_completeness_discharge_object_surface_scope_boundary.get("artifact_id")
        == EXPECTED_STAT_DERIVATION_COMPLETENESS_DISCHARGE_OBJECT_SURFACE_SCOPE_BOUNDARY_ARTIFACT_ID
    )
    assert stat_derivation_completeness_discharge_object_surface_scope_boundary.get("placeholder_template") is True
    assert isinstance(stat_derivation_completeness_discharge_object_surface_scope_boundary_payload, dict)
    assert (
        stat_derivation_completeness_discharge_object_surface_scope_boundary_payload.get("checkpoint")
        == "stat_derivation_completeness_discharge_object_surface_scope_boundary_cycle01"
    )
    assert (
        stat_derivation_completeness_discharge_object_surface_scope_boundary_payload.get("status")
        == "placeholder_non_promotional"
    )
    assert stat_derivation_completeness_discharge_object_surface_scope_boundary_payload.get("object_surface_scope_boundary") == [
        "derivation_completeness_discharge_object_surface_structure_placeholder_only",
        "derivation_completeness_discharge_observable_surface_placeholder_only",
        "no_derivation_completeness_object_discharge_claim",
        "no_label_promotion_claim",
        "no_external_truth_claim",
    ]
    assert (
        stat_derivation_completeness_discharge_object_surface_scope_boundary_payload.get("required_object_surface_inputs")
        == [
            "derivation_completeness_gate_scope_boundary_pinned_before_object_surface_execution",
            "derivation_completeness_discharge_surface_scope_boundary_pinned_before_object_surface_execution",
            "derivation_completeness_discharge_theorem_surface_scope_boundary_pinned_before_object_surface_execution",
            "failure_trigger_audit_scope_boundary_pinned_before_object_surface_execution",
            "evidence_adequacy_completion_token_required_before_object_surface_execution",
            "promotion_readiness_scope_boundary_pinned_before_object_surface_execution",
        ]
    )
    assert stat_derivation_completeness_discharge_object_surface_scope_boundary_payload.get("anti_shortcut_constraints") == [
        "no_phase_skip_promotion",
        "no_implicit_status_promotion",
        "artifact_hash_and_cross_surface_pointers_required",
    ]
    assert stat_derivation_completeness_discharge_object_surface_scope_boundary_payload.get("discharge_row_linkage") == (
        EXPECTED_ROW_IDS
    )
    assert (
        stat_derivation_completeness_discharge_coherence_scope_boundary.get("artifact_id")
        == EXPECTED_STAT_DERIVATION_COMPLETENESS_DISCHARGE_COHERENCE_SCOPE_BOUNDARY_ARTIFACT_ID
    )
    assert stat_derivation_completeness_discharge_coherence_scope_boundary.get("placeholder_template") is True
    assert isinstance(stat_derivation_completeness_discharge_coherence_scope_boundary_payload, dict)
    assert (
        stat_derivation_completeness_discharge_coherence_scope_boundary_payload.get("checkpoint")
        == "stat_derivation_completeness_discharge_coherence_scope_boundary_cycle01"
    )
    assert stat_derivation_completeness_discharge_coherence_scope_boundary_payload.get("status") == "placeholder_non_promotional"
    assert stat_derivation_completeness_discharge_coherence_scope_boundary_payload.get("coherence_scope_boundary") == [
        "derivation_completeness_discharge_surface_theorem_object_alignment_placeholder_only",
        "derivation_completeness_discharge_dependency_consistency_placeholder_only",
        "no_derivation_completeness_coherence_discharge_claim",
        "no_label_promotion_claim",
        "no_external_truth_claim",
    ]
    assert stat_derivation_completeness_discharge_coherence_scope_boundary_payload.get("required_coherence_inputs") == [
        "derivation_completeness_discharge_surface_scope_boundary_pinned_before_coherence_execution",
        "derivation_completeness_discharge_theorem_surface_scope_boundary_pinned_before_coherence_execution",
        "derivation_completeness_discharge_object_surface_scope_boundary_pinned_before_coherence_execution",
        "failure_trigger_discharge_surface_scope_boundary_pinned_before_coherence_execution",
        "evidence_adequacy_completion_token_required_before_coherence_execution",
        "promotion_readiness_scope_boundary_pinned_before_coherence_execution",
    ]
    assert stat_derivation_completeness_discharge_coherence_scope_boundary_payload.get("anti_shortcut_constraints") == [
        "no_phase_skip_promotion",
        "no_implicit_status_promotion",
        "artifact_hash_and_cross_surface_pointers_required",
    ]
    assert stat_derivation_completeness_discharge_coherence_scope_boundary_payload.get("discharge_row_linkage") == (
        EXPECTED_ROW_IDS
    )
    assert (
        stat_failure_trigger_discharge_surface_scope_boundary.get("artifact_id")
        == EXPECTED_STAT_FAILURE_TRIGGER_DISCHARGE_SURFACE_SCOPE_BOUNDARY_ARTIFACT_ID
    )
    assert stat_failure_trigger_discharge_surface_scope_boundary.get("placeholder_template") is True
    assert isinstance(stat_failure_trigger_discharge_surface_scope_boundary_payload, dict)
    assert (
        stat_failure_trigger_discharge_surface_scope_boundary_payload.get("checkpoint")
        == "stat_failure_trigger_discharge_surface_scope_boundary_cycle01"
    )
    assert stat_failure_trigger_discharge_surface_scope_boundary_payload.get("status") == "placeholder_non_promotional"
    assert stat_failure_trigger_discharge_surface_scope_boundary_payload.get("discharge_surface_scope_boundary") == [
        "failure_trigger_discharge_surface_structure_placeholder_only",
        "failure_trigger_discharge_theorem_surface_structure_placeholder_only",
        "failure_trigger_discharge_object_surface_structure_placeholder_only",
        "no_failure_trigger_surface_discharge_claim",
        "no_label_promotion_claim",
        "no_external_truth_claim",
    ]
    assert stat_failure_trigger_discharge_surface_scope_boundary_payload.get("required_surface_inputs") == [
        "failure_trigger_audit_scope_boundary_pinned_before_surface_execution",
        "derivation_completeness_discharge_surface_scope_boundary_pinned_before_surface_execution",
        "failure_trigger_discharge_theorem_surface_scope_boundary_pinned_before_surface_execution",
        "failure_trigger_discharge_object_surface_scope_boundary_pinned_before_surface_execution",
        "evidence_adequacy_completion_token_required_before_surface_execution",
        "promotion_readiness_scope_boundary_pinned_before_surface_execution",
    ]
    assert stat_failure_trigger_discharge_surface_scope_boundary_payload.get("anti_shortcut_constraints") == [
        "no_phase_skip_promotion",
        "no_implicit_status_promotion",
        "artifact_hash_and_cross_surface_pointers_required",
    ]
    assert stat_failure_trigger_discharge_surface_scope_boundary_payload.get("discharge_row_linkage") == EXPECTED_ROW_IDS
    assert (
        stat_failure_trigger_discharge_coherence_scope_boundary.get("artifact_id")
        == EXPECTED_STAT_FAILURE_TRIGGER_DISCHARGE_COHERENCE_SCOPE_BOUNDARY_ARTIFACT_ID
    )
    assert stat_failure_trigger_discharge_coherence_scope_boundary.get("placeholder_template") is True
    assert isinstance(stat_failure_trigger_discharge_coherence_scope_boundary_payload, dict)
    assert (
        stat_failure_trigger_discharge_coherence_scope_boundary_payload.get("checkpoint")
        == "stat_failure_trigger_discharge_coherence_scope_boundary_cycle01"
    )
    assert stat_failure_trigger_discharge_coherence_scope_boundary_payload.get("status") == "placeholder_non_promotional"
    assert stat_failure_trigger_discharge_coherence_scope_boundary_payload.get("coherence_scope_boundary") == [
        "failure_trigger_discharge_surface_theorem_object_alignment_placeholder_only",
        "failure_trigger_discharge_dependency_consistency_placeholder_only",
        "no_failure_trigger_coherence_discharge_claim",
        "no_label_promotion_claim",
        "no_external_truth_claim",
    ]
    assert stat_failure_trigger_discharge_coherence_scope_boundary_payload.get("required_coherence_inputs") == [
        "failure_trigger_discharge_surface_scope_boundary_pinned_before_coherence_execution",
        "failure_trigger_discharge_theorem_surface_scope_boundary_pinned_before_coherence_execution",
        "failure_trigger_discharge_object_surface_scope_boundary_pinned_before_coherence_execution",
        "derivation_completeness_discharge_surface_scope_boundary_pinned_before_coherence_execution",
        "evidence_adequacy_completion_token_required_before_coherence_execution",
        "promotion_readiness_scope_boundary_pinned_before_coherence_execution",
    ]
    assert stat_failure_trigger_discharge_coherence_scope_boundary_payload.get("anti_shortcut_constraints") == [
        "no_phase_skip_promotion",
        "no_implicit_status_promotion",
        "artifact_hash_and_cross_surface_pointers_required",
    ]
    assert stat_failure_trigger_discharge_coherence_scope_boundary_payload.get("discharge_row_linkage") == EXPECTED_ROW_IDS
    assert (
        stat_failure_trigger_discharge_theorem_surface_scope_boundary.get("artifact_id")
        == EXPECTED_STAT_FAILURE_TRIGGER_DISCHARGE_THEOREM_SURFACE_SCOPE_BOUNDARY_ARTIFACT_ID
    )
    assert stat_failure_trigger_discharge_theorem_surface_scope_boundary.get("placeholder_template") is True
    assert isinstance(stat_failure_trigger_discharge_theorem_surface_scope_boundary_payload, dict)
    assert (
        stat_failure_trigger_discharge_theorem_surface_scope_boundary_payload.get("checkpoint")
        == "stat_failure_trigger_discharge_theorem_surface_scope_boundary_cycle01"
    )
    assert stat_failure_trigger_discharge_theorem_surface_scope_boundary_payload.get("status") == "placeholder_non_promotional"
    assert stat_failure_trigger_discharge_theorem_surface_scope_boundary_payload.get("theorem_surface_scope_boundary") == [
        "failure_trigger_discharge_theorem_surface_structure_placeholder_only",
        "failure_trigger_discharge_assumption_surface_placeholder_only",
        "no_failure_trigger_theorem_discharge_claim",
        "no_label_promotion_claim",
        "no_external_truth_claim",
    ]
    assert stat_failure_trigger_discharge_theorem_surface_scope_boundary_payload.get("required_theorem_surface_inputs") == [
        "failure_trigger_audit_scope_boundary_pinned_before_theorem_surface_execution",
        "derivation_completeness_discharge_surface_scope_boundary_pinned_before_theorem_surface_execution",
        "evidence_adequacy_completion_token_required_before_theorem_surface_execution",
        "promotion_readiness_scope_boundary_pinned_before_theorem_surface_execution",
    ]
    assert stat_failure_trigger_discharge_theorem_surface_scope_boundary_payload.get("anti_shortcut_constraints") == [
        "no_phase_skip_promotion",
        "no_implicit_status_promotion",
        "artifact_hash_and_cross_surface_pointers_required",
    ]
    assert stat_failure_trigger_discharge_theorem_surface_scope_boundary_payload.get("discharge_row_linkage") == EXPECTED_ROW_IDS
    assert (
        stat_failure_trigger_discharge_object_surface_scope_boundary.get("artifact_id")
        == EXPECTED_STAT_FAILURE_TRIGGER_DISCHARGE_OBJECT_SURFACE_SCOPE_BOUNDARY_ARTIFACT_ID
    )
    assert stat_failure_trigger_discharge_object_surface_scope_boundary.get("placeholder_template") is True
    assert isinstance(stat_failure_trigger_discharge_object_surface_scope_boundary_payload, dict)
    assert (
        stat_failure_trigger_discharge_object_surface_scope_boundary_payload.get("checkpoint")
        == "stat_failure_trigger_discharge_object_surface_scope_boundary_cycle01"
    )
    assert stat_failure_trigger_discharge_object_surface_scope_boundary_payload.get("status") == "placeholder_non_promotional"
    assert stat_failure_trigger_discharge_object_surface_scope_boundary_payload.get("object_surface_scope_boundary") == [
        "failure_trigger_discharge_object_surface_structure_placeholder_only",
        "failure_trigger_discharge_observable_surface_placeholder_only",
        "no_failure_trigger_object_discharge_claim",
        "no_label_promotion_claim",
        "no_external_truth_claim",
    ]
    assert stat_failure_trigger_discharge_object_surface_scope_boundary_payload.get("required_object_surface_inputs") == [
        "failure_trigger_audit_scope_boundary_pinned_before_object_surface_execution",
        "derivation_completeness_discharge_surface_scope_boundary_pinned_before_object_surface_execution",
        "evidence_adequacy_completion_token_required_before_object_surface_execution",
        "promotion_readiness_scope_boundary_pinned_before_object_surface_execution",
    ]
    assert stat_failure_trigger_discharge_object_surface_scope_boundary_payload.get("anti_shortcut_constraints") == [
        "no_phase_skip_promotion",
        "no_implicit_status_promotion",
        "artifact_hash_and_cross_surface_pointers_required",
    ]
    assert stat_failure_trigger_discharge_object_surface_scope_boundary_payload.get("discharge_row_linkage") == EXPECTED_ROW_IDS
    assert (
        stat_discharge_completion_transition_scope_boundary.get("artifact_id")
        == EXPECTED_STAT_DISCHARGE_COMPLETION_TRANSITION_SCOPE_BOUNDARY_ARTIFACT_ID
    )
    assert stat_discharge_completion_transition_scope_boundary.get("placeholder_template") is True
    assert isinstance(stat_discharge_completion_transition_scope_boundary_payload, dict)
    assert (
        stat_discharge_completion_transition_scope_boundary_payload.get("checkpoint")
        == "stat_discharge_completion_transition_scope_boundary_cycle01"
    )
    assert stat_discharge_completion_transition_scope_boundary_payload.get("status") == "placeholder_non_promotional"
    assert stat_discharge_completion_transition_scope_boundary_payload.get("transition_scope_boundary") == [
        "derivation_completeness_and_failure_trigger_discharge_alignment_placeholder_only",
        "discharge_scope_bundle_transition_readiness_placeholder_only",
        "no_discharge_completion_transition_claim",
        "no_label_promotion_claim",
        "no_external_truth_claim",
    ]
    assert stat_discharge_completion_transition_scope_boundary_payload.get("required_transition_inputs") == [
        "derivation_completeness_discharge_surface_scope_boundary_pinned_before_transition_execution",
        "derivation_completeness_discharge_theorem_surface_scope_boundary_pinned_before_transition_execution",
        "derivation_completeness_discharge_object_surface_scope_boundary_pinned_before_transition_execution",
        "derivation_completeness_discharge_coherence_scope_boundary_pinned_before_transition_execution",
        "failure_trigger_discharge_surface_scope_boundary_pinned_before_transition_execution",
        "failure_trigger_discharge_theorem_surface_scope_boundary_pinned_before_transition_execution",
        "failure_trigger_discharge_object_surface_scope_boundary_pinned_before_transition_execution",
        "failure_trigger_discharge_coherence_scope_boundary_pinned_before_transition_execution",
        "derivation_completeness_gate_scope_boundary_pinned_before_transition_execution",
        "failure_trigger_audit_scope_boundary_pinned_before_transition_execution",
        "evidence_adequacy_completion_token_required_before_transition_execution",
        "promotion_readiness_scope_boundary_pinned_before_transition_execution",
    ]
    assert stat_discharge_completion_transition_scope_boundary_payload.get("anti_shortcut_constraints") == [
        "no_phase_skip_promotion",
        "no_implicit_status_promotion",
        "artifact_hash_and_cross_surface_pointers_required",
    ]
    assert stat_discharge_completion_transition_scope_boundary_payload.get("discharge_row_linkage") == EXPECTED_ROW_IDS
    assert (
        stat_adjudication_transition_scope_boundary.get("artifact_id")
        == EXPECTED_STAT_ADJUDICATION_TRANSITION_SCOPE_BOUNDARY_ARTIFACT_ID
    )
    assert stat_adjudication_transition_scope_boundary.get("placeholder_template") is True
    assert isinstance(stat_adjudication_transition_scope_boundary_payload, dict)
    assert (
        stat_adjudication_transition_scope_boundary_payload.get("checkpoint")
        == "stat_adjudication_transition_scope_boundary_cycle01"
    )
    assert stat_adjudication_transition_scope_boundary_payload.get("status") == "placeholder_non_promotional"
    assert stat_adjudication_transition_scope_boundary_payload.get("adjudication_transition_scope_boundary") == [
        "discharge_completion_transition_alignment_placeholder_only",
        "adjudication_transition_preexecution_guard_placeholder_only",
        "no_discharge_adjudication_claim",
        "no_inevitability_adjudication_claim",
        "no_label_promotion_claim",
        "no_external_truth_claim",
    ]
    assert (
        stat_adjudication_transition_scope_boundary_payload.get("required_adjudication_transition_inputs") == [
            "discharge_completion_transition_scope_boundary_pinned_before_adjudication_transition_execution",
            "derivation_completeness_discharge_coherence_scope_boundary_pinned_before_adjudication_transition_execution",
            "failure_trigger_discharge_coherence_scope_boundary_pinned_before_adjudication_transition_execution",
            "derivation_completeness_gate_scope_boundary_pinned_before_adjudication_transition_execution",
            "failure_trigger_audit_scope_boundary_pinned_before_adjudication_transition_execution",
            "evidence_adequacy_completion_token_required_before_adjudication_transition_execution",
            "promotion_readiness_scope_boundary_pinned_before_adjudication_transition_execution",
        ]
    )
    assert stat_adjudication_transition_scope_boundary_payload.get("anti_shortcut_constraints") == [
        "no_phase_skip_promotion",
        "no_implicit_status_promotion",
        "artifact_hash_and_cross_surface_pointers_required",
    ]
    assert stat_adjudication_transition_scope_boundary_payload.get("discharge_row_linkage") == EXPECTED_ROW_IDS
    assert (
        stat_inevitability_transition_scope_boundary.get("artifact_id")
        == EXPECTED_STAT_INEVITABILITY_TRANSITION_SCOPE_BOUNDARY_ARTIFACT_ID
    )
    assert stat_inevitability_transition_scope_boundary.get("placeholder_template") is True
    assert isinstance(stat_inevitability_transition_scope_boundary_payload, dict)
    assert (
        stat_inevitability_transition_scope_boundary_payload.get("checkpoint")
        == "stat_inevitability_transition_scope_boundary_cycle01"
    )
    assert stat_inevitability_transition_scope_boundary_payload.get("status") == "placeholder_non_promotional"
    assert stat_inevitability_transition_scope_boundary_payload.get("inevitability_transition_scope_boundary") == [
        "adjudication_transition_dependency_placeholder_only",
        "inevitability_transition_preexecution_guard_placeholder_only",
        "no_inevitability_adjudication_claim",
        "no_discharge_adjudication_claim",
        "no_label_promotion_claim",
        "no_external_truth_claim",
    ]
    assert (
        stat_inevitability_transition_scope_boundary_payload.get("required_inevitability_transition_inputs") == [
            "adjudication_transition_scope_boundary_pinned_before_inevitability_transition_execution",
            "discharge_completion_transition_scope_boundary_pinned_before_inevitability_transition_execution",
            "derivation_completeness_discharge_coherence_scope_boundary_pinned_before_inevitability_transition_execution",
            "failure_trigger_discharge_coherence_scope_boundary_pinned_before_inevitability_transition_execution",
            "derivation_completeness_gate_scope_boundary_pinned_before_inevitability_transition_execution",
            "failure_trigger_audit_scope_boundary_pinned_before_inevitability_transition_execution",
            "evidence_adequacy_completion_token_required_before_inevitability_transition_execution",
            "promotion_readiness_scope_boundary_pinned_before_inevitability_transition_execution",
        ]
    )
    assert stat_inevitability_transition_scope_boundary_payload.get("anti_shortcut_constraints") == [
        "no_phase_skip_promotion",
        "no_implicit_status_promotion",
        "artifact_hash_and_cross_surface_pointers_required",
    ]
    assert stat_inevitability_transition_scope_boundary_payload.get("discharge_row_linkage") == EXPECTED_ROW_IDS
    assert (
        stat_nonflip_execution_boundary_scope_boundary.get("artifact_id")
        == EXPECTED_STAT_NONFLIP_EXECUTION_BOUNDARY_SCOPE_BOUNDARY_ARTIFACT_ID
    )
    assert stat_nonflip_execution_boundary_scope_boundary.get("placeholder_template") is True
    assert isinstance(stat_nonflip_execution_boundary_scope_boundary_payload, dict)
    assert (
        stat_nonflip_execution_boundary_scope_boundary_payload.get("checkpoint")
        == "stat_nonflip_execution_boundary_scope_boundary_cycle01"
    )
    assert stat_nonflip_execution_boundary_scope_boundary_payload.get("status") == "placeholder_non_promotional"
    assert stat_nonflip_execution_boundary_scope_boundary_payload.get("nonflip_execution_boundary") == [
        "adjudication_and_inevitability_transition_alignment_placeholder_only",
        "nonflip_execution_custody_placeholder_only",
        "no_discharge_adjudication_flip",
        "no_inevitability_adjudication_flip",
        "no_label_promotion_claim",
        "no_external_truth_claim",
    ]
    assert stat_nonflip_execution_boundary_scope_boundary_payload.get("required_nonflip_inputs") == [
        "adjudication_transition_scope_boundary_pinned_before_nonflip_execution",
        "inevitability_transition_scope_boundary_pinned_before_nonflip_execution",
        "discharge_completion_transition_scope_boundary_pinned_before_nonflip_execution",
        "derivation_completeness_discharge_coherence_scope_boundary_pinned_before_nonflip_execution",
        "failure_trigger_discharge_coherence_scope_boundary_pinned_before_nonflip_execution",
        "evidence_adequacy_completion_token_required_before_nonflip_execution",
        "promotion_readiness_scope_boundary_pinned_before_nonflip_execution",
    ]
    assert stat_nonflip_execution_boundary_scope_boundary_payload.get("anti_shortcut_constraints") == [
        "no_phase_skip_promotion",
        "no_implicit_status_promotion",
        "artifact_hash_and_cross_surface_pointers_required",
    ]
    assert stat_nonflip_execution_boundary_scope_boundary_payload.get("discharge_row_linkage") == EXPECTED_ROW_IDS
    assert (
        stat_nonflip_execution_custody_scope_boundary.get("artifact_id")
        == EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_SCOPE_BOUNDARY_ARTIFACT_ID
    )
    assert stat_nonflip_execution_custody_scope_boundary.get("placeholder_template") is True
    assert isinstance(stat_nonflip_execution_custody_scope_boundary_payload, dict)
    assert (
        stat_nonflip_execution_custody_scope_boundary_payload.get("checkpoint")
        == "stat_nonflip_execution_custody_scope_boundary_cycle01"
    )
    assert stat_nonflip_execution_custody_scope_boundary_payload.get("status") == "placeholder_non_promotional"
    assert stat_nonflip_execution_custody_scope_boundary_payload.get("nonflip_execution_custody") == [
        "nonflip_execution_boundary_dependency_placeholder_only",
        "custody_chain_and_replay_guard_placeholder_only",
        "no_execution_replay_flip",
        "no_discharge_adjudication_flip",
        "no_inevitability_adjudication_flip",
        "no_label_promotion_claim",
        "no_external_truth_claim",
    ]
    assert stat_nonflip_execution_custody_scope_boundary_payload.get("required_nonflip_custody_inputs") == [
        "nonflip_execution_boundary_scope_boundary_pinned_before_nonflip_execution_custody",
        "adjudication_transition_scope_boundary_pinned_before_nonflip_execution_custody",
        "inevitability_transition_scope_boundary_pinned_before_nonflip_execution_custody",
        "discharge_completion_transition_scope_boundary_pinned_before_nonflip_execution_custody",
        "derivation_completeness_discharge_coherence_scope_boundary_pinned_before_nonflip_execution_custody",
        "failure_trigger_discharge_coherence_scope_boundary_pinned_before_nonflip_execution_custody",
        "evidence_adequacy_completion_token_required_before_nonflip_execution_custody",
        "promotion_readiness_scope_boundary_pinned_before_nonflip_execution_custody",
    ]
    assert stat_nonflip_execution_custody_scope_boundary_payload.get("anti_shortcut_constraints") == [
        "no_phase_skip_promotion",
        "no_implicit_status_promotion",
        "artifact_hash_and_cross_surface_pointers_required",
    ]
    assert stat_nonflip_execution_custody_scope_boundary_payload.get("discharge_row_linkage") == EXPECTED_ROW_IDS
    assert (
        stat_nonflip_execution_custody_attestation_scope_boundary.get("artifact_id")
        == EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_SCOPE_BOUNDARY_ARTIFACT_ID
    )
    assert stat_nonflip_execution_custody_attestation_scope_boundary.get("placeholder_template") is True
    assert isinstance(stat_nonflip_execution_custody_attestation_scope_boundary_payload, dict)
    assert (
        stat_nonflip_execution_custody_attestation_scope_boundary_payload.get("checkpoint")
        == "stat_nonflip_execution_custody_attestation_scope_boundary_cycle01"
    )
    assert stat_nonflip_execution_custody_attestation_scope_boundary_payload.get("status") == "placeholder_non_promotional"
    assert stat_nonflip_execution_custody_attestation_scope_boundary_payload.get("nonflip_execution_custody_attestation") == [
        "nonflip_execution_custody_dependency_placeholder_only",
        "attestation_chain_continuity_placeholder_only",
        "attestation_replay_and_fork_guard_placeholder_only",
        "no_execution_replay_flip",
        "no_discharge_adjudication_flip",
        "no_inevitability_adjudication_flip",
        "no_label_promotion_claim",
        "no_external_truth_claim",
    ]
    assert (
        stat_nonflip_execution_custody_attestation_scope_boundary_payload.get(
            "required_nonflip_custody_attestation_inputs"
        )
        == [
            "nonflip_execution_custody_scope_boundary_pinned_before_nonflip_execution_custody_attestation",
            "nonflip_execution_boundary_scope_boundary_pinned_before_nonflip_execution_custody_attestation",
            "adjudication_transition_scope_boundary_pinned_before_nonflip_execution_custody_attestation",
            "inevitability_transition_scope_boundary_pinned_before_nonflip_execution_custody_attestation",
            "discharge_completion_transition_scope_boundary_pinned_before_nonflip_execution_custody_attestation",
            "derivation_completeness_discharge_coherence_scope_boundary_pinned_before_nonflip_execution_custody_attestation",
            "failure_trigger_discharge_coherence_scope_boundary_pinned_before_nonflip_execution_custody_attestation",
            "evidence_adequacy_completion_token_required_before_nonflip_execution_custody_attestation",
            "promotion_readiness_scope_boundary_pinned_before_nonflip_execution_custody_attestation",
        ]
    )
    assert stat_nonflip_execution_custody_attestation_scope_boundary_payload.get("anti_shortcut_constraints") == [
        "no_phase_skip_promotion",
        "no_implicit_status_promotion",
        "artifact_hash_and_cross_surface_pointers_required",
    ]
    assert stat_nonflip_execution_custody_attestation_scope_boundary_payload.get("discharge_row_linkage") == (
        EXPECTED_ROW_IDS
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_scope_boundary.get("artifact_id")
        == EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_SCOPE_BOUNDARY_ARTIFACT_ID
    )
    assert stat_nonflip_execution_custody_attestation_confirmation_scope_boundary.get("placeholder_template") is True
    assert isinstance(stat_nonflip_execution_custody_attestation_confirmation_scope_boundary_payload, dict)
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_scope_boundary_payload.get("checkpoint")
        == "stat_nonflip_execution_custody_attestation_confirmation_scope_boundary_cycle01"
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_scope_boundary_payload.get("status")
        == "placeholder_non_promotional"
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_scope_boundary_payload.get(
            "nonflip_execution_custody_attestation_confirmation"
        )
        == [
            "nonflip_execution_custody_attestation_dependency_placeholder_only",
            "attestation_confirmation_chain_continuity_placeholder_only",
            "attestation_confirmation_replay_and_fork_guard_placeholder_only",
            "no_execution_replay_flip",
            "no_discharge_adjudication_flip",
            "no_inevitability_adjudication_flip",
            "no_label_promotion_claim",
            "no_external_truth_claim",
        ]
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_scope_boundary_payload.get(
            "required_nonflip_custody_attestation_confirmation_inputs"
        )
        == [
            "nonflip_execution_custody_attestation_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation",
            "nonflip_execution_custody_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation",
            "nonflip_execution_boundary_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation",
            "adjudication_transition_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation",
            "inevitability_transition_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation",
            "discharge_completion_transition_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation",
            "derivation_completeness_discharge_coherence_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation",
            "failure_trigger_discharge_coherence_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation",
            "evidence_adequacy_completion_token_required_before_nonflip_execution_custody_attestation_confirmation",
            "promotion_readiness_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation",
        ]
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_scope_boundary_payload.get(
            "anti_shortcut_constraints"
        )
        == [
            "no_phase_skip_promotion",
            "no_implicit_status_promotion",
            "artifact_hash_and_cross_surface_pointers_required",
        ]
    )
    assert stat_nonflip_execution_custody_attestation_confirmation_scope_boundary_payload.get(
        "discharge_row_linkage"
    ) == EXPECTED_ROW_IDS
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_scope_boundary.get("artifact_id")
        == EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_SCOPE_BOUNDARY_ARTIFACT_ID
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_scope_boundary.get(
            "placeholder_template"
        )
        is True
    )
    assert isinstance(
        stat_nonflip_execution_custody_attestation_confirmation_attestation_scope_boundary_payload, dict
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_scope_boundary_payload.get(
            "checkpoint"
        )
        == "stat_nonflip_execution_custody_attestation_confirmation_attestation_scope_boundary_cycle01"
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_scope_boundary_payload.get(
            "status"
        )
        == "placeholder_non_promotional"
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_scope_boundary_payload.get(
            "nonflip_execution_custody_attestation_confirmation_attestation"
        )
        == [
            "nonflip_execution_custody_attestation_confirmation_dependency_placeholder_only",
            "attestation_confirmation_attestation_chain_continuity_placeholder_only",
            "attestation_confirmation_attestation_replay_and_fork_guard_placeholder_only",
            "no_execution_replay_flip",
            "no_discharge_adjudication_flip",
            "no_inevitability_adjudication_flip",
            "no_label_promotion_claim",
            "no_external_truth_claim",
        ]
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_scope_boundary_payload.get(
            "required_nonflip_custody_attestation_confirmation_attestation_inputs"
        )
        == [
            "nonflip_execution_custody_attestation_confirmation_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation",
            "nonflip_execution_custody_attestation_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation",
            "nonflip_execution_custody_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation",
            "nonflip_execution_boundary_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation",
            "adjudication_transition_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation",
            "inevitability_transition_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation",
            "discharge_completion_transition_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation",
            "derivation_completeness_discharge_coherence_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation",
            "failure_trigger_discharge_coherence_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation",
            "evidence_adequacy_completion_token_required_before_nonflip_execution_custody_attestation_confirmation_attestation",
            "promotion_readiness_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation",
        ]
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_scope_boundary_payload.get(
            "anti_shortcut_constraints"
        )
        == [
            "no_phase_skip_promotion",
            "no_implicit_status_promotion",
            "artifact_hash_and_cross_surface_pointers_required",
        ]
    )
    assert stat_nonflip_execution_custody_attestation_confirmation_attestation_scope_boundary_payload.get(
        "discharge_row_linkage"
    ) == EXPECTED_ROW_IDS
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_scope_boundary.get(
            "artifact_id"
        )
        == EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_SCOPE_BOUNDARY_ARTIFACT_ID
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_scope_boundary.get(
            "placeholder_template"
        )
        is True
    )
    assert isinstance(
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_scope_boundary_payload, dict
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_scope_boundary_payload.get(
            "checkpoint"
        )
        == "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_scope_boundary_cycle01"
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_scope_boundary_payload.get(
            "status"
        )
        == "placeholder_non_promotional"
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_scope_boundary_payload.get(
            "nonflip_execution_custody_attestation_confirmation_attestation_confirmation"
        )
        == [
            "nonflip_execution_custody_attestation_confirmation_attestation_dependency_placeholder_only",
            "attestation_confirmation_attestation_confirmation_chain_continuity_placeholder_only",
            "attestation_confirmation_attestation_confirmation_replay_and_fork_guard_placeholder_only",
            "no_execution_replay_flip",
            "no_discharge_adjudication_flip",
            "no_inevitability_adjudication_flip",
            "no_label_promotion_claim",
            "no_external_truth_claim",
        ]
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_scope_boundary_payload.get(
            "required_nonflip_custody_attestation_confirmation_attestation_confirmation_inputs"
        )
        == [
            "nonflip_execution_custody_attestation_confirmation_attestation_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation",
            "nonflip_execution_custody_attestation_confirmation_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation",
            "nonflip_execution_custody_attestation_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation",
            "nonflip_execution_custody_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation",
            "nonflip_execution_boundary_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation",
            "adjudication_transition_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation",
            "inevitability_transition_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation",
            "discharge_completion_transition_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation",
            "derivation_completeness_discharge_coherence_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation",
            "failure_trigger_discharge_coherence_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation",
            "evidence_adequacy_completion_token_required_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation",
            "promotion_readiness_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation",
        ]
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_scope_boundary_payload.get(
            "anti_shortcut_constraints"
        )
        == [
            "no_phase_skip_promotion",
            "no_implicit_status_promotion",
            "artifact_hash_and_cross_surface_pointers_required",
        ]
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_scope_boundary_payload.get(
            "discharge_row_linkage"
        )
        == EXPECTED_ROW_IDS
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_scope_boundary.get(
            "artifact_id"
        )
        == EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_SCOPE_BOUNDARY_ARTIFACT_ID
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_scope_boundary.get(
            "placeholder_template"
        )
        is True
    )
    assert isinstance(
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_payload,
        dict,
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_payload.get(
            "checkpoint"
        )
        == "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_cycle01"
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_payload.get(
            "status"
        )
        == "placeholder_non_promotional"
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_payload.get(
            "nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation"
        )
        == [
            "nonflip_execution_custody_attestation_confirmation_attestation_confirmation_dependency_placeholder_only",
            "attestation_confirmation_attestation_confirmation_attestation_chain_continuity_placeholder_only",
            "attestation_confirmation_attestation_confirmation_attestation_replay_and_fork_guard_placeholder_only",
            "no_execution_replay_flip",
            "no_discharge_adjudication_flip",
            "no_inevitability_adjudication_flip",
            "no_label_promotion_claim",
            "no_external_truth_claim",
        ]
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_payload.get(
            "required_nonflip_custody_attestation_confirmation_attestation_confirmation_attestation_inputs"
        )
        == [
            "nonflip_execution_custody_attestation_confirmation_attestation_confirmation_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation",
            "nonflip_execution_custody_attestation_confirmation_attestation_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation",
            "nonflip_execution_custody_attestation_confirmation_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation",
            "nonflip_execution_custody_attestation_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation",
            "nonflip_execution_custody_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation",
            "nonflip_execution_boundary_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation",
            "adjudication_transition_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation",
            "inevitability_transition_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation",
            "discharge_completion_transition_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation",
            "derivation_completeness_discharge_coherence_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation",
            "failure_trigger_discharge_coherence_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation",
            "evidence_adequacy_completion_token_required_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation",
            "promotion_readiness_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation",
        ]
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_payload.get(
            "anti_shortcut_constraints"
        )
        == [
            "no_phase_skip_promotion",
            "no_implicit_status_promotion",
            "artifact_hash_and_cross_surface_pointers_required",
        ]
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_payload.get(
            "discharge_row_linkage"
        )
        == EXPECTED_ROW_IDS
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary.get(
            "artifact_id"
        )
        == EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_SCOPE_BOUNDARY_ARTIFACT_ID
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary.get(
            "placeholder_template"
        )
        is True
    )
    assert isinstance(
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_payload,
        dict,
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_payload.get(
            "checkpoint"
        )
        == "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_cycle01"
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_payload.get(
            "status"
        )
        == "placeholder_non_promotional"
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_payload.get(
            "nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation"
        )
        == [
            "nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_dependency_placeholder_only",
            "attestation_confirmation_attestation_confirmation_attestation_confirmation_chain_continuity_placeholder_only",
            "attestation_confirmation_attestation_confirmation_attestation_confirmation_replay_and_fork_guard_placeholder_only",
            "no_execution_replay_flip",
            "no_discharge_adjudication_flip",
            "no_inevitability_adjudication_flip",
            "no_label_promotion_claim",
            "no_external_truth_claim",
        ]
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_payload.get(
            "required_nonflip_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_inputs"
        )
        == [
            "nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation",
            "nonflip_execution_custody_attestation_confirmation_attestation_confirmation_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation",
            "nonflip_execution_custody_attestation_confirmation_attestation_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation",
            "nonflip_execution_custody_attestation_confirmation_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation",
            "nonflip_execution_custody_attestation_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation",
            "nonflip_execution_custody_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation",
            "nonflip_execution_boundary_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation",
            "adjudication_transition_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation",
            "inevitability_transition_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation",
            "discharge_completion_transition_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation",
            "derivation_completeness_discharge_coherence_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation",
            "failure_trigger_discharge_coherence_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation",
            "evidence_adequacy_completion_token_required_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation",
            "promotion_readiness_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation",
        ]
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_payload.get(
            "anti_shortcut_constraints"
        )
        == [
            "no_phase_skip_promotion",
            "no_implicit_status_promotion",
            "artifact_hash_and_cross_surface_pointers_required",
        ]
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_payload.get(
            "discharge_row_linkage"
        )
        == EXPECTED_ROW_IDS
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary.get(
            "artifact_id"
        )
        == EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_SCOPE_BOUNDARY_ARTIFACT_ID
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary.get(
            "placeholder_template"
        )
        is True
    )
    assert isinstance(
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_payload,
        dict,
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_payload.get(
            "checkpoint"
        )
        == "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_cycle01"
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_payload.get(
            "status"
        )
        == "placeholder_non_promotional"
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_payload.get(
            "nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation"
        )
        == [
            "nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_dependency_placeholder_only",
            "attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_chain_continuity_placeholder_only",
            "attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_replay_and_fork_guard_placeholder_only",
            "no_execution_replay_flip",
            "no_discharge_adjudication_flip",
            "no_inevitability_adjudication_flip",
            "no_label_promotion_claim",
            "no_external_truth_claim",
        ]
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_payload.get(
            "required_nonflip_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_inputs"
        )
        == [
            "nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation",
            "nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation",
            "nonflip_execution_custody_attestation_confirmation_attestation_confirmation_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation",
            "nonflip_execution_custody_attestation_confirmation_attestation_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation",
            "nonflip_execution_custody_attestation_confirmation_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation",
            "nonflip_execution_custody_attestation_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation",
            "nonflip_execution_custody_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation",
            "nonflip_execution_boundary_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation",
            "adjudication_transition_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation",
            "inevitability_transition_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation",
            "discharge_completion_transition_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation",
            "derivation_completeness_discharge_coherence_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation",
            "failure_trigger_discharge_coherence_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation",
            "evidence_adequacy_completion_token_required_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation",
            "promotion_readiness_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation",
        ]
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_payload.get(
            "anti_shortcut_constraints"
        )
        == [
            "no_phase_skip_promotion",
            "no_implicit_status_promotion",
            "artifact_hash_and_cross_surface_pointers_required",
        ]
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_payload.get(
            "discharge_row_linkage"
        )
        == EXPECTED_ROW_IDS
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary.get(
            "artifact_id"
        )
        == EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_SCOPE_BOUNDARY_ARTIFACT_ID
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary.get(
            "placeholder_template"
        )
        is True
    )
    assert isinstance(
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_payload,
        dict,
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_payload.get(
            "checkpoint"
        )
        == "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_cycle01"
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_payload.get(
            "status"
        )
        == "placeholder_non_promotional"
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_payload.get(
            "nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation"
        )
        == [
            "nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_dependency_placeholder_only",
            "attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_chain_continuity_placeholder_only",
            "attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_replay_and_fork_guard_placeholder_only",
            "no_execution_replay_flip",
            "no_discharge_adjudication_flip",
            "no_inevitability_adjudication_flip",
            "no_label_promotion_claim",
            "no_external_truth_claim",
        ]
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_payload.get(
            "required_nonflip_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_inputs"
        )
        == [
            "nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation",
            "nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation",
            "nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation",
            "nonflip_execution_custody_attestation_confirmation_attestation_confirmation_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation",
            "nonflip_execution_custody_attestation_confirmation_attestation_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation",
            "nonflip_execution_custody_attestation_confirmation_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation",
            "nonflip_execution_custody_attestation_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation",
            "nonflip_execution_custody_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation",
            "nonflip_execution_boundary_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation",
            "adjudication_transition_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation",
            "inevitability_transition_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation",
            "discharge_completion_transition_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation",
            "derivation_completeness_discharge_coherence_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation",
            "failure_trigger_discharge_coherence_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation",
            "evidence_adequacy_completion_token_required_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation",
            "promotion_readiness_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation",
        ]
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_payload.get(
            "anti_shortcut_constraints"
        )
        == [
            "no_phase_skip_promotion",
            "no_implicit_status_promotion",
            "artifact_hash_and_cross_surface_pointers_required",
        ]
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_payload.get(
            "discharge_row_linkage"
        )
        == EXPECTED_ROW_IDS
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary.get(
            "artifact_id"
        )
        == EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_SCOPE_BOUNDARY_ARTIFACT_ID
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary.get(
            "placeholder_template"
        )
        is True
    )
    assert isinstance(
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_payload,
        dict,
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_payload.get(
            "checkpoint"
        )
        == "stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_cycle01"
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_payload.get(
            "status"
        )
        == "placeholder_non_promotional"
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_payload.get(
            "nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation"
        )
        == [
            "nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_dependency_placeholder_only",
            "attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_chain_continuity_placeholder_only",
            "attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_replay_and_fork_guard_placeholder_only",
            "no_execution_replay_flip",
            "no_discharge_adjudication_flip",
            "no_inevitability_adjudication_flip",
            "no_label_promotion_claim",
            "no_external_truth_claim",
        ]
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_payload.get(
            "required_nonflip_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_inputs"
        )
        == [
            "nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation",
            "nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation",
            "nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation",
            "nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation",
            "nonflip_execution_custody_attestation_confirmation_attestation_confirmation_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation",
            "nonflip_execution_custody_attestation_confirmation_attestation_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation",
            "nonflip_execution_custody_attestation_confirmation_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation",
            "nonflip_execution_custody_attestation_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation",
            "nonflip_execution_custody_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation",
            "nonflip_execution_boundary_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation",
            "adjudication_transition_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation",
            "inevitability_transition_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation",
            "discharge_completion_transition_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation",
            "derivation_completeness_discharge_coherence_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation",
            "failure_trigger_discharge_coherence_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation",
            "evidence_adequacy_completion_token_required_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation",
            "promotion_readiness_scope_boundary_pinned_before_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation",
        ]
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_payload.get(
            "anti_shortcut_constraints"
        )
        == [
            "no_phase_skip_promotion",
            "no_implicit_status_promotion",
            "artifact_hash_and_cross_surface_pointers_required",
        ]
    )
    assert (
        stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_payload.get(
            "discharge_row_linkage"
        )
        == EXPECTED_ROW_IDS
    )

    assert der01_theorem_body_payload.get("sibling_theorem_surface_scaffold_dependency_artifact_id") == EXPECTED_DER01_ARTIFACT_ID
    assert der01_theorem_body_payload.get("sibling_theorem_surface_scaffold_dependency_artifact_path") == (
        "formal/output/stat_der01_entropy_balance_theorem_surface_scaffold_cycle01_v0.json"
    )
    assert der01_theorem_body_payload.get("sibling_theorem_surface_scaffold_dependency_gate") == EXPECTED_DER01_GATE_REL
    assert der01_theorem_body_payload.get("sibling_object_surface_scaffold_dependency_artifact_id") == (
        EXPECTED_DER01_OBJECT_ARTIFACT_ID
    )
    assert der01_theorem_body_payload.get("sibling_object_surface_scaffold_dependency_artifact_path") == (
        "formal/output/stat_der01_entropy_balance_object_surface_scaffold_cycle01_v0.json"
    )
    assert der01_theorem_body_payload.get("sibling_object_surface_scaffold_dependency_gate") == EXPECTED_DER01_OBJECT_GATE_REL
    assert der01_theorem_body_payload.get("theorem_body_scope_boundary_artifact_id") == (
        EXPECTED_DER01_THEOREM_BODY_SCOPE_BOUNDARY_ARTIFACT_ID
    )
    assert der01_theorem_body_payload.get("theorem_body_scope_boundary_artifact_path") == (
        "formal/output/stat_der01_theorem_body_scope_boundary_cycle01_v0.json"
    )
    assert der01_theorem_body_payload.get("theorem_body_scope_boundary_gate") == (
        EXPECTED_DER01_THEOREM_BODY_SCOPE_BOUNDARY_GATE_REL
    )

    assert der01_discharge_payload.get("sibling_theorem_body_scaffold_dependency_artifact_id") == (
        EXPECTED_DER01_THEOREM_BODY_ARTIFACT_ID
    )
    assert der01_discharge_payload.get("sibling_theorem_body_scaffold_dependency_artifact_path") == (
        "formal/output/stat_der01_entropy_balance_theorem_body_scaffold_cycle01_v0.json"
    )
    assert der01_discharge_payload.get("sibling_theorem_body_scaffold_dependency_gate") == (
        EXPECTED_DER01_THEOREM_BODY_GATE_REL
    )
    assert der01_discharge_payload.get("sibling_theorem_surface_scaffold_dependency_artifact_id") == (
        EXPECTED_DER01_ARTIFACT_ID
    )
    assert der01_discharge_payload.get("sibling_theorem_surface_scaffold_dependency_artifact_path") == (
        "formal/output/stat_der01_entropy_balance_theorem_surface_scaffold_cycle01_v0.json"
    )
    assert der01_discharge_payload.get("sibling_theorem_surface_scaffold_dependency_gate") == EXPECTED_DER01_GATE_REL
    assert der01_discharge_payload.get("sibling_object_surface_scaffold_dependency_artifact_id") == (
        EXPECTED_DER01_OBJECT_ARTIFACT_ID
    )
    assert der01_discharge_payload.get("sibling_object_surface_scaffold_dependency_artifact_path") == (
        "formal/output/stat_der01_entropy_balance_object_surface_scaffold_cycle01_v0.json"
    )
    assert der01_discharge_payload.get("sibling_object_surface_scaffold_dependency_gate") == EXPECTED_DER01_OBJECT_GATE_REL
    assert der01_discharge_payload.get("theorem_body_scope_boundary_artifact_id") == (
        EXPECTED_DER01_THEOREM_BODY_SCOPE_BOUNDARY_ARTIFACT_ID
    )
    assert der01_discharge_payload.get("theorem_body_scope_boundary_artifact_path") == (
        "formal/output/stat_der01_theorem_body_scope_boundary_cycle01_v0.json"
    )
    assert der01_discharge_payload.get("theorem_body_scope_boundary_gate") == (
        EXPECTED_DER01_THEOREM_BODY_SCOPE_BOUNDARY_GATE_REL
    )

    assert der01_object_payload.get("sibling_theorem_surface_scaffold_dependency_artifact_id") == EXPECTED_DER01_ARTIFACT_ID
    assert der01_object_payload.get("sibling_theorem_surface_scaffold_dependency_artifact_path") == (
        "formal/output/stat_der01_entropy_balance_theorem_surface_scaffold_cycle01_v0.json"
    )
    assert der01_object_payload.get("sibling_theorem_surface_scaffold_dependency_gate") == EXPECTED_DER01_GATE_REL

    assert der02_payload.get("sibling_row_scaffold_dependency_artifact_id") == EXPECTED_DER01_ARTIFACT_ID
    assert der02_payload.get("sibling_row_scaffold_dependency_artifact_path") == (
        "formal/output/stat_der01_entropy_balance_theorem_surface_scaffold_cycle01_v0.json"
    )
    assert der02_payload.get("sibling_row_scaffold_dependency_gate") == EXPECTED_DER01_GATE_REL
    assert der02_payload.get("sibling_der01_discharge_scaffold_dependency_artifact_id") == (
        EXPECTED_DER01_DISCHARGE_ARTIFACT_ID
    )
    assert der02_payload.get("sibling_der01_discharge_scaffold_dependency_artifact_path") == (
        "formal/output/stat_der01_entropy_balance_discharge_scaffold_cycle01_v0.json"
    )
    assert der02_payload.get("sibling_der01_discharge_scaffold_dependency_gate") == (
        EXPECTED_DER01_DISCHARGE_GATE_REL
    )
    assert der02_payload.get("sibling_der01_theorem_body_scope_boundary_dependency_artifact_id") == (
        EXPECTED_DER01_THEOREM_BODY_SCOPE_BOUNDARY_ARTIFACT_ID
    )
    assert der02_payload.get("sibling_der01_theorem_body_scope_boundary_dependency_artifact_path") == (
        "formal/output/stat_der01_theorem_body_scope_boundary_cycle01_v0.json"
    )
    assert der02_payload.get("sibling_der01_theorem_body_scope_boundary_dependency_gate") == (
        EXPECTED_DER01_THEOREM_BODY_SCOPE_BOUNDARY_GATE_REL
    )
    assert der02_payload.get("sibling_der02_theorem_body_scope_boundary_dependency_artifact_id") == (
        EXPECTED_DER02_THEOREM_BODY_SCOPE_BOUNDARY_ARTIFACT_ID
    )
    assert der02_payload.get("sibling_der02_theorem_body_scope_boundary_dependency_artifact_path") == (
        "formal/output/stat_der02_theorem_body_scope_boundary_cycle01_v0.json"
    )
    assert der02_payload.get("sibling_der02_theorem_body_scope_boundary_dependency_gate") == (
        EXPECTED_DER02_THEOREM_BODY_SCOPE_BOUNDARY_GATE_REL
    )
    assert der02_theorem_body_payload.get("sibling_der02_regime_closure_scaffold_dependency_artifact_id") == (
        EXPECTED_DER02_ARTIFACT_ID
    )
    assert der02_theorem_body_payload.get("sibling_der02_regime_closure_scaffold_dependency_artifact_path") == (
        "formal/output/stat_der02_regime_closure_coupling_scaffold_cycle01_v0.json"
    )
    assert der02_theorem_body_payload.get("sibling_der02_regime_closure_scaffold_dependency_gate") == (
        EXPECTED_DER02_GATE_REL
    )
    assert der02_theorem_body_payload.get("sibling_der01_discharge_scaffold_dependency_artifact_id") == (
        EXPECTED_DER01_DISCHARGE_ARTIFACT_ID
    )
    assert der02_theorem_body_payload.get("sibling_der01_discharge_scaffold_dependency_artifact_path") == (
        "formal/output/stat_der01_entropy_balance_discharge_scaffold_cycle01_v0.json"
    )
    assert der02_theorem_body_payload.get("sibling_der01_discharge_scaffold_dependency_gate") == (
        EXPECTED_DER01_DISCHARGE_GATE_REL
    )
    assert der02_theorem_body_payload.get("sibling_der01_theorem_body_scope_boundary_dependency_artifact_id") == (
        EXPECTED_DER01_THEOREM_BODY_SCOPE_BOUNDARY_ARTIFACT_ID
    )
    assert der02_theorem_body_payload.get("sibling_der01_theorem_body_scope_boundary_dependency_artifact_path") == (
        "formal/output/stat_der01_theorem_body_scope_boundary_cycle01_v0.json"
    )
    assert der02_theorem_body_payload.get("sibling_der01_theorem_body_scope_boundary_dependency_gate") == (
        EXPECTED_DER01_THEOREM_BODY_SCOPE_BOUNDARY_GATE_REL
    )
    assert der02_theorem_body_payload.get("theorem_body_scope_boundary_artifact_id") == (
        EXPECTED_DER02_THEOREM_BODY_SCOPE_BOUNDARY_ARTIFACT_ID
    )
    assert der02_theorem_body_payload.get("theorem_body_scope_boundary_artifact_path") == (
        "formal/output/stat_der02_theorem_body_scope_boundary_cycle01_v0.json"
    )
    assert der02_theorem_body_payload.get("theorem_body_scope_boundary_gate") == (
        EXPECTED_DER02_THEOREM_BODY_SCOPE_BOUNDARY_GATE_REL
    )
    assert der02_discharge_payload.get("sibling_der02_theorem_body_scaffold_dependency_artifact_id") == (
        EXPECTED_DER02_THEOREM_BODY_ARTIFACT_ID
    )
    assert der02_discharge_payload.get("sibling_der02_theorem_body_scaffold_dependency_artifact_path") == (
        "formal/output/stat_der02_regime_closure_theorem_body_scaffold_cycle01_v0.json"
    )
    assert der02_discharge_payload.get("sibling_der02_theorem_body_scaffold_dependency_gate") == (
        EXPECTED_DER02_THEOREM_BODY_GATE_REL
    )
    assert der02_discharge_payload.get("sibling_der02_regime_closure_scaffold_dependency_artifact_id") == (
        EXPECTED_DER02_ARTIFACT_ID
    )
    assert der02_discharge_payload.get("sibling_der02_regime_closure_scaffold_dependency_artifact_path") == (
        "formal/output/stat_der02_regime_closure_coupling_scaffold_cycle01_v0.json"
    )
    assert der02_discharge_payload.get("sibling_der02_regime_closure_scaffold_dependency_gate") == (
        EXPECTED_DER02_GATE_REL
    )
    assert der02_discharge_payload.get("sibling_der01_discharge_scaffold_dependency_artifact_id") == (
        EXPECTED_DER01_DISCHARGE_ARTIFACT_ID
    )
    assert der02_discharge_payload.get("sibling_der01_discharge_scaffold_dependency_artifact_path") == (
        "formal/output/stat_der01_entropy_balance_discharge_scaffold_cycle01_v0.json"
    )
    assert der02_discharge_payload.get("sibling_der01_discharge_scaffold_dependency_gate") == (
        EXPECTED_DER01_DISCHARGE_GATE_REL
    )
    assert der02_discharge_payload.get("sibling_der01_theorem_body_scope_boundary_dependency_artifact_id") == (
        EXPECTED_DER01_THEOREM_BODY_SCOPE_BOUNDARY_ARTIFACT_ID
    )
    assert der02_discharge_payload.get("sibling_der01_theorem_body_scope_boundary_dependency_artifact_path") == (
        "formal/output/stat_der01_theorem_body_scope_boundary_cycle01_v0.json"
    )
    assert der02_discharge_payload.get("sibling_der01_theorem_body_scope_boundary_dependency_gate") == (
        EXPECTED_DER01_THEOREM_BODY_SCOPE_BOUNDARY_GATE_REL
    )
    assert der02_discharge_payload.get("theorem_body_scope_boundary_artifact_id") == (
        EXPECTED_DER02_THEOREM_BODY_SCOPE_BOUNDARY_ARTIFACT_ID
    )
    assert der02_discharge_payload.get("theorem_body_scope_boundary_artifact_path") == (
        "formal/output/stat_der02_theorem_body_scope_boundary_cycle01_v0.json"
    )
    assert der02_discharge_payload.get("theorem_body_scope_boundary_gate") == (
        EXPECTED_DER02_THEOREM_BODY_SCOPE_BOUNDARY_GATE_REL
    )
    assert der02_object_payload.get("sibling_der02_theorem_body_scaffold_dependency_artifact_id") == (
        EXPECTED_DER02_THEOREM_BODY_ARTIFACT_ID
    )
    assert der02_object_payload.get("sibling_der02_theorem_body_scaffold_dependency_artifact_path") == (
        "formal/output/stat_der02_regime_closure_theorem_body_scaffold_cycle01_v0.json"
    )
    assert der02_object_payload.get("sibling_der02_theorem_body_scaffold_dependency_gate") == (
        EXPECTED_DER02_THEOREM_BODY_GATE_REL
    )
    assert der02_object_payload.get("sibling_der02_discharge_scaffold_dependency_artifact_id") == (
        EXPECTED_DER02_DISCHARGE_ARTIFACT_ID
    )
    assert der02_object_payload.get("sibling_der02_discharge_scaffold_dependency_artifact_path") == (
        "formal/output/stat_der02_regime_closure_discharge_scaffold_cycle01_v0.json"
    )
    assert der02_object_payload.get("sibling_der02_discharge_scaffold_dependency_gate") == (
        EXPECTED_DER02_DISCHARGE_GATE_REL
    )
    assert der02_object_payload.get("sibling_der02_regime_closure_scaffold_dependency_artifact_id") == (
        EXPECTED_DER02_ARTIFACT_ID
    )
    assert der02_object_payload.get("sibling_der02_regime_closure_scaffold_dependency_artifact_path") == (
        "formal/output/stat_der02_regime_closure_coupling_scaffold_cycle01_v0.json"
    )
    assert der02_object_payload.get("sibling_der02_regime_closure_scaffold_dependency_gate") == (
        EXPECTED_DER02_GATE_REL
    )
    assert der02_object_payload.get("sibling_der01_discharge_scaffold_dependency_artifact_id") == (
        EXPECTED_DER01_DISCHARGE_ARTIFACT_ID
    )
    assert der02_object_payload.get("sibling_der01_discharge_scaffold_dependency_artifact_path") == (
        "formal/output/stat_der01_entropy_balance_discharge_scaffold_cycle01_v0.json"
    )
    assert der02_object_payload.get("sibling_der01_discharge_scaffold_dependency_gate") == (
        EXPECTED_DER01_DISCHARGE_GATE_REL
    )
    assert der02_object_payload.get("sibling_der01_theorem_body_scope_boundary_dependency_artifact_id") == (
        EXPECTED_DER01_THEOREM_BODY_SCOPE_BOUNDARY_ARTIFACT_ID
    )
    assert der02_object_payload.get("sibling_der01_theorem_body_scope_boundary_dependency_artifact_path") == (
        "formal/output/stat_der01_theorem_body_scope_boundary_cycle01_v0.json"
    )
    assert der02_object_payload.get("sibling_der01_theorem_body_scope_boundary_dependency_gate") == (
        EXPECTED_DER01_THEOREM_BODY_SCOPE_BOUNDARY_GATE_REL
    )
    assert der02_object_payload.get("theorem_body_scope_boundary_artifact_id") == (
        EXPECTED_DER02_THEOREM_BODY_SCOPE_BOUNDARY_ARTIFACT_ID
    )
    assert der02_object_payload.get("theorem_body_scope_boundary_artifact_path") == (
        "formal/output/stat_der02_theorem_body_scope_boundary_cycle01_v0.json"
    )
    assert der02_object_payload.get("theorem_body_scope_boundary_gate") == (
        EXPECTED_DER02_THEOREM_BODY_SCOPE_BOUNDARY_GATE_REL
    )
    assert der02_theorem_body_scope_boundary_payload.get("sibling_der02_regime_closure_scaffold_dependency_artifact_id") == (
        EXPECTED_DER02_ARTIFACT_ID
    )
    assert der02_theorem_body_scope_boundary_payload.get("sibling_der02_regime_closure_scaffold_dependency_artifact_path") == (
        "formal/output/stat_der02_regime_closure_coupling_scaffold_cycle01_v0.json"
    )
    assert der02_theorem_body_scope_boundary_payload.get("sibling_der02_regime_closure_scaffold_dependency_gate") == (
        EXPECTED_DER02_GATE_REL
    )
    assert der02_theorem_body_scope_boundary_payload.get("sibling_der02_theorem_body_scaffold_dependency_artifact_id") == (
        EXPECTED_DER02_THEOREM_BODY_ARTIFACT_ID
    )
    assert der02_theorem_body_scope_boundary_payload.get("sibling_der02_theorem_body_scaffold_dependency_artifact_path") == (
        "formal/output/stat_der02_regime_closure_theorem_body_scaffold_cycle01_v0.json"
    )
    assert der02_theorem_body_scope_boundary_payload.get("sibling_der02_theorem_body_scaffold_dependency_gate") == (
        EXPECTED_DER02_THEOREM_BODY_GATE_REL
    )
    assert der02_theorem_body_scope_boundary_payload.get("sibling_der02_discharge_scaffold_dependency_artifact_id") == (
        EXPECTED_DER02_DISCHARGE_ARTIFACT_ID
    )
    assert der02_theorem_body_scope_boundary_payload.get("sibling_der02_discharge_scaffold_dependency_artifact_path") == (
        "formal/output/stat_der02_regime_closure_discharge_scaffold_cycle01_v0.json"
    )
    assert der02_theorem_body_scope_boundary_payload.get("sibling_der02_discharge_scaffold_dependency_gate") == (
        EXPECTED_DER02_DISCHARGE_GATE_REL
    )
    assert der02_theorem_body_scope_boundary_payload.get("sibling_der02_object_surface_scaffold_dependency_artifact_id") == (
        EXPECTED_DER02_OBJECT_ARTIFACT_ID
    )
    assert der02_theorem_body_scope_boundary_payload.get("sibling_der02_object_surface_scaffold_dependency_artifact_path") == (
        "formal/output/stat_der02_regime_closure_object_surface_scaffold_cycle01_v0.json"
    )
    assert der02_theorem_body_scope_boundary_payload.get("sibling_der02_object_surface_scaffold_dependency_gate") == (
        EXPECTED_DER02_OBJECT_GATE_REL
    )

    expected_checkpoint_row_set = set(checkpoint_payload["required_results_rows_refs"])
    assert {der01_payload["results_row_id"], der02_payload["results_row_id"]} == expected_checkpoint_row_set
    assert (
        der01_theorem_body_scope_boundary_payload.get("results_row_id") == der01_payload.get("results_row_id") == "TOE-STAT-DER-01"
    )
    assert der01_theorem_body_payload.get("results_row_id") == der01_payload.get("results_row_id") == "TOE-STAT-DER-01"
    assert der01_discharge_payload.get("results_row_id") == der01_payload.get("results_row_id") == "TOE-STAT-DER-01"
    assert der01_object_payload.get("results_row_id") == der01_payload.get("results_row_id") == "TOE-STAT-DER-01"
    assert der02_theorem_body_payload.get("results_row_id") == der02_payload.get("results_row_id") == "TOE-STAT-DER-02"
    assert der02_discharge_payload.get("results_row_id") == der02_payload.get("results_row_id") == "TOE-STAT-DER-02"
    assert der02_object_payload.get("results_row_id") == der02_payload.get("results_row_id") == "TOE-STAT-DER-02"
    assert (
        der02_theorem_body_scope_boundary_payload.get("results_row_id")
        == der02_payload.get("results_row_id")
        == "TOE-STAT-DER-02"
    )

    for row_id in EXPECTED_ROW_IDS:
        row_line = _results_row_line(results_text, row_id)
        assert f"| {row_id} | `{EXPECTED_ROW_LABEL}` |" in row_line
        assert "label promotion" in row_line

    for doc_text, doc_label in (
        (stat_text, "STAT plan"),
        (state_text, "state"),
        (roadmap_text, "roadmap"),
    ):
        assert "formal/output/stat_evidence_checkpoint_cycle01_v0.json" in doc_text, (
            f"{doc_label} must pin the STAT cycle01 checkpoint artifact."
        )
        assert "formal/output/stat_der01_entropy_balance_theorem_surface_scaffold_cycle01_v0.json" in doc_text, (
            f"{doc_label} must pin the STAT DER01 scaffold artifact."
        )
        assert "formal/output/stat_der01_theorem_body_scope_boundary_cycle01_v0.json" in doc_text, (
            f"{doc_label} must pin the STAT DER01 theorem-body scope-boundary artifact."
        )
        assert "formal/output/stat_der01_entropy_balance_theorem_body_scaffold_cycle01_v0.json" in doc_text, (
            f"{doc_label} must pin the STAT DER01 theorem-body scaffold artifact."
        )
        assert "formal/output/stat_der01_entropy_balance_discharge_scaffold_cycle01_v0.json" in doc_text, (
            f"{doc_label} must pin the STAT DER01 discharge scaffold artifact."
        )
        assert "formal/output/stat_der01_entropy_balance_object_surface_scaffold_cycle01_v0.json" in doc_text, (
            f"{doc_label} must pin the STAT DER01 object-surface scaffold artifact."
        )
        assert "formal/output/stat_der02_regime_closure_coupling_scaffold_cycle01_v0.json" in doc_text, (
            f"{doc_label} must pin the STAT DER02 scaffold artifact."
        )
        assert "formal/output/stat_der02_regime_closure_theorem_body_scaffold_cycle01_v0.json" in doc_text, (
            f"{doc_label} must pin the STAT DER02 theorem-body scaffold artifact."
        )
        assert "formal/output/stat_der02_regime_closure_discharge_scaffold_cycle01_v0.json" in doc_text, (
            f"{doc_label} must pin the STAT DER02 discharge scaffold artifact."
        )
        assert "formal/output/stat_der02_regime_closure_object_surface_scaffold_cycle01_v0.json" in doc_text, (
            f"{doc_label} must pin the STAT DER02 object-surface scaffold artifact."
        )
        assert "formal/output/stat_der02_theorem_body_scope_boundary_cycle01_v0.json" in doc_text, (
            f"{doc_label} must pin the STAT DER02 theorem-body scope-boundary artifact."
        )
        assert "formal/output/stat_closure_hardening_bundle_cycle01_v0.json" in doc_text, (
            f"{doc_label} must pin the STAT closure-hardening artifact."
        )
        assert "formal/output/stat_evidence_interface_lane_scope_boundary_cycle01_v0.json" in doc_text, (
            f"{doc_label} must pin the STAT evidence-interface scope-boundary artifact."
        )
        assert "formal/output/stat_multi_cycle_drift_resistance_sweep_cycle02_v0.json" in doc_text, (
            f"{doc_label} must pin the STAT multi-cycle drift-resistance artifact."
        )
        assert "formal/output/stat_evidence_adequacy_5x5_justification_scaffold_cycle01_v0.json" in doc_text, (
            f"{doc_label} must pin the STAT adequacy 5x5 scaffold artifact."
        )
        assert "formal/output/stat_promotion_readiness_scope_boundary_cycle01_v0.json" in doc_text, (
            f"{doc_label} must pin the STAT promotion-readiness scope-boundary artifact."
        )
        assert "formal/output/stat_derivation_completeness_gate_scope_boundary_cycle01_v0.json" in doc_text, (
            f"{doc_label} must pin the STAT derivation-completeness gate scope-boundary artifact."
        )
        assert "formal/output/stat_failure_trigger_audit_scope_boundary_cycle01_v0.json" in doc_text, (
            f"{doc_label} must pin the STAT failure-trigger audit scope-boundary artifact."
        )
        assert "formal/output/stat_derivation_completeness_discharge_surface_scope_boundary_cycle01_v0.json" in doc_text, (
            f"{doc_label} must pin the STAT derivation-completeness discharge-surface scope-boundary artifact."
        )
        assert "formal/output/stat_derivation_completeness_discharge_theorem_surface_scope_boundary_cycle01_v0.json" in doc_text, (
            f"{doc_label} must pin the STAT derivation-completeness discharge theorem-surface scope-boundary artifact."
        )
        assert "formal/output/stat_derivation_completeness_discharge_object_surface_scope_boundary_cycle01_v0.json" in doc_text, (
            f"{doc_label} must pin the STAT derivation-completeness discharge object-surface scope-boundary artifact."
        )
        assert "formal/output/stat_derivation_completeness_discharge_coherence_scope_boundary_cycle01_v0.json" in doc_text, (
            f"{doc_label} must pin the STAT derivation-completeness discharge coherence scope-boundary artifact."
        )
        assert "formal/output/stat_failure_trigger_discharge_surface_scope_boundary_cycle01_v0.json" in doc_text, (
            f"{doc_label} must pin the STAT failure-trigger discharge-surface scope-boundary artifact."
        )
        assert "formal/output/stat_failure_trigger_discharge_coherence_scope_boundary_cycle01_v0.json" in doc_text, (
            f"{doc_label} must pin the STAT failure-trigger discharge coherence scope-boundary artifact."
        )
        assert "formal/output/stat_failure_trigger_discharge_theorem_surface_scope_boundary_cycle01_v0.json" in doc_text, (
            f"{doc_label} must pin the STAT failure-trigger discharge theorem-surface scope-boundary artifact."
        )
        assert "formal/output/stat_failure_trigger_discharge_object_surface_scope_boundary_cycle01_v0.json" in doc_text, (
            f"{doc_label} must pin the STAT failure-trigger discharge object-surface scope-boundary artifact."
        )
        assert "formal/output/stat_discharge_completion_transition_scope_boundary_cycle01_v0.json" in doc_text, (
            f"{doc_label} must pin the STAT discharge completion transition scope-boundary artifact."
        )
        assert "formal/output/stat_adjudication_transition_scope_boundary_cycle01_v0.json" in doc_text, (
            f"{doc_label} must pin the STAT adjudication transition scope-boundary artifact."
        )
        assert "formal/output/stat_inevitability_transition_scope_boundary_cycle01_v0.json" in doc_text, (
            f"{doc_label} must pin the STAT inevitability transition scope-boundary artifact."
        )
        assert "formal/output/stat_nonflip_execution_boundary_scope_boundary_cycle01_v0.json" in doc_text, (
            f"{doc_label} must pin the STAT nonflip execution boundary scope-boundary artifact."
        )
        assert "formal/output/stat_nonflip_execution_custody_scope_boundary_cycle01_v0.json" in doc_text, (
            f"{doc_label} must pin the STAT nonflip execution custody scope-boundary artifact."
        )
        assert "formal/output/stat_nonflip_execution_custody_attestation_scope_boundary_cycle01_v0.json" in doc_text, (
            f"{doc_label} must pin the STAT nonflip execution custody attestation scope-boundary artifact."
        )
        assert (
            "formal/output/stat_nonflip_execution_custody_attestation_confirmation_scope_boundary_cycle01_v0.json"
            in doc_text
        ), (
            f"{doc_label} must pin the STAT nonflip execution custody attestation confirmation scope-boundary artifact."
        )
        assert (
            "formal/output/stat_nonflip_execution_custody_attestation_confirmation_attestation_scope_boundary_cycle01_v0.json"
            in doc_text
        ), (
            f"{doc_label} must pin the STAT nonflip execution custody attestation confirmation attestation scope-boundary artifact."
        )
        assert (
            "formal/output/stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_scope_boundary_cycle01_v0.json"
            in doc_text
        ), (
            f"{doc_label} must pin the STAT nonflip execution custody attestation confirmation attestation confirmation scope-boundary artifact."
        )
        assert (
            "formal/output/stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_cycle01_v0.json"
            in doc_text
        ), (
            f"{doc_label} must pin the STAT nonflip execution custody attestation confirmation attestation confirmation attestation scope-boundary artifact."
        )
        assert (
            "formal/output/stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_cycle01_v0.json"
            in doc_text
        ), (
            f"{doc_label} must pin the STAT nonflip execution custody attestation confirmation attestation confirmation attestation confirmation scope-boundary artifact."
        )
        assert (
            "formal/output/stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_cycle01_v0.json"
            in doc_text
        ), (
            f"{doc_label} must pin the STAT nonflip execution custody attestation confirmation attestation confirmation attestation confirmation attestation scope-boundary artifact."
        )
        assert (
            "formal/output/stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_cycle01_v0.json"
            in doc_text
        ), (
            f"{doc_label} must pin the STAT nonflip execution custody attestation confirmation attestation confirmation attestation confirmation attestation confirmation scope-boundary artifact."
        )
        assert (
            "formal/output/stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_cycle01_v0.json"
            in doc_text
        ), (
            f"{doc_label} must pin the STAT nonflip execution custody attestation confirmation attestation confirmation attestation confirmation attestation confirmation attestation scope-boundary artifact."
        )
        assert EXPECTED_DER01_GATE_REL in doc_text, f"{doc_label} must pin the STAT DER01 scaffold gate path."
        assert EXPECTED_DER01_THEOREM_BODY_SCOPE_BOUNDARY_GATE_REL in doc_text, (
            f"{doc_label} must pin the STAT DER01 theorem-body scope-boundary gate path."
        )
        assert EXPECTED_DER01_THEOREM_BODY_GATE_REL in doc_text, (
            f"{doc_label} must pin the STAT DER01 theorem-body scaffold gate path."
        )
        assert EXPECTED_DER01_DISCHARGE_GATE_REL in doc_text, (
            f"{doc_label} must pin the STAT DER01 discharge scaffold gate path."
        )
        assert EXPECTED_DER01_OBJECT_GATE_REL in doc_text, (
            f"{doc_label} must pin the STAT DER01 object-surface scaffold gate path."
        )
        assert EXPECTED_DER02_GATE_REL in doc_text, f"{doc_label} must pin the STAT DER02 scaffold gate path."
        assert EXPECTED_DER02_THEOREM_BODY_GATE_REL in doc_text, (
            f"{doc_label} must pin the STAT DER02 theorem-body scaffold gate path."
        )
        assert EXPECTED_DER02_DISCHARGE_GATE_REL in doc_text, (
            f"{doc_label} must pin the STAT DER02 discharge scaffold gate path."
        )
        assert EXPECTED_DER02_OBJECT_GATE_REL in doc_text, (
            f"{doc_label} must pin the STAT DER02 object-surface scaffold gate path."
        )
        assert EXPECTED_DER02_THEOREM_BODY_SCOPE_BOUNDARY_GATE_REL in doc_text, (
            f"{doc_label} must pin the STAT DER02 theorem-body scope-boundary gate path."
        )
        assert EXPECTED_STAT_CLOSURE_HARDENING_GATE_REL in doc_text, (
            f"{doc_label} must pin the STAT closure-hardening gate path."
        )
        assert EXPECTED_STAT_EVIDENCE_INTERFACE_SCOPE_BOUNDARY_GATE_REL in doc_text, (
            f"{doc_label} must pin the STAT evidence-interface scope-boundary gate path."
        )
        assert EXPECTED_STAT_MULTI_CYCLE_DRIFT_RESISTANCE_GATE_REL in doc_text, (
            f"{doc_label} must pin the STAT multi-cycle drift-resistance gate path."
        )
        assert EXPECTED_STAT_EVIDENCE_ADEQUACY_5X5_SCAFFOLD_GATE_REL in doc_text, (
            f"{doc_label} must pin the STAT adequacy 5x5 scaffold gate path."
        )
        assert EXPECTED_STAT_PROMOTION_READINESS_SCOPE_BOUNDARY_GATE_REL in doc_text, (
            f"{doc_label} must pin the STAT promotion-readiness scope-boundary gate path."
        )
        assert EXPECTED_STAT_DERIVATION_COMPLETENESS_GATE_SCOPE_BOUNDARY_GATE_REL in doc_text, (
            f"{doc_label} must pin the STAT derivation-completeness gate scope-boundary gate path."
        )
        assert EXPECTED_STAT_FAILURE_TRIGGER_AUDIT_SCOPE_BOUNDARY_GATE_REL in doc_text, (
            f"{doc_label} must pin the STAT failure-trigger audit scope-boundary gate path."
        )
        assert EXPECTED_STAT_DERIVATION_COMPLETENESS_DISCHARGE_SURFACE_SCOPE_BOUNDARY_GATE_REL in doc_text, (
            f"{doc_label} must pin the STAT derivation-completeness discharge-surface scope-boundary gate path."
        )
        assert EXPECTED_STAT_DERIVATION_COMPLETENESS_DISCHARGE_THEOREM_SURFACE_SCOPE_BOUNDARY_GATE_REL in doc_text, (
            f"{doc_label} must pin the STAT derivation-completeness discharge theorem-surface scope-boundary gate path."
        )
        assert EXPECTED_STAT_DERIVATION_COMPLETENESS_DISCHARGE_OBJECT_SURFACE_SCOPE_BOUNDARY_GATE_REL in doc_text, (
            f"{doc_label} must pin the STAT derivation-completeness discharge object-surface scope-boundary gate path."
        )
        assert EXPECTED_STAT_DERIVATION_COMPLETENESS_DISCHARGE_COHERENCE_SCOPE_BOUNDARY_GATE_REL in doc_text, (
            f"{doc_label} must pin the STAT derivation-completeness discharge coherence scope-boundary gate path."
        )
        assert EXPECTED_STAT_FAILURE_TRIGGER_DISCHARGE_SURFACE_SCOPE_BOUNDARY_GATE_REL in doc_text, (
            f"{doc_label} must pin the STAT failure-trigger discharge-surface scope-boundary gate path."
        )
        assert EXPECTED_STAT_FAILURE_TRIGGER_DISCHARGE_COHERENCE_SCOPE_BOUNDARY_GATE_REL in doc_text, (
            f"{doc_label} must pin the STAT failure-trigger discharge coherence scope-boundary gate path."
        )
        assert EXPECTED_STAT_FAILURE_TRIGGER_DISCHARGE_THEOREM_SURFACE_SCOPE_BOUNDARY_GATE_REL in doc_text, (
            f"{doc_label} must pin the STAT failure-trigger discharge theorem-surface scope-boundary gate path."
        )
        assert EXPECTED_STAT_FAILURE_TRIGGER_DISCHARGE_OBJECT_SURFACE_SCOPE_BOUNDARY_GATE_REL in doc_text, (
            f"{doc_label} must pin the STAT failure-trigger discharge object-surface scope-boundary gate path."
        )
        assert EXPECTED_STAT_DISCHARGE_COMPLETION_TRANSITION_SCOPE_BOUNDARY_GATE_REL in doc_text, (
            f"{doc_label} must pin the STAT discharge completion transition scope-boundary gate path."
        )
        assert EXPECTED_STAT_ADJUDICATION_TRANSITION_SCOPE_BOUNDARY_GATE_REL in doc_text, (
            f"{doc_label} must pin the STAT adjudication transition scope-boundary gate path."
        )
        assert EXPECTED_STAT_INEVITABILITY_TRANSITION_SCOPE_BOUNDARY_GATE_REL in doc_text, (
            f"{doc_label} must pin the STAT inevitability transition scope-boundary gate path."
        )
        assert EXPECTED_STAT_NONFLIP_EXECUTION_BOUNDARY_SCOPE_BOUNDARY_GATE_REL in doc_text, (
            f"{doc_label} must pin the STAT nonflip execution boundary scope-boundary gate path."
        )
        assert EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_SCOPE_BOUNDARY_GATE_REL in doc_text, (
            f"{doc_label} must pin the STAT nonflip execution custody scope-boundary gate path."
        )
        assert EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_SCOPE_BOUNDARY_GATE_REL in doc_text, (
            f"{doc_label} must pin the STAT nonflip execution custody attestation scope-boundary gate path."
        )
        assert EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_SCOPE_BOUNDARY_GATE_REL in doc_text, (
            f"{doc_label} must pin the STAT nonflip execution custody attestation confirmation scope-boundary gate path."
        )
        assert (
            EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_SCOPE_BOUNDARY_GATE_REL
            in doc_text
        ), (
            f"{doc_label} must pin the STAT nonflip execution custody attestation confirmation attestation scope-boundary gate path."
        )
        assert (
            EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_SCOPE_BOUNDARY_GATE_REL
            in doc_text
        ), (
            f"{doc_label} must pin the STAT nonflip execution custody attestation confirmation attestation confirmation scope-boundary gate path."
        )
        assert (
            EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_SCOPE_BOUNDARY_GATE_REL
            in doc_text
        ), (
            f"{doc_label} must pin the STAT nonflip execution custody attestation confirmation attestation confirmation attestation scope-boundary gate path."
        )
        assert (
            EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_SCOPE_BOUNDARY_GATE_REL
            in doc_text
        ), (
            f"{doc_label} must pin the STAT nonflip execution custody attestation confirmation attestation confirmation attestation confirmation scope-boundary gate path."
        )
        assert (
            EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_SCOPE_BOUNDARY_GATE_REL
            in doc_text
        ), (
            f"{doc_label} must pin the STAT nonflip execution custody attestation confirmation attestation confirmation attestation confirmation attestation scope-boundary gate path."
        )
        assert (
            EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_SCOPE_BOUNDARY_GATE_REL
            in doc_text
        ), (
            f"{doc_label} must pin the STAT nonflip execution custody attestation confirmation attestation confirmation attestation confirmation attestation confirmation scope-boundary gate path."
        )
        assert (
            EXPECTED_STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_SCOPE_BOUNDARY_GATE_REL
            in doc_text
        ), (
            f"{doc_label} must pin the STAT nonflip execution custody attestation confirmation attestation confirmation attestation confirmation attestation confirmation attestation scope-boundary gate path."
        )

    assert "does not authorize `TOE-STAT-DER-01` label promotion" in stat_text
    assert "does not authorize `TOE-STAT-DER-02` label promotion" in stat_text

    for text, text_label in (
        (stat_text, "STAT plan"),
        (state_text, "state"),
        (roadmap_text, "roadmap"),
        (results_text, "results"),
    ):
        for pattern in DISALLOWED_STAT_TOKEN_PATTERNS:
            assert re.search(pattern, text) is None, (
                f"{text_label} contains premature STAT DER02 object-surface token matching `{pattern}`."
            )

    der01_object_surface_payloads = sorted(REPO_ROOT.glob("formal/output/stat_der01_*object_surface*.json"))
    assert der01_object_surface_payloads == [DER01_OBJECT_ARTIFACT_PATH], (
        "STAT row-scaffold aggregation phase admits exactly one DER01 object-surface payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in der01_object_surface_payloads]}"
    )
    der01_theorem_body_payloads = sorted(REPO_ROOT.glob("formal/output/stat_der01_*theorem_body_scaffold*.json"))
    assert der01_theorem_body_payloads == [DER01_THEOREM_BODY_ARTIFACT_PATH], (
        "STAT row-scaffold aggregation phase admits exactly one DER01 theorem-body scaffold payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in der01_theorem_body_payloads]}"
    )
    der01_theorem_body_scope_boundary_payloads = sorted(REPO_ROOT.glob("formal/output/stat_der01_*scope_boundary*.json"))
    assert der01_theorem_body_scope_boundary_payloads == [DER01_THEOREM_BODY_SCOPE_BOUNDARY_ARTIFACT_PATH], (
        "STAT row-scaffold aggregation phase admits exactly one DER01 theorem-body scope-boundary payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in der01_theorem_body_scope_boundary_payloads]}"
    )
    der01_discharge_payloads = sorted(REPO_ROOT.glob("formal/output/stat_der01_*discharge*.json"))
    assert der01_discharge_payloads == [DER01_DISCHARGE_ARTIFACT_PATH], (
        "STAT row-scaffold aggregation phase admits exactly one DER01 discharge scaffold payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in der01_discharge_payloads]}"
    )
    der02_theorem_body_payloads = sorted(REPO_ROOT.glob("formal/output/stat_der02_*theorem_body_scaffold*.json"))
    assert der02_theorem_body_payloads == [DER02_THEOREM_BODY_ARTIFACT_PATH], (
        "STAT row-scaffold aggregation phase admits exactly one DER02 theorem-body scaffold payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in der02_theorem_body_payloads]}"
    )
    der02_discharge_payloads = sorted(REPO_ROOT.glob("formal/output/stat_der02_*discharge*.json"))
    assert der02_discharge_payloads == [DER02_DISCHARGE_ARTIFACT_PATH], (
        "STAT row-scaffold aggregation phase admits exactly one DER02 discharge scaffold payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in der02_discharge_payloads]}"
    )
    der02_object_surface_payloads = sorted(REPO_ROOT.glob("formal/output/stat_der02_*object_surface*.json"))
    assert der02_object_surface_payloads == [DER02_OBJECT_ARTIFACT_PATH], (
        "STAT row-scaffold aggregation phase admits exactly one DER02 object-surface scaffold payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in der02_object_surface_payloads]}"
    )
    der02_theorem_body_scope_boundary_payloads = sorted(REPO_ROOT.glob("formal/output/stat_der02_*scope_boundary*.json"))
    assert der02_theorem_body_scope_boundary_payloads == [DER02_THEOREM_BODY_SCOPE_BOUNDARY_ARTIFACT_PATH], (
        "STAT row-scaffold aggregation phase admits exactly one DER02 theorem-body scope-boundary payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in der02_theorem_body_scope_boundary_payloads]}"
    )
    stat_closure_hardening_payloads = sorted(REPO_ROOT.glob("formal/output/stat_closure_hardening_bundle_cycle01_v0.json"))
    assert stat_closure_hardening_payloads == [STAT_CLOSURE_HARDENING_ARTIFACT_PATH], (
        "STAT row-scaffold aggregation phase admits exactly one STAT closure-hardening payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_closure_hardening_payloads]}"
    )
    stat_evidence_interface_scope_boundary_payloads = sorted(
        REPO_ROOT.glob("formal/output/stat_evidence_interface_lane_scope_boundary_cycle01_v0.json")
    )
    assert stat_evidence_interface_scope_boundary_payloads == [STAT_EVIDENCE_INTERFACE_SCOPE_BOUNDARY_ARTIFACT_PATH], (
        "STAT row-scaffold aggregation phase admits exactly one STAT evidence-interface scope-boundary payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_evidence_interface_scope_boundary_payloads]}"
    )
    stat_multi_cycle_drift_resistance_payloads = sorted(
        REPO_ROOT.glob("formal/output/stat_multi_cycle_drift_resistance_sweep_cycle02_v0.json")
    )
    assert stat_multi_cycle_drift_resistance_payloads == [STAT_MULTI_CYCLE_DRIFT_RESISTANCE_ARTIFACT_PATH], (
        "STAT row-scaffold aggregation phase admits exactly one STAT multi-cycle drift-resistance payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_multi_cycle_drift_resistance_payloads]}"
    )
    stat_evidence_adequacy_5x5_scaffold_payloads = sorted(
        REPO_ROOT.glob("formal/output/stat_evidence_adequacy_5x5_justification_scaffold_cycle01_v0.json")
    )
    assert stat_evidence_adequacy_5x5_scaffold_payloads == [STAT_EVIDENCE_ADEQUACY_5X5_SCAFFOLD_ARTIFACT_PATH], (
        "STAT row-scaffold aggregation phase admits exactly one STAT adequacy 5x5 scaffold payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_evidence_adequacy_5x5_scaffold_payloads]}"
    )
    stat_promotion_readiness_scope_boundary_payloads = sorted(
        REPO_ROOT.glob("formal/output/stat_promotion_readiness_scope_boundary_cycle01_v0.json")
    )
    assert stat_promotion_readiness_scope_boundary_payloads == [STAT_PROMOTION_READINESS_SCOPE_BOUNDARY_ARTIFACT_PATH], (
        "STAT row-scaffold aggregation phase admits exactly one STAT promotion-readiness scope-boundary payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_promotion_readiness_scope_boundary_payloads]}"
    )
    stat_derivation_completeness_gate_scope_boundary_payloads = sorted(
        REPO_ROOT.glob("formal/output/stat_derivation_completeness_gate_scope_boundary_cycle01_v0.json")
    )
    assert stat_derivation_completeness_gate_scope_boundary_payloads == [
        STAT_DERIVATION_COMPLETENESS_GATE_SCOPE_BOUNDARY_ARTIFACT_PATH
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT derivation-completeness gate scope-boundary payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_derivation_completeness_gate_scope_boundary_payloads]}"
    )
    stat_failure_trigger_audit_scope_boundary_payloads = sorted(
        REPO_ROOT.glob("formal/output/stat_failure_trigger_audit_scope_boundary_cycle01_v0.json")
    )
    assert stat_failure_trigger_audit_scope_boundary_payloads == [STAT_FAILURE_TRIGGER_AUDIT_SCOPE_BOUNDARY_ARTIFACT_PATH], (
        "STAT row-scaffold aggregation phase admits exactly one STAT failure-trigger audit scope-boundary payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_failure_trigger_audit_scope_boundary_payloads]}"
    )
    stat_derivation_completeness_discharge_surface_scope_boundary_payloads = sorted(
        REPO_ROOT.glob("formal/output/stat_derivation_completeness_discharge_surface_scope_boundary_cycle01_v0.json")
    )
    assert stat_derivation_completeness_discharge_surface_scope_boundary_payloads == [
        STAT_DERIVATION_COMPLETENESS_DISCHARGE_SURFACE_SCOPE_BOUNDARY_ARTIFACT_PATH
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT derivation-completeness discharge-surface scope-boundary payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_derivation_completeness_discharge_surface_scope_boundary_payloads]}"
    )
    stat_derivation_completeness_discharge_theorem_surface_scope_boundary_payloads = sorted(
        REPO_ROOT.glob("formal/output/stat_derivation_completeness_discharge_theorem_surface_scope_boundary_cycle01_v0.json")
    )
    assert stat_derivation_completeness_discharge_theorem_surface_scope_boundary_payloads == [
        STAT_DERIVATION_COMPLETENESS_DISCHARGE_THEOREM_SURFACE_SCOPE_BOUNDARY_ARTIFACT_PATH
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT derivation-completeness discharge theorem-surface scope-boundary payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_derivation_completeness_discharge_theorem_surface_scope_boundary_payloads]}"
    )
    stat_derivation_completeness_discharge_object_surface_scope_boundary_payloads = sorted(
        REPO_ROOT.glob("formal/output/stat_derivation_completeness_discharge_object_surface_scope_boundary_cycle01_v0.json")
    )
    assert stat_derivation_completeness_discharge_object_surface_scope_boundary_payloads == [
        STAT_DERIVATION_COMPLETENESS_DISCHARGE_OBJECT_SURFACE_SCOPE_BOUNDARY_ARTIFACT_PATH
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT derivation-completeness discharge object-surface scope-boundary payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_derivation_completeness_discharge_object_surface_scope_boundary_payloads]}"
    )
    stat_derivation_completeness_discharge_coherence_scope_boundary_payloads = sorted(
        REPO_ROOT.glob("formal/output/stat_derivation_completeness_discharge_coherence_scope_boundary_cycle01_v0.json")
    )
    assert stat_derivation_completeness_discharge_coherence_scope_boundary_payloads == [
        STAT_DERIVATION_COMPLETENESS_DISCHARGE_COHERENCE_SCOPE_BOUNDARY_ARTIFACT_PATH
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT derivation-completeness discharge coherence scope-boundary payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_derivation_completeness_discharge_coherence_scope_boundary_payloads]}"
    )
    stat_failure_trigger_discharge_surface_scope_boundary_payloads = sorted(
        REPO_ROOT.glob("formal/output/stat_failure_trigger_discharge_surface_scope_boundary_cycle01_v0.json")
    )
    assert stat_failure_trigger_discharge_surface_scope_boundary_payloads == [
        STAT_FAILURE_TRIGGER_DISCHARGE_SURFACE_SCOPE_BOUNDARY_ARTIFACT_PATH
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT failure-trigger discharge-surface scope-boundary payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_failure_trigger_discharge_surface_scope_boundary_payloads]}"
    )
    stat_failure_trigger_discharge_coherence_scope_boundary_payloads = sorted(
        REPO_ROOT.glob("formal/output/stat_failure_trigger_discharge_coherence_scope_boundary_cycle01_v0.json")
    )
    assert stat_failure_trigger_discharge_coherence_scope_boundary_payloads == [
        STAT_FAILURE_TRIGGER_DISCHARGE_COHERENCE_SCOPE_BOUNDARY_ARTIFACT_PATH
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT failure-trigger discharge coherence scope-boundary payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_failure_trigger_discharge_coherence_scope_boundary_payloads]}"
    )
    stat_failure_trigger_discharge_theorem_surface_scope_boundary_payloads = sorted(
        REPO_ROOT.glob("formal/output/stat_failure_trigger_discharge_theorem_surface_scope_boundary_cycle01_v0.json")
    )
    assert stat_failure_trigger_discharge_theorem_surface_scope_boundary_payloads == [
        STAT_FAILURE_TRIGGER_DISCHARGE_THEOREM_SURFACE_SCOPE_BOUNDARY_ARTIFACT_PATH
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT failure-trigger discharge theorem-surface scope-boundary payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_failure_trigger_discharge_theorem_surface_scope_boundary_payloads]}"
    )
    stat_failure_trigger_discharge_object_surface_scope_boundary_payloads = sorted(
        REPO_ROOT.glob("formal/output/stat_failure_trigger_discharge_object_surface_scope_boundary_cycle01_v0.json")
    )
    assert stat_failure_trigger_discharge_object_surface_scope_boundary_payloads == [
        STAT_FAILURE_TRIGGER_DISCHARGE_OBJECT_SURFACE_SCOPE_BOUNDARY_ARTIFACT_PATH
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT failure-trigger discharge object-surface scope-boundary payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_failure_trigger_discharge_object_surface_scope_boundary_payloads]}"
    )
    stat_failure_trigger_discharge_object_surface_status_payloads = sorted(
        REPO_ROOT.glob("formal/output/stat_failure_trigger_discharge_object_surface_status_cycle01_v0.json")
    )
    assert stat_failure_trigger_discharge_object_surface_status_payloads == [
        STAT_FAILURE_TRIGGER_DISCHARGE_OBJECT_SURFACE_STATUS_ARTIFACT_PATH
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT failure-trigger discharge object-surface status payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_failure_trigger_discharge_object_surface_status_payloads]}"
    )
    stat_failure_trigger_discharge_coherence_status_payloads = sorted(
        REPO_ROOT.glob("formal/output/stat_failure_trigger_discharge_coherence_status_cycle01_v0.json")
    )
    assert stat_failure_trigger_discharge_coherence_status_payloads == [
        STAT_FAILURE_TRIGGER_DISCHARGE_COHERENCE_STATUS_ARTIFACT_PATH
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT failure-trigger discharge coherence-status payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_failure_trigger_discharge_coherence_status_payloads]}"
    )
    stat_discharge_completion_transition_status_payloads = sorted(
        REPO_ROOT.glob("formal/output/stat_discharge_completion_transition_status_cycle01_v0.json")
    )
    assert stat_discharge_completion_transition_status_payloads == [
        STAT_DISCHARGE_COMPLETION_TRANSITION_STATUS_ARTIFACT_PATH
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT discharge-completion transition-status payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_discharge_completion_transition_status_payloads]}"
    )
    stat_adjudication_transition_status_payloads = sorted(
        REPO_ROOT.glob("formal/output/stat_adjudication_transition_status_cycle01_v0.json")
    )
    assert stat_adjudication_transition_status_payloads == [
        STAT_ADJUDICATION_TRANSITION_STATUS_ARTIFACT_PATH
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT adjudication-transition status payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_adjudication_transition_status_payloads]}"
    )
    stat_inevitability_transition_status_payloads = sorted(
        REPO_ROOT.glob("formal/output/stat_inevitability_transition_status_cycle01_v0.json")
    )
    assert stat_inevitability_transition_status_payloads == [
        STAT_INEVITABILITY_TRANSITION_STATUS_ARTIFACT_PATH
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT inevitability-transition status payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_inevitability_transition_status_payloads]}"
    )
    stat_nonflip_execution_boundary_status_payloads = sorted(
        REPO_ROOT.glob("formal/output/stat_nonflip_execution_boundary_status_cycle01_v0.json")
    )
    assert stat_nonflip_execution_boundary_status_payloads == [
        STAT_NONFLIP_EXECUTION_BOUNDARY_STATUS_ARTIFACT_PATH
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT nonflip-execution-boundary status payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_nonflip_execution_boundary_status_payloads]}"
    )
    stat_nonflip_execution_custody_status_payloads = sorted(
        REPO_ROOT.glob("formal/output/stat_nonflip_execution_custody_status_cycle01_v0.json")
    )
    assert stat_nonflip_execution_custody_status_payloads == [
        STAT_NONFLIP_EXECUTION_CUSTODY_STATUS_ARTIFACT_PATH
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT nonflip-execution-custody status payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_nonflip_execution_custody_status_payloads]}"
    )
    stat_nonflip_execution_custody_attestation_status_payloads = sorted(
        REPO_ROOT.glob("formal/output/stat_nonflip_execution_custody_attestation_status_cycle01_v0.json")
    )
    assert stat_nonflip_execution_custody_attestation_status_payloads == [
        STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_STATUS_ARTIFACT_PATH
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT nonflip-execution-custody-attestation status payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_nonflip_execution_custody_attestation_status_payloads]}"
    )
    stat_nonflip_execution_custody_attestation_confirmation_status_payloads = sorted(
        REPO_ROOT.glob("formal/output/stat_nonflip_execution_custody_attestation_confirmation_status_cycle01_v0.json")
    )
    assert stat_nonflip_execution_custody_attestation_confirmation_status_payloads == [
        STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_STATUS_ARTIFACT_PATH
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT nonflip-execution-custody-attestation-confirmation status payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_nonflip_execution_custody_attestation_confirmation_status_payloads]}"
    )
    stat_nonflip_execution_custody_attestation_confirmation_attestation_status_payloads = sorted(
        REPO_ROOT.glob(
            "formal/output/stat_nonflip_execution_custody_attestation_confirmation_attestation_status_cycle01_v0.json"
        )
    )
    assert stat_nonflip_execution_custody_attestation_confirmation_attestation_status_payloads == [
        STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_STATUS_ARTIFACT_PATH
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT nonflip-execution-custody-attestation-confirmation-attestation status payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_nonflip_execution_custody_attestation_confirmation_attestation_status_payloads]}"
    )
    stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_status_payloads = sorted(
        REPO_ROOT.glob(
            "formal/output/stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_status_cycle01_v0.json"
        )
    )
    assert stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_status_payloads == [
        STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_STATUS_ARTIFACT_PATH
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT nonflip-execution-custody-attestation-confirmation-attestation-confirmation status payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_status_payloads]}"
    )
    stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_status_payloads = sorted(
        REPO_ROOT.glob(
            "formal/output/stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_status_cycle01_v0.json"
        )
    )
    assert stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_status_payloads == [
        STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_STATUS_ARTIFACT_PATH
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT nonflip-execution-custody-attestation-confirmation-attestation-confirmation-attestation status payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_status_payloads]}"
    )
    stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_status_payloads = sorted(
        REPO_ROOT.glob(
            "formal/output/stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_status_cycle01_v0.json"
        )
    )
    assert stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_status_payloads == [
        STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_STATUS_ARTIFACT_PATH
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT nonflip-execution-custody-attestation-confirmation-attestation-confirmation-attestation-confirmation status payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_status_payloads]}"
    )
    stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_status_payloads = sorted(
        REPO_ROOT.glob(
            "formal/output/stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_status_cycle01_v0.json"
        )
    )
    assert stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_status_payloads == [
        STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_STATUS_ARTIFACT_PATH
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT nonflip-execution-custody-attestation-confirmation-attestation-confirmation-attestation-confirmation-attestation status payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_status_payloads]}"
    )
    stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_status_payloads = sorted(
        REPO_ROOT.glob(
            "formal/output/stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_status_cycle01_v0.json"
        )
    )
    assert stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_status_payloads == [
        STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_STATUS_ARTIFACT_PATH
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT nonflip-execution-custody-attestation-confirmation-attestation-confirmation-attestation-confirmation-attestation-confirmation status payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_status_payloads]}"
    )
    stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_status_payloads = sorted(
        REPO_ROOT.glob(
            "formal/output/stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_status_cycle01_v0.json"
        )
    )
    assert stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_status_payloads == [
        STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_STATUS_ARTIFACT_PATH
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT nonflip-execution-custody-attestation-confirmation-attestation-confirmation-attestation-confirmation-attestation-confirmation-attestation status payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_status_payloads]}"
    )
    stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_status_payloads = sorted(
        REPO_ROOT.glob(
            "formal/output/stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_status_cycle01_v0.json"
        )
    )
    assert stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_status_payloads == [
        REPO_ROOT / "formal/output/stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_status_cycle01_v0.json"
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT attestation-confirmation-attestation-confirmation-attestation-confirmation-attestation-confirmation-attestation-confirmation status payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_status_payloads]}"
    )
    stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_status_payloads = (
        sorted(
            REPO_ROOT.glob(
                "formal/output/stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_status_cycle01_v0.json"
            )
        )
    )
    assert stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_status_payloads == [
        REPO_ROOT
        / "formal/output/stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_status_cycle01_v0.json"
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT attestation-confirmation-attestation-confirmation-attestation-confirmation-attestation-confirmation-attestation-confirmation-attestation status payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_status_payloads]}"
    )
    stat_discharge_completion_transition_scope_boundary_payloads = sorted(
        REPO_ROOT.glob("formal/output/stat_discharge_completion_transition_scope_boundary_cycle01_v0.json")
    )
    assert stat_discharge_completion_transition_scope_boundary_payloads == [
        STAT_DISCHARGE_COMPLETION_TRANSITION_SCOPE_BOUNDARY_ARTIFACT_PATH
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT discharge completion transition scope-boundary payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_discharge_completion_transition_scope_boundary_payloads]}"
    )
    stat_adjudication_transition_scope_boundary_payloads = sorted(
        REPO_ROOT.glob("formal/output/stat_adjudication_transition_scope_boundary_cycle01_v0.json")
    )
    assert stat_adjudication_transition_scope_boundary_payloads == [
        STAT_ADJUDICATION_TRANSITION_SCOPE_BOUNDARY_ARTIFACT_PATH
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT adjudication transition scope-boundary payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_adjudication_transition_scope_boundary_payloads]}"
    )
    stat_inevitability_transition_scope_boundary_payloads = sorted(
        REPO_ROOT.glob("formal/output/stat_inevitability_transition_scope_boundary_cycle01_v0.json")
    )
    assert stat_inevitability_transition_scope_boundary_payloads == [
        STAT_INEVITABILITY_TRANSITION_SCOPE_BOUNDARY_ARTIFACT_PATH
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT inevitability transition scope-boundary payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_inevitability_transition_scope_boundary_payloads]}"
    )
    stat_nonflip_execution_boundary_scope_boundary_payloads = sorted(
        REPO_ROOT.glob("formal/output/stat_nonflip_execution_boundary_scope_boundary_cycle01_v0.json")
    )
    assert stat_nonflip_execution_boundary_scope_boundary_payloads == [
        STAT_NONFLIP_EXECUTION_BOUNDARY_SCOPE_BOUNDARY_ARTIFACT_PATH
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT nonflip execution boundary scope-boundary payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_nonflip_execution_boundary_scope_boundary_payloads]}"
    )
    stat_nonflip_execution_custody_scope_boundary_payloads = sorted(
        REPO_ROOT.glob("formal/output/stat_nonflip_execution_custody_scope_boundary_cycle01_v0.json")
    )
    assert stat_nonflip_execution_custody_scope_boundary_payloads == [
        STAT_NONFLIP_EXECUTION_CUSTODY_SCOPE_BOUNDARY_ARTIFACT_PATH
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT nonflip execution custody scope-boundary payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_nonflip_execution_custody_scope_boundary_payloads]}"
    )
    stat_nonflip_execution_custody_attestation_scope_boundary_payloads = sorted(
        REPO_ROOT.glob("formal/output/stat_nonflip_execution_custody_attestation_scope_boundary_cycle01_v0.json")
    )
    assert stat_nonflip_execution_custody_attestation_scope_boundary_payloads == [
        STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_SCOPE_BOUNDARY_ARTIFACT_PATH
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT nonflip execution custody attestation scope-boundary payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_nonflip_execution_custody_attestation_scope_boundary_payloads]}"
    )
    stat_nonflip_execution_custody_attestation_confirmation_scope_boundary_payloads = sorted(
        REPO_ROOT.glob("formal/output/stat_nonflip_execution_custody_attestation_confirmation_scope_boundary_cycle01_v0.json")
    )
    assert stat_nonflip_execution_custody_attestation_confirmation_scope_boundary_payloads == [
        STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_SCOPE_BOUNDARY_ARTIFACT_PATH
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT nonflip execution custody attestation confirmation scope-boundary payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_nonflip_execution_custody_attestation_confirmation_scope_boundary_payloads]}"
    )
    stat_nonflip_execution_custody_attestation_confirmation_attestation_scope_boundary_payloads = sorted(
        REPO_ROOT.glob(
            "formal/output/stat_nonflip_execution_custody_attestation_confirmation_attestation_scope_boundary_cycle01_v0.json"
        )
    )
    assert stat_nonflip_execution_custody_attestation_confirmation_attestation_scope_boundary_payloads == [
        STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_SCOPE_BOUNDARY_ARTIFACT_PATH
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT nonflip execution custody attestation confirmation attestation scope-boundary payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_nonflip_execution_custody_attestation_confirmation_attestation_scope_boundary_payloads]}"
    )
    stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_scope_boundary_payloads = sorted(
        REPO_ROOT.glob(
            "formal/output/stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_scope_boundary_cycle01_v0.json"
        )
    )
    assert stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_scope_boundary_payloads == [
        STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_SCOPE_BOUNDARY_ARTIFACT_PATH
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT nonflip execution custody attestation confirmation attestation confirmation scope-boundary payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_scope_boundary_payloads]}"
    )
    stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_payloads = sorted(
        REPO_ROOT.glob(
            "formal/output/stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_cycle01_v0.json"
        )
    )
    assert stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_payloads == [
        STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_SCOPE_BOUNDARY_ARTIFACT_PATH
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT nonflip execution custody attestation confirmation attestation confirmation attestation scope-boundary payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_payloads]}"
    )
    stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_payloads = (
        sorted(
            REPO_ROOT.glob(
                "formal/output/stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_cycle01_v0.json"
            )
        )
    )
    assert stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_payloads == [
        STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_SCOPE_BOUNDARY_ARTIFACT_PATH
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT nonflip execution custody attestation confirmation attestation confirmation attestation confirmation scope-boundary payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_payloads]}"
    )
    stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_payloads = (
        sorted(
            REPO_ROOT.glob(
                "formal/output/stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_cycle01_v0.json"
            )
        )
    )
    assert stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_payloads == [
        STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_SCOPE_BOUNDARY_ARTIFACT_PATH
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT nonflip execution custody attestation confirmation attestation confirmation attestation confirmation attestation scope-boundary payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_payloads]}"
    )
    stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_payloads = (
        sorted(
            REPO_ROOT.glob(
                "formal/output/stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_cycle01_v0.json"
            )
        )
    )
    assert stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_payloads == [
        STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_SCOPE_BOUNDARY_ARTIFACT_PATH
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT nonflip execution custody attestation confirmation attestation confirmation attestation confirmation attestation confirmation scope-boundary payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_payloads]}"
    )
    stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_payloads = (
        sorted(
            REPO_ROOT.glob(
                "formal/output/stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_cycle01_v0.json"
            )
        )
    )
    assert stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_payloads == [
        STAT_NONFLIP_EXECUTION_CUSTODY_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_SCOPE_BOUNDARY_ARTIFACT_PATH
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT nonflip execution custody attestation confirmation attestation confirmation attestation confirmation attestation confirmation attestation scope-boundary payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_payloads]}"
    )
    stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_payloads = (
        sorted(
            REPO_ROOT.glob(
                "formal/output/stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_cycle01_v0.json"
            )
        )
    )
    assert stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_payloads == [
        REPO_ROOT / "formal/output/stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_cycle01_v0.json"
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT attestation-confirmation-attestation-confirmation-attestation-confirmation-attestation-confirmation-attestation-confirmation scope-boundary payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_scope_boundary_payloads]}"
    )
    stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_payloads = (
        sorted(
            REPO_ROOT.glob(
                "formal/output/stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_cycle01_v0.json"
            )
        )
    )
    assert stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_payloads == [
        REPO_ROOT / "formal/output/stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_cycle01_v0.json"
    ], (
        "STAT row-scaffold aggregation phase admits exactly one STAT attestation-confirmation-attestation-confirmation-attestation-confirmation-attestation-confirmation-attestation-confirmation-attestation scope-boundary payload at this stage: "
        f"{[str(p.relative_to(REPO_ROOT)) for p in stat_nonflip_execution_custody_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_scope_boundary_payloads]}"
    )

    for glob_pattern in DISALLOWED_OUTPUT_GLOBS:
        matches = list(REPO_ROOT.glob(glob_pattern))
        assert not matches, (
            "Premature STAT DER02 object-surface payload(s) detected before row-scaffold aggregation phase "
            f"is cleared: {[str(p.relative_to(REPO_ROOT)) for p in matches]}"
        )

"""Verified Physics Calculator v1 trusted public surface.

The package intentionally imports no historical runner, oracle, candidate
producer, or scientific acceptance module.
"""
from .api import (
    ContractSetV1,
    EvaluatedRunV1,
    JuliaEvidenceV1,
    LeanEvidenceV1,
    assemble_evidence_bundle,
    attach_scientific_authority,
    evaluate_candidate,
    freeze_evidence,
    inspect_receipt,
    load_contract_set,
    replay_evidence,
    run_challenges,
    verify_run,
)
from .contracts import (
    AlgebraicFieldV1,
    CalculationRequestV1,
    CandidatePacketV1,
    PhysicsProfileV1,
    ScientificAuthorityBindingV1,
    VerificationPolicyV1,
)
from .independent import (
    crosscheck_covariance,
    crosscheck_interval,
    crosscheck_ode,
    crosscheck_qmc,
    run_julia_independent,
    run_lean_certificate_checker,
)

__all__ = [
    "AlgebraicFieldV1", "CalculationRequestV1", "CandidatePacketV1", "ContractSetV1",
    "EvaluatedRunV1", "JuliaEvidenceV1", "LeanEvidenceV1", "PhysicsProfileV1",
    "ScientificAuthorityBindingV1", "VerificationPolicyV1", "attach_scientific_authority",
    "assemble_evidence_bundle", "evaluate_candidate", "freeze_evidence", "inspect_receipt", "load_contract_set",
    "replay_evidence", "run_challenges", "verify_run",
    "run_julia_independent", "run_lean_certificate_checker",
    "crosscheck_covariance", "crosscheck_interval", "crosscheck_ode", "crosscheck_qmc",
]

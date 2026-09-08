"""D-01 non-circular binding for actual runtime and qualification evidence."""
from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping, Sequence

from .canonical import digest
from .challenges import ChallengeResultV1, ChallengeSpecV1
from .errors import require


COMMITMENT_FIELDS = (
    "certificate_format_version", "runtime_certificate_hash",
    "computation_id", "calculation_request_hash", "candidate_hash",
    "physics_profile_hash", "verification_policy_hash",
    "source_receipt_set_hash", "graph_hash", "ordered_node_trace_hash",
    "authoritative_roots", "canonical_exact_output_value_hashes",
    "julia_evidence_hash", "mandatory_challenge_spec_set_hash",
    "mandatory_challenge_packet_set_hash", "mandatory_challenge_result_set_hash",
    "challenge_applicability_hash", "type_signature_set_hash",
    "status_ceiling", "scientific_promotion", "product_v1_release",
    "production_activation",
)


def qualification_commitments(
    run: Any,
    julia_evidence: Any,
    challenge_specs: Sequence[ChallengeSpecV1],
    challenge_results: Sequence[ChallengeResultV1],
) -> dict[str, Any]:
    mandatory_hashes = set(run.contracts.policy.mandatory_challenge_hashes)
    specs = sorted((row for row in challenge_specs if row.spec_hash in mandatory_hashes), key=lambda row: row.spec_hash)
    results = sorted((row for row in challenge_results if row.mandatory), key=lambda row: row.challenge_packet_hash)
    require({row.spec_hash for row in specs} == mandatory_hashes, "QUALIFICATION_CHALLENGE_SPEC_SET")
    require(results and all(row.disposition.value == "PASSED" for row in results), "QUALIFICATION_CHALLENGE_RESULT_SET")
    require(julia_evidence is not None, "QUALIFICATION_JULIA_EVIDENCE")
    type_receipts = [row.to_dict() for row in run.evaluation.type_signature_receipts]
    require(len(type_receipts) == len(run.evaluation.receipts), "QUALIFICATION_TYPE_SIGNATURE_COVERAGE")
    certificate = run.certificate
    return {
        "certificate_format_version": "RuntimeCertificateV1+QualificationEnvelopeV1",
        "runtime_certificate_hash": certificate.certificate_hash,
        "computation_id": run.request.computation_id,
        "calculation_request_hash": digest(run.request.to_dict(), "CalculationRequestV1:transport"),
        "candidate_hash": run.candidate.candidate_hash,
        "physics_profile_hash": run.contracts.profile.contract_hash,
        "verification_policy_hash": run.contracts.policy.contract_hash,
        "source_receipt_set_hash": digest(list(certificate.source_receipt_hashes), "ResolvedSourceReceiptSetV1"),
        "graph_hash": certificate.graph_hash,
        "ordered_node_trace_hash": digest(list(certificate.node_trace), "OrderedNodeTraceV1"),
        "authoritative_roots": sorted(certificate.output_value_hashes),
        "canonical_exact_output_value_hashes": dict(sorted(certificate.output_value_hashes.items())),
        "julia_evidence_hash": julia_evidence.receipt_hash,
        "mandatory_challenge_spec_set_hash": digest([row.to_dict() for row in specs], "MandatoryChallengeSpecSetV1"),
        "mandatory_challenge_packet_set_hash": digest([row.challenge_packet_hash for row in results], "MandatoryChallengePacketSetV1"),
        "mandatory_challenge_result_set_hash": digest([row.to_dict() for row in results], "MandatoryChallengeResultSetV1"),
        "challenge_applicability_hash": digest([
            {"challenge_packet_hash": row.challenge_packet_hash, "affected_roots": list(row.affected_roots), "disposition": row.disposition.value}
            for row in results
        ], "ChallengeApplicabilitySetV1"),
        "type_signature_set_hash": digest(type_receipts, "C03RVTypeSignatureReceiptSetV1"),
        "status_ceiling": "DETERMINISTICALLY_RECOMPUTED",
        "scientific_promotion": False,
        "product_v1_release": False,
        "production_activation": False,
    }


@dataclass(frozen=True)
class QualificationEnvelopeV1:
    commitments: Mapping[str, Any]

    def __post_init__(self) -> None:
        require(set(self.commitments) == set(COMMITMENT_FIELDS), "QUALIFICATION_ENVELOPE_FIELDS")
        require(self.commitments["status_ceiling"] == "DETERMINISTICALLY_RECOMPUTED", "QUALIFICATION_STATUS_CEILING")
        require(all(self.commitments[field] is False for field in ("scientific_promotion", "product_v1_release", "production_activation")), "QUALIFICATION_NON_PROMOTION")

    @property
    def envelope_hash(self) -> str:
        return digest(self.to_dict(), "QualificationEnvelopeV1")

    def to_dict(self) -> dict[str, Any]:
        return {"schema_id": "QualificationEnvelopeV1", **dict(self.commitments)}


@dataclass(frozen=True)
class QualificationExpectedContextV1:
    commitments: Mapping[str, Any]

    def __post_init__(self) -> None:
        require(set(self.commitments) == set(COMMITMENT_FIELDS), "QUALIFICATION_CONTEXT_FIELDS")

    def to_dict(self) -> dict[str, Any]:
        return {"schema_id": "QualificationExpectedContextV1", **dict(self.commitments)}


@dataclass(frozen=True)
class LeanQualificationEvidenceV1:
    verifier_id: str
    accepted_envelope_hash: str
    bound_runtime_certificate_hash: str
    receipt_payload: Mapping[str, Any]

    @property
    def accepted_certificate_hash(self) -> str:
        """Compatibility view: the promoted evidence identity is the envelope."""
        return self.accepted_envelope_hash

    @property
    def receipt_hash(self) -> str:
        return digest(self.receipt_payload, "LeanQualificationEnvelopeEvidenceV1")


def build_envelope_and_context(
    run: Any,
    julia_evidence: Any,
    challenge_specs: Sequence[ChallengeSpecV1],
    challenge_results: Sequence[ChallengeResultV1],
) -> tuple[QualificationEnvelopeV1, QualificationExpectedContextV1]:
    # These are deliberately serialized as distinct objects.  The context is
    # supplied to Lean as the independent expectation; it never contains or
    # asserts an accepted envelope identity.
    commitments = qualification_commitments(run, julia_evidence, challenge_specs, challenge_results)
    return QualificationEnvelopeV1(dict(commitments)), QualificationExpectedContextV1(dict(commitments))

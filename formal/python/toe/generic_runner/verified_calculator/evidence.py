"""Receipts, actual runtime certificates, authority attachments, and freeze."""
from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
import os
import platform
import sys
from typing import Any, Mapping, Sequence

from .canonical import canonical_bytes, canonical_data, digest, file_sha256
from .challenges import ChallengePacketV1, ChallengeResultV1, ChallengeSpecV1, coverage_by_root
from .contracts import (
    AuthorityAttachmentV1,
    CalculationRequestV1,
    CandidatePacketV1,
    ExecutionStatus,
    ReplayStatus,
    ScientificAuthorityBindingV1,
    VerificationClass,
)
from .dag import EvaluationResultV1
from .errors import require


FORBIDDEN_THEORY_PROMOTIONS = (
    "SU(5) is physically correct",
    "CCFT is physically correct",
    "The production runner is globally qualified",
)


@dataclass(frozen=True)
class ClaimLedgerEntryV1:
    claim_id: str
    claim_text: str
    evidence_class: VerificationClass
    supporting_receipts: tuple[str, ...]
    limitations: tuple[str, ...]
    does_not_claim: tuple[str, ...] = FORBIDDEN_THEORY_PROMOTIONS

    def __post_init__(self) -> None:
        require(self.claim_id and self.claim_text and self.limitations, "CLAIM_LEDGER_ENTRY")
        require(set(FORBIDDEN_THEORY_PROMOTIONS) <= set(self.does_not_claim), "CLAIM_NON_PROMOTION_MISSING")
        require(all(isinstance(value, str) and len(value) == 64 and all(character in "0123456789abcdef" for character in value) for value in self.supporting_receipts), "CLAIM_SUPPORTING_RECEIPT_HASH")

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "ClaimLedgerEntryV1":
        require(set(value) == {"claim_id", "claim_text", "evidence_class", "supporting_receipts", "limitations", "does_not_claim"}, "CLAIM_LEDGER_SCHEMA")
        return cls(value["claim_id"], value["claim_text"], VerificationClass(value["evidence_class"]), tuple(value["supporting_receipts"]), tuple(value["limitations"]), tuple(value["does_not_claim"]))

    def to_dict(self) -> dict[str, Any]:
        return {"claim_id": self.claim_id, "claim_text": self.claim_text, "evidence_class": self.evidence_class.value, "supporting_receipts": list(self.supporting_receipts), "limitations": list(self.limitations), "does_not_claim": list(self.does_not_claim)}


@dataclass(frozen=True)
class OutputEvidenceV1:
    root_id: str
    value: Mapping[str, Any]
    verification_class: VerificationClass
    python_receipt_hash: str | None
    julia_receipt_hash: str | None
    lean_certificate_hash: str | None
    challenge_coverage: Mapping[str, Any]
    uncertainty_semantics: str | None = None

    def __post_init__(self) -> None:
        if self.verification_class == VerificationClass.VERIFIED_EXACT:
            require(self.python_receipt_hash is not None and self.julia_receipt_hash is not None and self.lean_certificate_hash is not None and self.challenge_coverage.get("complete") is True, "VERIFIED_EXACT_EVIDENCE_INCOMPLETE", self.root_id)
        if self.verification_class == VerificationClass.VERIFIED_ENCLOSURE:
            require(self.uncertainty_semantics == "GUARANTEED_RANGE", "VERIFIED_ENCLOSURE_SEMANTICS", self.root_id)

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "OutputEvidenceV1":
        require(set(value) == {"root_id", "value", "verification_class", "python_receipt_hash", "julia_receipt_hash", "lean_certificate_hash", "challenge_coverage", "uncertainty_semantics"}, "OUTPUT_EVIDENCE_SCHEMA")
        return cls(value["root_id"], dict(value["value"]), VerificationClass(value["verification_class"]), value["python_receipt_hash"], value["julia_receipt_hash"], value["lean_certificate_hash"], dict(value["challenge_coverage"]), value["uncertainty_semantics"])

    def to_dict(self) -> dict[str, Any]:
        return {"root_id": self.root_id, "value": dict(self.value), "verification_class": self.verification_class.value, "python_receipt_hash": self.python_receipt_hash, "julia_receipt_hash": self.julia_receipt_hash, "lean_certificate_hash": self.lean_certificate_hash, "challenge_coverage": dict(self.challenge_coverage), "uncertainty_semantics": self.uncertainty_semantics}


@dataclass(frozen=True)
class RuntimeCertificateV1:
    computation_id: str
    candidate_hash: str
    physics_profile_hash: str
    verification_policy_hash: str
    graph_hash: str
    output_value_hashes: Mapping[str, str]
    output_node_value_digests: Mapping[str, str]
    node_trace: tuple[Mapping[str, Any], ...]
    source_receipt_hashes: tuple[str, ...]
    status_ceiling: str
    scientific_promotion: bool = False

    def __post_init__(self) -> None:
        hashes = (self.computation_id, self.candidate_hash, self.physics_profile_hash, self.verification_policy_hash, self.graph_hash, *self.output_value_hashes.values(), *self.output_node_value_digests.values(), *self.source_receipt_hashes)
        require(all(isinstance(value, str) and len(value) == 64 and all(character in "0123456789abcdef" for character in value) for value in hashes), "RUNTIME_CERTIFICATE_HASH")
        require(self.status_ceiling in {"DETERMINISTICALLY_RECOMPUTED", "CROSSCHECKED_NUMERICAL", "VERIFIED_EXACT", "VERIFIED_ENCLOSURE"}, "CERTIFICATE_STATUS_CEILING")
        require(self.scientific_promotion is False, "COMPUTATION_CANNOT_PROMOTE_SCIENCE")
        require(self.node_trace and len({row.get("node_id") for row in self.node_trace}) == len(self.node_trace), "RUNTIME_CERTIFICATE_TRACE")
        source_hashes = tuple(sorted(digest(row["source_receipt"], "ResolvedSourceReceiptV1") for row in self.node_trace if row.get("source_receipt") is not None))
        require(source_hashes == tuple(self.source_receipt_hashes), "RUNTIME_CERTIFICATE_SOURCE_BINDING")
        require(set(self.output_value_hashes) == set(self.output_node_value_digests), "RUNTIME_CERTIFICATE_OUTPUT_SET")
        trace_by_id = {row["node_id"]: row for row in self.node_trace}
        require(all(root in trace_by_id and trace_by_id[root].get("kind") == "OUTPUT" and trace_by_id[root].get("value_digest") == value_digest for root, value_digest in self.output_node_value_digests.items()), "RUNTIME_CERTIFICATE_OUTPUT_BINDING")

    @property
    def certificate_hash(self) -> str:
        return digest(self.to_dict(), "RuntimeCertificateV1")

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "RuntimeCertificateV1":
        required = {
            "schema_id", "computation_id", "candidate_hash", "physics_profile_hash",
            "verification_policy_hash", "graph_hash", "output_value_hashes",
            "output_node_value_digests", "node_trace", "source_receipt_hashes",
            "status_ceiling", "scientific_promotion",
        }
        require(set(value) == required and value["schema_id"] == "RuntimeCertificateV1", "RUNTIME_CERTIFICATE_SCHEMA")
        return cls(
            value["computation_id"], value["candidate_hash"], value["physics_profile_hash"],
            value["verification_policy_hash"], value["graph_hash"], dict(value["output_value_hashes"]),
            dict(value["output_node_value_digests"]), tuple(dict(row) for row in value["node_trace"]),
            tuple(value["source_receipt_hashes"]), value["status_ceiling"], value["scientific_promotion"],
        )

    def to_dict(self) -> dict[str, Any]:
        return {"schema_id": "RuntimeCertificateV1", "computation_id": self.computation_id, "candidate_hash": self.candidate_hash, "physics_profile_hash": self.physics_profile_hash, "verification_policy_hash": self.verification_policy_hash, "graph_hash": self.graph_hash, "output_value_hashes": dict(self.output_value_hashes), "output_node_value_digests": dict(self.output_node_value_digests), "node_trace": [dict(row) for row in self.node_trace], "source_receipt_hashes": list(self.source_receipt_hashes), "status_ceiling": self.status_ceiling, "scientific_promotion": self.scientific_promotion}


def runtime_environment() -> dict[str, Any]:
    return {"python": platform.python_version(), "implementation": platform.python_implementation(), "platform": platform.platform(), "executable_sha256": file_sha256(Path(sys.executable)), "network_policy": "FORBIDDEN", "offline_enforcement": os.environ.get("VPC_OFFLINE_ENFORCEMENT", "PROCESS_POLICY_ONLY__NONCANONICAL_RELEASE_EVIDENCE")}


def build_runtime_certificate(computation_id: str, candidate_hash: str, profile_hash: str, policy_hash: str, evaluation: EvaluationResultV1) -> RuntimeCertificateV1:
    output_hashes = {root: digest(value.to_dict(), "ExactOutputValueV1") for root, value in evaluation.outputs.items()}
    by_node = {row.node_id: row for row in evaluation.receipts}
    output_node_digests = {root: by_node[root].value_digest for root in evaluation.outputs}
    source_hashes = tuple(sorted(digest(row.source_receipt, "ResolvedSourceReceiptV1") for row in evaluation.receipts if row.source_receipt is not None))
    return RuntimeCertificateV1(computation_id, candidate_hash, profile_hash, policy_hash, evaluation.graph_hash, output_hashes, output_node_digests, tuple(row.to_dict() for row in evaluation.receipts), source_hashes, "DETERMINISTICALLY_RECOMPUTED")


def promote_exact_outputs(
    evaluation: EvaluationResultV1,
    certificate: RuntimeCertificateV1,
    *,
    python_receipt_hash: str,
    julia_output_hashes: Mapping[str, str] | None,
    julia_receipt_hash: str | None,
    lean_accepted_certificate_hash: str | None,
    challenge_results: Sequence[ChallengeResultV1],
    mandatory_packets_by_root: Mapping[str, Sequence[str]],
) -> tuple[OutputEvidenceV1, ...]:
    coverage = coverage_by_root(tuple(evaluation.outputs), mandatory_packets_by_root, challenge_results)
    outputs: list[OutputEvidenceV1] = []
    for root, value in evaluation.outputs.items():
        value_hash = digest(value.to_dict(), "ExactOutputValueV1")
        exact_ready = (
            julia_output_hashes is not None and julia_output_hashes.get(root) == value_hash and julia_receipt_hash is not None
            and lean_accepted_certificate_hash == certificate.certificate_hash
            and coverage[root]["complete"]
            and set(coverage[root]["mandatory_applicable_packet_hashes"]) == {row.challenge_packet_hash for row in challenge_results if row.mandatory and root in row.affected_roots}
        )
        verification_class = VerificationClass.VERIFIED_EXACT if exact_ready else VerificationClass.DETERMINISTICALLY_RECOMPUTED
        outputs.append(OutputEvidenceV1(root, value.to_dict(), verification_class, python_receipt_hash, julia_receipt_hash if exact_ready else None, lean_accepted_certificate_hash if exact_ready else None, coverage[root]))
    return tuple(outputs)


@dataclass(frozen=True)
class VerificationReceiptV1:
    computation_id: str
    candidate_hash: str
    physics_profile_hash: str
    verification_policy_hash: str
    execution_status: ExecutionStatus
    replay_status: ReplayStatus
    environment: Mapping[str, Any]
    source_evidence: tuple[Mapping[str, Any], ...]
    outputs: tuple[OutputEvidenceV1, ...]
    challenge_results: tuple[ChallengeResultV1, ...]
    runtime_certificate_hash: str
    claim_ledger: tuple[ClaimLedgerEntryV1, ...]
    scientific_promotion: bool = False
    product_v1_release: bool = False
    production_activation: bool = False

    def __post_init__(self) -> None:
        require(not self.scientific_promotion and not self.product_v1_release and not self.production_activation, "RECEIPT_NON_PROMOTION")
        require(self.execution_status == ExecutionStatus.SUCCEEDED, "RECEIPT_EXECUTION_STATUS")
        require(len({row.root_id for row in self.outputs}) == len(self.outputs), "OUTPUT_EVIDENCE_DUPLICATE")
        require(len({row.claim_id for row in self.claim_ledger}) == len(self.claim_ledger), "CLAIM_LEDGER_DUPLICATE")

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "VerificationReceiptV1":
        required = {"schema_id", "computation_id", "candidate_hash", "physics_profile_hash", "verification_policy_hash", "execution_status", "replay_status", "environment", "source_evidence", "outputs", "challenge_results", "runtime_certificate_hash", "claim_ledger", "scientific_promotion", "product_v1_release", "production_activation"}
        require(set(value) == required and value["schema_id"] == "VerificationReceiptV1", "VERIFICATION_RECEIPT_SCHEMA")
        return cls(value["computation_id"], value["candidate_hash"], value["physics_profile_hash"], value["verification_policy_hash"], ExecutionStatus(value["execution_status"]), ReplayStatus(value["replay_status"]), dict(value["environment"]), tuple(dict(row) for row in value["source_evidence"]), tuple(OutputEvidenceV1.from_dict(row) for row in value["outputs"]), tuple(ChallengeResultV1.from_dict(row) for row in value["challenge_results"]), value["runtime_certificate_hash"], tuple(ClaimLedgerEntryV1.from_dict(row) for row in value["claim_ledger"]), value["scientific_promotion"], value["product_v1_release"], value["production_activation"])

    @property
    def receipt_hash(self) -> str:
        return digest(self.to_dict(), "VerificationReceiptV1")

    def to_dict(self) -> dict[str, Any]:
        return {"schema_id": "VerificationReceiptV1", "computation_id": self.computation_id, "candidate_hash": self.candidate_hash, "physics_profile_hash": self.physics_profile_hash, "verification_policy_hash": self.verification_policy_hash, "execution_status": self.execution_status.value, "replay_status": self.replay_status.value, "environment": dict(self.environment), "source_evidence": [dict(row) for row in self.source_evidence], "outputs": [row.to_dict() for row in self.outputs], "challenge_results": [row.to_dict() for row in self.challenge_results], "runtime_certificate_hash": self.runtime_certificate_hash, "claim_ledger": [row.to_dict() for row in self.claim_ledger], "scientific_promotion": self.scientific_promotion, "product_v1_release": self.product_v1_release, "production_activation": self.production_activation}


@dataclass(frozen=True)
class FrozenEvidenceBundleV1:
    request: Mapping[str, Any]
    candidate: Mapping[str, Any]
    verification_receipt: Mapping[str, Any]
    runtime_certificate: Mapping[str, Any]
    authority_bindings: tuple[Mapping[str, Any], ...]
    authority_attachments: tuple[Mapping[str, Any], ...]
    dependency_manifests: tuple[Mapping[str, Any], ...]
    challenge_specs: tuple[Mapping[str, Any], ...] = ()
    challenge_packets: tuple[Mapping[str, Any], ...] = ()
    verifier_evidence: tuple[Mapping[str, Any], ...] = ()

    def __post_init__(self) -> None:
        request = CalculationRequestV1.from_dict(self.request)
        candidate = CandidatePacketV1.from_dict(self.candidate)
        receipt = VerificationReceiptV1.from_dict(self.verification_receipt)
        certificate = RuntimeCertificateV1.from_dict(self.runtime_certificate)
        require(candidate.computation_id == request.computation_id == receipt.computation_id == certificate.computation_id, "BUNDLE_COMPUTATION_BINDING")
        require(candidate.candidate_hash == receipt.candidate_hash == certificate.candidate_hash, "BUNDLE_CANDIDATE_BINDING")
        require(request.physics_profile_hash == receipt.physics_profile_hash == certificate.physics_profile_hash, "BUNDLE_PROFILE_BINDING")
        require(request.verification_policy_hash == receipt.verification_policy_hash == certificate.verification_policy_hash, "BUNDLE_POLICY_BINDING")
        require(receipt.runtime_certificate_hash == certificate.certificate_hash, "BUNDLE_CERTIFICATE_BINDING")
        require(set(certificate.output_value_hashes) == {row.root_id for row in receipt.outputs}, "BUNDLE_OUTPUT_SET")
        for output in receipt.outputs:
            require(certificate.output_value_hashes[output.root_id] == digest(output.value, "ExactOutputValueV1"), "BUNDLE_OUTPUT_VALUE_BINDING", output.root_id)

        specs = tuple(ChallengeSpecV1.from_dict(row) for row in self.challenge_specs)
        packets = tuple(ChallengePacketV1.from_dict(row) for row in self.challenge_packets)
        spec_hashes = {row.spec_hash for row in specs}
        packet_hashes = {row.packet_hash for row in packets}
        require(len(spec_hashes) == len(specs) and len(packet_hashes) == len(packets), "BUNDLE_CHALLENGE_DUPLICATE")
        require(all(row.challenge_spec_hash in spec_hashes for row in packets), "BUNDLE_CHALLENGE_SPEC_BINDING")
        require({row.challenge_packet_hash for row in receipt.challenge_results} <= packet_hashes, "BUNDLE_CHALLENGE_RESULT_BINDING")

        bindings = tuple(ScientificAuthorityBindingV1.from_dict(row) for row in self.authority_bindings)
        attachments = tuple(AuthorityAttachmentV1.from_dict(row) for row in self.authority_attachments)
        bindings_by_hash = {row.binding_hash: row for row in bindings}
        require(len(bindings_by_hash) == len(bindings), "BUNDLE_AUTHORITY_DUPLICATE")
        require(all(row.verification_receipt_hash == receipt.receipt_hash and row.authority_binding_hash in bindings_by_hash for row in attachments), "BUNDLE_AUTHORITY_ATTACHMENT_BINDING")
        require(len({row.attachment_hash for row in attachments}) == len(attachments), "BUNDLE_AUTHORITY_ATTACHMENT_DUPLICATE")
        for row in self.dependency_manifests:
            canonical_data(row)
        evidence_by_kind: dict[str, Mapping[str, Any]] = {}
        evidence_domains = {
            "PYTHON_TRUSTED_VERIFICATION": "PythonTrustedVerificationV1",
            "JULIA_INDEPENDENT_RECOMPUTATION": "JuliaIndependentEvidenceV1",
            "LEAN_RUNTIME_CERTIFICATE_CHECK": "LeanRuntimeCertificateEvidenceV1",
        }
        for row in self.verifier_evidence:
            require(set(row) == {"evidence_kind", "receipt_hash", "payload"}, "BUNDLE_VERIFIER_EVIDENCE_SCHEMA")
            kind = row["evidence_kind"]
            require(kind in evidence_domains and kind not in evidence_by_kind, "BUNDLE_VERIFIER_EVIDENCE_KIND")
            payload = row["payload"]
            require(isinstance(payload, Mapping), "BUNDLE_VERIFIER_EVIDENCE_PAYLOAD")
            require(row["receipt_hash"] == digest(payload, evidence_domains[kind]), "BUNDLE_VERIFIER_EVIDENCE_HASH")
            evidence_by_kind[kind] = row
        python_hashes = {row.python_receipt_hash for row in receipt.outputs if row.python_receipt_hash is not None}
        if python_hashes:
            require(len(python_hashes) == 1 and evidence_by_kind.get("PYTHON_TRUSTED_VERIFICATION", {}).get("receipt_hash") in python_hashes, "BUNDLE_PYTHON_EVIDENCE_BINDING")
        julia_hashes = {row.julia_receipt_hash for row in receipt.outputs if row.julia_receipt_hash is not None}
        if julia_hashes:
            require(len(julia_hashes) == 1 and evidence_by_kind.get("JULIA_INDEPENDENT_RECOMPUTATION", {}).get("receipt_hash") in julia_hashes, "BUNDLE_JULIA_EVIDENCE_BINDING")
        lean_hashes = {row.lean_certificate_hash for row in receipt.outputs if row.lean_certificate_hash is not None}
        if lean_hashes:
            lean_payload = evidence_by_kind.get("LEAN_RUNTIME_CERTIFICATE_CHECK", {}).get("payload", {})
            require(lean_hashes == {certificate.certificate_hash} and lean_payload.get("accepted_certificate_hash") == certificate.certificate_hash, "BUNDLE_LEAN_EVIDENCE_BINDING")

    @property
    def bundle_hash(self) -> str:
        return digest(self.to_dict(), "FrozenEvidenceBundleV1")

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "FrozenEvidenceBundleV1":
        required = {
            "schema_id", "request", "candidate", "verification_receipt", "runtime_certificate",
            "authority_bindings", "authority_attachments", "dependency_manifests", "challenge_specs",
            "challenge_packets", "verifier_evidence", "frozen_semantics",
        }
        require(set(value) == required and value["schema_id"] == "FrozenEvidenceBundleV1", "FROZEN_BUNDLE_SCHEMA")
        require(value["frozen_semantics"] == "CONTENT_ADDRESSED_HASH_BOUND_NOT_FILESYSTEM_IMMUTABLE", "FROZEN_BUNDLE_SEMANTICS")
        return cls(
            dict(value["request"]), dict(value["candidate"]), dict(value["verification_receipt"]),
            dict(value["runtime_certificate"]), tuple(dict(row) for row in value["authority_bindings"]),
            tuple(dict(row) for row in value["authority_attachments"]), tuple(dict(row) for row in value["dependency_manifests"]),
            tuple(dict(row) for row in value["challenge_specs"]), tuple(dict(row) for row in value["challenge_packets"]),
            tuple(dict(row) for row in value["verifier_evidence"]),
        )

    def to_dict(self) -> dict[str, Any]:
        return {"schema_id": "FrozenEvidenceBundleV1", "request": dict(self.request), "candidate": dict(self.candidate), "verification_receipt": dict(self.verification_receipt), "runtime_certificate": dict(self.runtime_certificate), "authority_bindings": [dict(row) for row in self.authority_bindings], "authority_attachments": [dict(row) for row in self.authority_attachments], "dependency_manifests": [dict(row) for row in self.dependency_manifests], "challenge_specs": [dict(row) for row in self.challenge_specs], "challenge_packets": [dict(row) for row in self.challenge_packets], "verifier_evidence": [dict(row) for row in self.verifier_evidence], "frozen_semantics": "CONTENT_ADDRESSED_HASH_BOUND_NOT_FILESYSTEM_IMMUTABLE"}


def attach_authority(receipt: VerificationReceiptV1, binding: ScientificAuthorityBindingV1) -> AuthorityAttachmentV1:
    require(receipt.physics_profile_hash == binding.profile_hash, "AUTHORITY_PROFILE_MISMATCH")
    receipt_claims = {row.claim_id for row in receipt.claim_ledger}
    require(set(binding.claim_bindings) <= receipt_claims, "AUTHORITY_UNKNOWN_CLAIM")
    return AuthorityAttachmentV1(receipt.receipt_hash, binding.binding_hash)


def freeze_bundle(bundle: FrozenEvidenceBundleV1, destination: Path, *, max_bytes: int = 256 * 1024 * 1024) -> Path:
    body = canonical_bytes(bundle.to_dict())
    require(len(body) <= max_bytes, "EVIDENCE_SIZE_LIMIT")
    destination.mkdir(parents=True, exist_ok=True)
    path = destination / f"{bundle.bundle_hash}.json"
    if path.exists():
        require(path.read_bytes() == body, "CONTENT_ADDRESS_COLLISION")
    else:
        path.write_bytes(body)
    return path


def replay_bundle(path: Path) -> dict[str, Any]:
    from .canonical import strict_json_file
    value = strict_json_file(path, max_bytes=256 * 1024 * 1024)
    bundle = FrozenEvidenceBundleV1.from_dict(value)
    actual = digest(value, "FrozenEvidenceBundleV1")
    require(path.stem == actual, "FROZEN_BUNDLE_HASH")
    return {
        "replay_status": ReplayStatus.MATCHED.value,
        "bundle_hash": actual,
        "computation_id": CalculationRequestV1.from_dict(bundle.request).computation_id,
        "structural_and_hash_bindings_checked": True,
    }

"""Stable public Python API for verified calculator v1."""
from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping, Sequence

from .canonical import digest, strict_json_file
from .challenges import ChallengeResultV1, ChallengeSpecV1, instantiate, run_challenge, select_targets
from .contracts import AuthorityAttachmentV1, CandidatePacketV1, CalculationRequestV1, ExecutionStatus, PhysicsProfileV1, ReplayStatus, ScientificAuthorityBindingV1, VerificationPolicyV1
from .dag import EvaluationResultV1, ExactDagVerifierV1
from .evidence import ClaimLedgerEntryV1, FrozenEvidenceBundleV1, RuntimeCertificateV1, VerificationReceiptV1, attach_authority as _attach_authority, build_runtime_certificate, freeze_bundle, promote_exact_outputs, replay_bundle, runtime_environment
from .errors import require
from .offline import trusted_offline
from .sources import SourceResolverV1


@dataclass(frozen=True)
class ContractSetV1:
    profile: PhysicsProfileV1
    policy: VerificationPolicyV1
    source_root: Path


@dataclass(frozen=True)
class JuliaEvidenceV1:
    verifier_id: str
    computation_id: str
    candidate_hash: str
    output_value_hashes: Mapping[str, str]
    shared_physics_routines: bool
    arbitrary_code_from_candidate_executed: bool
    receipt_payload: Mapping[str, Any]

    def __post_init__(self) -> None:
        require(not self.shared_physics_routines and not self.arbitrary_code_from_candidate_executed, "JULIA_INDEPENDENCE")

    @property
    def receipt_hash(self) -> str:
        return digest(self.receipt_payload, "JuliaIndependentEvidenceV1")


@dataclass(frozen=True)
class LeanEvidenceV1:
    verifier_id: str
    accepted_certificate_hash: str
    receipt_payload: Mapping[str, Any]

    @property
    def receipt_hash(self) -> str:
        return digest(self.receipt_payload, "LeanRuntimeCertificateEvidenceV1")


@dataclass(frozen=True)
class EvaluatedRunV1:
    contracts: ContractSetV1
    request: CalculationRequestV1
    candidate: CandidatePacketV1
    evaluation: EvaluationResultV1
    certificate: RuntimeCertificateV1


def load_contract_set(profile_path: Path, policy_path: Path, source_root: Path) -> ContractSetV1:
    profile = PhysicsProfileV1.from_dict(strict_json_file(profile_path))
    policy = VerificationPolicyV1.from_dict(strict_json_file(policy_path))
    require(profile_path.is_file() and policy_path.is_file(), "CONTRACT_FILE")
    return ContractSetV1(profile, policy, source_root.resolve(strict=True))


def evaluate_candidate(contracts: ContractSetV1, request: CalculationRequestV1, candidate: CandidatePacketV1) -> EvaluatedRunV1:
    require(request.physics_profile_hash == contracts.profile.contract_hash, "REQUEST_PROFILE_HASH")
    require(request.verification_policy_hash == contracts.policy.contract_hash, "REQUEST_POLICY_HASH")
    require(set(request.requested_roots) == set(contracts.profile.output_roots), "REQUEST_ROOTS")
    require(candidate.computation_id == request.computation_id, "CANDIDATE_COMPUTATION_ID")
    allowed_budgets = {"total_seconds", "python_seconds", "julia_seconds", "lean_seconds", "challenge_seconds"}
    require(set(request.execution_budgets) <= allowed_budgets, "EXECUTION_BUDGET_KIND")
    require(request.execution_budgets.get("total_seconds", contracts.policy.resource_limits.trusted_total_seconds) <= contracts.policy.resource_limits.trusted_total_seconds, "TRUSTED_TOTAL_RUNTIME_BUDGET")
    require(all(value <= contracts.policy.resource_limits.trusted_route_seconds for key, value in request.execution_budgets.items() if key != "total_seconds"), "TRUSTED_ROUTE_RUNTIME_BUDGET")
    with trusted_offline():
        resolver = SourceResolverV1(contracts.source_root, contracts.profile.source_declarations, contracts.policy.resource_limits)
        evaluation = ExactDagVerifierV1(contracts.profile, resolver, contracts.policy.resource_limits).verify(candidate)
    certificate = build_runtime_certificate(request.computation_id, candidate.candidate_hash, contracts.profile.contract_hash, contracts.policy.contract_hash, evaluation)
    return EvaluatedRunV1(contracts, request, candidate, evaluation, certificate)


def run_challenges(run: EvaluatedRunV1, specs: Sequence[ChallengeSpecV1]) -> tuple[ChallengeResultV1, ...]:
    verifier = lambda candidate: evaluate_candidate(run.contracts, run.request, candidate).evaluation
    results: list[ChallengeResultV1] = []
    for spec in specs:
        for target in select_targets(spec, run.candidate):
            packet = instantiate(spec, run.candidate, run.evaluation.graph_hash, target)
            results.append(run_challenge(spec, packet, run.candidate, verifier))
    return tuple(results)


def verify_run(
    run: EvaluatedRunV1,
    *,
    challenge_results: Sequence[ChallengeResultV1] = (),
    challenge_specs: Sequence[ChallengeSpecV1] = (),
    julia_evidence: JuliaEvidenceV1 | None = None,
    lean_evidence: LeanEvidenceV1 | None = None,
) -> VerificationReceiptV1:
    if julia_evidence is not None:
        require(julia_evidence.verifier_id == run.contracts.policy.julia_verifier, "JULIA_VERIFIER_ID")
        require(julia_evidence.computation_id == run.request.computation_id and julia_evidence.candidate_hash == run.candidate.candidate_hash, "JULIA_EVIDENCE_BINDING")
    if lean_evidence is not None:
        require(lean_evidence.verifier_id == run.contracts.policy.lean_verifier, "LEAN_VERIFIER_ID")
    specs_by_hash = {row.spec_hash: row for row in challenge_specs}
    require(len(specs_by_hash) == len(challenge_specs), "CHALLENGE_SPEC_DUPLICATE")
    if challenge_specs:
        recomputed_challenges = run_challenges(run, challenge_specs)
        if challenge_results:
            require(
                [row.to_dict() for row in challenge_results] == [row.to_dict() for row in recomputed_challenges],
                "CHALLENGE_RESULT_NOT_REPRODUCIBLE",
            )
        challenge_results = recomputed_challenges
    else:
        require(not challenge_results, "CHALLENGE_RESULT_WITHOUT_SPEC")
    mandatory_hashes = set(run.contracts.policy.mandatory_challenge_hashes)
    mandatory_packets_by_root: dict[str, list[str]] = {root: [] for root in run.evaluation.outputs}
    if mandatory_hashes:
        require(set(specs_by_hash) >= mandatory_hashes, "MANDATORY_CHALLENGE_SPEC_MISSING")
        expected_packets = []
        for spec_hash in sorted(mandatory_hashes):
            spec = specs_by_hash[spec_hash]
            targets = select_targets(spec, run.candidate)
            require(targets, "MANDATORY_CHALLENGE_NOT_APPLICABLE", spec.challenge_id)
            for target in targets:
                packet = instantiate(spec, run.candidate, run.evaluation.graph_hash, target)
                expected_packets.append(packet.packet_hash)
                for root in packet.affected_roots:
                    mandatory_packets_by_root[root].append(packet.packet_hash)
        observed_packets = {row.challenge_packet_hash for row in challenge_results if row.mandatory}
        require(observed_packets == set(expected_packets), "MANDATORY_CHALLENGE_EXECUTION_INCOMPLETE")
    python_payload = {"verifier": run.contracts.policy.python_verifier, "certificate": run.certificate.to_dict(), "node_receipts": [row.to_dict() for row in run.evaluation.receipts]}
    python_hash = digest(python_payload, "PythonTrustedVerificationV1")
    outputs = promote_exact_outputs(
        run.evaluation, run.certificate, python_receipt_hash=python_hash,
        julia_output_hashes=julia_evidence.output_value_hashes if julia_evidence else None,
        julia_receipt_hash=julia_evidence.receipt_hash if julia_evidence else None,
        lean_accepted_certificate_hash=lean_evidence.accepted_certificate_hash if lean_evidence else None,
        challenge_results=challenge_results, mandatory_packets_by_root=mandatory_packets_by_root,
    )
    source_evidence = tuple(row.source_receipt for row in run.evaluation.receipts if row.source_receipt is not None)
    claims = tuple(
        ClaimLedgerEntryV1(
            run.contracts.profile.output_claims[output.root_id],
            f"Under profile {run.contracts.profile.profile_id}, output {output.root_id} equals the receipt-bound canonical value.",
            output.verification_class,
            tuple(item for item in (output.python_receipt_hash, output.julia_receipt_hash, output.lean_certificate_hash) if item),
            ("Computational statement under frozen inputs, conventions, operations, and policy.", "Does not establish that Nature uses the profile assumptions."),
        ) for output in outputs
    )
    return VerificationReceiptV1(
        run.request.computation_id, run.candidate.candidate_hash, run.contracts.profile.contract_hash, run.contracts.policy.contract_hash,
        ExecutionStatus.SUCCEEDED, ReplayStatus.NOT_RUN, runtime_environment(), source_evidence, outputs, tuple(challenge_results),
        run.certificate.certificate_hash, claims,
    )


def attach_scientific_authority(receipt: VerificationReceiptV1, binding: ScientificAuthorityBindingV1):
    return _attach_authority(receipt, binding)


def assemble_evidence_bundle(
    run: EvaluatedRunV1,
    receipt: VerificationReceiptV1,
    *,
    challenge_specs: Sequence[ChallengeSpecV1] = (),
    julia_evidence: JuliaEvidenceV1 | None = None,
    lean_evidence: LeanEvidenceV1 | None = None,
    dependency_manifests: Sequence[Mapping[str, Any]] = (),
    authority_bindings: Sequence[ScientificAuthorityBindingV1] = (),
    authority_attachments: Sequence[AuthorityAttachmentV1] = (),
) -> FrozenEvidenceBundleV1:
    require(receipt.computation_id == run.request.computation_id and receipt.candidate_hash == run.candidate.candidate_hash, "BUNDLE_RUN_RECEIPT_BINDING")
    packets = []
    packet_hashes = {row.challenge_packet_hash for row in receipt.challenge_results}
    for spec in challenge_specs:
        for target in select_targets(spec, run.candidate):
            packet = instantiate(spec, run.candidate, run.evaluation.graph_hash, target)
            if packet.packet_hash in packet_hashes:
                packets.append(packet.to_dict())
    require({digest(row, "ChallengePacketV1") for row in packets} == packet_hashes, "BUNDLE_CHALLENGE_PACKET_MISSING")
    python_payload = {
        "verifier": run.contracts.policy.python_verifier,
        "certificate": run.certificate.to_dict(),
        "node_receipts": [row.to_dict() for row in run.evaluation.receipts],
    }
    verifier_evidence: list[Mapping[str, Any]] = [{
        "evidence_kind": "PYTHON_TRUSTED_VERIFICATION",
        "receipt_hash": digest(python_payload, "PythonTrustedVerificationV1"),
        "payload": python_payload,
    }]
    if julia_evidence is not None:
        verifier_evidence.append({"evidence_kind": "JULIA_INDEPENDENT_RECOMPUTATION", "receipt_hash": julia_evidence.receipt_hash, "payload": dict(julia_evidence.receipt_payload)})
    if lean_evidence is not None:
        verifier_evidence.append({"evidence_kind": "LEAN_RUNTIME_CERTIFICATE_CHECK", "receipt_hash": lean_evidence.receipt_hash, "payload": dict(lean_evidence.receipt_payload)})
    return FrozenEvidenceBundleV1(
        run.request.to_dict(), run.candidate.to_dict(), receipt.to_dict(), run.certificate.to_dict(),
        tuple(row.to_dict() for row in authority_bindings), tuple(row.to_dict() for row in authority_attachments),
        tuple(dict(row) for row in dependency_manifests), tuple(row.to_dict() for row in challenge_specs),
        tuple(packets), tuple(verifier_evidence),
    )


def freeze_evidence(bundle: FrozenEvidenceBundleV1, destination: Path) -> Path:
    return freeze_bundle(bundle, destination)


def replay_evidence(path: Path) -> dict[str, Any]:
    return replay_bundle(path)


def inspect_receipt(receipt: VerificationReceiptV1) -> dict[str, Any]:
    return {"receipt_hash": receipt.receipt_hash, "computation_id": receipt.computation_id, "execution_status": receipt.execution_status.value, "replay_status": receipt.replay_status.value, "outputs": [{"root_id": row.root_id, "verification_class": row.verification_class.value, "challenge_complete": row.challenge_coverage.get("complete", False)} for row in receipt.outputs], "scientific_promotion": receipt.scientific_promotion, "product_v1_release": receipt.product_v1_release, "production_activation": receipt.production_activation}

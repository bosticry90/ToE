"""Fail-closed internal milestone and all-or-nothing v1 release gates."""
from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping, Sequence

from .canonical import digest
from .contracts import ScientificAuthorityBindingV1, VerificationClass
from .evidence import VerificationReceiptV1
from .errors import require


C03_RV_ROOTS = (
    "C03.OUTPUT.PHYSICAL_COEFFICIENT",
    "C03.OUTPUT.EVANESCENT_COORDINATES",
    "C03.OUTPUT.EVANESCENT_STATE",
    "RV01.OUTPUT.PHYSICAL_COEFFICIENT", "RV01.OUTPUT.EVANESCENT_STATE",
    "RV02.OUTPUT.PHYSICAL_COEFFICIENT", "RV02.OUTPUT.EVANESCENT_STATE",
    "RV03.OUTPUT.PHYSICAL_COEFFICIENT", "RV03.OUTPUT.EVANESCENT_STATE", "RV03.OUTPUT.SOURCE_CHANNEL",
    "RV04.OUTPUT.PHYSICAL_COEFFICIENT", "RV04.OUTPUT.EVANESCENT_STATE",
    "RV05.OUTPUT.PHYSICAL_COEFFICIENT", "RV05.OUTPUT.EVANESCENT_STATE",
    "RV06.OUTPUT.PHYSICAL_COEFFICIENT", "RV06.OUTPUT.EVANESCENT_STATE",
)


def _is_sha256(value: Any) -> bool:
    return isinstance(value, str) and len(value) == 64 and all(character in "0123456789abcdef" for character in value)


@dataclass(frozen=True)
class InternalMilestoneV1:
    milestone_id: str
    supporting_receipt_hashes: tuple[str, ...]
    gates: Mapping[str, Any]
    scientific_promotion: bool = False
    product_v1_release: bool = False
    production_activation: bool = False

    def __post_init__(self) -> None:
        require(not self.scientific_promotion and not self.product_v1_release and not self.production_activation, "INTERNAL_MILESTONE_NON_PROMOTION")
        require(all(value is True for value in self.gates.values()), "MILESTONE_GATE_FAILED")
        require(self.supporting_receipt_hashes and all(_is_sha256(value) for value in self.supporting_receipt_hashes), "MILESTONE_RECEIPT_HASH")

    @property
    def milestone_hash(self) -> str:
        return digest(self.to_dict(), "InternalMilestoneV1")

    def to_dict(self) -> dict[str, Any]:
        return {"schema_id": "InternalMilestoneV1", "milestone_id": self.milestone_id, "supporting_receipt_hashes": list(self.supporting_receipt_hashes), "gates": dict(self.gates), "scientific_promotion": self.scientific_promotion, "product_v1_release": self.product_v1_release, "production_activation": self.production_activation}


def exact_c03_rv_milestone(
    receipt: VerificationReceiptV1,
    *,
    replay_bundle_hashes: Sequence[str],
    derived_node_census: Mapping[str, Any],
    challenge_registry_census: Mapping[str, Any],
    authority_binding: ScientificAuthorityBindingV1,
) -> InternalMilestoneV1:
    outputs = {row.root_id: row for row in receipt.outputs}
    claims = {row.claim_id for row in receipt.claim_ledger}
    gates = {
        "seven_records_sixteen_roots": set(outputs) == set(C03_RV_ROOTS) and len(outputs) == 16,
        "all_roots_verified_exact": all(row.verification_class == VerificationClass.VERIFIED_EXACT for row in outputs.values()),
        "python_julia_lean_bound_per_root": all(row.python_receipt_hash and row.julia_receipt_hash and row.lean_certificate_hash for row in outputs.values()),
        "mandatory_challenges_complete_per_root": all(row.challenge_coverage.get("complete") is True for row in outputs.values()),
        "derived_corruption_census_complete": derived_node_census.get("unexpected_survivors") == [] and derived_node_census.get("challenged_count") == derived_node_census.get("derived_node_count") and derived_node_census.get("c03_intermediate_challenges", 0) >= 38,
        "historical_falsifier_registry_complete": challenge_registry_census.get("unclassified") == [] and challenge_registry_census.get("mandatory_count", 0) > 0,
        "two_isolated_replays_match": len(replay_bundle_hashes) == 2 and replay_bundle_hashes[0] == replay_bundle_hashes[1],
        "claim_authority_distinctions_preserved": (
            authority_binding.profile_hash == receipt.physics_profile_hash
            and set(authority_binding.claim_bindings) == claims
            and authority_binding.calculator_profile_review_status == "SCIENTIFIC_REQUALIFICATION_NOT_EARNED"
            and authority_binding.claim_bindings.get("C03.claim.PHYSICAL_COEFFICIENT", None) is not None
            and authority_binding.claim_bindings["C03.claim.PHYSICAL_COEFFICIENT"].authority_state == "TERMINALLY_ADJUDICATED"
            and authority_binding.claim_bindings.get("RV03.claim.SOURCE_CHANNEL", None) is not None
            and authority_binding.claim_bindings["RV03.claim.SOURCE_CHANNEL"].historical_label == "WRONG_SOURCE_CHANNEL_NO_SCALAR_MAP"
        ),
        "receipt_non_promotion": not receipt.scientific_promotion and not receipt.product_v1_release and not receipt.production_activation,
    }
    return InternalMilestoneV1("C03_RV_COMPUTATION_VERIFIED_EXACT_PRE_RELEASE", (receipt.receipt_hash,), gates)


@dataclass(frozen=True)
class ProductReleaseV1:
    version: str
    milestone_hashes: Mapping[str, str]
    generated_dependency_closure_hash: str
    platform_receipts: Mapping[str, str]
    release_gates: Mapping[str, bool]
    scientific_promotion: bool = False
    production_activation: bool = False
    product_v1_release: bool = True

    def __post_init__(self) -> None:
        require(self.version == "1.0.0" and self.product_v1_release, "PRODUCT_RELEASE_VERSION")
        require(not self.scientific_promotion and not self.production_activation, "PRODUCT_RELEASE_NON_PROMOTION")
        require(all(self.release_gates.values()), "PRODUCT_RELEASE_GATE_FAILED")
        require(set(self.milestone_hashes) == {"exact_c03_rv", "interval", "ode_rge", "uncertainty", "plugin_boundary", "synthetic_profile"}, "PRODUCT_MILESTONE_SET")
        require(set(self.platform_receipts) == {"windows", "linux"}, "PLATFORM_RECEIPT_SET")
        require(_is_sha256(self.generated_dependency_closure_hash) and all(_is_sha256(value) for value in self.milestone_hashes.values()) and all(_is_sha256(value) for value in self.platform_receipts.values()), "PRODUCT_RELEASE_HASH_BINDING")

    @property
    def release_hash(self) -> str:
        return digest(self.to_dict(), "VerifiedCalculatorProductReleaseV1")

    def to_dict(self) -> dict[str, Any]:
        return {"schema_id": "VerifiedCalculatorProductReleaseV1", "version": self.version, "milestone_hashes": dict(self.milestone_hashes), "generated_dependency_closure_hash": self.generated_dependency_closure_hash, "platform_receipts": dict(self.platform_receipts), "release_gates": dict(self.release_gates), "scientific_promotion": self.scientific_promotion, "production_activation": self.production_activation, "product_v1_release": self.product_v1_release}


def interval_milestone(crosscheck_receipt: Mapping[str, Any]) -> InternalMilestoneV1:
    gates = {
        "python_and_julia_certificate_checkers": set(crosscheck_receipt) >= {"python_checker", "julia_checker"},
        "strict_enclosure_class": crosscheck_receipt.get("verification_class") == "VERIFIED_ENCLOSURE",
        "guaranteed_containment_claim": "guarantee" in crosscheck_receipt,
        "scientific_non_promotion": crosscheck_receipt.get("scientific_promotion") is False,
    }
    return InternalMilestoneV1("VERIFIED_CALCULATOR_INTERVAL_SUBSYSTEM_ACCEPTED_PRE_RELEASE", (digest(crosscheck_receipt, "EnclosureCrosscheckReceiptV1"),), gates)


def ode_rge_milestone(ode_receipt: Mapping[str, Any], rge_receipt: Mapping[str, Any]) -> InternalMilestoneV1:
    gates = {
        "ode_crosschecked": ode_receipt.get("verification_class") == "CROSSCHECKED_NUMERICAL" and ode_receipt.get("system_kind") == "ODE",
        "rge_crosschecked": rge_receipt.get("verification_class") == "CROSSCHECKED_NUMERICAL" and rge_receipt.get("system_kind") == "RGE",
        "declarative_no_callback": all(row.get("python", {}).get("arbitrary_callback_executed") is False and row.get("julia", {}).get("arbitrary_callback_executed") is False for row in (ode_receipt, rge_receipt)),
        "no_rigorous_inflation": all(row.get("rigorous_enclosure") is False for row in (ode_receipt, rge_receipt)),
        "scientific_non_promotion": all(row.get("scientific_promotion") is False for row in (ode_receipt, rge_receipt)),
    }
    return InternalMilestoneV1("VERIFIED_CALCULATOR_ODE_RGE_SUBSYSTEM_ACCEPTED_PRE_RELEASE", (digest(ode_receipt, "NumericalCrosscheckReceiptV1"), digest(rge_receipt, "NumericalCrosscheckReceiptV1")), gates)


def uncertainty_milestone(range_receipt: Mapping[str, Any], covariance_receipt: Mapping[str, Any], qmc_receipt: Mapping[str, Any]) -> InternalMilestoneV1:
    gates = {
        "guaranteed_range_distinct": range_receipt.get("verification_class") == "VERIFIED_ENCLOSURE",
        "local_covariance_distinct": covariance_receipt.get("semantics") == "LOCAL_LINEAR_COVARIANCE" and covariance_receipt.get("rigorous_enclosure") is False,
        "sample_distribution_distinct": qmc_receipt.get("semantics") == "SAMPLED_DISTRIBUTION_ESTIMATE" and qmc_receipt.get("rigorous_enclosure") is False,
        "qmc_input_set_cross_language_identical": qmc_receipt.get("python", {}).get("generated_input_set_sha256") == qmc_receipt.get("julia", {}).get("generated_input_set_sha256"),
        "scientific_non_promotion": all(row.get("scientific_promotion") is False for row in (range_receipt, covariance_receipt, qmc_receipt)),
    }
    return InternalMilestoneV1("VERIFIED_CALCULATOR_UNCERTAINTY_SUBSYSTEM_ACCEPTED_PRE_RELEASE", (digest(range_receipt, "EnclosureCrosscheckReceiptV1"), digest(covariance_receipt, "NumericalCrosscheckReceiptV1"), digest(qmc_receipt, "NumericalCrosscheckReceiptV1")), gates)


def plugin_boundary_milestone(test_receipts: Sequence[Mapping[str, Any]]) -> InternalMilestoneV1:
    gates = {
        "explicit_unsafe_flag": any(row.get("unsafe_flag_required") is True for row in test_receipts),
        "candidate_only": all(row.get("trusted_receipt_emitted") is False for row in test_receipts),
        "no_os_sandbox_claim": all(row.get("os_sandbox_claimed") is False for row in test_receipts),
        "promotion_attempts_rejected": any(row.get("self_promotion_rejected") is True for row in test_receipts),
    }
    return InternalMilestoneV1("VERIFIED_CALCULATOR_UNSAFE_PLUGIN_BOUNDARY_ACCEPTED_PRE_RELEASE", tuple(digest(row, "UnsafePluginBoundaryTestV1") for row in test_receipts), gates)


def synthetic_profile_milestone(receipt: VerificationReceiptV1) -> InternalMilestoneV1:
    gates = {
        "synthetic_profile_verified": bool(receipt.outputs) and all(row.verification_class == VerificationClass.VERIFIED_EXACT for row in receipt.outputs),
        "not_a_second_physics_domain": all(not row.claim_id.startswith(("C03", "RV", "SU5", "CCFT")) for row in receipt.claim_ledger),
        "scientific_non_promotion": receipt.scientific_promotion is False,
    }
    return InternalMilestoneV1("VERIFIED_CALCULATOR_SYNTHETIC_PROFILE_ACCEPTED_PRE_RELEASE", (receipt.receipt_hash,), gates)

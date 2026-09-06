"""Execute and explicitly freeze one C03/RV exact qualification replay.

This orchestration module is outside the trusted package because it invokes
the untrusted historical-proposal adapter and attaches existing authority.  It
cannot promote scientific authority, product release, or production use.
"""
from __future__ import annotations

import argparse
from pathlib import Path
from typing import Any

from formal.python.toe.generic_runner.verified_calculator import api
from formal.python.toe.generic_runner.verified_calculator.c03_rv_policy import challenge_registry_census, mandatory_challenge_specs
from formal.python.toe.generic_runner.verified_calculator.canonical import canonical_json
from formal.python.toe.generic_runner.verified_calculator.contracts import ChallengeDisposition, VerificationClass
from formal.python.toe.generic_runner.verified_calculator.dependency_closure import generate_dependency_closure, validate_dependency_closure
from formal.python.toe.generic_runner.verified_calculator.errors import require
from formal.python.toe.generic_runner.verified_calculator.independent import run_julia_independent, run_lean_certificate_checker
from formal.python.toe.generic_runner.verified_calculator_c03_rv_candidate_v1 import candidate
from formal.python.toe.generic_runner.verified_calculator_c03_rv_census_v1 import scientific_authority_binding


REPOSITORY_ROOT = Path(__file__).resolve().parents[4]
DEFAULT_FREEZE_DIRECTORY = REPOSITORY_ROOT / "formal" / "docs" / "release" / "verified_calculator" / "c03_rv_exact"


def qualify(destination: Path = DEFAULT_FREEZE_DIRECTORY) -> dict[str, Any]:
    profile, policy, request, packet = candidate(REPOSITORY_ROOT)
    contracts = api.ContractSetV1(profile, policy, REPOSITORY_ROOT)
    run = api.evaluate_candidate(contracts, request, packet)
    require(len(run.evaluation.receipts) == 207 and len(run.evaluation.outputs) == 16, "C03_RV_QUALIFICATION_CENSUS")

    julia = run_julia_independent(run)
    lean = run_lean_certificate_checker(run)
    specs = mandatory_challenge_specs()
    receipt = api.verify_run(run, challenge_specs=specs, julia_evidence=julia, lean_evidence=lean)
    require(all(row.disposition == ChallengeDisposition.PASSED for row in receipt.challenge_results), "C03_RV_CHALLENGE_SURVIVOR")
    require(all(row.verification_class == VerificationClass.VERIFIED_EXACT for row in receipt.outputs), "C03_RV_OUTPUT_NOT_VERIFIED_EXACT")

    authority = scientific_authority_binding(profile.contract_hash)
    attachment = api.attach_scientific_authority(receipt, authority)
    closure = generate_dependency_closure(REPOSITORY_ROOT)
    validate_dependency_closure(closure)
    bundle = api.assemble_evidence_bundle(
        run,
        receipt,
        challenge_specs=specs,
        julia_evidence=julia,
        lean_evidence=lean,
        dependency_manifests=(closure,),
        authority_bindings=(authority,),
        authority_attachments=(attachment,),
    )
    path = api.freeze_evidence(bundle, destination)
    replay = api.replay_evidence(path)
    derived_results = [row for row in receipt.challenge_results if row.challenge_id == "ALL_DERIVED_INTERMEDIATE_CORRUPTION"]
    require(len(derived_results) == 160, "C03_RV_DERIVED_CHALLENGE_CENSUS")
    return {
        "schema_id": "C03RVExactQualificationReplayV1",
        "computation_id": request.computation_id,
        "candidate_hash": packet.candidate_hash,
        "profile_hash": profile.contract_hash,
        "policy_hash": policy.contract_hash,
        "graph_hash": run.evaluation.graph_hash,
        "runtime_certificate_hash": run.certificate.certificate_hash,
        "verification_receipt_hash": receipt.receipt_hash,
        "frozen_bundle_hash": bundle.bundle_hash,
        "frozen_bundle_path": path.resolve().relative_to(REPOSITORY_ROOT).as_posix(),
        "replay_status": replay["replay_status"],
        "source_node_count": 31,
        "derived_node_count": 160,
        "output_root_count": 16,
        "trusted_physics_operation_count": 19,
        "challenge_result_count": len(receipt.challenge_results),
        "derived_corruption_challenged_count": len(derived_results),
        "derived_corruption_unexpected_survivors": [row.injection_node for row in derived_results if row.disposition != ChallengeDisposition.PASSED],
        "c03_intermediate_challenges": sum(row.injection_node.startswith("C03.") for row in derived_results),
        "challenge_registry": challenge_registry_census(),
        "dependency_closure_hash": closure["closure_hash"],
        "calculator_profile_review_status": authority.calculator_profile_review_status,
        "scientific_promotion": False,
        "product_v1_release": False,
        "production_activation": False,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--freeze-directory", type=Path, default=DEFAULT_FREEZE_DIRECTORY)
    arguments = parser.parse_args()
    print(canonical_json(qualify(arguments.freeze_directory)))


if __name__ == "__main__":
    main()

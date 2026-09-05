from __future__ import annotations

from copy import deepcopy
from dataclasses import replace
from decimal import Decimal
from fractions import Fraction
import hashlib
import importlib
import json
import math
import os
from pathlib import Path
import shutil
import socket
import subprocess
import sys

import pytest
from jsonschema import Draft202012Validator

from formal.python.toe.generic_runner.verified_calculator import api
from formal.python.toe.generic_runner.verified_calculator.canonical import canonical_bytes, digest, strict_json_bytes
from formal.python.toe.generic_runner.verified_calculator.challenges import ChallengePacketV1, ChallengeSpecV1, apply_mutation, instantiate
from formal.python.toe.generic_runner.verified_calculator.contracts import (
    AlgebraicFieldV1,
    CalculationRequestV1,
    CandidatePacketV1,
    ChallengeDisposition,
    ClaimAuthorityBindingV1,
    DimensionSystemV1,
    PhysicsProfileV1,
    QMCPolicyV1,
    ResourceLimitsV1,
    ScientificAuthorityBindingV1,
    VerificationClass,
    VerificationPolicyV1,
)
from formal.python.toe.generic_runner.verified_calculator.dimensions import DimensionQuotientV1, DimensionVectorV1
from formal.python.toe.generic_runner.verified_calculator.dependency_closure import generate_dependency_closure, validate_dependency_closure
from formal.python.toe.generic_runner.verified_calculator.evidence import FrozenEvidenceBundleV1, attach_authority, replay_bundle
from formal.python.toe.generic_runner.verified_calculator.errors import CalculatorError
from formal.python.toe.generic_runner.verified_calculator.exact import ExactRuntimeV1
from formal.python.toe.generic_runner.verified_calculator.independent import (
    crosscheck_covariance,
    crosscheck_interval,
    crosscheck_ode,
    crosscheck_qmc,
    LEAN_CHECKER,
    _julia_executable,
    run_julia_independent,
    run_lean_certificate_checker,
)
from formal.python.toe.generic_runner.verified_calculator.milestones import (
    ProductReleaseV1,
    exact_c03_rv_milestone,
    interval_milestone,
    ode_rge_milestone,
    plugin_boundary_milestone,
    synthetic_profile_milestone,
    uncertainty_milestone,
)
from formal.python.toe.generic_runner.verified_calculator.numerics import (
    covariance_propagation,
    evaluate_interval_certificate,
    qmc_ensemble,
    sobol_uint32,
    solve_declarative_ode,
)
from formal.python.toe.generic_runner.verified_calculator.offline import trusted_offline
from formal.python.toe.generic_runner.verified_calculator.plugin import run_unsafe_plugin
from formal.python.toe.generic_runner.verified_calculator.sources import SourceResolverV1


def _cross_language_tools_available() -> bool:
    julia = _julia_executable()
    return (julia.is_file() or shutil.which(str(julia)) is not None) and LEAN_CHECKER.is_file()


cross_language = pytest.mark.skipif(
    not _cross_language_tools_available() and os.environ.get("VPC_REQUIRE_CROSS_LANGUAGE") != "1",
    reason="Julia and built Lean runtime-certificate checker are exercised in the dedicated calculator matrix",
)


def _value(runtime: ExactRuntimeV1, text: str) -> dict:
    return runtime.parse_rational_text(text).to_dict()


def _value_type(dimension=("0", "0"), semantic="SCALAR") -> dict:
    return {
        "mathematical_kind": "EXACT_SCALAR",
        "semantic_type": semantic,
        "dimension": list(dimension),
        "unit_convention": "SYNTHETIC_NATURAL",
        "index_spaces": [],
        "representation_tags": [],
        "domain": {"kind": "EXACT"},
    }


def _numerical_policy() -> dict:
    return {
        "exact_language": "CANONICAL_MATH_V1_RATIONAL_FUNCTIONS",
        "enclosure_promotion": "INDEPENDENT_CERTIFICATE_REQUIRED",
        "floating_agreement_ceiling": "CROSSCHECKED_NUMERICAL",
        "trusted_ode_rhs": "DECLARATIVE_IR_ONLY",
        "ode_python_methods": ["DOP853", "RK45", "Radau"],
        "ode_julia_method": "Vern9",
        "ode_rtol_ceiling": "1/1000",
        "ode_atol_ceiling": "1/1000",
        "uncertainty_semantics": ["GUARANTEED_RANGE", "LOCAL_LINEAR_COVARIANCE", "SAMPLED_DISTRIBUTION_ESTIMATE"],
    }


def _synthetic(tmp_path: Path):
    runtime = ExactRuntimeV1(AlgebraicFieldV1.rational(), ("x",))
    source_value = _value(runtime, "2")
    source_raw = canonical_bytes({"value": source_value})
    (tmp_path / "source.json").write_bytes(source_raw)
    source_hash = hashlib.sha256(source_raw).hexdigest()
    profile = PhysicsProfileV1(
        "SYNTHETIC_NON_PHYSICS_PROFILE_v1",
        ("x",),
        AlgebraicFieldV1.rational(),
        DimensionSystemV1(("ENERGY", "TIME"), "RATIONAL", (("1", "1"),)),
        ("SYNTHETIC_NATURAL",),
        ("SCALAR",),
        {},
        (),
        ({"path": "source.json", "sha256": source_hash, "byte_size": len(source_raw), "media_type": "application/json"},),
        ("SOURCE_DECODE", "LITERAL", "MUL", "ADD", "OUTPUT_BIND"),
        ("OUTPUT.RESULT",),
        {"OUTPUT.RESULT": "SYNTHETIC.result"},
    )
    challenge = ChallengeSpecV1(
        "SYNTHETIC_CORRUPT_ONE", {"node_id": "ONE"}, {"kind": "REPLACE_CLAIMED_VALUE", "value": _value(runtime, "0")},
        "Every claimed intermediate is recomputed", "VERIFIER_REJECTS", {"roots": "ANCESTRY"},
        "FROZEN_BASELINE_DESCENDANTS_ONLY", {"kind": "FIXED", "seed": 7}, "synthetic control", "2026-09-05T00:00:00Z", True,
    )
    policy = VerificationPolicyV1(
        "VPC_SYNTHETIC_POLICY_v1", "2026-09-05T23:59:59Z", "python-verified-calculator-v1",
        "julia-nemo-verified-calculator-v1", "lean-runtime-certificate-v1", (challenge.spec_hash,),
        _numerical_policy(),
        QMCPolicyV1("SOBOL", "VPC_SOBOL_UINT32_V1", "VPC_SOBOL_2D_BRATLEY_FOX_BASE_V1", "DIGITAL_XOR_SHA256_V1", "GRAY_CODE_INDEX_ORDER", "FIRST_N_FROM_INDEX_ZERO"),
    )
    request = CalculationRequestV1(profile.contract_hash, policy.contract_hash, {"case": "synthetic"}, profile.output_roots, {"total_seconds": 60})
    reference = {"type": "JsonPointerValueRef", "artifact_path": "source.json", "artifact_sha256": source_hash, "pointer": "/value"}
    nodes = [
        {"node_id": "SOURCE.TWO", "kind": "SOURCE", "operation": "SOURCE_DECODE", "parents": [], "parameters": {"reference": reference}, "value_type": _value_type(), "claimed_value": _value(runtime, "2")},
        {"node_id": "X", "kind": "LITERAL", "operation": "LITERAL", "parents": [], "parameters": {}, "value_type": _value_type(), "claimed_value": _value(runtime, "x")},
        {"node_id": "TWO_X", "kind": "DERIVED", "operation": "MUL", "parents": ["SOURCE.TWO", "X"], "parameters": {}, "value_type": _value_type(), "claimed_value": _value(runtime, "2*x")},
        {"node_id": "ONE", "kind": "LITERAL", "operation": "LITERAL", "parents": [], "parameters": {}, "value_type": _value_type(), "claimed_value": _value(runtime, "1")},
        {"node_id": "RESULT", "kind": "DERIVED", "operation": "ADD", "parents": ["TWO_X", "ONE"], "parameters": {}, "value_type": _value_type(), "claimed_value": _value(runtime, "2*x+1")},
        {"node_id": "OUTPUT.RESULT", "kind": "OUTPUT", "operation": "OUTPUT_BIND", "parents": ["RESULT"], "parameters": {}, "value_type": _value_type(), "claimed_value": _value(runtime, "2*x+1")},
    ]
    edges = [[parent, node["node_id"]] for node in nodes for parent in node["parents"]]
    candidate = CandidatePacketV1(request.computation_id, {"kind": "TEST_FIXTURE", "trust": "UNTRUSTED_PROPOSAL"}, {"nodes": nodes, "edges": edges}, {"OUTPUT.RESULT": _value(runtime, "2*x+1")}, ({"node_id": "SOURCE.TWO", "reference": reference},))
    return api.ContractSetV1(profile, policy, tmp_path), request, candidate, challenge


def test_computational_identity_excludes_scientific_authority(tmp_path: Path) -> None:
    contracts, request, candidate, _ = _synthetic(tmp_path)
    first = ScientificAuthorityBindingV1(contracts.profile.contract_hash, {}, "SCIENTIFIC_REQUALIFICATION_NOT_EARNED")
    second = ScientificAuthorityBindingV1(contracts.profile.contract_hash, {}, "REQUALIFIED")
    assert first.binding_hash != second.binding_hash
    assert request.computation_id == CalculationRequestV1.from_dict(request.to_dict()).computation_id
    assert "authority" not in json.dumps(request.to_dict()).lower()


def test_strict_json_limits_duplicate_keys_float_and_depth() -> None:
    with pytest.raises(CalculatorError, match="DUPLICATE_JSON_KEY"):
        strict_json_bytes(b'{"a":1,"a":2}')
    with pytest.raises(CalculatorError, match="BINARY_FLOAT_INPUT_FORBIDDEN"):
        strict_json_bytes(b'{"a":0.1}')
    with pytest.raises(CalculatorError, match="JSON_DEPTH_LIMIT"):
        strict_json_bytes(("[" * 65 + "]" * 65).encode())


def test_natural_units_are_dimension_quotient_relations() -> None:
    system = DimensionSystemV1(("ENERGY", "TIME"), "RATIONAL", (("1", "1"),))
    quotient = DimensionQuotientV1(system)
    energy = DimensionVectorV1.decode(("1", "0"), system)
    inverse_time = DimensionVectorV1.decode(("0", "-1"), system)
    length = DimensionVectorV1.decode(("0", "1"), system)
    assert quotient.equivalent(energy, inverse_time)
    assert not quotient.equivalent(energy, length)


def test_all_typed_source_references_resolve_values_not_evidence_labels(tmp_path: Path) -> None:
    document = {
        "value": "direct",
        "rows": [{"id": "a", "answer": "selected"}, {"id": "b", "answer": "other"}],
        "tensor": [["00", "01"], ["10", "11"]],
        "conventions": {"natural": "hbar=c=1"},
    }
    raw = canonical_bytes(document)
    (tmp_path / "sources.json").write_bytes(raw)
    sha = hashlib.sha256(raw).hexdigest()
    resolver = SourceResolverV1(tmp_path, ({"path": "sources.json", "sha256": sha, "byte_size": len(raw), "media_type": "application/json"},))
    base = {"artifact_path": "sources.json", "artifact_sha256": sha}
    assert resolver.resolve(dict(base, type="JsonPointerValueRef", pointer="/value")).value == "direct"
    assert resolver.resolve(dict(base, type="UniqueTableCellRef", table_pointer="/rows", match_field="id", match_value="a", value_pointer="/answer")).value == "selected"
    assert resolver.resolve(dict(base, type="TensorComponentRef", pointer="/tensor", indices=[1, 0])).value == "10"
    assert resolver.resolve(dict(base, type="NamedConventionRef", conventions_pointer="/conventions", name="natural")).value == "hbar=c=1"
    with pytest.raises(CalculatorError, match="SOURCE_LOCATOR_NOT_FOUND"):
        resolver.resolve(dict(base, type="JsonPointerValueRef", pointer="/artifact-hash-is-not-a-value-locator"))


def test_closed_exact_language_and_rational_function_normalization() -> None:
    runtime = ExactRuntimeV1(AlgebraicFieldV1.rational(), ("x",))
    assert runtime.parse_rational_text("(2*x+2)/2") == runtime.parse_rational_text("x+1")
    with pytest.raises(CalculatorError, match="UNSUPPORTED_EXACT"):
        runtime.parse_rational_text("sin(x)")


def test_semantic_unit_domain_and_budget_mismatches_fail_closed(tmp_path: Path) -> None:
    contracts, request, candidate, _ = _synthetic(tmp_path)
    raised_budget = replace(request, execution_budgets={"total_seconds": contracts.policy.resource_limits.trusted_total_seconds + 1})
    raised_candidate = replace(candidate, computation_id=raised_budget.computation_id)
    with pytest.raises(CalculatorError, match="TRUSTED_TOTAL_RUNTIME_BUDGET"):
        api.evaluate_candidate(contracts, raised_budget, raised_candidate)

    profile = replace(contracts.profile, semantic_types=("SCALAR", "WILSON_COEFFICIENT"))
    typed_request = CalculationRequestV1(profile.contract_hash, contracts.policy.contract_hash, request.inputs, request.requested_roots, request.execution_budgets)
    raw = candidate.to_dict(); raw["computation_id"] = typed_request.computation_id
    next(row for row in raw["graph"]["nodes"] if row["node_id"] == "TWO_X")["value_type"]["semantic_type"] = "WILSON_COEFFICIENT"
    typed_candidate = CandidatePacketV1.from_dict(raw)
    with pytest.raises(CalculatorError, match="MULTIPLICATIVE_TYPE_MISMATCH"):
        api.evaluate_candidate(api.ContractSetV1(profile, contracts.policy, tmp_path), typed_request, typed_candidate)

    raw = candidate.to_dict()
    next(row for row in raw["graph"]["nodes"] if row["node_id"] == "X")["value_type"]["unit_convention"] = "UNDECLARED_SI"
    with pytest.raises(CalculatorError, match="UNIT_CONVENTION"):
        api.evaluate_candidate(contracts, request, CandidatePacketV1.from_dict(raw))


def test_profile_wide_common_algebraic_field_coordinates() -> None:
    field = AlgebraicFieldV1(
        "SQRT2_SQRT3_I_COMMON_FIELD", "alpha",
        ("144", "0", "192", "0", "88", "0", "-16", "0", "1"),
        {"kind": "COMPLEX_RECTANGLE", "real_lower": "3", "real_upper": "4", "imag_lower": "1/2", "imag_upper": "3/2"},
        ("1", "alpha", "alpha^2", "alpha^3", "alpha^4", "alpha^5", "alpha^6", "alpha^7"),
    )
    runtime = ExactRuntimeV1(field, ())
    sqrt2 = runtime.algebraic(("0", "13/12", "0", "14/9", "0", "-35/144", "0", "1/72"))
    sqrt3 = runtime.algebraic(("0", "-21/16", "0", "-181/96", "0", "59/192", "0", "-7/384"))
    imaginary = runtime.algebraic(("0", "59/48", "0", "95/288", "0", "-37/576", "0", "5/1152"))
    alpha = runtime.algebraic(("0", "1", "0", "0", "0", "0", "0", "0"))
    assert runtime.add(runtime.add(sqrt2, sqrt3), imaginary) == alpha
    assert runtime.power(sqrt2, 2) == runtime.rational(2)
    assert runtime.power(sqrt3, 2) == runtime.rational(3)
    assert runtime.power(imaginary, 2) == runtime.rational(-1)


@cross_language
def test_common_algebraic_field_is_identical_in_python_and_julia(tmp_path: Path) -> None:
    field = AlgebraicFieldV1(
        "SQRT2_SQRT3_I_COMMON_FIELD", "alpha",
        ("144", "0", "192", "0", "88", "0", "-16", "0", "1"),
        {"kind": "COMPLEX_RECTANGLE", "real_lower": "3", "real_upper": "4", "imag_lower": "1/2", "imag_upper": "3/2"},
        ("1", "alpha", "alpha^2", "alpha^3", "alpha^4", "alpha^5", "alpha^6", "alpha^7"),
    )
    runtime = ExactRuntimeV1(field, ())
    sqrt2 = runtime.algebraic(("0", "13/12", "0", "14/9", "0", "-35/144", "0", "1/72"))
    sqrt3 = runtime.algebraic(("0", "-21/16", "0", "-181/96", "0", "59/192", "0", "-7/384"))
    imaginary = runtime.algebraic(("0", "59/48", "0", "95/288", "0", "-37/576", "0", "5/1152"))
    alpha = runtime.algebraic(("0", "1", "0", "0", "0", "0", "0", "0"))
    raw = canonical_bytes({"sqrt2": sqrt2.to_dict()})
    (tmp_path / "field.json").write_bytes(raw)
    sha = hashlib.sha256(raw).hexdigest()
    profile = PhysicsProfileV1(
        "COMMON_FIELD_CROSS_LANGUAGE_v1", (), field, DimensionSystemV1(("D",), "INTEGER", ()), ("NONE",),
        ("SCALAR",), {}, (), ({"path": "field.json", "sha256": sha, "byte_size": len(raw), "media_type": "application/json"},),
        ("SOURCE_DECODE", "LITERAL", "ADD", "OUTPUT_BIND"), ("OUTPUT.ALPHA",), {"OUTPUT.ALPHA": "COMMON_FIELD.alpha"},
    )
    policy = VerificationPolicyV1(
        "COMMON_FIELD_POLICY_v1", "2026-09-05T23:59:59Z", "python-verified-calculator-v1", "julia-nemo-verified-calculator-v1", "lean-runtime-certificate-v1", (),
        _numerical_policy(), QMCPolicyV1("SOBOL", "VPC_SOBOL_UINT32_V1", "VPC_SOBOL_2D_BRATLEY_FOX_BASE_V1", "DIGITAL_XOR_SHA256_V1", "GRAY_CODE_INDEX_ORDER", "FIRST_N_FROM_INDEX_ZERO"),
    )
    request = CalculationRequestV1(profile.contract_hash, policy.contract_hash, {}, profile.output_roots, {"total_seconds": 60})
    reference = {"type": "JsonPointerValueRef", "artifact_path": "field.json", "artifact_sha256": sha, "pointer": "/sqrt2"}
    vt = {"mathematical_kind": "EXACT_SCALAR", "semantic_type": "SCALAR", "dimension": ["0"], "unit_convention": "NONE", "index_spaces": [], "representation_tags": [], "domain": {"kind": "EXACT"}}
    sum23 = runtime.add(sqrt2, sqrt3)
    nodes = [
        {"node_id": "SQRT2", "kind": "SOURCE", "operation": "SOURCE_DECODE", "parents": [], "parameters": {"reference": reference}, "value_type": vt, "claimed_value": sqrt2.to_dict()},
        {"node_id": "SQRT3", "kind": "LITERAL", "operation": "LITERAL", "parents": [], "parameters": {}, "value_type": vt, "claimed_value": sqrt3.to_dict()},
        {"node_id": "I", "kind": "LITERAL", "operation": "LITERAL", "parents": [], "parameters": {}, "value_type": vt, "claimed_value": imaginary.to_dict()},
        {"node_id": "SUM23", "kind": "DERIVED", "operation": "ADD", "parents": ["SQRT2", "SQRT3"], "parameters": {}, "value_type": vt, "claimed_value": sum23.to_dict()},
        {"node_id": "ALPHA", "kind": "DERIVED", "operation": "ADD", "parents": ["SUM23", "I"], "parameters": {}, "value_type": vt, "claimed_value": alpha.to_dict()},
        {"node_id": "OUTPUT.ALPHA", "kind": "OUTPUT", "operation": "OUTPUT_BIND", "parents": ["ALPHA"], "parameters": {}, "value_type": vt, "claimed_value": alpha.to_dict()},
    ]
    candidate = CandidatePacketV1(request.computation_id, {"trust": "UNTRUSTED_PROPOSAL"}, {"nodes": nodes, "edges": [[parent, node["node_id"]] for node in nodes for parent in node["parents"]]}, {"OUTPUT.ALPHA": alpha.to_dict()}, ({"node_id": "SQRT2", "reference": reference},))
    run = api.evaluate_candidate(api.ContractSetV1(profile, policy, tmp_path), request, candidate)
    julia = run_julia_independent(run)
    lean = run_lean_certificate_checker(run)
    receipt = api.verify_run(run, julia_evidence=julia, lean_evidence=lean)
    assert receipt.outputs[0].verification_class == VerificationClass.VERIFIED_EXACT


@cross_language
def test_end_to_end_python_julia_lean_challenge_and_per_output_status(tmp_path: Path) -> None:
    contracts, request, candidate, challenge = _synthetic(tmp_path)
    run = api.evaluate_candidate(contracts, request, candidate)
    challenge_results = api.run_challenges(run, (challenge,))
    assert len(challenge_results) == 1 and challenge_results[0].disposition.value == "PASSED"
    julia = run_julia_independent(run)
    lean = run_lean_certificate_checker(run)
    receipt = api.verify_run(run, challenge_results=challenge_results, challenge_specs=(challenge,), julia_evidence=julia, lean_evidence=lean)
    assert receipt.outputs[0].verification_class == VerificationClass.VERIFIED_EXACT
    assert receipt.scientific_promotion is False
    assert all("SU(5) is physically correct" in row.does_not_claim for row in receipt.claim_ledger)


def test_mutant_cannot_expand_its_frozen_descendant_permission(tmp_path: Path) -> None:
    contracts, request, candidate, challenge = _synthetic(tmp_path)
    run = api.evaluate_candidate(contracts, request, candidate)
    packet = instantiate(challenge, candidate, run.evaluation.graph_hash, "ONE")
    forged = replace(packet, permitted_descendants=tuple(sorted((*packet.permitted_descendants, "SOURCE.TWO"))))
    with pytest.raises(CalculatorError, match="CHALLENGE_PACKET_BASELINE_DERIVATION"):
        apply_mutation(challenge, forged, candidate)


def test_verification_reexecutes_and_rejects_forged_challenge_results(tmp_path: Path) -> None:
    contracts, request, candidate, challenge = _synthetic(tmp_path)
    run = api.evaluate_candidate(contracts, request, candidate)
    result = api.run_challenges(run, (challenge,))[0]
    forged = replace(result, disposition=ChallengeDisposition.FAILED, observed_consequence="MUTATION_ACCEPTED")
    with pytest.raises(CalculatorError, match="CHALLENGE_RESULT_NOT_REPRODUCIBLE"):
        api.verify_run(run, challenge_results=(forged,), challenge_specs=(challenge,))


@cross_language
def test_optional_challenge_failure_blocks_only_affected_output_branch(tmp_path: Path) -> None:
    contracts, _, baseline, mandatory = _synthetic(tmp_path)
    profile = replace(
        contracts.profile,
        output_roots=("OUTPUT.RESULT", "OUTPUT.SECOND"),
        output_claims={"OUTPUT.RESULT": "SYNTHETIC.first", "OUTPUT.SECOND": "SYNTHETIC.second"},
    )
    request = CalculationRequestV1(profile.contract_hash, contracts.policy.contract_hash, {"case": "two-branch"}, profile.output_roots, {"total_seconds": 60})
    raw = baseline.to_dict()
    second_value = raw["graph"]["nodes"][2]["claimed_value"]
    raw["graph"]["nodes"].append({
        "node_id": "OUTPUT.SECOND", "kind": "OUTPUT", "operation": "OUTPUT_BIND", "parents": ["TWO_X"],
        "parameters": {}, "value_type": _value_type(), "claimed_value": deepcopy(second_value),
    })
    raw["graph"]["edges"].append(["TWO_X", "OUTPUT.SECOND"])
    raw["claimed_outputs"]["OUTPUT.SECOND"] = deepcopy(second_value)
    raw["computation_id"] = request.computation_id
    candidate = CandidatePacketV1.from_dict(raw)
    optional = ChallengeSpecV1(
        "OPTIONAL_OUTPUT_BRANCH_FAILURE", {"node_id": "OUTPUT.RESULT"}, {"kind": "PERTURB_OUTPUT_ONLY"},
        "Optional probes may lower only affected roots", "AFFECTED_ROOT_VALUE_CHANGES", {"roots": "ANCESTRY"},
        "FROZEN_BASELINE_DESCENDANTS_ONLY", {"kind": "FIXED", "seed": 9}, "AI_PROPOSED_UNREVIEWED", None, False,
    )
    run = api.evaluate_candidate(api.ContractSetV1(profile, contracts.policy, tmp_path), request, candidate)
    challenge_results = api.run_challenges(run, (mandatory, optional))
    assert {row.challenge_id: row.disposition.value for row in challenge_results} == {
        "SYNTHETIC_CORRUPT_ONE": "PASSED", "OPTIONAL_OUTPUT_BRANCH_FAILURE": "FAILED",
    }
    julia, lean = run_julia_independent(run), run_lean_certificate_checker(run)
    receipt = api.verify_run(run, challenge_results=challenge_results, challenge_specs=(mandatory, optional), julia_evidence=julia, lean_evidence=lean)
    outputs = {row.root_id: row for row in receipt.outputs}
    assert outputs["OUTPUT.RESULT"].verification_class == VerificationClass.DETERMINISTICALLY_RECOMPUTED
    assert outputs["OUTPUT.SECOND"].verification_class == VerificationClass.VERIFIED_EXACT


@cross_language
def test_mutated_runtime_certificate_is_rejected_by_lean(tmp_path: Path) -> None:
    contracts, request, candidate, _ = _synthetic(tmp_path)
    run = api.evaluate_candidate(contracts, request, candidate)
    broken = deepcopy(run.certificate.to_dict())
    broken["node_trace"][-1]["claimed_value_digest"] = "0" * 64
    certificate_path = tmp_path / "broken.json"
    certificate_path.write_bytes(canonical_bytes(broken))
    from formal.python.toe.generic_runner.verified_calculator.independent import LEAN_CHECKER
    import subprocess
    process = subprocess.run([str(LEAN_CHECKER), str(certificate_path), hashlib.sha256(certificate_path.read_bytes()).hexdigest(), "0" * 64], capture_output=True)
    assert process.returncode != 0
    assert b"claimed/computed digest mismatch" in process.stderr


@cross_language
def test_lean_file_binding_rejects_graph_source_output_and_status_mutations(tmp_path: Path) -> None:
    contracts, request, candidate, _ = _synthetic(tmp_path)
    run = api.evaluate_candidate(contracts, request, candidate)
    original = canonical_bytes(run.certificate.to_dict())
    original_sha = hashlib.sha256(original).hexdigest()
    mutations = []
    for field in ("graph_hash",):
        value = deepcopy(run.certificate.to_dict()); value[field] = "0" * 64; mutations.append(value)
    value = deepcopy(run.certificate.to_dict()); value["source_receipt_hashes"][0] = "0" * 64; mutations.append(value)
    value = deepcopy(run.certificate.to_dict()); value["output_value_hashes"]["OUTPUT.RESULT"] = "0" * 64; mutations.append(value)
    value = deepcopy(run.certificate.to_dict()); value["scientific_promotion"] = True; mutations.append(value)
    value = deepcopy(run.certificate.to_dict()); value["node_trace"][-1]["value_digest"] = "0" * 64; mutations.append(value)
    for index, mutated in enumerate(mutations):
        path = tmp_path / f"mutated-{index}.json"
        path.write_bytes(canonical_bytes(mutated))
        process = subprocess.run([str(LEAN_CHECKER), str(path), original_sha, run.certificate.certificate_hash], capture_output=True)
        assert process.returncode != 0
        assert b"REJECTED FILE_HASH certificate bytes changed" in process.stderr


def test_authority_attachment_changes_bundle_not_computation(tmp_path: Path) -> None:
    contracts, request, candidate, challenge = _synthetic(tmp_path)
    run = api.evaluate_candidate(contracts, request, candidate)
    results = api.run_challenges(run, (challenge,))
    receipt = api.verify_run(run, challenge_results=results, challenge_specs=(challenge,))
    binding = ScientificAuthorityBindingV1(
        contracts.profile.contract_hash,
        {"SYNTHETIC.result": ClaimAuthorityBindingV1("PENDING", "SYNTHETIC_ONLY", (), "synthetic", ("No scientific authority",), "2026-09-05T00:00:00Z", "NO_SCIENTIFIC_PROMOTION")},
    )
    attachment = attach_authority(receipt, binding)
    base = api.assemble_evidence_bundle(run, receipt, challenge_specs=(challenge,))
    attached = replace(base, authority_bindings=(binding.to_dict(),), authority_attachments=(attachment.to_dict(),))
    assert base.bundle_hash != attached.bundle_hash
    assert request.computation_id == receipt.computation_id


@cross_language
def test_frozen_bundle_validates_internal_bindings_and_replays(tmp_path: Path) -> None:
    contracts, request, candidate, challenge = _synthetic(tmp_path)
    run = api.evaluate_candidate(contracts, request, candidate)
    results = api.run_challenges(run, (challenge,))
    julia, lean = run_julia_independent(run), run_lean_certificate_checker(run)
    receipt = api.verify_run(run, challenge_results=results, challenge_specs=(challenge,), julia_evidence=julia, lean_evidence=lean)
    bundle = api.assemble_evidence_bundle(run, receipt, challenge_specs=(challenge,), julia_evidence=julia, lean_evidence=lean)
    path = api.freeze_evidence(bundle, tmp_path / "frozen")
    replay = replay_bundle(path)
    assert replay["replay_status"] == "MATCHED"
    assert replay["structural_and_hash_bindings_checked"] is True
    broken = deepcopy(bundle.to_dict())
    broken["runtime_certificate"]["candidate_hash"] = "0" * 64
    with pytest.raises(CalculatorError, match="BUNDLE_CANDIDATE_BINDING"):
        FrozenEvidenceBundleV1.from_dict(broken)


@cross_language
def test_interval_certificate_and_strict_enclosure_definition() -> None:
    certificate = {
        "schema_id": "IntervalCertificateV1", "arithmetic": "EXACT_RATIONAL",
        "inputs": {"x": {"kind": "RATIONAL_INTERVAL", "lower": "1/10", "upper": "1/5"}, "y": {"kind": "RATIONAL_INTERVAL", "lower": "2", "upper": "3"}},
        "steps": [{"id": "z", "operation": "MUL", "parents": ["x", "y"]}],
        "output": {"value_id": "z", "claimed_enclosure": {"kind": "RATIONAL_INTERVAL", "lower": "1/5", "upper": "3/5"}},
    }
    result = evaluate_interval_certificate(certificate)
    assert result["status"] == "VERIFIED_ENCLOSURE"
    broken = deepcopy(certificate); broken["output"]["claimed_enclosure"]["upper"] = "1/2"
    with pytest.raises(CalculatorError, match="INTERVAL_CERTIFICATE_MISMATCH"):
        evaluate_interval_certificate(broken)
    assert crosscheck_interval(certificate)["verification_class"] == "VERIFIED_ENCLOSURE"


@cross_language
def test_directed_decimal_interval_and_power_are_independently_contained() -> None:
    certificate = {
        "schema_id": "IntervalCertificateV1", "arithmetic": "DECIMAL_DIRECTED",
        "inputs": {
            "x": {"kind": "DECIMAL_INTERVAL", "lower": "0.1", "upper": "0.2", "precision_digits": 20},
            "three": {"kind": "DECIMAL_INTERVAL", "lower": "3", "upper": "3", "precision_digits": 20},
        },
        "steps": [
            {"id": "product", "operation": "MUL", "parents": ["x", "three"]},
            {"id": "square", "operation": "POW_INT", "parents": ["product"], "parameters": {"exponent": 2}},
        ],
        "output": {"value_id": "square", "claimed_enclosure": {"kind": "DECIMAL_INTERVAL", "lower": "0.089999999999999999", "upper": "0.360000000000000001", "precision_digits": 20}},
    }
    checked = crosscheck_interval(certificate)
    assert checked["verification_class"] == "VERIFIED_ENCLOSURE"
    assert checked["enclosure"] == certificate["output"]["claimed_enclosure"]


@cross_language
def test_declarative_ode_and_rge_controls() -> None:
    state = {"op": "STATE", "index": 0}
    minus_state = {"op": "NEG", "argument": state}
    base = {"schema_id": "DeclarativeOdeSpecV1", "system_kind": "ODE", "rhs": [minus_state], "initial_time": "0", "final_time": "1", "initial_state": ["1"], "parameters": {}, "rtol": "1e-11", "atol": "1e-13", "method": "DOP853"}
    ode = solve_declarative_ode(base)
    assert abs(float.fromhex(ode["final_state_hex"][0]) - math.exp(-1)) < 1e-10
    rge_spec = deepcopy(base); rge_spec["system_kind"] = "RGE"
    assert solve_declarative_ode(rge_spec)["system_kind"] == "RGE"
    assert ode["arbitrary_callback_executed"] is False
    assert crosscheck_ode(base)["verification_class"] == "CROSSCHECKED_NUMERICAL"
    assert crosscheck_ode(rge_spec)["system_kind"] == "RGE"
    harmonic = dict(
        base,
        final_time=str(math.pi / 2),
        initial_state=["1", "0"],
        rhs=[{"op": "STATE", "index": 1}, {"op": "NEG", "argument": {"op": "STATE", "index": 0}}],
    )
    harmonic_result = crosscheck_ode(harmonic)
    final = [float.fromhex(value) for value in harmonic_result["python"]["final_state_hex"]]
    assert abs(final[0]) < 1e-9 and abs(final[1] + 1) < 1e-9


@cross_language
def test_covariance_semantics_and_exact_linear_jacobian() -> None:
    spec = {
        "schema_id": "CovariancePropagationSpecV1", "variables": ["x", "y"], "mean": {"x": "1", "y": "2"},
        "covariance": [["0.04", "0"], ["0", "0.09"]],
        "outputs": [{"op": "ADD", "left": {"op": "MUL", "left": {"op": "CONST", "value": "2"}, "right": {"op": "VAR", "name": "x"}}, "right": {"op": "VAR", "name": "y"}}],
    }
    result = covariance_propagation(spec)
    assert result["semantics"] == "LOCAL_LINEAR_COVARIANCE"
    assert [[float.fromhex(value) for value in row] for row in result["jacobian_hex"]] == [[2.0, 1.0]]
    assert abs(float.fromhex(result["output_covariance_hex"][0][0]) - 0.25) < 1e-15
    assert crosscheck_covariance(spec)["semantics"] == "LOCAL_LINEAR_COVARIANCE"


@cross_language
def test_deterministic_sobol_qmc_freezes_full_algorithm_identity() -> None:
    assert sobol_uint32(4, 2, 0, "NONE") == ((0, 0), (2**31, 2**31), (3 * 2**30, 2**30), (2**30, 3 * 2**30))
    spec = {
        "schema_id": "QMCEnsembleSpecV1", "variables": ["x", "y"], "bounds": [["0", "1"], ["0", "1"]],
        "integrand": {"op": "ADD", "left": {"op": "VAR", "name": "x"}, "right": {"op": "VAR", "name": "y"}},
        "generator_family": "SOBOL", "specification_version": "VPC_SOBOL_UINT32_V1", "direction_table": "VPC_SOBOL_2D_BRATLEY_FOX_BASE_V1",
        "scrambling": "DIGITAL_XOR_SHA256_V1", "ordering": "GRAY_CODE_INDEX_ORDER", "sample_count_convention": "FIRST_N_FROM_INDEX_ZERO", "sample_count": 1024, "seed": 12345,
    }
    first, second = qmc_ensemble(spec), qmc_ensemble(spec)
    assert first["generated_input_set_sha256"] == second["generated_input_set_sha256"]
    assert first["generator_identity"]["seed"] == 12345
    assert first["semantics"] == "SAMPLED_DISTRIBUTION_ESTIMATE"
    assert "Not a guaranteed range" in first["limitations"]
    assert crosscheck_qmc(spec)["generated_input_set_sha256"] == first["generated_input_set_sha256"]
    constant = deepcopy(spec)
    constant["integrand"] = {"op": "CONST", "value": "3.5"}
    constant_result = crosscheck_qmc(constant)
    assert float.fromhex(constant_result["python"]["mean_hex"]) == 3.5


def test_trusted_offline_guard_and_import_boundary() -> None:
    with trusted_offline(), pytest.raises(CalculatorError, match="TRUSTED_NETWORK_ACCESS_FORBIDDEN"):
        socket.create_connection(("example.com", 80))
    trusted_root = Path(importlib.import_module("formal.python.toe.generic_runner.verified_calculator").__file__).parent
    forbidden = ("c03_", "rv_", "seven_record", "oracle", "acceptance")
    for path in trusted_root.glob("*.py"):
        text = path.read_text(encoding="utf-8").lower()
        assert not any(f"generic_runner import {token}" in text or f"generic_runner.{token}" in text for token in forbidden)


def test_public_contract_json_schema_and_generated_dependency_closure(tmp_path: Path) -> None:
    contracts, request, candidate, challenge = _synthetic(tmp_path)
    schema_path = Path("formal/python/toe/generic_runner/verified_calculator/schemas/contracts_v1.schema.json")
    schema = json.loads(schema_path.read_text(encoding="utf-8"))
    Draft202012Validator.check_schema(schema)
    validator = Draft202012Validator(schema)
    for value in (contracts.profile.to_dict(), contracts.policy.to_dict(), request.to_dict(), candidate.to_dict(), challenge.to_dict()):
        validator.validate(value)
    closure = generate_dependency_closure(Path.cwd())
    validate_dependency_closure(closure)
    assert closure["unresolved_dynamic_imports"] == []
    assert closure["manually_excluded_dependencies"] == []
    assert closure["platform_runtime_commands"] == {"windows": ["certutil"], "linux": ["sha256sum"]}


def test_exact_c03_rv_milestone_cannot_be_inflated_by_synthetic_receipt(tmp_path: Path) -> None:
    contracts, request, candidate, challenge = _synthetic(tmp_path)
    run = api.evaluate_candidate(contracts, request, candidate)
    results = api.run_challenges(run, (challenge,))
    receipt = api.verify_run(run, challenge_results=results, challenge_specs=(challenge,))
    with pytest.raises(CalculatorError, match="MILESTONE_GATE_FAILED"):
        exact_c03_rv_milestone(
            receipt,
            replay_bundle_hashes=("a" * 64, "a" * 64),
            derived_node_census={"unexpected_survivors": [], "challenged_count": 38, "derived_node_count": 38, "c03_intermediate_challenges": 38},
            challenge_registry_census={"unclassified": [], "mandatory_count": 1},
            authority_binding=ScientificAuthorityBindingV1(contracts.profile.contract_hash, {}, "SCIENTIFIC_REQUALIFICATION_NOT_EARNED"),
        )


def test_c03_rv_profile_census_is_complete_but_does_not_claim_milestone() -> None:
    from formal.python.toe.generic_runner.verified_calculator.c03_rv_policy import physics_profile
    from formal.python.toe.generic_runner.verified_calculator_c03_rv_census_v1 import census, scientific_authority_binding
    result = census()
    assert result["output_root_count"] == 16
    assert result["output_roots"] == result["expected_output_roots"]
    assert result["derived_node_count"] >= 160
    assert result["per_record_spec_count"]["C03"] == 43
    assert result["challenge_registry"]["unclassified"] == []
    assert all(count > 0 for count in result["challenge_target_counts"].values())
    assert result["exact_milestone_earned"] is False
    assert result["scientific_promotion"] is False
    frozen = json.loads(Path("formal/docs/release/VERIFIED_CALCULATOR_C03_RV_POLICY_FREEZE_20260905_v1.json").read_text(encoding="utf-8"))
    assert frozen == result
    profile = physics_profile(())
    binding = scientific_authority_binding(profile.contract_hash)
    assert len(binding.claim_bindings) == 16
    assert binding.claim_bindings["C03.claim.PHYSICAL_COEFFICIENT"].authority_state == "TERMINALLY_ADJUDICATED"
    assert binding.claim_bindings["RV03.claim.SOURCE_CHANNEL"].historical_label == "WRONG_SOURCE_CHANNEL_NO_SCALAR_MAP"
    assert binding.calculator_profile_review_status == "SCIENTIFIC_REQUALIFICATION_NOT_EARNED"


@cross_language
def test_subsystem_and_product_release_gates_are_explicit(tmp_path: Path) -> None:
    contracts, request, candidate, challenge = _synthetic(tmp_path)
    run = api.evaluate_candidate(contracts, request, candidate)
    results = api.run_challenges(run, (challenge,))
    julia, lean = run_julia_independent(run), run_lean_certificate_checker(run)
    receipt = api.verify_run(run, challenge_results=results, challenge_specs=(challenge,), julia_evidence=julia, lean_evidence=lean)
    assert synthetic_profile_milestone(receipt).product_v1_release is False

    enclosure = {"python_checker": {}, "julia_checker": {}, "verification_class": "VERIFIED_ENCLOSURE", "guarantee": "contains true result", "scientific_promotion": False}
    ode = {"verification_class": "CROSSCHECKED_NUMERICAL", "system_kind": "ODE", "python": {"arbitrary_callback_executed": False}, "julia": {"arbitrary_callback_executed": False}, "rigorous_enclosure": False, "scientific_promotion": False}
    rge = dict(ode, system_kind="RGE")
    covariance = {"semantics": "LOCAL_LINEAR_COVARIANCE", "rigorous_enclosure": False, "scientific_promotion": False}
    qmc = {"semantics": "SAMPLED_DISTRIBUTION_ESTIMATE", "python": {"generated_input_set_sha256": "a" * 64}, "julia": {"generated_input_set_sha256": "a" * 64}, "rigorous_enclosure": False, "scientific_promotion": False}
    assert interval_milestone(enclosure).scientific_promotion is False
    assert ode_rge_milestone(ode, rge).product_v1_release is False
    assert uncertainty_milestone(enclosure, covariance, qmc).production_activation is False
    plugin = plugin_boundary_milestone(({"unsafe_flag_required": True, "trusted_receipt_emitted": False, "os_sandbox_claimed": False, "self_promotion_rejected": True},))
    assert plugin.product_v1_release is False
    with pytest.raises(CalculatorError, match="PRODUCT_MILESTONE_SET"):
        ProductReleaseV1("1.0.0", {}, "a" * 64, {"windows": "b" * 64, "linux": "c" * 64}, {"all": True})


def test_unsafe_plugin_is_explicit_candidate_only_and_output_bounded(tmp_path: Path) -> None:
    _, _, candidate, _ = _synthetic(tmp_path)
    echo = [sys.executable, "-c", "import sys;sys.stdout.buffer.write(sys.stdin.buffer.read())"]
    with pytest.raises(CalculatorError, match="UNSAFE_PLUGIN_FLAG_REQUIRED"):
        run_unsafe_plugin(echo, input_packet=canonical_bytes(candidate.to_dict()), unsafe_allow_arbitrary_code=False)
    returned, provenance = run_unsafe_plugin(echo, input_packet=canonical_bytes(candidate.to_dict()), unsafe_allow_arbitrary_code=True)
    assert returned.candidate_hash == candidate.candidate_hash
    assert provenance["trusted_receipt_emitted"] is False
    assert "not sandboxed" in provenance["warning"]
    noisy = [sys.executable, "-c", "import sys;sys.stdout.buffer.write(b'x'*4096)"]
    with pytest.raises(CalculatorError, match="PLUGIN_OUTPUT_LIMIT"):
        run_unsafe_plugin(noisy, input_packet=b"{}", unsafe_allow_arbitrary_code=True, limits=replace(ResourceLimitsV1(), plugin_output_bytes=256))


def test_cli_run_and_freeze_rejects_non_bundle(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    from formal.python.toe.generic_runner.verified_calculator.cli import main
    contracts, request, candidate, _ = _synthetic(tmp_path)
    profile_path, policy_path, request_path, candidate_path = (tmp_path / name for name in ("profile.json", "policy.json", "request.json", "candidate.json"))
    profile_path.write_bytes(canonical_bytes(contracts.profile.to_dict()))
    policy_path.write_bytes(canonical_bytes(contracts.policy.to_dict()))
    request_path.write_bytes(canonical_bytes(request.to_dict()))
    candidate_path.write_bytes(canonical_bytes(candidate.to_dict()))
    assert main(["run", "--profile", str(profile_path), "--policy", str(policy_path), "--source-root", str(tmp_path), "--request", str(request_path), "--candidate", str(candidate_path)]) == 0
    output = json.loads(capsys.readouterr().out)
    assert output["execution_status"] == "SUCCEEDED"
    bad = tmp_path / "not-a-bundle.json"
    bad.write_bytes(canonical_bytes({"schema_id": "NotABundle"}))
    assert main(["freeze", str(bad), "--destination", str(tmp_path / "frozen")]) == 2
    assert json.loads(capsys.readouterr().err)["error_code"] == "FROZEN_BUNDLE_SCHEMA"


def test_implementation_status_is_truthful_and_closure_bound() -> None:
    status = json.loads(Path("formal/docs/release/VERIFIED_CALCULATOR_V1_IMPLEMENTATION_STATUS_20260905_v1.json").read_text(encoding="utf-8"))
    closure = generate_dependency_closure(Path.cwd())
    validate_dependency_closure(closure)
    assert status["local_validation"]["dependency_closure_hash"] == closure["closure_hash"]
    assert status["milestones"]["C03_RV_COMPUTATION_VERIFIED_EXACT_PRE_RELEASE"] == "NOT_EARNED"
    assert status["milestones"]["product_v1"] == "NOT_RELEASED"
    assert status["scientific_promotion"] is False
    assert status["product_v1_release"] is False
    assert status["production_activation"] is False

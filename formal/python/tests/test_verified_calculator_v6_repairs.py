from __future__ import annotations

from dataclasses import replace
import hashlib
import json
import os
from pathlib import Path
import subprocess

import pytest

from formal.python.toe.generic_runner.verified_calculator.c03_rv_operation_contracts import DERIVED_SIGNATURES, SOURCE_SIGNATURES
from formal.python.toe.generic_runner.verified_calculator.c03_rv_policy import physics_profile
from formal.python.toe.generic_runner.verified_calculator.c03_rv_type_contracts import trusted_value_type, trusted_value_type_registry, validate_node_edge, validate_node_type
from formal.python.toe.generic_runner.verified_calculator.challenges import canonical_graph_hash, challenge_seed_graph_hash, instantiate, select_targets
from formal.python.toe.generic_runner.verified_calculator.dag import NodeV1
from formal.python.toe.generic_runner.verified_calculator.dependency_closure import _identity_row, canonical_text_v1_bytes, canonical_text_v1_sha256
from formal.python.toe.generic_runner.verified_calculator.errors import CalculatorError
from formal.python.toe.generic_runner.verified_calculator.canonical import canonical_bytes, digest
from formal.python.toe.generic_runner.verified_calculator.evidence import RuntimeCertificateV1
from formal.python.toe.generic_runner.verified_calculator.qualification_envelope import COMMITMENT_FIELDS, QualificationEnvelopeV1, QualificationExpectedContextV1
from formal.python.toe.generic_runner.verified_calculator.dimensions import DimensionQuotientV1, DimensionVectorV1


def test_d07_canonical_text_controls() -> None:
    lf = b"xi1\nvalue = xi1\n"
    crlf = lf.replace(b"\n", b"\r\n")
    mixed = b"xi1\r\nvalue = xi1\r"
    assert len({hashlib.sha256(row).hexdigest() for row in (lf, crlf, mixed)}) == 3
    assert len({canonical_text_v1_sha256(row) for row in (lf, crlf, mixed)}) == 1
    for changed in (b"xi1\nvalue = xi1 + 1\n", b"xi1 \nvalue = xi1\n", b"xi1\nvalue = xi1"):
        assert canonical_text_v1_sha256(changed) != canonical_text_v1_sha256(lf)
    with pytest.raises(CalculatorError, match="CANONICAL_TEXT_V1_BOM"):
        canonical_text_v1_bytes(b"\xef\xbb\xbf" + lf)
    with pytest.raises(CalculatorError, match="CANONICAL_TEXT_V1_UTF8"):
        canonical_text_v1_bytes(b"\xff")


def test_d07_git_blob_is_primary_and_worktree_only_input_rejects(tmp_path: Path) -> None:
    subprocess.run(["git", "init", "-q", str(tmp_path)], check=True)
    subprocess.run(["git", "-C", str(tmp_path), "config", "user.email", "vpc@example.invalid"], check=True)
    subprocess.run(["git", "-C", str(tmp_path), "config", "user.name", "VPC test"], check=True)
    tracked = tmp_path / "science.txt"
    tracked.write_bytes(b"xi1\n")
    subprocess.run(["git", "-C", str(tmp_path), "add", "science.txt"], check=True)
    subprocess.run(["git", "-C", str(tmp_path), "commit", "-qm", "fixture"], check=True)
    tracked.write_bytes(b"xi1\r\n")
    row = _identity_row(tmp_path, "science.txt", "HEAD")
    assert row["hash_domain"] == "GIT_BLOB_BYTES_V1"
    assert row["git_blob_sha256"] != row["filesystem_sha256"]
    assert row["canonical_text_v1_sha256"] == row["filesystem_canonical_text_v1_sha256"]
    (tmp_path / "untracked.txt").write_bytes(b"not committed\n")
    with pytest.raises(CalculatorError, match="DEPENDENCY_GIT_IDENTITY"):
        _identity_row(tmp_path, "untracked.txt", "HEAD")


def _profile_with_alternates():
    baseline = physics_profile(())
    return replace(baseline, unit_conventions=(*baseline.unit_conventions, "SYNTHETIC_ALTERNATE_UNIT"))


def _nodes():
    profile = _profile_with_alternates()
    result = {}
    for node_id in sorted({*SOURCE_SIGNATURES, *DERIVED_SIGNATURES}):
        if node_id in SOURCE_SIGNATURES:
            kind, operation, parents, parameters = "SOURCE", "SOURCE_DECODE", (), {"reference": {}}
        else:
            row = DERIVED_SIGNATURES[node_id]
            kind, operation, parents, parameters = row["kind"], row["operation"], row["parents"], {}
        result[node_id] = NodeV1.from_dict({
            "node_id": node_id,
            "kind": kind,
            "operation": operation,
            "parents": list(parents),
            "parameters": parameters,
            "value_type": trusted_value_type(node_id),
            "claimed_value": {},
        }, profile)
    return profile, result


def _mutated_value_type(base: dict, axis: str, semantic_alternate: str) -> dict:
    value = {**base, "dimension": list(base["dimension"]), "index_spaces": list(base["index_spaces"]), "representation_tags": list(base["representation_tags"]), "domain": dict(base["domain"]), "shape": None if base["shape"] is None else list(base["shape"])}
    if axis == "mathematical_kind":
        value["mathematical_kind"] = "EXACT_ATOM" if base["mathematical_kind"] != "EXACT_ATOM" else "EXACT_SCALAR"
    elif axis == "semantic_type":
        value["semantic_type"] = semantic_alternate
    elif axis == "physical_dimension_equivalence_class":
        value["dimension"] = ["1", "0", "0"]
    elif axis == "canonical_unit_convention":
        value["unit_convention"] = "SYNTHETIC_ALTERNATE_UNIT"
    elif axis == "exact_shape_and_rank":
        value["shape"] = [] if base["shape"] is None else ([1] if base["shape"] == [] else [13])
    elif axis == "ordered_index_spaces":
        value["index_spaces"] = [] if base["index_spaces"] else ["NATIVE_E"]
    elif axis == "representation_tags":
        value["representation_tags"] = ["BMHV"]
    elif axis == "domain_status_and_prerequisites":
        value["domain"] = {**base["domain"], "status": "UNEVALUATED"}
    else:
        raise AssertionError(axis)
    return value


def test_d02_complete_registry_and_exhaustive_metadata_mutations() -> None:
    profile, nodes = _nodes()
    registry = trusted_value_type_registry()
    assert len(nodes) == len(registry) == 207
    semantic_alternates = list(profile.semantic_types)
    mutation_count = 0
    for node_id, node in nodes.items():
        receipt = validate_node_type(node)
        assert receipt.status == "TRUSTED_SIGNATURE_MATCHED"
        alternate = next(value for value in semantic_alternates if value != node.value_type.semantic_type)
        for axis in receipt.applicable_axes:
            raw = node.to_dict()
            raw["value_type"] = _mutated_value_type(registry[node_id], axis, alternate)
            mutant = NodeV1.from_dict(raw, profile)
            with pytest.raises(CalculatorError) as rejected:
                validate_node_type(mutant)
            assert rejected.value.code == "C03_RV_VALUE_TYPE_SIGNATURE"
            assert rejected.value.location == node_id
            mutation_count += 1
    assert mutation_count == 207 * 8


def test_d02_every_frozen_derived_edge_is_independently_bound() -> None:
    _, nodes = _nodes()
    alternatives = iter(sorted(nodes))
    for node_id in sorted(DERIVED_SIGNATURES):
        node = nodes[node_id]
        replacement_parent = next(value for value in sorted(nodes) if value not in node.parents and value != node_id)
        mutant = replace(node, parents=(replacement_parent, *node.parents[1:]) if node.parents else (replacement_parent,))
        with pytest.raises(CalculatorError) as rejected:
            validate_node_edge(mutant, {**nodes, node_id: mutant})
        assert rejected.value.code == "C03_RV_TYPE_EDGE_SIGNATURE"
        assert rejected.value.location == node_id


def test_d02_type_registry_has_no_candidate_value_fields() -> None:
    for row in trusted_value_type_registry().values():
        assert set(row) == {"mathematical_kind", "semantic_type", "dimension", "unit_convention", "shape", "index_spaces", "representation_tags", "domain"}
        assert "claimed_value" not in row


def test_d02_declared_natural_unit_quotient_only() -> None:
    profile = physics_profile(())
    quotient = DimensionQuotientV1(profile.dimensions)
    mass = DimensionVectorV1.decode(["1", "0", "0"], profile.dimensions)
    inverse_length = DimensionVectorV1.decode(["0", "-1", "0"], profile.dimensions)
    length = DimensionVectorV1.decode(["0", "1", "0"], profile.dimensions)
    zero = DimensionVectorV1.decode(["0", "0", "0"], profile.dimensions)
    assert quotient.equivalent(mass, inverse_length)
    assert not quotient.equivalent(length, zero)


def test_d02_explicit_shape_preserves_frozen_challenge_seeds() -> None:
    from formal.python.toe.generic_runner import verified_calculator_c03_rv_candidate_v1 as candidate_v1
    from formal.python.toe.generic_runner import verified_calculator_c03_rv_candidate_v2 as candidate_v2
    from formal.python.toe.generic_runner.verified_calculator.c03_rv_policy import mandatory_challenge_specs

    *_, old_candidate = candidate_v1.candidate()
    *_, amended_candidate = candidate_v2.candidate()
    old_graph_hash = canonical_graph_hash(old_candidate)
    amended_graph_hash = canonical_graph_hash(amended_candidate)
    assert old_graph_hash != amended_graph_hash
    assert challenge_seed_graph_hash(old_candidate) == challenge_seed_graph_hash(amended_candidate) == old_graph_hash

    spec = mandatory_challenge_specs()[0]
    target = select_targets(spec, old_candidate)[0]
    old_packet = instantiate(spec, old_candidate, old_graph_hash, target)
    amended_packet = instantiate(spec, amended_candidate, amended_graph_hash, target)
    assert old_packet.baseline_graph_hash != amended_packet.baseline_graph_hash
    assert old_packet.concrete_seed == amended_packet.concrete_seed


def test_payload_comparator_covers_all_frozen_rows(tmp_path: Path) -> None:
    reference = Path("formal/docs/release/verified_calculator/c03_rv_exact/93691fa8f8793bb343ccebd0b1a92c15618b25a7f56e71f67ebaa7cff771471f.json")
    output = tmp_path / "comparison.json"
    environment = dict(os.environ)
    environment["PYTHONPATH"] = str(Path("formal/python").resolve())
    process = subprocess.run([
        "python", "formal/python/tools/compare_vpc_v6_payload.py",
        "--seed", "formal/docs/release/VERIFIED_CALCULATOR_C03_RV_EXACT_V6_PAYLOAD_MISMATCH_REPORT_20260907_v1.json",
        "--reference", str(reference), "--amended", str(reference),
        "--output", str(output), "--attempt-id", "SELF_COMPARISON_CONTROL",
    ], capture_output=True, text=True, check=False, env=environment)
    assert process.returncode == 0, process.stderr
    result = json.loads(output.read_text(encoding="utf-8"))
    assert result["schema_id"] == "VerifiedCalculatorC03RVExactPayloadEquivalenceResultV1"
    assert result["status"] == "PASS"
    assert len(result["rows"]) == result["summary"]["MATCH"] == 643
    assert all(row["reference_projection"] == row["amended_projection"] for row in result["rows"])


def _minimal_d01_fixture():
    ids = {name: hashlib.sha256(name.encode()).hexdigest() for name in ("computation", "candidate", "profile", "policy", "graph", "value")}
    trace = (
        {"node_id": "source", "kind": "SOURCE", "operation": "SOURCE_DECODE", "parents": [], "value_digest": ids["value"], "claimed_value_digest": ids["value"], "status": "RESOLVED_OR_RECOMPUTED_AND_EQUAL"},
        {"node_id": "root", "kind": "OUTPUT", "operation": "OUTPUT_BIND", "parents": ["source"], "value_digest": ids["value"], "claimed_value_digest": ids["value"], "status": "RESOLVED_OR_RECOMPUTED_AND_EQUAL"},
    )
    certificate = RuntimeCertificateV1(ids["computation"], ids["candidate"], ids["profile"], ids["policy"], ids["graph"], {"root": ids["value"]}, {"root": ids["value"]}, trace, (), "DETERMINISTICALLY_RECOMPUTED")
    filler = hashlib.sha256(b"filler").hexdigest()
    commitments = {field: filler for field in COMMITMENT_FIELDS}
    commitments.update({
        "certificate_format_version": "RuntimeCertificateV1+QualificationEnvelopeV1",
        "runtime_certificate_hash": certificate.certificate_hash,
        "computation_id": certificate.computation_id,
        "calculation_request_hash": filler,
        "candidate_hash": certificate.candidate_hash,
        "physics_profile_hash": certificate.physics_profile_hash,
        "verification_policy_hash": certificate.verification_policy_hash,
        "graph_hash": certificate.graph_hash,
        "authoritative_roots": ["root"],
        "canonical_exact_output_value_hashes": dict(certificate.output_value_hashes),
        "status_ceiling": "DETERMINISTICALLY_RECOMPUTED",
        "scientific_promotion": False,
        "product_v1_release": False,
        "production_activation": False,
    })
    return certificate, QualificationEnvelopeV1(commitments), QualificationExpectedContextV1(dict(commitments))


def _lean_checker() -> Path:
    suffix = ".exe" if __import__("os").name == "nt" else ""
    return Path("formal/toe_formal/.lake/build/bin") / f"vpc_qualification_envelope_checker{suffix}"


def _invoke_d01(tmp_path: Path, certificate: dict, envelope: dict, context: dict, *extra: str) -> subprocess.CompletedProcess:
    tmp_path.mkdir(parents=True, exist_ok=True)
    paths = []
    for name, value in (("certificate", certificate), ("envelope", envelope), ("context", context)):
        path = tmp_path / f"{name}.json"
        path.write_bytes(canonical_bytes(value))
        paths.append(str(path))
    return subprocess.run([str(_lean_checker()), *paths, *extra], capture_output=True, text=True, check=False)


def test_d01_lean_computes_identity_and_rejects_substitution(tmp_path: Path) -> None:
    certificate, envelope, context = _minimal_d01_fixture()
    accepted = _invoke_d01(tmp_path, certificate.to_dict(), envelope.to_dict(), context.to_dict())
    assert accepted.returncode == 0
    assert f"ACCEPTED ENVELOPE {envelope.envelope_hash}" in accepted.stdout
    assert f"RUNTIME_CERTIFICATE {certificate.certificate_hash}" in accepted.stdout

    # No fourth, caller-selected accepted-hash argument exists.
    chosen = _invoke_d01(tmp_path, certificate.to_dict(), envelope.to_dict(), context.to_dict(), "0" * 64)
    assert chosen.returncode != 0 and "usage:" in chosen.stderr

    mutations = {
        "contract": ("computation_id", "1" * 64),
        "graph_trace_source": ("ordered_node_trace_hash", "2" * 64),
        "root_value": ("canonical_exact_output_value_hashes", {"root": "3" * 64}),
        "independent_evidence": ("julia_evidence_hash", "4" * 64),
        "challenge_evidence": ("mandatory_challenge_result_set_hash", "5" * 64),
        "status": ("status_ceiling", "VERIFIED_EXACT"),
        "promotion": ("scientific_promotion", True),
    }
    for label, (field, changed) in mutations.items():
        body = envelope.to_dict()
        body[field] = changed
        rejected = _invoke_d01(tmp_path / label, certificate.to_dict(), body, context.to_dict())
        assert rejected.returncode != 0
        assert "REJECTED ENVELOPE" in rejected.stderr

    # A separately valid same-output runtime certificate cannot be substituted
    # while retaining the independently serialized original context.
    other = replace(certificate, computation_id="6" * 64)
    substitute = envelope.to_dict()
    substitute["runtime_certificate_hash"] = other.certificate_hash
    substitute["computation_id"] = other.computation_id
    rejected = _invoke_d01(tmp_path / "substitute", other.to_dict(), substitute, context.to_dict())
    assert rejected.returncode != 0 and "context mismatch" in rejected.stderr

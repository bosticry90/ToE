"""Execute and preserve the v6 D-07, D-01, and D-02 repair controls.

This is an evidence generator, not an authority decision.  On Windows, D-07
remains INCONCLUSIVE until a Linux closure from the same commit is supplied.
"""
from __future__ import annotations

import argparse
from copy import deepcopy
from dataclasses import replace
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
from typing import Any, Mapping

from formal.python.toe.generic_runner import verified_calculator_c03_rv_candidate_v2
from formal.python.toe.generic_runner.verified_calculator import api
from formal.python.toe.generic_runner.verified_calculator.c03_rv_policy import physics_profile
from formal.python.toe.generic_runner.verified_calculator.c03_rv_type_contracts import (
    trusted_value_type_registry,
    validate_node_edge,
    validate_node_type,
)
from formal.python.toe.generic_runner.verified_calculator.canonical import canonical_bytes, digest
from formal.python.toe.generic_runner.verified_calculator.contracts import CandidatePacketV1
from formal.python.toe.generic_runner.verified_calculator.dag import NodeV1
from formal.python.toe.generic_runner.verified_calculator.dependency_closure import (
    canonical_text_v1_bytes,
    canonical_text_v1_sha256,
    validate_dependency_closure_v2,
)
from formal.python.toe.generic_runner.verified_calculator.dimensions import DimensionQuotientV1, DimensionVectorV1
from formal.python.toe.generic_runner.verified_calculator.errors import CalculatorError, require
from formal.python.toe.generic_runner.verified_calculator.evidence import FrozenEvidenceBundleV1, RuntimeCertificateV1


AXES = (
    "mathematical_kind", "semantic_type", "physical_dimension_equivalence_class",
    "canonical_unit_convention", "exact_shape_and_rank", "ordered_index_spaces",
    "representation_tags", "domain_status_and_prerequisites",
)


def _now() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def _json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _checker(repo_root: Path) -> Path:
    suffix = ".exe" if os.name == "nt" else ""
    return repo_root / "formal" / "toe_formal" / ".lake" / "build" / "bin" / f"vpc_qualification_envelope_checker{suffix}"


def _invoke_lean(checker: Path, certificate: Mapping[str, Any], envelope: Mapping[str, Any], context: Mapping[str, Any], extra: tuple[str, ...] = ()) -> dict[str, Any]:
    with tempfile.TemporaryDirectory(prefix="vpc-v6-d01-") as directory:
        root = Path(directory)
        paths = []
        for name, value in (("certificate", certificate), ("envelope", envelope), ("context", context)):
            path = root / f"{name}.json"
            path.write_bytes(canonical_bytes(value))
            paths.append(path)
        process = subprocess.run([str(checker), *(str(path) for path in paths), *extra], capture_output=True, text=True, check=False)
        return {
            "exit_code": process.returncode,
            "stdout": process.stdout.strip(),
            "stderr": process.stderr.strip(),
            "input_sha256": {path.stem: hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        }


def _d07(bundle: Mapping[str, Any], peer_closure: Mapping[str, Any] | None) -> dict[str, Any]:
    require(len(bundle["dependency_manifests"]) == 1, "D07_CLOSURE_CENSUS")
    closure = bundle["dependency_manifests"][0]
    validate_dependency_closure_v2(closure)
    rows = [*closure["python"], closure["runtime_requirement_lock"], *closure["julia"], *closure["lean"], *closure["profile_policy_artifact_references"]]
    path_rows = [{
        "path": row["repository_relative_path"],
        "hash_domain": row["hash_domain"],
        "git_object_id": row["git_object_id"],
        "git_blob_sha256": row["git_blob_sha256"],
        "checkout_domain": row["checkout_domain"],
        "filesystem_sha256": row["filesystem_sha256"],
        "canonical_text_v1_sha256": row.get("canonical_text_v1_sha256"),
        "filesystem_canonical_text_v1_sha256": row.get("filesystem_canonical_text_v1_sha256"),
        "status": "PASS",
    } for row in rows]
    lf = b"xi1\nvalue = xi1\n"
    newline_variants = (lf, lf.replace(b"\n", b"\r\n"), b"xi1\r\nvalue = xi1\r")
    controls = {
        "A-P01-GIT-BLOB-PRIMARY": all(row["hash_domain"] == "GIT_BLOB_BYTES_V1" and len(row["git_blob_sha256"]) == 64 for row in rows),
        "A-P02-LF-CRLF-EQUIVALENCE": len({canonical_text_v1_sha256(row) for row in newline_variants}) == 1 and len({hashlib.sha256(row).hexdigest() for row in newline_variants}) == 3,
        "A-N01-GENUINE-CONTENT-MUTATION": canonical_text_v1_sha256(b"xi1\nvalue = xi1 + 1\n") != canonical_text_v1_sha256(lf),
        "A-N02-TRAILING-WHITESPACE-MUTATION": canonical_text_v1_sha256(b"xi1 \nvalue = xi1\n") != canonical_text_v1_sha256(lf),
        "A-N03-FINAL-NEWLINE-MUTATION": canonical_text_v1_sha256(lf[:-1]) != canonical_text_v1_sha256(lf),
    }
    try:
        canonical_text_v1_bytes(b"\xef\xbb\xbf" + lf)
        controls["A-N04-BOM"] = False
    except CalculatorError as exc:
        controls["A-N04-BOM"] = exc.code == "CANONICAL_TEXT_V1_BOM"
    binary_rows = [row for row in rows if row["checkout_domain"] == "BINARY_BYTES_V1"]
    controls["A-N05-BINARY-NEWLINE-LAUNDERING"] = all(row["git_blob_sha256"] == row["filesystem_sha256"] for row in binary_rows)
    controls["A-N06-WORKTREE-ONLY-DEPENDENCY"] = all(row["git_object_id"] and row["git_commit"] == closure["tested_commit"] for row in rows)
    mismatch_paths = {"lean-toolchain", "lakefile.toml", "lake-manifest.json"}
    controls["V5-THREE-PATH-RECHECK"] = all(any(Path(row["repository_relative_path"]).name == name for row in rows) for name in mismatch_paths)
    controls["NO-UNRESOLVED-OR-MANUAL-EXCLUSIONS"] = not closure["unresolved_runtime_requirements"] and not closure["unresolved_dynamic_imports"] and not closure["manually_excluded_dependencies"]
    peer = None
    if peer_closure is not None:
        validate_dependency_closure_v2(peer_closure)
        stable = lambda value: {key: item for key, item in value.items() if key not in {"filesystem_sha256", "filesystem_canonical_text_v1_sha256"}}
        peer = {
            "closure_hash_match": closure["closure_hash"] == peer_closure["closure_hash"],
            "tested_commit_match": closure["tested_commit"] == peer_closure["tested_commit"],
            "path_identity_match": sorted((row["repository_relative_path"], stable(row)) for row in rows) == sorted((row["repository_relative_path"], stable(row)) for row in [*peer_closure["python"], peer_closure["runtime_requirement_lock"], *peer_closure["julia"], *peer_closure["lean"], *peer_closure["profile_policy_artifact_references"]]),
        }
        controls["A-P03-CLEAN-CHECKOUT-CLOSURE"] = all(peer.values())
    else:
        controls["A-P03-CLEAN-CHECKOUT-CLOSURE"] = None
    local_pass = all(value is True for key, value in controls.items() if key != "A-P03-CLEAN-CHECKOUT-CLOSURE")
    status = "PASS" if local_pass and controls["A-P03-CLEAN-CHECKOUT-CLOSURE"] is True else "INCONCLUSIVE" if local_pass else "FAIL"
    return {"status": status, "closure": closure, "per_path_ledger": path_rows, "controls": controls, "peer_comparison": peer}


def _changed_hex(value: str, digit: str) -> str:
    return digit * 64 if value != digit * 64 else ("e" if digit != "e" else "d") * 64


def _d01(repo_root: Path, bundle: Mapping[str, Any]) -> dict[str, Any]:
    checker = _checker(repo_root)
    require(checker.is_file(), "D01_CHECKER_NOT_BUILT", detail=str(checker))
    lean_rows = [row for row in bundle["verifier_evidence"] if row["evidence_kind"] == "LEAN_QUALIFICATION_ENVELOPE_CHECK"]
    require(len(lean_rows) == 1, "D01_EVIDENCE_CENSUS")
    payload = lean_rows[0]["payload"]
    certificate = dict(bundle["runtime_certificate"])
    envelope = dict(payload["qualification_envelope"])
    context = {"schema_id": "QualificationExpectedContextV1", **{key: value for key, value in envelope.items() if key != "schema_id"}}
    controls: list[dict[str, Any]] = []

    def record(case_id: str, observed: Mapping[str, Any], expected_accept: bool) -> None:
        accepted = observed["exit_code"] == 0
        controls.append({"case_id": case_id, "expected": "ACCEPT" if expected_accept else "REJECT", "observed": dict(observed), "status": "PASS" if accepted == expected_accept else "FAIL"})

    record("B-P01-ACTUAL-RUNTIME-EVIDENCE", _invoke_lean(checker, certificate, envelope, context), True)
    record("B-P02-SEPARATE-REPLAY", _invoke_lean(checker, certificate, envelope, context), True)
    substituted_certificate = dict(certificate)
    substituted_certificate["computation_id"] = _changed_hex(certificate["computation_id"], "6")
    substitute = dict(envelope)
    substitute["runtime_certificate_hash"] = RuntimeCertificateV1.from_dict(substituted_certificate).certificate_hash
    substitute["computation_id"] = substituted_certificate["computation_id"]
    record("B-N01-VALID-SUBSTITUTE-SAME-OUTPUT", _invoke_lean(checker, substituted_certificate, substitute, context), False)
    for name, chosen in (("ZERO", "0" * 64), ("FF", "f" * 64), ("ARBITRARY", "a" * 64)):
        record(f"B-N02-CALLER-CHOSEN-HASH-{name}", _invoke_lean(checker, certificate, envelope, context, (chosen,)), False)
    for case_id, fields in (
        ("B-N03-CONTRACT-IDENTITY", ("computation_id", "calculation_request_hash", "candidate_hash", "physics_profile_hash", "verification_policy_hash")),
        ("B-N04-GRAPH-TRACE-SOURCE", ("graph_hash", "ordered_node_trace_hash", "source_receipt_set_hash")),
        ("B-N05-OUTPUT-ROOT-VALUE", ("canonical_exact_output_value_hashes",)),
        ("B-N06-INDEPENDENT-EVIDENCE", ("julia_evidence_hash", "mandatory_challenge_spec_set_hash", "mandatory_challenge_packet_set_hash", "mandatory_challenge_result_set_hash", "challenge_applicability_hash", "type_signature_set_hash")),
    ):
        for field in fields:
            mutant = deepcopy(envelope)
            if field == "canonical_exact_output_value_hashes":
                root = sorted(mutant[field])[0]
                mutant[field][root] = _changed_hex(mutant[field][root], "3")
            else:
                mutant[field] = _changed_hex(mutant[field], "4")
            record(f"{case_id}:{field}", _invoke_lean(checker, certificate, mutant, context), False)
    for field, changed in (("status_ceiling", "VERIFIED_EXACT"), ("scientific_promotion", True), ("product_v1_release", True), ("production_activation", True)):
        mutant = dict(envelope); mutant[field] = changed
        record(f"B-N07-STATUS-OR-PROMOTION:{field}", _invoke_lean(checker, certificate, mutant, context), False)
    broken_bundle = deepcopy(bundle)
    broken_bundle["verification_receipt"]["runtime_certificate_hash"] = "7" * 64
    try:
        FrozenEvidenceBundleV1.from_dict(broken_bundle)
        edge = {"case_id": "B-N08-RECEIPT-BUNDLE-EDGE", "expected": "REJECT", "observed": "ACCEPT", "status": "FAIL"}
    except CalculatorError as exc:
        edge = {"case_id": "B-N08-RECEIPT-BUNDLE-EDGE", "expected": "REJECT", "observed": exc.code, "status": "PASS"}
    controls.append(edge)
    return {
        "status": "PASS" if all(row["status"] == "PASS" for row in controls) else "FAIL",
        "checker_path": checker.as_posix(),
        "checker_sha256": hashlib.sha256(checker.read_bytes()).hexdigest(),
        "accepted_envelope_hash": payload["accepted_envelope_hash"],
        "bound_runtime_certificate_hash": payload["bound_runtime_certificate_hash"],
        "controls": controls,
    }


def _mutated_type(base: Mapping[str, Any], axis: str, semantic_alternate: str, unit_alternate: str) -> dict[str, Any]:
    value = deepcopy(dict(base))
    if axis == "mathematical_kind": value["mathematical_kind"] = "EXACT_ATOM" if base["mathematical_kind"] != "EXACT_ATOM" else "EXACT_SCALAR"
    elif axis == "semantic_type": value["semantic_type"] = semantic_alternate
    elif axis == "physical_dimension_equivalence_class": value["dimension"] = ["1", "0", "0"] if base["dimension"] != ["1", "0", "0"] else ["0", "1", "0"]
    elif axis == "canonical_unit_convention": value["unit_convention"] = unit_alternate
    elif axis == "exact_shape_and_rank": value["shape"] = [13] if base["shape"] != [13] else []
    elif axis == "ordered_index_spaces": value["index_spaces"] = ["NATIVE_E"] if base["index_spaces"] != ["NATIVE_E"] else []
    elif axis == "representation_tags": value["representation_tags"] = ["BMHV"] if base["representation_tags"] != ["BMHV"] else []
    elif axis == "domain_status_and_prerequisites": value["domain"] = {**base["domain"], "status": "UNEVALUATED"}
    else: raise ValueError(axis)
    return value


def _d02(bundle: Mapping[str, Any]) -> dict[str, Any]:
    profile, policy, request, candidate = verified_calculator_c03_rv_candidate_v2.candidate()
    nodes = {row["node_id"]: NodeV1.from_dict(row, profile) for row in candidate.graph["nodes"]}
    registry = trusted_value_type_registry()
    require(len(nodes) == len(registry) == 207, "D02_NODE_CENSUS")
    baseline = [validate_node_type(nodes[identity]).to_dict() for identity in sorted(nodes)]
    alternate_semantic = {identity: next(value for value in profile.semantic_types if value != nodes[identity].value_type.semantic_type) for identity in nodes}
    unit_alternate = "SYNTHETIC_ALTERNATE_UNIT"
    profile_for_mutations = replace(profile, unit_conventions=(*profile.unit_conventions, unit_alternate))
    mutations = []
    for identity in sorted(nodes):
        base = registry[identity]
        for axis in AXES:
            raw = nodes[identity].to_dict()
            raw["value_type"] = _mutated_type(base, axis, alternate_semantic[identity], unit_alternate)
            mutant = NodeV1.from_dict(raw, profile_for_mutations)
            try:
                validate_node_type(mutant)
                result = {"status": "FAIL", "error_code": None, "location": None}
            except CalculatorError as exc:
                result = {"status": "PASS" if exc.code == "C03_RV_VALUE_TYPE_SIGNATURE" and exc.location == identity else "FAIL", "error_code": exc.code, "location": exc.location}
            mutations.append({"node_id": identity, "axis": axis, **result})
    edge_mutations = []
    for identity in sorted(row for row, node in nodes.items() if node.kind == "DERIVED"):
        node = nodes[identity]
        replacement = next(value for value in sorted(nodes) if value not in node.parents and value != identity)
        mutant = replace(node, parents=(replacement, *node.parents[1:]) if node.parents else (replacement,))
        try:
            validate_node_edge(mutant, {**nodes, identity: mutant})
            result = {"status": "FAIL", "error_code": None, "location": None}
        except CalculatorError as exc:
            result = {"status": "PASS" if exc.code == "C03_RV_TYPE_EDGE_SIGNATURE" and exc.location == identity else "FAIL", "error_code": exc.code, "location": exc.location}
        edge_mutations.append({"node_id": identity, "replacement_parent": replacement, **result})
    quotient = DimensionQuotientV1(physics_profile(()).dimensions)
    mass = DimensionVectorV1.decode(["1", "0", "0"], physics_profile(()).dimensions)
    inverse_length = DimensionVectorV1.decode(["0", "-1", "0"], physics_profile(()).dimensions)
    zero = DimensionVectorV1.decode(["0", "0", "0"], physics_profile(()).dimensions)
    quotient_control = quotient.equivalent(mass, inverse_length) and not quotient.equivalent(mass, zero)
    python_payload = next(row["payload"] for row in bundle["verifier_evidence"] if row["evidence_kind"] == "PYTHON_TRUSTED_VERIFICATION")
    retained_receipts = python_payload.get("type_signature_receipts", [])
    retention = len(retained_receipts) == 207 and digest(retained_receipts, "C03RVTypeSignatureReceiptSetV1") == next(row["payload"]["qualification_envelope"]["type_signature_set_hash"] for row in bundle["verifier_evidence"] if row["evidence_kind"] == "LEAN_QUALIFICATION_ENVELOPE_CHECK")
    invalid = candidate.to_dict()
    invalid["graph"]["nodes"][0]["value_type"] = _mutated_type(invalid["graph"]["nodes"][0]["value_type"], "semantic_type", alternate_semantic[invalid["graph"]["nodes"][0]["node_id"]], unit_alternate)
    invalid["candidate_hash"] = None if "candidate_hash" in invalid else None
    invalid.pop("candidate_hash", None)
    invalid_rejected = False
    invalid_code = None
    try:
        mutant_candidate = CandidatePacketV1.from_dict(invalid, profile)
        api.evaluate_candidate(api.ContractSetV1(profile, policy, verified_calculator_c03_rv_candidate_v2.v1.normalization.ROOT), request, mutant_candidate)
    except CalculatorError as exc:
        invalid_rejected = True; invalid_code = exc.code
    status = "PASS" if all(row["status"] == "PASS" for row in mutations) and all(row["status"] == "PASS" for row in edge_mutations) and quotient_control and retention and invalid_rejected else "FAIL"
    return {
        "status": status,
        "baseline_signature_receipts": baseline,
        "baseline_count": len(baseline),
        "metadata_mutation_results": mutations,
        "metadata_mutation_count": len(mutations),
        "edge_mutation_results": edge_mutations,
        "edge_mutation_count": len(edge_mutations),
        "natural_unit_quotient_control": quotient_control,
        "bundle_type_receipt_retention": retention,
        "metadata_invalid_candidate_rejected_before_certificate": invalid_rejected,
        "metadata_invalid_candidate_error_code": invalid_code,
    }


def execute(repo_root: Path, bundle_path: Path, output_path: Path, attempt_id: str, peer_closure_path: Path | None) -> dict[str, Any]:
    bundle = _json(bundle_path)
    FrozenEvidenceBundleV1.from_dict(bundle)
    peer = _json(peer_closure_path) if peer_closure_path else None
    started = _now()
    d07 = _d07(bundle, peer)
    d01 = _d01(repo_root, bundle)
    d02 = _d02(bundle)
    result = {
        "schema_id": "VerifiedCalculatorC03RVExactV6RepairAcceptanceResultV1",
        "attempt_id": attempt_id,
        "started_at": started,
        "completed_at": _now(),
        "bundle": {"path": bundle_path.as_posix(), "bundle_id": bundle_path.stem, "raw_file_sha256": hashlib.sha256(bundle_path.read_bytes()).hexdigest()},
        "tested_commit": d07["closure"]["tested_commit"],
        "D-07": d07,
        "D-01": d01,
        "D-02": d02,
        "status": "PASS" if all(row["status"] == "PASS" for row in (d07, d01, d02)) else "INCONCLUSIVE" if d01["status"] == d02["status"] == "PASS" and d07["status"] == "INCONCLUSIVE" else "FAIL",
        "scientific_promotion": False,
        "product_v1_release": False,
        "production_activation": False,
    }
    result["result_hash"] = digest(result, result["schema_id"])
    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_bytes(canonical_bytes(result))
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--bundle", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--attempt-id", required=True)
    parser.add_argument("--peer-closure", type=Path)
    args = parser.parse_args()
    result = execute(args.repo_root.resolve(), args.bundle.resolve(), args.output.resolve(), args.attempt_id, args.peer_closure.resolve() if args.peer_closure else None)
    print(json.dumps({"status": result["status"], "D-07": result["D-07"]["status"], "D-01": result["D-01"]["status"], "D-02": result["D-02"]["status"], "result_hash": result["result_hash"]}, sort_keys=True))


if __name__ == "__main__":
    main()

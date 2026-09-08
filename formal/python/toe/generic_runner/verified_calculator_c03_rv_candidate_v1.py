"""Untrusted C03/RV proposal adapter for Verified Physics Calculator v1.

This module intentionally lives outside the trusted package.  It reads the
preserved repair corpus and emits candidate values; the trusted verifier must
independently recompute every derived node.
"""
from __future__ import annotations

import argparse
from pathlib import Path
from typing import Any, Mapping

import sympy as sp

from formal.python.toe.generic_runner import c03_normalization_v1 as normalization
from formal.python.toe.generic_runner import c03_physical_dag_verifier_v1 as candidate_c03_operations
from formal.python.toe.generic_runner import fine_verification_profile_v1 as candidate_profile
from formal.python.toe.generic_runner import native_e_operation_checker_v1 as candidate_native_operations
from formal.python.toe.generic_runner import rv_operation_checker_v1 as candidate_rv_operations
from formal.python.toe.generic_runner.verified_calculator.canonical import canonical_json, digest, file_sha256
from formal.python.toe.generic_runner.verified_calculator.c03_rv_operation_contracts import DERIVED_SIGNATURES, SOURCE_SIGNATURES
from formal.python.toe.generic_runner.verified_calculator.c03_rv_policy import physics_profile, verification_policy
from formal.python.toe.generic_runner.verified_calculator.c03_rv_profile_values import encode_profile_value, wrapped_profile_value
from formal.python.toe.generic_runner.verified_calculator.contracts import CalculationRequestV1, CandidatePacketV1
from formal.python.toe.generic_runner.verified_calculator.errors import require
from formal.python.toe.generic_runner.verified_calculator.exact import ExactRuntimeV1


MATERIAL_CONTRACT_RELATIVE = "formal/docs/release/VERIFIED_CALCULATOR_C03_RV_SOURCE_MATERIAL_CONTRACT_20260905_v1.json"


def _typed_reference(reference: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "type": "JsonPointerValueRef",
        "artifact_path": reference["artifact_path"],
        "artifact_sha256": reference["artifact_sha256"],
        "pointer": reference["semantic_locator"],
    }


def source_material_contract(root: Path = normalization.ROOT) -> dict[str, Any]:
    material, _ = candidate_profile.source_material(root)
    require(set(material) == set(SOURCE_SIGNATURES), "C03_RV_CANDIDATE_SOURCE_CENSUS")
    nodes: dict[str, Any] = {}
    for node_id in sorted(material):
        row = material[node_id]
        references = [_typed_reference(reference) for reference in row["evidence_refs"]]
        encoded = encode_profile_value(row["typed_value"])
        nodes[node_id] = {
            "semantic_type": row["semantic_type"],
            "source_operation": row["operation"],
            "profile_value_digest": digest(encoded, "C03RVProfileValueV1"),
            "evidence_references_digest": digest(references, "C03RVSourceEvidenceReferencesV1"),
            "evidence_reference_count": len(references),
        }
    return {
        "schema_id": "C03RVSourceMaterialContractV1",
        "profile_id": "C03_RV_SU5_EXACT_PROFILE_v1",
        "nodes": nodes,
        "source_material_is_output_answer_table": False,
        "scientific_promotion": False,
    }


def source_declarations(root: Path = normalization.ROOT) -> tuple[dict[str, Any], ...]:
    _, profile = normalization.load_contract(root)
    rows = [dict(row) for row in profile["allowed_inputs"]]
    contract = profile["contract"]
    contract_path = root / contract["path"]
    rows.append({"path": contract["path"], "sha256": contract["sha256"], "byte_size": contract["byte_size"], "media_type": "application/json"})
    material_path = root / MATERIAL_CONTRACT_RELATIVE
    require(material_path.is_file(), "C03_RV_SOURCE_MATERIAL_CONTRACT_MISSING")
    rows.append({"path": MATERIAL_CONTRACT_RELATIVE, "sha256": file_sha256(material_path), "byte_size": material_path.stat().st_size, "media_type": "application/json"})
    normalized = []
    for row in rows:
        normalized.append({"path": row["path"], "sha256": row["sha256"], "byte_size": row["byte_size"], "media_type": row.get("media_type", "application/json")})
    require(len({row["path"] for row in normalized}) == len(normalized), "C03_RV_SOURCE_DECLARATION_DUPLICATE")
    return tuple(sorted(normalized, key=lambda row: row["path"]))


def _candidate_native_operation(node_id: str, parents: list[Any]) -> Any:
    """Evaluate proposal-side native operations with canonical exact equality.

    The preserved checker compares two algebraically equal SymPy matrices by
    structure at WITNESS/RESIDUAL.  The candidate adapter must be able to emit
    the frozen calculation without modifying that preservation checkpoint.
    """
    suffix = node_id.removeprefix("C03.NATIVE.")
    if suffix == "WITNESS":
        relations, ambient, projected = parents
        target = sp.Matrix(ambient) - sp.Matrix(projected)
        solution, parameters = relations.T.gauss_jordan_solve(target)
        solution = solution.subs({symbol: 0 for symbol in parameters}).applyfunc(sp.cancel)
        require(
            all(sp.cancel(value) == 0 for value in relations.T * solution - target),
            "C03_NATIVE_CANDIDATE_RELATION_WITNESS",
        )
        return {"coefficients": list(solution)}
    if suffix == "RESIDUAL":
        ambient, projected, relation_part, witness, relations = parents
        remainder = sp.Matrix(ambient) - sp.Matrix(projected)
        witness_delta = (remainder - relations.T * sp.Matrix(witness["coefficients"])).applyfunc(sp.cancel)
        part_delta = (remainder - sp.Matrix(relation_part)).applyfunc(sp.cancel)
        require(all(value == 0 for value in witness_delta), "C03_NATIVE_CANDIDATE_WITNESS_RESIDUAL")
        require(all(value == 0 for value in part_delta), "C03_NATIVE_CANDIDATE_RELATION_RESIDUAL")
        return tuple(sp.cancel(value) for value in part_delta)
    return candidate_native_operations.operation(node_id, parents)


def contracts(root: Path = normalization.ROOT):
    profile = physics_profile(source_declarations(root))
    policy = verification_policy()
    request = CalculationRequestV1(
        profile.contract_hash,
        policy.contract_hash,
        {"frozen_source_material_contract_sha256": next(row["sha256"] for row in profile.source_declarations if row["path"] == MATERIAL_CONTRACT_RELATIVE)},
        tuple(profile.output_roots),
        {"total_seconds": policy.resource_limits.trusted_total_seconds, "python_seconds": policy.resource_limits.trusted_route_seconds, "julia_seconds": policy.resource_limits.trusted_route_seconds, "lean_seconds": policy.resource_limits.trusted_route_seconds, "challenge_seconds": policy.resource_limits.trusted_route_seconds},
    )
    return profile, policy, request


def _topological_values(material: Mapping[str, Any]) -> dict[str, Any]:
    values = {
        node_id: (
            candidate_c03_operations.x.typed_decode(row["semantic_type"], row["typed_value"])
            if row["semantic_type"] in candidate_c03_operations.x.SCALARS
            else row["typed_value"]
        )
        for node_id, row in material.items()
    }
    pending = set(DERIVED_SIGNATURES)
    while pending:
        ready = sorted(node_id for node_id in pending if set(DERIVED_SIGNATURES[node_id]["parents"]) <= set(values))
        require(ready, "C03_RV_CANDIDATE_TOPOLOGY")
        for node_id in ready:
            spec = DERIVED_SIGNATURES[node_id]
            parents = [values[parent] for parent in spec["parents"]]
            if spec["operation"] == "OUTPUT_BIND":
                value = parents[0]
            elif node_id.startswith("C03.NATIVE."):
                value = _candidate_native_operation(node_id, parents)
            elif node_id.startswith("C03."):
                value = candidate_c03_operations.operation(node_id, parents)[0]
            elif node_id == "RV03.CHANNEL":
                # Candidate-side repair for a preserved historical checker
                # that recognizes the obsolete shorthand ``2`` while the
                # frozen source spells the representation ``FUNDAMENTAL_2``.
                # This remains proposal code; the trusted route implements
                # and checks the operation independently.
                context, admission, tensor = parents
                record = context["record"]
                require(record["topology"]["coupling_monomial"][0] == "g2", "RV03_CANDIDATE_CHANNEL_GAUGE")
                require(record["registered"] is None, "RV03_CANDIDATE_CHANNEL_REGISTERED")
                require(record["fields"][0]["su2"] == "FUNDAMENTAL_2", "RV03_CANDIDATE_CHANNEL_REPRESENTATION")
                require(tensor["dims"] == [2, 2, 2, 2], "RV03_CANDIDATE_CHANNEL_DIMENSIONS")
                tensor_data = {tuple(entry["index"]): entry["coefficient"] for entry in tensor["entries"]}
                require(
                    all(
                        sp.simplify(value - tensor_data.get((index[1], index[0], index[2], index[3]), 0)) == 0
                        for index, value in tensor_data.items()
                    ),
                    "RV03_CANDIDATE_CHANNEL_SYMMETRY",
                )
                value = "WEAK_TRIPLET_A_FLAVOR"
            else:
                value = candidate_rv_operations.operation(node_id, parents)
            values[node_id] = value
            pending.remove(node_id)
    return values


def _exact_output(runtime: ExactRuntimeV1, semantic_type: str, value: Any) -> dict[str, Any]:
    if semantic_type in {"SYMBOLIC_COEFFICIENT", "SYMBOLIC_SCALAR"}:
        return runtime.parse_rational_text(sp.sstr(sp.cancel(value))).to_dict()
    if semantic_type == "NATIVE_COORDINATE_VECTOR":
        entries = list(value) if isinstance(value, sp.MatrixBase) else list(value)
        return runtime.tensor((len(entries),), [runtime.parse_rational_text(sp.sstr(sp.cancel(item))) for item in entries]).to_dict()
    if semantic_type == "EVANESCENT_EVALUATION_STATE":
        return {"kind": "ATOM", "atom_type": "ENUM", "value": str(value)}
    if semantic_type == "SYMBOL_TEXT":
        return {"kind": "ATOM", "atom_type": "SYMBOL_TEXT", "value": str(value)}
    raise ValueError(f"unsupported output semantic type: {semantic_type}")


def candidate(root: Path = normalization.ROOT) -> tuple[Any, Any, CalculationRequestV1, CandidatePacketV1]:
    material, _ = candidate_profile.source_material(root)
    profile, policy, request = contracts(root)
    values = _topological_values(material)
    runtime = ExactRuntimeV1(profile.algebraic_field, profile.symbols, policy.resource_limits)
    material_contract_path = next(row for row in profile.source_declarations if row["path"] == MATERIAL_CONTRACT_RELATIVE)
    nodes: list[dict[str, Any]] = []
    source_bindings: list[dict[str, Any]] = []
    zero_dimension = ["0"] * len(profile.dimensions.basis)
    for node_id in sorted(SOURCE_SIGNATURES):
        row = material[node_id]
        references = [_typed_reference(reference) for reference in row["evidence_refs"]]
        reference = {"type": "JsonPointerValueRef", "artifact_path": MATERIAL_CONTRACT_RELATIVE, "artifact_sha256": material_contract_path["sha256"], "pointer": f"/nodes/{node_id}/profile_value_digest"}
        parameters = {"reference": reference, "evidence_references": references}
        nodes.append({
            "node_id": node_id,
            "kind": "SOURCE",
            "operation": "SOURCE_DECODE",
            "parents": [],
            "parameters": parameters,
            "value_type": {"mathematical_kind": "EXACT_DOCUMENT", "semantic_type": row["semantic_type"], "dimension": zero_dimension, "unit_convention": "SU5_NATURAL_HBAR_C_1", "index_spaces": [], "representation_tags": ["SU5"], "domain": {"profile": "C03_RV_SU5_EXACT_PROFILE_v1"}},
            "claimed_value": wrapped_profile_value(row["typed_value"]),
        })
        source_bindings.append({"node_id": node_id, **parameters})
    for node_id in sorted(DERIVED_SIGNATURES):
        spec = DERIVED_SIGNATURES[node_id]
        output = spec["kind"] == "OUTPUT"
        claimed = _exact_output(runtime, spec["semantic_type"], values[node_id]) if output else wrapped_profile_value(values[node_id])
        mathematical_kind = "EXACT_DOCUMENT"
        index_spaces: list[str] = []
        if output:
            if spec["semantic_type"] in {"SYMBOLIC_COEFFICIENT", "SYMBOLIC_SCALAR"}:
                mathematical_kind = "EXACT_SCALAR"
            elif spec["semantic_type"] == "NATIVE_COORDINATE_VECTOR":
                mathematical_kind, index_spaces = "EXACT_TENSOR", ["NATIVE_E"]
            else:
                mathematical_kind = "EXACT_ATOM"
        nodes.append({
            "node_id": node_id,
            "kind": spec["kind"],
            "operation": spec["operation"],
            "parents": list(spec["parents"]),
            "parameters": {},
            "value_type": {"mathematical_kind": mathematical_kind, "semantic_type": spec["semantic_type"], "dimension": zero_dimension, "unit_convention": "SU5_NATURAL_HBAR_C_1", "index_spaces": index_spaces, "representation_tags": ["SU5"], "domain": {"profile": "C03_RV_SU5_EXACT_PROFILE_v1"}},
            "claimed_value": claimed,
        })
    graph = {"nodes": nodes, "edges": [[parent, node["node_id"]] for node in nodes for parent in node["parents"]]}
    outputs = {root: next(node["claimed_value"] for node in nodes if node["node_id"] == root) for root in profile.output_roots}
    packet = CandidatePacketV1(request.computation_id, {"producer_id": "C03_RV_PRESERVED_INDEPENDENT_CHECKER_PROPOSAL_v1", "trust": "UNTRUSTED_PROPOSAL", "imports_trusted_physics_operations": False}, graph, outputs, tuple(source_bindings), {"candidate_route": "PRESERVED_REPAIR_CORPUS", "comparison_oracle_read": False})
    return profile, policy, request, packet


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("material-contract", "profile", "policy", "request", "candidate"))
    args = parser.parse_args()
    if args.mode == "material-contract":
        value = source_material_contract()
    else:
        profile, policy, request, packet = candidate()
        value = {"profile": profile.to_dict(), "policy": policy.to_dict(), "request": request.to_dict(), "candidate": packet.to_dict()}[args.mode]
    print(canonical_json(value))


if __name__ == "__main__":
    main()

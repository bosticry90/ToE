"""Trusted Python verifier for the frozen 207-node C03/RV exact profile.

The module imports no historical runner, candidate, oracle, or acceptance
code.  It consumes only the profile contract, hash-bound source declarations,
the source-material decoder contract, and an untrusted candidate packet.
"""
from __future__ import annotations

from collections import deque
from pathlib import Path
from typing import Any, Mapping

import sympy as sp

from .canonical import digest
from .c03_rv_operation_contracts import DERIVED_SIGNATURES, SOURCE_SIGNATURES, execute_trusted_python, validate_operation_contracts
from .c03_rv_profile_values import encode_profile_value, unwrap_profile_value
from . import c03_rv_operation_support as operation_support
from .contracts import CandidatePacketV1, PhysicsProfileV1, ResourceLimitsV1
from .dag import EvaluationResultV1, NodeReceiptV1, NodeV1
from .errors import require
from .exact import ExactAtomV1, ExactRuntimeV1, ExactValueV1
from .sources import SourceResolverV1


MATERIAL_CONTRACT_SCHEMA = "C03RVSourceMaterialContractV1"
PROFILE_SCALAR_SOURCE_TYPES = {"INTEGER", "SIGN", "RATIONAL", "PHASE", "SYMBOL", "SYMBOLIC_SCALAR", "SYMBOLIC_COEFFICIENT", "INVERTIBLE_SCALE"}


def _profile_digest(value: Any) -> str:
    return digest(encode_profile_value(value), "C03RVProfileValueV1")


def _exact_output(runtime: ExactRuntimeV1, semantic_type: str, value: Any) -> ExactValueV1:
    if semantic_type in {"SYMBOLIC_COEFFICIENT", "SYMBOLIC_SCALAR"}:
        return runtime.parse_rational_text(sp.sstr(sp.cancel(value)))
    if semantic_type == "NATIVE_COORDINATE_VECTOR":
        entries = list(value)
        return runtime.tensor((len(entries),), [runtime.parse_rational_text(sp.sstr(sp.cancel(item))) for item in entries])
    if semantic_type == "EVANESCENT_EVALUATION_STATE":
        return ExactAtomV1("ENUM", str(value))
    if semantic_type == "SYMBOL_TEXT":
        return ExactAtomV1("SYMBOL_TEXT", str(value))
    raise ValueError(f"unsupported C03/RV output semantic type: {semantic_type}")


class C03RVExactProfileVerifierV1:
    def __init__(self, profile: PhysicsProfileV1, resolver: SourceResolverV1, limits: ResourceLimitsV1 | None = None) -> None:
        require(profile.profile_id == "C03_RV_SU5_EXACT_PROFILE_v1", "C03_RV_PROFILE_ID")
        validate_operation_contracts()
        self.profile = profile
        self.resolver = resolver
        self.limits = limits or ResourceLimitsV1()
        self.exact = ExactRuntimeV1(profile.algebraic_field, profile.symbols, self.limits)

    def _validate_graph(self, packet: CandidatePacketV1) -> tuple[dict[str, NodeV1], tuple[str, ...], str]:
        require(packet.producer.get("imports_trusted_physics_operations") is False, "C03_RV_CANDIDATE_VERIFIER_ROUTINE_SHARING")
        graph = packet.graph
        require(set(graph) == {"nodes", "edges"}, "GRAPH_FIELDS")
        raw_nodes = graph["nodes"]
        require(isinstance(raw_nodes, list) and len(raw_nodes) == 207 <= self.limits.dag_nodes, "C03_RV_NODE_CENSUS")
        nodes: dict[str, NodeV1] = {}
        for raw in raw_nodes:
            node = NodeV1.from_dict(raw, self.profile)
            require(node.node_id not in nodes, "DUPLICATE_NODE", node.node_id)
            nodes[node.node_id] = node
        require(set(nodes) == set(SOURCE_SIGNATURES) | set(DERIVED_SIGNATURES), "C03_RV_EXACT_NODE_SET")
        for node_id, semantic_type in SOURCE_SIGNATURES.items():
            node = nodes[node_id]
            require(node.kind == "SOURCE" and node.operation == "SOURCE_DECODE" and not node.parents and node.value_type.mathematical_kind == "EXACT_DOCUMENT" and node.value_type.semantic_type == semantic_type, "C03_RV_SOURCE_SIGNATURE", node_id)
        for node_id, signature in DERIVED_SIGNATURES.items():
            node = nodes[node_id]
            require(node.kind == signature["kind"] and node.operation == signature["operation"] and node.parents == signature["parents"] and node.value_type.semantic_type == signature["semantic_type"], "C03_RV_DERIVED_SIGNATURE", node_id)
            require(not node.parameters, "C03_RV_DERIVED_PARAMETERS", node_id)
            require((node.value_type.mathematical_kind != "EXACT_DOCUMENT") == (signature["kind"] == "OUTPUT"), "C03_RV_OUTPUT_VALUE_KIND", node_id)
        expected_edges = {(parent, node.node_id) for node in nodes.values() for parent in node.parents}
        edges = graph["edges"]
        require(isinstance(edges, list) and all(isinstance(edge, list) and len(edge) == 2 and all(isinstance(item, str) for item in edge) for edge in edges), "EDGE_SCHEMA")
        actual_edges = {tuple(edge) for edge in edges}
        require(len(actual_edges) == len(edges) and actual_edges == expected_edges, "PARENT_EDGE_DISAGREEMENT")
        source_bindings = {row.get("node_id"): row for row in packet.source_bindings}
        require(len(source_bindings) == len(packet.source_bindings) and set(source_bindings) == set(SOURCE_SIGNATURES), "C03_RV_SOURCE_BINDING_SET")
        for node_id in SOURCE_SIGNATURES:
            node = nodes[node_id]
            require(source_bindings[node_id] == {"node_id": node_id, **node.parameters}, "C03_RV_SOURCE_BINDING_MISMATCH", node_id)
        require(set(packet.claimed_outputs) == set(self.profile.output_roots), "CLAIMED_OUTPUT_SET")
        pending = set(nodes)
        visited: set[str] = set()
        order: list[str] = []
        while pending:
            ready = sorted(node_id for node_id in pending if set(nodes[node_id].parents) <= visited)
            require(ready, "CYCLIC_GRAPH")
            order.extend(ready)
            visited.update(ready)
            pending.difference_update(ready)
        graph_hash = digest({"nodes": [nodes[node_id].to_dict() for node_id in sorted(nodes)], "edges": [list(edge) for edge in sorted(actual_edges)]}, "CandidateGraphV1")
        return nodes, tuple(order), graph_hash

    def _source_value(self, node: NodeV1) -> tuple[Any, Mapping[str, Any]]:
        require(set(node.parameters) == {"reference", "evidence_references"}, "C03_RV_SOURCE_PARAMETERS", node.node_id)
        reference = node.parameters["reference"]
        evidence_references = node.parameters["evidence_references"]
        require(isinstance(evidence_references, list), "C03_RV_SOURCE_EVIDENCE_LIST", node.node_id)
        resolved_contract_value = self.resolver.resolve(reference)
        require(isinstance(resolved_contract_value.value, str) and len(resolved_contract_value.value) == 64, "C03_RV_SOURCE_MATERIAL_DIGEST", node.node_id)
        claimed_wire_value = unwrap_profile_value(node.claimed_value)
        claimed_digest = _profile_digest(claimed_wire_value)
        require(claimed_digest == resolved_contract_value.value, "C03_RV_SOURCE_MATERIAL_MISMATCH", node.node_id)
        contract_path = reference["artifact_path"]
        contract_document = self.resolver.documents[contract_path]
        require(contract_document.get("schema_id") == MATERIAL_CONTRACT_SCHEMA and contract_document.get("profile_id") == self.profile.profile_id and contract_document.get("source_material_is_output_answer_table") is False and contract_document.get("scientific_promotion") is False, "C03_RV_SOURCE_MATERIAL_CONTRACT")
        contract_row = contract_document["nodes"][node.node_id]
        require(contract_row["semantic_type"] == node.value_type.semantic_type and contract_row["profile_value_digest"] == claimed_digest, "C03_RV_SOURCE_MATERIAL_BINDING", node.node_id)
        require(contract_row["evidence_reference_count"] == len(evidence_references) and contract_row["evidence_references_digest"] == digest(evidence_references, "C03RVSourceEvidenceReferencesV1"), "C03_RV_SOURCE_EVIDENCE_BINDING", node.node_id)
        evidence_receipts = [self.resolver.resolve(item).receipt() for item in evidence_references]
        runtime_value = operation_support.exact_expr(claimed_wire_value) if node.value_type.semantic_type in PROFILE_SCALAR_SOURCE_TYPES else claimed_wire_value
        return runtime_value, {"material_contract": resolved_contract_value.receipt(), "evidence_references": evidence_receipts, "decoder_contract_schema": MATERIAL_CONTRACT_SCHEMA}

    def verify(self, packet: CandidatePacketV1) -> EvaluationResultV1:
        nodes, order, graph_hash = self._validate_graph(packet)
        output_by_parent = {
            nodes[root].parents[0]: (root, nodes[root].value_type.semantic_type)
            for root in self.profile.output_roots
        }
        values: dict[str, Any] = {}
        exact_outputs: dict[str, ExactValueV1] = {}
        receipts: list[NodeReceiptV1] = []
        for node_id in order:
            node = nodes[node_id]
            source_receipt = None
            if node.kind == "SOURCE":
                actual, source_receipt = self._source_value(node)
                claimed_digest = _profile_digest(unwrap_profile_value(node.claimed_value))
                value_digest = claimed_digest
            else:
                actual = execute_trusted_python(node_id, node.operation, [values[parent] for parent in node.parents])
                if node.kind == "OUTPUT":
                    actual_exact = _exact_output(self.exact, node.value_type.semantic_type, actual)
                    claimed_exact = self.exact.decode(node.claimed_value)
                    require(actual_exact.to_dict() == claimed_exact.to_dict(), "RECOMPUTATION_MISMATCH", node_id)
                    exact_outputs[node_id] = actual_exact
                    value_digest = digest(actual_exact.to_dict(), "ExactNodeValueV1")
                    claimed_digest = digest(claimed_exact.to_dict(), "ExactNodeValueV1")
                else:
                    claimed = unwrap_profile_value(node.claimed_value)
                    require(_profile_digest(actual) == _profile_digest(claimed), "RECOMPUTATION_MISMATCH", node_id)
                    value_digest = _profile_digest(actual)
                    claimed_digest = _profile_digest(claimed)
                    # A parent immediately bound to an authoritative root uses
                    # the same canonical exact-output digest as that root.
                    # This lets the runtime certificate checker validate the
                    # concrete parent/output binding across the profile-ledger
                    # and CanonicalMath serialization boundary.
                    if node_id in output_by_parent:
                        _, output_semantic_type = output_by_parent[node_id]
                        exact_parent = _exact_output(self.exact, output_semantic_type, actual)
                        value_digest = claimed_digest = digest(exact_parent.to_dict(), "ExactNodeValueV1")
            values[node_id] = actual
            receipts.append(NodeReceiptV1(node_id, node.kind, node.operation, node.parents, value_digest, claimed_digest, "RESOLVED_OR_RECOMPUTED_AND_EQUAL", source_receipt))
        require(set(exact_outputs) == set(self.profile.output_roots), "C03_RV_OUTPUT_SET")
        for root, value in exact_outputs.items():
            require(value.to_dict() == self.exact.decode(packet.claimed_outputs[root]).to_dict(), "EMITTED_ROOT_MISMATCH", root)
        ancestry: dict[str, tuple[str, ...]] = {}
        for root in self.profile.output_roots:
            active: set[str] = set()
            pending = deque([root])
            while pending:
                node_id = pending.popleft()
                if node_id not in active:
                    active.add(node_id)
                    pending.extend(nodes[node_id].parents)
            require(any(nodes[node_id].kind == "SOURCE" for node_id in active), "OUTPUT_WITHOUT_SOURCE", root)
            ancestry[root] = tuple(sorted(active))
        require(set().union(*(set(row) for row in ancestry.values())) == set(nodes), "DECORATIVE_NODE")
        return EvaluationResultV1(graph_hash, values, exact_outputs, tuple(receipts), ancestry)

    def probe_rejecting_challenge(
        self,
        packet: CandidatePacketV1,
        baseline: EvaluationResultV1,
        baseline_candidate: CandidatePacketV1,
        *,
        injection_node: str,
        resolve_source_node: str | None = None,
    ) -> EvaluationResultV1:
        """Check a reject-expected mutant against an already recomputed baseline.

        The frozen profile admits no dynamic operation signatures.  Therefore,
        after the mutation machinery has proved baseline binding and mutation
        confinement, this probe validates the one injected node, global edge
        consistency, source bindings, and all emitted roots against the
        receipt-bound baseline.  It does not rerun the expensive 38-dimensional
        native projection.  A source-locator mutant re-resolves its one changed
        source.  This path cannot issue a verification receipt and is used only
        to decide whether a controlled challenge mutant is rejected.
        """
        baseline_nodes = {
            row["node_id"]: row
            for row in baseline_candidate.graph["nodes"]
        }
        mutant_nodes = {row["node_id"]: row for row in packet.graph["nodes"]}
        require(len(mutant_nodes) == len(packet.graph["nodes"]) == 207, "C03_RV_CHALLENGE_NODE_CENSUS")
        require(set(baseline.values) == set(baseline_nodes) == set(mutant_nodes), "C03_RV_CHALLENGE_BASELINE_NODE_SET")
        require(injection_node in mutant_nodes, "C03_RV_CHALLENGE_INJECTION_NODE")
        require(packet.computation_id == baseline_candidate.computation_id and packet.producer == baseline_candidate.producer, "C03_RV_CHALLENGE_CANDIDATE_BINDING")
        require(
            all(mutant_nodes[node_id] == baseline_nodes[node_id] for node_id in mutant_nodes if node_id != injection_node),
            "C03_RV_CHALLENGE_MULTIPLE_NODE_MUTATION",
        )

        # A stale edge must be rejected even when the node mutation itself is
        # otherwise well-formed.  Computing this set is domain-neutral and
        # much cheaper than reparsing every large source-document value.
        expected_edges = {
            (parent, row["node_id"])
            for row in packet.graph["nodes"]
            for parent in row["parents"]
        }
        actual_edges = {tuple(edge) for edge in packet.graph["edges"]}
        require(len(actual_edges) == len(packet.graph["edges"]) and actual_edges == expected_edges, "PARENT_EDGE_DISAGREEMENT")

        node = NodeV1.from_dict(mutant_nodes[injection_node], self.profile)
        if injection_node in SOURCE_SIGNATURES:
            require(node.kind == "SOURCE" and node.operation == "SOURCE_DECODE" and not node.parents and node.value_type.mathematical_kind == "EXACT_DOCUMENT" and node.value_type.semantic_type == SOURCE_SIGNATURES[injection_node], "C03_RV_SOURCE_SIGNATURE", injection_node)
        else:
            signature = DERIVED_SIGNATURES[injection_node]
            require(node.kind == signature["kind"] and node.operation == signature["operation"] and node.parents == signature["parents"] and node.value_type.semantic_type == signature["semantic_type"], "C03_RV_DERIVED_SIGNATURE", injection_node)
            require(not node.parameters, "C03_RV_DERIVED_PARAMETERS", injection_node)

        source_bindings = {row.get("node_id"): row for row in packet.source_bindings}
        baseline_source_bindings = {row.get("node_id"): row for row in baseline_candidate.source_bindings}
        require(len(source_bindings) == len(packet.source_bindings) and set(source_bindings) == set(SOURCE_SIGNATURES), "C03_RV_SOURCE_BINDING_SET")
        require(
            all(source_bindings[node_id] == baseline_source_bindings[node_id] for node_id in source_bindings if node_id != injection_node),
            "C03_RV_CHALLENGE_MULTIPLE_SOURCE_BINDING_MUTATION",
        )
        if injection_node in SOURCE_SIGNATURES:
            require(source_bindings[injection_node] == {"node_id": injection_node, **node.parameters}, "C03_RV_SOURCE_BINDING_MISMATCH", injection_node)
        if resolve_source_node is not None:
            require(resolve_source_node == injection_node and resolve_source_node in SOURCE_SIGNATURES, "C03_RV_CHALLENGE_SOURCE_TARGET")
            resolved, _ = self._source_value(node)
            require(operation_support.exact_equal(resolved, baseline.values[injection_node]), "C03_RV_CHALLENGE_SOURCE_CHANGED", injection_node)
        elif node.kind == "SOURCE":
            require(node.to_dict() == baseline_nodes[injection_node], "C03_RV_CHALLENGE_UNEXPECTED_SOURCE_CHANGE", injection_node)
        elif node.kind == "OUTPUT":
            actual_exact = _exact_output(self.exact, node.value_type.semantic_type, baseline.values[injection_node])
            require(actual_exact.to_dict() == self.exact.decode(node.claimed_value).to_dict(), "RECOMPUTATION_MISMATCH", injection_node)
        else:
            claimed = unwrap_profile_value(node.claimed_value)
            require(_profile_digest(baseline.values[injection_node]) == _profile_digest(claimed), "RECOMPUTATION_MISMATCH", injection_node)
        for root in self.profile.output_roots:
            root_semantic_type = DERIVED_SIGNATURES[root]["semantic_type"]
            require(
                _exact_output(self.exact, root_semantic_type, baseline.values[root]).to_dict()
                == self.exact.decode(packet.claimed_outputs[root]).to_dict(),
                "EMITTED_ROOT_MISMATCH",
                root,
            )
        return baseline

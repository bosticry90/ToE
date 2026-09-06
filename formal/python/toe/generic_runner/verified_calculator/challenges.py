"""Graph-independent challenge specifications and frozen-baseline instances."""
from __future__ import annotations

from copy import deepcopy
from dataclasses import dataclass
from fractions import Fraction
from typing import Any, Callable, Mapping, Sequence

from .canonical import canonical_data, digest
from .contracts import CandidatePacketV1, ChallengeDisposition
from .errors import CalculatorError, require


@dataclass(frozen=True)
class ChallengeSpecV1:
    challenge_id: str
    semantic_target: Mapping[str, Any]
    mutation_rule: Mapping[str, Any]
    attacked_invariant: str
    required_consequence: str
    applicability_selector: Mapping[str, Any]
    descendant_confinement_rule: str
    seed_policy: Mapping[str, Any]
    origin: str
    accepted_on: str | None
    mandatory: bool

    def __post_init__(self) -> None:
        require(self.challenge_id and self.attacked_invariant, "CHALLENGE_ID")
        require(self.required_consequence in {"VERIFIER_REJECTS", "AFFECTED_ROOT_VALUE_CHANGES"}, "CHALLENGE_CONSEQUENCE")
        require(self.descendant_confinement_rule == "FROZEN_BASELINE_DESCENDANTS_ONLY", "CHALLENGE_DESCENDANT_RULE")
        require(self.seed_policy.get("kind") in {"FIXED", "DERIVED_FROM_BASELINE"}, "CHALLENGE_SEED_POLICY")
        roots = self.applicability_selector.get("roots")
        require(set(self.applicability_selector) == {"roots"} and (roots == "ANCESTRY" or isinstance(roots, list) and roots and len(roots) == len(set(roots)) and all(isinstance(root, str) and root for root in roots)), "CHALLENGE_APPLICABILITY_SELECTOR")
        require(not self.mandatory or self.accepted_on is not None, "MANDATORY_CHALLENGE_ACCEPTANCE")
        canonical_data(self.to_dict())

    @property
    def spec_hash(self) -> str:
        return digest(self.to_dict(), "ChallengeSpecV1")

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "ChallengeSpecV1":
        required = {"schema_id", "challenge_id", "semantic_target", "mutation_rule", "attacked_invariant", "required_consequence", "applicability_selector", "descendant_confinement_rule", "seed_policy", "origin", "accepted_on", "mandatory"}
        require(set(value) == required and value["schema_id"] == "ChallengeSpecV1", "CHALLENGE_SPEC_SCHEMA")
        return cls(value["challenge_id"], dict(value["semantic_target"]), dict(value["mutation_rule"]), value["attacked_invariant"], value["required_consequence"], dict(value["applicability_selector"]), value["descendant_confinement_rule"], dict(value["seed_policy"]), value["origin"], value["accepted_on"], value["mandatory"])

    def to_dict(self) -> dict[str, Any]:
        return {"schema_id": "ChallengeSpecV1", "challenge_id": self.challenge_id, "semantic_target": dict(self.semantic_target), "mutation_rule": dict(self.mutation_rule), "attacked_invariant": self.attacked_invariant, "required_consequence": self.required_consequence, "applicability_selector": dict(self.applicability_selector), "descendant_confinement_rule": self.descendant_confinement_rule, "seed_policy": dict(self.seed_policy), "origin": self.origin, "accepted_on": self.accepted_on, "mandatory": self.mandatory}


@dataclass(frozen=True)
class ChallengePacketV1:
    challenge_spec_hash: str
    baseline_graph_hash: str
    injection_node: str
    permitted_descendants: tuple[str, ...]
    affected_roots: tuple[str, ...]
    concrete_seed: int

    def __post_init__(self) -> None:
        require(isinstance(self.challenge_spec_hash, str) and len(self.challenge_spec_hash) == 64, "CHALLENGE_SPEC_HASH")
        require(isinstance(self.baseline_graph_hash, str) and len(self.baseline_graph_hash) == 64, "CHALLENGE_BASELINE_HASH")
        require(self.injection_node and len(set(self.permitted_descendants)) == len(self.permitted_descendants), "CHALLENGE_PACKET_NODES")
        require(self.affected_roots and len(set(self.affected_roots)) == len(self.affected_roots), "CHALLENGE_PACKET_ROOTS")
        require(type(self.concrete_seed) is int and 0 <= self.concrete_seed < 2 ** 64, "CHALLENGE_SEED")

    @property
    def packet_hash(self) -> str:
        return digest(self.to_dict(), "ChallengePacketV1")

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "ChallengePacketV1":
        required = {
            "schema_id", "challenge_spec_hash", "baseline_graph_hash", "injection_node",
            "permitted_descendants", "affected_roots", "concrete_seed",
        }
        require(set(value) == required and value["schema_id"] == "ChallengePacketV1", "CHALLENGE_PACKET_SCHEMA")
        require(type(value["concrete_seed"]) is int and 0 <= value["concrete_seed"] < 2 ** 64, "CHALLENGE_SEED")
        return cls(
            value["challenge_spec_hash"], value["baseline_graph_hash"], value["injection_node"],
            tuple(value["permitted_descendants"]), tuple(value["affected_roots"]), value["concrete_seed"],
        )

    def to_dict(self) -> dict[str, Any]:
        return {"schema_id": "ChallengePacketV1", "challenge_spec_hash": self.challenge_spec_hash, "baseline_graph_hash": self.baseline_graph_hash, "injection_node": self.injection_node, "permitted_descendants": list(self.permitted_descendants), "affected_roots": list(self.affected_roots), "concrete_seed": self.concrete_seed}


@dataclass(frozen=True)
class ChallengeResultV1:
    challenge_id: str
    challenge_spec_hash: str
    challenge_packet_hash: str
    injection_node: str
    affected_roots: tuple[str, ...]
    disposition: ChallengeDisposition
    observed_consequence: str
    verifier_error_code: str | None
    mandatory: bool

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "ChallengeResultV1":
        required = {"challenge_id", "challenge_spec_hash", "challenge_packet_hash", "injection_node", "affected_roots", "disposition", "observed_consequence", "verifier_error_code", "mandatory"}
        require(set(value) == required, "CHALLENGE_RESULT_SCHEMA")
        return cls(value["challenge_id"], value["challenge_spec_hash"], value["challenge_packet_hash"], value["injection_node"], tuple(value["affected_roots"]), ChallengeDisposition(value["disposition"]), value["observed_consequence"], value["verifier_error_code"], value["mandatory"])

    def to_dict(self) -> dict[str, Any]:
        return {"challenge_id": self.challenge_id, "challenge_spec_hash": self.challenge_spec_hash, "challenge_packet_hash": self.challenge_packet_hash, "injection_node": self.injection_node, "affected_roots": list(self.affected_roots), "disposition": self.disposition.value, "observed_consequence": self.observed_consequence, "verifier_error_code": self.verifier_error_code, "mandatory": self.mandatory}


def _baseline_nodes(candidate: CandidatePacketV1) -> dict[str, Mapping[str, Any]]:
    nodes = candidate.graph.get("nodes")
    require(isinstance(nodes, list), "GRAPH_NODES")
    result = {row.get("node_id"): row for row in nodes}
    require(None not in result and len(result) == len(nodes), "GRAPH_NODE_IDS")
    return result


def canonical_graph_hash(candidate: CandidatePacketV1) -> str:
    nodes = _baseline_nodes(candidate)
    edges = [tuple(edge) for edge in candidate.graph["edges"]]
    return digest({"nodes": [nodes[key] for key in sorted(nodes)], "edges": [list(edge) for edge in sorted(edges)]}, "CandidateGraphV1")


def _descendants(candidate: CandidatePacketV1, target: str) -> tuple[str, ...]:
    nodes = _baseline_nodes(candidate)
    require(target in nodes, "CHALLENGE_TARGET_NOT_FOUND", target)
    children = {identity: [] for identity in nodes}
    for node in nodes.values():
        for parent in node["parents"]:
            require(parent in children, "MISSING_PARENT")
            children[parent].append(node["node_id"])
    result: set[str] = set()
    pending = list(children[target])
    while pending:
        identity = pending.pop()
        if identity not in result:
            result.add(identity)
            pending.extend(children[identity])
    return tuple(sorted(result))


def _ancestry(candidate: CandidatePacketV1, root: str) -> set[str]:
    nodes = _baseline_nodes(candidate)
    active: set[str] = set()
    pending = [root]
    while pending:
        identity = pending.pop()
        require(identity in nodes, "MISSING_ROOT_OR_PARENT", identity)
        if identity not in active:
            active.add(identity)
            pending.extend(nodes[identity]["parents"])
    return active


def select_targets(spec: ChallengeSpecV1, candidate: CandidatePacketV1) -> tuple[str, ...]:
    nodes = _baseline_nodes(candidate)
    selector = spec.semantic_target
    require(set(selector) in ({"node_id"}, {"operation"}, {"semantic_type"}, {"kind"}), "CHALLENGE_TARGET_SELECTOR")
    field, expected = next(iter(selector.items()))
    targets = tuple(sorted(identity for identity, node in nodes.items() if (identity if field == "node_id" else node.get("value_type", {}).get("semantic_type") if field == "semantic_type" else node.get(field)) == expected))
    return targets


def instantiate(
    spec: ChallengeSpecV1,
    candidate: CandidatePacketV1,
    baseline_graph_hash: str,
    target: str,
    *,
    baseline_binding_prevalidated: bool = False,
) -> ChallengePacketV1:
    if not baseline_binding_prevalidated:
        require(canonical_graph_hash(candidate) == baseline_graph_hash, "CHALLENGE_BASELINE_GRAPH_BINDING")
    require(target in select_targets(spec, candidate), "CHALLENGE_TARGET_NOT_APPLICABLE", target)
    descendants = _descendants(candidate, target)
    roots = tuple(sorted(root for root in candidate.claimed_outputs if target in _ancestry(candidate, root)))
    selected_roots = spec.applicability_selector["roots"]
    if selected_roots != "ANCESTRY":
        roots = tuple(root for root in roots if root in selected_roots)
    require(roots, "CHALLENGE_AFFECTS_NO_ROOT", target)
    policy = spec.seed_policy
    if policy["kind"] == "FIXED":
        seed = policy["seed"]
    else:
        seed = int(digest({"spec": spec.spec_hash, "graph": baseline_graph_hash, "target": target}, "ChallengeSeedV1")[:16], 16)
    require(type(seed) is int and 0 <= seed < 2 ** 64, "CHALLENGE_SEED")
    return ChallengePacketV1(spec.spec_hash, baseline_graph_hash, target, descendants, roots, seed)


def apply_mutation(
    spec: ChallengeSpecV1,
    packet: ChallengePacketV1,
    candidate: CandidatePacketV1,
    *,
    packet_derivation_prevalidated: bool = False,
) -> CandidatePacketV1:
    if not packet_derivation_prevalidated:
        require(canonical_graph_hash(candidate) == packet.baseline_graph_hash, "CHALLENGE_BASELINE_GRAPH_BINDING")
    require(packet.challenge_spec_hash == spec.spec_hash, "CHALLENGE_SPEC_BINDING")
    if not packet_derivation_prevalidated:
        expected = instantiate(spec, candidate, packet.baseline_graph_hash, packet.injection_node)
        require(packet == expected, "CHALLENGE_PACKET_BASELINE_DERIVATION")
    # Copy the mutation target and the small top-level collections, while
    # sharing untouched canonical subtrees from the frozen baseline.  C03/RV
    # source contexts are deliberately large; deep-copying all 207 nodes for
    # each of hundreds of independent mutants adds no assurance.
    baseline_raw = candidate.to_dict()
    graph = {
        "nodes": list(baseline_raw["graph"]["nodes"]),
        "edges": list(baseline_raw["graph"]["edges"]),
    }
    target_index = next((index for index, row in enumerate(graph["nodes"]) if row["node_id"] == packet.injection_node), None)
    require(target_index is not None, "CHALLENGE_TARGET_NOT_FOUND")
    graph["nodes"][target_index] = deepcopy(graph["nodes"][target_index])
    raw = {
        **baseline_raw,
        "graph": graph,
        "claimed_outputs": dict(baseline_raw["claimed_outputs"]),
        "source_bindings": list(baseline_raw["source_bindings"]),
    }
    nodes = {row["node_id"]: row for row in graph["nodes"]}
    require(packet.injection_node in nodes, "CHALLENGE_TARGET_NOT_FOUND")
    rule = spec.mutation_rule
    kind = rule.get("kind")
    target = nodes[packet.injection_node]
    def perturb_profile_wire(value):
        profile_kind = value.get("type")
        if profile_kind == "BOOLEAN":
            value["value"] = not value["value"]
        elif profile_kind == "INTEGER":
            value["value"] += 1
        elif profile_kind == "EXACT_EXPRESSION":
            value["value"] = f"({value['value']})+1"
        elif profile_kind == "TEXT":
            value["value"] = "__VPC_CORRUPTED_PROFILE_TEXT__"
        elif profile_kind == "NULL":
            value = {"type": "TEXT", "value": "__VPC_CORRUPTED_NULL__"}
        elif profile_kind in {"LIST", "TUPLE"}:
            if value["items"]:
                value["items"][0] = perturb_profile_wire(value["items"][0])
            else:
                value = {"type": "TEXT", "value": "__VPC_CORRUPTED_EMPTY_SEQUENCE__"}
        elif profile_kind == "MAP":
            if value["entries"]:
                value["entries"][0][1] = perturb_profile_wire(value["entries"][0][1])
            else:
                value = {"type": "TEXT", "value": "__VPC_CORRUPTED_EMPTY_MAP__"}
        elif profile_kind == "MATRIX":
            require(value["entries"], "CHALLENGE_EMPTY_PROFILE_MATRIX")
            value["entries"][0] = perturb_profile_wire(value["entries"][0])
        else:
            raise CalculatorError("CHALLENGE_PROFILE_VALUE_KIND")
        return value

    def perturb(value):
        if value.get("kind") == "PROFILE_VALUE":
            require(set(value) == {"kind", "value"}, "CHALLENGE_PROFILE_VALUE_SCHEMA")
            value["value"] = perturb_profile_wire(value["value"])
            return value
        if value.get("kind") == "BOOLEAN":
            value["value"] = not value["value"]
            return value
        if value.get("kind") == "ATOM":
            value["value"] = "__VPC_CORRUPTED_ATOM__"
            return value
        if value.get("kind") == "TENSOR":
            require(value["entries"], "CHALLENGE_EMPTY_TENSOR")
            value["entries"][0] = perturb(value["entries"][0])
            return value
        require(value.get("kind") == "RATIONAL_FUNCTION", "CHALLENGE_EXACT_VALUE_KIND")
        terms = value["numerator"]["terms"]
        if terms:
            coefficient = terms[0]["coefficient"]
            coefficient[0] = str(Fraction(coefficient[0]) + 1)
        else:
            degree = len(value["denominator"]["terms"][0]["coefficient"])
            terms.append({"powers": [0] * len(value["symbols"]), "coefficient": ["1"] + ["0"] * (degree - 1)})
        return value
    if kind == "REPLACE_CLAIMED_VALUE":
        require(set(rule) == {"kind", "value"}, "CHALLENGE_MUTATION_SCHEMA")
        target["claimed_value"] = deepcopy(rule["value"])
        if packet.injection_node in raw["claimed_outputs"]:
            raw["claimed_outputs"][packet.injection_node] = deepcopy(rule["value"])
    elif kind == "PERTURB_EXACT_VALUE_BY_ONE":
        require(set(rule) == {"kind"}, "CHALLENGE_MUTATION_SCHEMA")
        target["claimed_value"] = perturb(deepcopy(target["claimed_value"]))
        if packet.injection_node in raw["claimed_outputs"]:
            raw["claimed_outputs"][packet.injection_node] = deepcopy(target["claimed_value"])
    elif kind == "REPLACE_OPERATION":
        require(set(rule) == {"kind", "operation"}, "CHALLENGE_MUTATION_SCHEMA")
        target["operation"] = rule["operation"]
    elif kind == "CORRUPT_SOURCE_LOCATOR":
        require(set(rule) == {"kind"} and target["operation"] == "SOURCE_DECODE", "CHALLENGE_MUTATION_SCHEMA")
        reference = deepcopy(target["parameters"]["reference"])
        if reference["type"] in {"JsonPointerValueRef", "TensorComponentRef"}:
            reference["pointer"] = "/__vpc_nonexistent_source_locator__"
        elif reference["type"] == "UniqueTableCellRef":
            reference["table_pointer"] = "/__vpc_nonexistent_source_locator__"
        elif reference["type"] == "NamedConventionRef":
            reference["conventions_pointer"] = "/__vpc_nonexistent_source_locator__"
        else:
            raise CalculatorError("CHALLENGE_SOURCE_REFERENCE_TYPE")
        target["parameters"]["reference"] = reference
        for index, row in enumerate(raw["source_bindings"]):
            if row["node_id"] == packet.injection_node:
                replacement = dict(row)
                replacement["reference"] = deepcopy(reference)
                raw["source_bindings"][index] = replacement
    elif kind == "REPLACE_SOURCE_REFERENCE":
        require(set(rule) == {"kind", "reference"}, "CHALLENGE_MUTATION_SCHEMA")
        target["parameters"]["reference"] = deepcopy(rule["reference"])
        for index, row in enumerate(raw["source_bindings"]):
            if row["node_id"] == packet.injection_node:
                replacement = dict(row)
                replacement["reference"] = deepcopy(rule["reference"])
                raw["source_bindings"][index] = replacement
    elif kind == "REMOVE_PARENT":
        require(set(rule) == {"kind", "parent_index"} and type(rule["parent_index"]) is int, "CHALLENGE_MUTATION_SCHEMA")
        index = rule["parent_index"]
        require(0 <= index < len(target["parents"]), "CHALLENGE_PARENT_INDEX")
        parent = target["parents"].pop(index)
        graph["edges"] = [edge for edge in graph["edges"] if edge != [parent, packet.injection_node]]
    elif kind == "REMOVE_FIRST_PARENT_STALE_EDGE":
        require(set(rule) == {"kind"} and target["parents"], "CHALLENGE_MUTATION_SCHEMA")
        target["parents"].pop(0)
    elif kind == "BYPASS_FIRST_PARENT":
        require(set(rule) == {"kind"} and target["parents"], "CHALLENGE_MUTATION_SCHEMA")
        old_parent = target["parents"][0]
        grandparents = nodes[old_parent]["parents"]
        require(grandparents, "CHALLENGE_PARENT_HAS_NO_PARENT")
        new_parent = grandparents[0]
        target["parents"][0] = new_parent
        graph["edges"] = [[new_parent, packet.injection_node] if edge == [old_parent, packet.injection_node] else edge for edge in graph["edges"]]
    elif kind == "ADD_EDGE":
        require(set(rule) == {"kind", "parent"} and rule["parent"] in nodes, "CHALLENGE_MUTATION_SCHEMA")
        require(rule["parent"] not in target["parents"], "CHALLENGE_EDGE_EXISTS")
        target["parents"].append(rule["parent"])
        graph["edges"].append([rule["parent"], packet.injection_node])
    elif kind == "REPLACE_OUTPUT":
        require(packet.injection_node in raw["claimed_outputs"] and set(rule) == {"kind", "value"}, "CHALLENGE_MUTATION_SCHEMA")
        raw["claimed_outputs"][packet.injection_node] = deepcopy(rule["value"])
    elif kind == "PERTURB_OUTPUT_ONLY":
        require(set(rule) == {"kind"} and packet.injection_node in raw["claimed_outputs"], "CHALLENGE_MUTATION_SCHEMA")
        raw["claimed_outputs"][packet.injection_node] = perturb(deepcopy(raw["claimed_outputs"][packet.injection_node]))
    else:
        raise CalculatorError("UNSUPPORTED_CHALLENGE_MUTATION")
    allowed = {packet.injection_node, *packet.permitted_descendants}
    changed = {identity for identity in nodes if nodes[identity] != _baseline_nodes(candidate)[identity]}
    require(changed <= allowed, "MUTATION_ESCAPED_BASELINE_DESCENDANTS")
    return CandidatePacketV1.from_dict(raw)


def run_challenge(
    spec: ChallengeSpecV1,
    packet: ChallengePacketV1,
    candidate: CandidatePacketV1,
    verifier: Callable[[CandidatePacketV1], Any],
    baseline_result: Any | None = None,
    *,
    packet_derivation_prevalidated: bool = False,
) -> ChallengeResultV1:
    mutated = apply_mutation(spec, packet, candidate, packet_derivation_prevalidated=packet_derivation_prevalidated)
    baseline_result = verifier(candidate) if baseline_result is None else baseline_result
    try:
        mutant_result = verifier(mutated)
        if spec.required_consequence == "AFFECTED_ROOT_VALUE_CHANGES":
            changed = any(baseline_result.output_data()[root] != mutant_result.output_data()[root] for root in packet.affected_roots)
            disposition = ChallengeDisposition.PASSED if changed else ChallengeDisposition.FAILED
            consequence = "AFFECTED_ROOT_VALUE_CHANGES" if changed else "MUTATION_SURVIVED_WITHOUT_AFFECTED_OUTPUT_CHANGE"
        else:
            disposition = ChallengeDisposition.FAILED
            consequence = "MUTATION_ACCEPTED"
        error_code = None
    except CalculatorError as exc:
        disposition = ChallengeDisposition.PASSED if spec.required_consequence == "VERIFIER_REJECTS" else ChallengeDisposition.FAILED
        consequence = "VERIFIER_REJECTS"
        error_code = exc.code
    return ChallengeResultV1(spec.challenge_id, spec.spec_hash, packet.packet_hash, packet.injection_node, packet.affected_roots, disposition, consequence, error_code, spec.mandatory)


def coverage_by_root(roots: Sequence[str], mandatory_packets_by_root: Mapping[str, Sequence[str]], results: Sequence[ChallengeResultV1]) -> dict[str, dict[str, Any]]:
    output: dict[str, dict[str, Any]] = {}
    for root in roots:
        applicable = [row for row in results if root in row.affected_roots]
        passed = {row.challenge_packet_hash for row in applicable if row.disposition == ChallengeDisposition.PASSED}
        failed = [row.challenge_id for row in applicable if row.disposition == ChallengeDisposition.FAILED]
        required_applicable = set(mandatory_packets_by_root.get(root, ()))
        missing = sorted(required_applicable - passed)
        output[root] = {"applicable_result_count": len(applicable), "mandatory_applicable_packet_hashes": sorted(required_applicable), "mandatory_missing_or_failed": missing, "failed_challenges": failed, "complete": not missing and not failed}
    return output


def validate_registry(specs: Sequence[ChallengeSpecV1], freeze_timestamp: str, expected_falsifier_ids: Sequence[str]) -> dict[str, Any]:
    ids = [row.challenge_id for row in specs]
    hashes = [row.spec_hash for row in specs]
    require(len(ids) == len(set(ids)) and len(hashes) == len(set(hashes)), "CHALLENGE_REGISTRY_DUPLICATE")
    mandatory = [row for row in specs if row.mandatory]
    require(all(row.accepted_on is not None and row.accepted_on <= freeze_timestamp for row in mandatory), "CHALLENGE_AFTER_POLICY_FREEZE")
    require(set(expected_falsifier_ids) <= set(ids), "UNCLASSIFIED_HISTORICAL_FALSIFIER")
    return {"schema_id": "ChallengeRegistryCensusV1", "freeze_timestamp": freeze_timestamp, "spec_count": len(specs), "mandatory_count": len(mandatory), "spec_hashes": sorted(hashes), "falsifier_ids": sorted(ids), "unclassified": []}

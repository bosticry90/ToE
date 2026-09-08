"""Independent complete ValueType contracts for the frozen C03/RV profile.

Candidate metadata is never used to manufacture these signatures.  They are
derived from the frozen source/operation registries and authoritative output
semantics in the trusted package.
"""
from __future__ import annotations

from typing import Any, Mapping

from .c03_rv_operation_contracts import DERIVED_SIGNATURES, SOURCE_SIGNATURES
from .dag import NodeV1, TypeSignatureReceiptV1
from .errors import CalculatorError, require
from .exact import ExactAtomV1, ExactTensorV1, RationalFunctionV1


TYPE_AXES = (
    "mathematical_kind",
    "semantic_type",
    "physical_dimension_equivalence_class",
    "canonical_unit_convention",
    "exact_shape_and_rank",
    "ordered_index_spaces",
    "representation_tags",
    "domain_status_and_prerequisites",
)
ZERO_DIMENSION = ["0", "0", "0"]
UNIT = "SU5_NATURAL_HBAR_C_1"
DOMAIN = {"profile": "C03_RV_SU5_EXACT_PROFILE_v1"}


def _output_kind_shape(semantic_type: str) -> tuple[str, list[int], list[str]]:
    if semantic_type in {"SYMBOLIC_COEFFICIENT", "SYMBOLIC_SCALAR"}:
        return "EXACT_SCALAR", [], []
    if semantic_type == "NATIVE_COORDINATE_VECTOR":
        return "EXACT_TENSOR", [14], ["NATIVE_E"]
    if semantic_type in {"EVANESCENT_EVALUATION_STATE", "SYMBOL_TEXT"}:
        return "EXACT_ATOM", [], []
    raise CalculatorError("C03_RV_TRUSTED_OUTPUT_TYPE", detail=semantic_type)


def trusted_value_type(node_id: str) -> dict[str, Any]:
    if node_id in SOURCE_SIGNATURES:
        mathematical_kind, shape, index_spaces = "EXACT_DOCUMENT", None, []
        semantic_type = SOURCE_SIGNATURES[node_id]
    else:
        require(node_id in DERIVED_SIGNATURES, "C03_RV_TRUSTED_SIGNATURE_NODE", node_id)
        signature = DERIVED_SIGNATURES[node_id]
        semantic_type = signature["semantic_type"]
        if signature["kind"] == "OUTPUT":
            mathematical_kind, shape, index_spaces = _output_kind_shape(semantic_type)
        else:
            mathematical_kind, shape, index_spaces = "EXACT_DOCUMENT", None, []
    return {
        "mathematical_kind": mathematical_kind,
        "semantic_type": semantic_type,
        "dimension": list(ZERO_DIMENSION),
        "unit_convention": UNIT,
        "shape": shape,
        "index_spaces": index_spaces,
        "representation_tags": ["SU5"],
        "domain": dict(DOMAIN),
    }


def trusted_value_type_registry() -> dict[str, dict[str, Any]]:
    return {node_id: trusted_value_type(node_id) for node_id in sorted({*SOURCE_SIGNATURES, *DERIVED_SIGNATURES})}


def _observed_complete(node: NodeV1) -> dict[str, Any]:
    observed = node.value_type.to_dict()
    observed.setdefault("shape", None)
    return observed


def validate_node_type(node: NodeV1) -> TypeSignatureReceiptV1:
    expected = trusted_value_type(node.node_id)
    observed = _observed_complete(node)
    require(observed == expected, "C03_RV_VALUE_TYPE_SIGNATURE", node.node_id)
    return TypeSignatureReceiptV1(node.node_id, expected, observed, TYPE_AXES, None)


def bind_actual_value_shape(receipt: TypeSignatureReceiptV1, value: object) -> TypeSignatureReceiptV1:
    kind = receipt.expected["mathematical_kind"]
    if kind == "EXACT_TENSOR":
        require(isinstance(value, ExactTensorV1), "C03_RV_ACTUAL_VALUE_KIND", receipt.node_id)
        actual_shape: tuple[int, ...] | None = value.shape
    elif kind == "EXACT_SCALAR":
        require(isinstance(value, RationalFunctionV1), "C03_RV_ACTUAL_VALUE_KIND", receipt.node_id)
        actual_shape = ()
    elif kind == "EXACT_ATOM":
        require(isinstance(value, ExactAtomV1), "C03_RV_ACTUAL_VALUE_KIND", receipt.node_id)
        actual_shape = ()
    else:
        actual_shape = None
    declared = receipt.expected["shape"]
    require(declared is None or tuple(declared) == actual_shape, "C03_RV_ACTUAL_VALUE_SHAPE", receipt.node_id)
    return TypeSignatureReceiptV1(
        receipt.node_id, receipt.expected, receipt.observed,
        receipt.applicable_axes, actual_shape,
    )


def validate_edge_types(nodes: Mapping[str, NodeV1]) -> None:
    """Fail closed on profile edges independently of candidate metadata.

    Output binding is the strict equality edge.  Every other frozen physics
    edge is already fixed by DERIVED_SIGNATURES; checking its ordered parent
    list here prevents a locally plausible metadata object from authorizing a
    different scientific edge.
    """
    for node_id, signature in DERIVED_SIGNATURES.items():
        node = nodes[node_id]
        validate_node_edge(node, nodes)


def validate_node_edge(node: NodeV1, nodes: Mapping[str, NodeV1]) -> None:
    require(node.node_id in DERIVED_SIGNATURES, "C03_RV_TYPE_EDGE_NODE", node.node_id)
    signature = DERIVED_SIGNATURES[node.node_id]
    require(node.parents == signature["parents"], "C03_RV_TYPE_EDGE_SIGNATURE", node.node_id)
    if node.operation == "OUTPUT_BIND":
        parent = nodes[node.parents[0]]
        expected = trusted_value_type(node.node_id)
        parent_expected = trusted_value_type(parent.node_id)
        require(
            expected["semantic_type"] == parent_expected["semantic_type"]
            and expected["dimension"] == parent_expected["dimension"]
            and expected["unit_convention"] == parent_expected["unit_convention"]
            and expected["representation_tags"] == parent_expected["representation_tags"]
            and expected["domain"] == parent_expected["domain"],
            "C03_RV_TYPE_EDGE_SIGNATURE", node.node_id,
        )

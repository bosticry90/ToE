"""Frozen trusted operation and node-signature contracts for C03/RV.

The operation vocabulary is profile-specific; implementations are kept in
separate modules and import no candidate, historical runner, oracle, or
acceptance code.  Nodes are applications of these reviewed semantics.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Callable, Mapping

from . import c03_rv_c03_operations as c03
from . import c03_rv_native_operations as native
from . import c03_rv_rv_operations as rv
from .errors import CalculatorError, require


@dataclass(frozen=True)
class TrustedPhysicsOperationV1:
    operation: str
    input_contract: str
    output_contract: str
    semantic_requirements: tuple[str, ...]
    unit_rule: str
    domain_requirements: tuple[str, ...]
    provenance_rule: str
    failure_mode: str
    python_implementation: str
    julia_implementation: str

    def to_dict(self) -> dict[str, Any]:
        return {
            "operation": self.operation,
            "input_contract": self.input_contract,
            "output_contract": self.output_contract,
            "semantic_requirements": list(self.semantic_requirements),
            "unit_rule": self.unit_rule,
            "domain_requirements": list(self.domain_requirements),
            "provenance_rule": self.provenance_rule,
            "failure_mode": self.failure_mode,
            "python_implementation": self.python_implementation,
            "julia_implementation": self.julia_implementation,
        }


def _contract(operation: str, inputs: str, output: str, semantics: tuple[str, ...], domains: tuple[str, ...]) -> TrustedPhysicsOperationV1:
    return TrustedPhysicsOperationV1(
        operation,
        inputs,
        output,
        semantics,
        "PROFILE_DECLARED_EXACT_DIMENSIONS_AND_NATURAL_UNIT_QUOTIENT",
        domains,
        "ALL_ORDERED_PARENTS_AND_OPERATION_ID_ARE_RECEIPT_BOUND",
        "FAIL_CLOSED_WITH_STABLE_ERROR_CODE",
        f"trusted-python:{operation}:v1",
        f"independent-julia-nemo:{operation}:v1",
    )


TRUSTED_C03_RV_OPERATION_CONTRACTS: Mapping[str, TrustedPhysicsOperationV1] = {
    "ANGULAR_AVERAGE": _contract("ANGULAR_AVERAGE", "bounded source occurrence/word domain", "exact pairing or coverage ledger", ("metric sectors and actual contracted slots are preserved",), ("rank and denominator domain",)),
    "DOMAIN_PREDICATE": _contract("DOMAIN_PREDICATE", "typed source context and prerequisite ledgers", "applicability decision", ("source, topology, representation, and regulator identities agree",), ("frozen C03/RV applicability domains",)),
    "EPISTEMIC_CLASSIFICATION": _contract("EPISTEMIC_CLASSIFICATION", "computed exact residual/evidence objects", "evaluated-zero/nonzero state", ("NOT_EVALUATED is never inferred as zero",), ("complete residual and evidence coverage",)),
    "EXACT_CLIFFORD_ACTION": _contract("EXACT_CLIFFORD_ACTION", "typed spinor words or contracted-word ledger", "exact matrix/vector/reduction ledger", ("Clifford and chirality conventions are source-bound",), ("supported BMHV word/rank profile",)),
    "EXACT_MATRIX_PROJECTION": _contract("EXACT_MATRIX_PROJECTION", "exact matrices/tensors/vectors", "exact projection or scalar", ("full residual is checked",), ("shape, rank, and invertibility",)),
    "GAUGE_GENERATOR_ACTION": _contract("GAUGE_GENERATOR_ACTION", "source tensor and exact generator representation", "exact tensor image", ("representation and generator normalization are checked",), ("supported U1/SU2/SU3 source channel",)),
    "INVERTIBLE_NORMALIZATION": _contract("INVERTIBLE_NORMALIZATION", "exact value, scale, and inverse witness", "normalized exact value", ("scale times inverse equals one",), ("nonzero normalization and target direction",)),
    "LINEAR_COMBINATION": _contract("LINEAR_COMBINATION", "ordered exact coefficient/value parents", "exact scalar/vector", ("profile formula and gauge parameter binding are fixed",), ("matching shape and semantic type",)),
    "NORMALIZATION_MONOMIAL": _contract("NORMALIZATION_MONOMIAL", "source coupling monomial and Wilson symbol", "exact monomial", ("removed symbols are distinct and source declared",), ("two identical gauge factors",)),
    "NORMALIZATION_RECIPROCAL": _contract("NORMALIZATION_RECIPROCAL", "nonzero exact reference scalar", "invertible scale", ("reciprocal is computed, never asserted",), ("nonzero reference",)),
    "NORMALIZATION_REFERENCE_SCALAR": _contract("NORMALIZATION_REFERENCE_SCALAR", "source prefactor, removed monomial, normalization domain", "exact rational reference", ("all repeated prefactors agree",), ("frozen one-loop C03 topology",)),
    "PERMUTATION_PARITY": _contract("PERMUTATION_PARITY", "ordered labelled fermion fields", "sign", ("repeated slots are exchanged explicitly",), ("frozen four-fermion orbit",)),
    "PRODUCT": _contract("PRODUCT", "ordered exact factors or profile ledger", "exact product/weighted ledger", ("no hidden factors are admitted",), ("profile-specific arity and factor domain",)),
    "RELATION_REDUCTION": _contract("RELATION_REDUCTION", "exact N7/N8 matrices or contracted-word reductions", "exact relation certificate/remainder/pole", ("nullspace, dual, and residue identities are checked",), ("rank, shape, and simple-pole domain",)),
    "TENSOR_DIFFERENCE": _contract("TENSOR_DIFFERENCE", "same-space exact tensors/vectors", "exact difference", ("no component may be discarded",), ("identical shape/index spaces",)),
    "TENSOR_EXCHANGE_EIGENVALUE": _contract("TENSOR_EXCHANGE_EIGENVALUE", "source color tensor with labelled axes", "sign", ("the full exchanged tensor is compared",), ("nonzero tensor and sign eigenvalue",)),
    "TENSOR_SUM": _contract("TENSOR_SUM", "same-space exact tensors/vectors or source tensor context", "exact sum/tree", ("weights and all components are retained",), ("matching shape/index spaces",)),
    "WARD_REDUCTION": _contract("WARD_REDUCTION", "source spinor words/tree and routing", "exact longitudinal image", ("the explicit Ward identity is checked",), ("supported closed four-gamma word",)),
    "OUTPUT_BIND": _contract("OUTPUT_BIND", "one computed parent", "authoritative output value", ("the output equals its declared parent exactly",), ("one parent with identical semantic type",)),
}


C03_RV_PHYSICS_OPERATIONS = tuple(TRUSTED_C03_RV_OPERATION_CONTRACTS)


SOURCE_SIGNATURES: Mapping[str, str] = {
    "C03.SOURCE.ORDERED_FIELDS": "LABELLED_FIELD_CONTEXT",
    "C03.SOURCE.COLOR_TENSOR": "COLOR_EXCHANGE_CONTEXT",
    "C03.SOURCE.SPINOR_X": "SOURCE_BILINEAR_CONTEXT",
    "C03.SOURCE.SPINOR_Y": "SOURCE_BILINEAR_CONTEXT",
    "C03.SOURCE.CLIFFORD_DOMAIN": "CLIFFORD_DOMAIN_CONTEXT",
    "C03.SOURCE.GAUGE_PARAMETER": "GAUGE_SYMBOL_CONTEXT",
    "C03.SOURCE.HYPERCHARGE_D": "RATIONAL",
    "C03.SOURCE.HYPERCHARGE_E": "RATIONAL",
    "C03.SOURCE.DIAGRAM_PHASE": "RAW_FEYNMAN_LEDGER",
    "C03.SOURCE.COMMON_PREFACTOR": "SYMBOLIC_SCALAR",
    "C03.SOURCE.COUPLING_MONOMIAL": "GAUGE_MONOMIAL",
    "C03.SOURCE.NORMALIZATION_DOMAIN": "NORMALIZATION_DOMAIN_CONTEXT",
    "C03.CONVENTION.WILSON_SYMBOL": "SYMBOL",
    "C03.NATIVE.SOURCE.OCCURRENCES": "SOURCE_CONTEXT",
    "C03.NATIVE.SOURCE.REQUESTS": "SOURCE_CONTEXT",
    "C03.NATIVE.SOURCE.DEFECTS": "INHERITED_RELATION_CONTEXT",
    "C03.NATIVE.SOURCE.COLUMNS": "SOURCE_CONTEXT",
    "C03.NATIVE.SOURCE.LEDGER": "INHERITED_RELATION_CONTEXT",
    "C03.NATIVE.SOURCE.RELATIONS": "INHERITED_RELATION_CONTEXT",
    "C03.NATIVE.SOURCE.REPRESENTATIVES": "SOURCE_CONTEXT",
    "C03.NATIVE.SOURCE.ORDER": "SOURCE_CONTEXT",
    "C03.NATIVE.SOURCE.REP_CACHE": "SOURCE_CONTEXT",
    "C03.NATIVE.SOURCE.DUAL_CACHE": "SOURCE_CONTEXT",
    "C03.NATIVE.SOURCE.Q_CACHE": "SOURCE_CONTEXT",
    "C03.NATIVE.SOURCE.K_CACHE": "SOURCE_CONTEXT",
    **{f"RV{index:02d}.SOURCE.CONTEXT": "SOURCE_CONTEXT" for index in range(1, 7)},
}


def derived_signatures() -> dict[str, dict[str, Any]]:
    specs: dict[str, dict[str, Any]] = {}

    def add(key: str, operation: str, parents: list[str], semantic_type: str = "BASIS_VECTOR_XY", kind: str = "DERIVED") -> None:
        specs[key] = {"kind": kind, "operation": operation, "parents": tuple(parents), "semantic_type": semantic_type}

    prefix = "C03."
    add(prefix + "DERIVED.GRASSMANN_EXCHANGE_SIGN", "PERMUTATION_PARITY", [prefix + "SOURCE.ORDERED_FIELDS"], "SIGN")
    add(prefix + "DERIVED.COLOR_EXCHANGE_SIGN", "TENSOR_EXCHANGE_EIGENVALUE", [prefix + "SOURCE.COLOR_TENSOR"], "SIGN")
    add(prefix + "DERIVED.IDENTITY_OCCURRENCE_WEIGHT", "PRODUCT", [prefix + "SOURCE.ORDERED_FIELDS"], "SIGN")
    add(prefix + "DERIVED.EXCHANGE_OCCURRENCE_WEIGHT", "PRODUCT", [prefix + "DERIVED.GRASSMANN_EXCHANGE_SIGN", prefix + "DERIVED.COLOR_EXCHANGE_SIGN"], "SIGN")
    for label in ("X", "Y"):
        other = "Y" if label == "X" else "X"
        add(prefix + f"DERIVED.G_{label}", "EXACT_CLIFFORD_ACTION", [prefix + f"SOURCE.SPINOR_{label}", prefix + f"SOURCE.SPINOR_{other}", prefix + "SOURCE.CLIFFORD_DOMAIN"])
        add(prefix + f"DERIVED.L_{label}", "WARD_REDUCTION", [prefix + f"SOURCE.SPINOR_{label}", prefix + f"SOURCE.SPINOR_{other}", prefix + "SOURCE.CLIFFORD_DOMAIN"])
    for label in ("G", "L"):
        add(prefix + f"DERIVED.{label}_SUM", "TENSOR_SUM", [prefix + "DERIVED.IDENTITY_OCCURRENCE_WEIGHT", prefix + "DERIVED.EXCHANGE_OCCURRENCE_WEIGHT", prefix + f"DERIVED.{label}_X", prefix + f"DERIVED.{label}_Y"])
    add(prefix + "DERIVED.PT_SUM", "TENSOR_DIFFERENCE", [prefix + "DERIVED.G_SUM", prefix + "DERIVED.L_SUM"])
    add(prefix + "DERIVED.COVARIANT_NUMERATOR", "LINEAR_COMBINATION", [prefix + "DERIVED.PT_SUM", prefix + "DERIVED.L_SUM", prefix + "SOURCE.GAUGE_PARAMETER"])
    add(prefix + "DERIVED.CHARGE_PRODUCT", "PRODUCT", [prefix + "SOURCE.HYPERCHARGE_D", prefix + "SOURCE.HYPERCHARGE_E"], "RATIONAL")
    add(prefix + "DERIVED.RAW_GRAPH", "PRODUCT", [prefix + "DERIVED.COVARIANT_NUMERATOR", prefix + "SOURCE.DIAGRAM_PHASE", prefix + "DERIVED.CHARGE_PRODUCT"])
    add(prefix + "DERIVED.REMOVED_MONOMIAL", "NORMALIZATION_MONOMIAL", [prefix + "SOURCE.COUPLING_MONOMIAL", prefix + "CONVENTION.WILSON_SYMBOL"], "SYMBOLIC_SCALAR")
    add(prefix + "DERIVED.REFERENCE_SCALAR", "NORMALIZATION_REFERENCE_SCALAR", [prefix + "SOURCE.COMMON_PREFACTOR", prefix + "DERIVED.REMOVED_MONOMIAL", prefix + "SOURCE.NORMALIZATION_DOMAIN"], "RATIONAL")
    # Historical transcripts called these nodes NORMALIZATION_MAP.  In the VPC
    # graph grammar that is a scientific operation/type distinction, not an
    # execution-kind escape hatch: both nodes are independently recomputed
    # DERIVED nodes.
    add(prefix + "DERIVED.TARGET_NORMALIZATION_SCALE", "NORMALIZATION_RECIPROCAL", [prefix + "DERIVED.REFERENCE_SCALAR"], "INVERTIBLE_SCALE")
    add(prefix + "DERIVED.COMMON_NORMALIZED_COEFFICIENT", "INVERTIBLE_NORMALIZATION", [prefix + "DERIVED.RAW_GRAPH", prefix + "DERIVED.TARGET_NORMALIZATION_SCALE", prefix + "DERIVED.REFERENCE_SCALAR"], "SYMBOLIC_COEFFICIENT")
    add(prefix + "OUTPUT.PHYSICAL_COEFFICIENT", "OUTPUT_BIND", [prefix + "DERIVED.COMMON_NORMALIZED_COEFFICIENT"], "SYMBOLIC_COEFFICIENT", "OUTPUT")

    native_prefix = "C03.NATIVE."

    def n(key: str, operation: str, parents: list[str], semantic_type: str = "EXACT_LEDGER", kind: str = "DERIVED") -> None:
        add(native_prefix + key, operation, [parent if parent.startswith("C03.") else native_prefix + parent for parent in parents], semantic_type, kind)

    n("JOIN", "DOMAIN_PREDICATE", ["SOURCE.OCCURRENCES", "SOURCE.REQUESTS", "SOURCE.DEFECTS", "SOURCE.COLUMNS", "SOURCE.ORDER", "SOURCE.LEDGER"], kind="DERIVED")
    n("CLIFFORD", "EXACT_CLIFFORD_ACTION", ["SOURCE.OCCURRENCES", "JOIN", "C03.SOURCE.CLIFFORD_DOMAIN"])
    n("ANGULAR", "ANGULAR_AVERAGE", ["SOURCE.OCCURRENCES", "JOIN", "C03.SOURCE.CLIFFORD_DOMAIN"])
    n("CHANNEL", "LINEAR_COMBINATION", ["SOURCE.OCCURRENCES", "C03.SOURCE.GAUGE_PARAMETER", "C03.SOURCE.DIAGRAM_PHASE"])
    n("LEGACY", "PRODUCT", ["SOURCE.OCCURRENCES", "CLIFFORD", "ANGULAR"])
    n("WEIGHTS", "PRODUCT", ["SOURCE.OCCURRENCES", "C03.DERIVED.IDENTITY_OCCURRENCE_WEIGHT", "C03.DERIVED.EXCHANGE_OCCURRENCE_WEIGHT"])
    n("PHASE", "PRODUCT", ["C03.SOURCE.DIAGRAM_PHASE"])
    n("AMBIENT", "PRODUCT", ["JOIN", "CLIFFORD", "ANGULAR", "CHANNEL", "LEGACY", "WEIGHTS", "PHASE", "C03.DERIVED.CHARGE_PRODUCT"], "NATIVE_AMBIENT_VECTOR")
    n("RELATIONS", "RELATION_REDUCTION", ["SOURCE.RELATIONS", "JOIN"], "SYMBOLIC_MATRIX")
    n("REPRESENTATIVE", "EXACT_MATRIX_PROJECTION", ["SOURCE.REPRESENTATIVES", "SOURCE.REP_CACHE", "JOIN"], "SYMBOLIC_MATRIX")
    n("DUAL", "RELATION_REDUCTION", ["RELATIONS", "REPRESENTATIVE", "SOURCE.DUAL_CACHE"], "SYMBOLIC_MATRIX")
    n("QUOTIENT", "EXACT_MATRIX_PROJECTION", ["REPRESENTATIVE", "DUAL", "SOURCE.Q_CACHE"], "SYMBOLIC_MATRIX")
    n("REMAINDER", "TENSOR_DIFFERENCE", ["QUOTIENT", "SOURCE.K_CACHE"], "SYMBOLIC_MATRIX")
    n("RELATION_CERTIFICATE", "RELATION_REDUCTION", ["RELATIONS", "DUAL", "REPRESENTATIVE", "QUOTIENT", "REMAINDER"])
    n("COORDINATES", "EXACT_MATRIX_PROJECTION", ["DUAL", "AMBIENT"], "NATIVE_COORDINATE_VECTOR")
    n("PROJECTED", "EXACT_MATRIX_PROJECTION", ["REPRESENTATIVE", "COORDINATES"], "NATIVE_AMBIENT_VECTOR")
    n("RELATION_PART", "EXACT_MATRIX_PROJECTION", ["REMAINDER", "AMBIENT"], "NATIVE_AMBIENT_VECTOR")
    n("WITNESS", "RELATION_REDUCTION", ["RELATIONS", "AMBIENT", "PROJECTED"])
    n("RESIDUAL", "TENSOR_DIFFERENCE", ["AMBIENT", "PROJECTED", "RELATION_PART", "WITNESS", "RELATIONS"], "NATIVE_AMBIENT_VECTOR")
    n("LEAKAGE_ROW", "LINEAR_COMBINATION", ["SOURCE.DEFECTS", "JOIN", "C03.SOURCE.CLIFFORD_DOMAIN"], "NATIVE_AMBIENT_VECTOR")
    n("LEAKAGE", "EXACT_MATRIX_PROJECTION", ["LEAKAGE_ROW", "PROJECTED"], "SYMBOLIC_SCALAR")
    n("STATE", "EPISTEMIC_CLASSIFICATION", ["COORDINATES", "RESIDUAL", "LEAKAGE", "RELATION_CERTIFICATE"], "EVANESCENT_EVALUATION_STATE", "DERIVED")
    add("C03.OUTPUT.EVANESCENT_COORDINATES", "OUTPUT_BIND", [native_prefix + "COORDINATES"], "NATIVE_COORDINATE_VECTOR", "OUTPUT")
    add("C03.OUTPUT.EVANESCENT_STATE", "OUTPUT_BIND", [native_prefix + "STATE"], "EVANESCENT_EVALUATION_STATE", "OUTPUT")

    for record in ("RV01", "RV02", "RV03", "RV04", "RV05", "RV06"):
        def r(key: str, operation: str, parents: list[str], semantic_type: str = "EXACT_LEDGER", kind: str = "DERIVED") -> None:
            add(f"{record}.{key}", operation, [f"{record}.{parent}" for parent in parents], semantic_type, kind)

        r("DOMAIN", "DOMAIN_PREDICATE", ["SOURCE.CONTEXT"])
        r("TENSOR", "TENSOR_SUM", ["SOURCE.CONTEXT", "DOMAIN"])
        r("CHANNEL", "DOMAIN_PREDICATE", ["SOURCE.CONTEXT", "DOMAIN", "TENSOR"], "SYMBOL_TEXT")
        r("GROUP_IMAGE", "GAUGE_GENERATOR_ACTION", ["SOURCE.CONTEXT", "TENSOR", "CHANNEL"])
        r("GROUP", "EXACT_MATRIX_PROJECTION", ["TENSOR", "GROUP_IMAGE"], "SYMBOLIC_SCALAR")
        r("TREE", "TENSOR_SUM", ["SOURCE.CONTEXT", "DOMAIN"], "SYMBOLIC_MATRIX")
        r("WORDS", "PRODUCT", ["SOURCE.CONTEXT", "DOMAIN", "TREE"])
        r("METRIC_IMAGE", "EXACT_CLIFFORD_ACTION", ["SOURCE.CONTEXT", "WORDS", "TREE"], "SYMBOLIC_MATRIX")
        r("WARD_IMAGE", "WARD_REDUCTION", ["SOURCE.CONTEXT", "WORDS", "TREE"], "SYMBOLIC_MATRIX")
        r("SPINOR_PROJECTION", "EXACT_MATRIX_PROJECTION", ["TREE", "METRIC_IMAGE", "WARD_IMAGE"])
        r("PHASE", "PRODUCT", ["SOURCE.CONTEXT", "WORDS"])
        r("COVARIANT", "LINEAR_COMBINATION", ["SOURCE.CONTEXT", "SPINOR_PROJECTION"], "SYMBOLIC_SCALAR")
        r("RAW", "PRODUCT", ["SOURCE.CONTEXT", "GROUP", "COVARIANT", "PHASE"], "SYMBOLIC_SCALAR")
        r("TREE_MAP", "EXACT_MATRIX_PROJECTION", ["SOURCE.CONTEXT", "TENSOR", "TREE"])
        r("NORMALIZED", "INVERTIBLE_NORMALIZATION", ["RAW", "TREE_MAP"], "SYMBOLIC_SCALAR")
        r("ABSENCE_DOMAIN", "DOMAIN_PREDICATE", ["SOURCE.CONTEXT", "DOMAIN", "WORDS"])
        r("WORD_COVERAGE", "ANGULAR_AVERAGE", ["SOURCE.CONTEXT", "ABSENCE_DOMAIN", "WORDS"])
        r("WORD_REDUCTIONS", "EXACT_CLIFFORD_ACTION", ["WORD_COVERAGE"])
        r("POLE", "RELATION_REDUCTION", ["SOURCE.CONTEXT", "WORD_REDUCTIONS", "ABSENCE_DOMAIN"])
        r("STATE", "EPISTEMIC_CLASSIFICATION", ["POLE", "ABSENCE_DOMAIN", "WORD_COVERAGE"], "EVANESCENT_EVALUATION_STATE")
        r("OUTPUT.PHYSICAL_COEFFICIENT", "OUTPUT_BIND", ["NORMALIZED"], "SYMBOLIC_SCALAR", "OUTPUT")
        r("OUTPUT.EVANESCENT_STATE", "OUTPUT_BIND", ["STATE"], "EVANESCENT_EVALUATION_STATE", "OUTPUT")
        if record == "RV03":
            r("OUTPUT.SOURCE_CHANNEL", "OUTPUT_BIND", ["CHANNEL"], "SYMBOL_TEXT", "OUTPUT")
    return specs


DERIVED_SIGNATURES = derived_signatures()


def execute_trusted_python(node_id: str, operation: str, parents: list[Any]) -> Any:
    require(node_id in DERIVED_SIGNATURES, "C03_RV_NODE_NOT_IN_FROZEN_PROFILE", node_id)
    require(DERIVED_SIGNATURES[node_id]["operation"] == operation, "C03_RV_OPERATION_SIGNATURE", node_id)
    if operation == "OUTPUT_BIND":
        require(len(parents) == 1, "C03_RV_OUTPUT_BIND_ARITY", node_id)
        return parents[0]
    try:
        if node_id.startswith("C03.NATIVE."):
            return native.operation(node_id, parents)
        if node_id.startswith("C03."):
            return c03.operation(node_id, parents)[0]
        if node_id.startswith("RV"):
            return rv.operation(node_id, parents)
    except CalculatorError:
        raise
    except Exception as exc:
        raise CalculatorError("C03_RV_OPERATION_FAILURE", node_id, type(exc).__name__) from exc
    raise CalculatorError("C03_RV_OPERATION_DISPATCH", node_id)


def validate_operation_contracts() -> None:
    used = {row["operation"] for row in DERIVED_SIGNATURES.values()}
    require(used == set(TRUSTED_C03_RV_OPERATION_CONTRACTS), "C03_RV_OPERATION_CONTRACT_COVERAGE")
    derived_count = sum(row["kind"] != "OUTPUT" for row in DERIVED_SIGNATURES.values())
    output_count = sum(row["kind"] == "OUTPUT" for row in DERIVED_SIGNATURES.values())
    require(derived_count == 160 and output_count == 16 and len(SOURCE_SIGNATURES) == 31, "C03_RV_FROZEN_NODE_CENSUS")

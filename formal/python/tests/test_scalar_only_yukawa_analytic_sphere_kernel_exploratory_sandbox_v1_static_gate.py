from __future__ import annotations

import ast
import hashlib
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
V0 = ROOT / (
    "formal/python/tools/scalar_only_yukawa_analytic_sphere_kernel_"
    "exploratory_sandbox_v0.py"
)
V1 = ROOT / (
    "formal/python/tools/scalar_only_yukawa_analytic_sphere_kernel_"
    "exploratory_sandbox_v1.py"
)
SELECTOR = ROOT / (
    "formal/docs/release/POST_SCALAR_ONLY_YUKAWA_ANALYTIC_SPHERE_KERNEL_"
    "EXPLORATORY_SANDBOX_V0_EXECUTION_RESULT_REVIEW_SCIENTIFIC_RESPONSE_"
    "SELECTION_20260719_v0.json"
)
V0_SHA256 = "27a32f540465ed78cb2094629033a4aa30e3142c1f75aa113fc88eb10c7563ae"
SELECTOR_SHA256 = "f8a9fb6ce2f11a4b19247f2a61a3bfeebddf9d121856a6c082aeaa36e3dbda35"


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _tree() -> ast.Module:
    return ast.parse(V1.read_text(encoding="utf-8"), filename=str(V1))


def test_frozen_v0_and_selector_hashes_are_exact() -> None:
    assert _sha256(V0) == V0_SHA256
    assert _sha256(SELECTOR) == SELECTOR_SHA256


def test_v1_is_a_serialization_wrapper_not_a_scientific_reimplementation() -> None:
    tree = _tree()
    functions = {
        node.name for node in tree.body if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
    }
    for forbidden in (
        "_h_factor",
        "_candidate_core",
        "pair_energy_and_radial_derivative",
        "_run_regressions",
        "_run_probes",
        "_run_interface_checks",
        "_run_kernel_mutations",
        "_run_runtime",
        "_run_overlap_checks",
        "adjudicate_v0",
        "scan_python_dependency_contract",
    ):
        assert forbidden not in functions
    assert {
        "_normalize_canonical",
        "_validate_canonical_tree",
        "_validate_final_result_schema",
        "_canonical_bytes_v1",
        "_atomic_write_verified",
        "_serialization_controls_v1",
        "_install_v1_boundary",
        "main",
    }.issubset(functions)


def test_no_permissive_json_fallback_or_production_dependency() -> None:
    text = V1.read_text(encoding="utf-8")
    assert "default=str" not in text
    assert "scalar_only_yukawa_torsion_balance_production_v1" not in text
    assert "reduced_four_dimensional_density_integral_yukawa_energy" not in text
    assert "exploratory_sandbox_v0 as base" in text


def test_real_aggregate_control_and_terminal_paths_are_wired() -> None:
    text = V1.read_text(encoding="utf-8")
    for token in (
        "_synthetic_final_aggregate",
        "actual_nested_adjudication_record_exercised",
        "decimal_count_after_normalization",
        "atomic_write_and_postwrite_verification_passed",
        "os.fsync",
        "os.replace",
        "execute_scalar_only_yukawa_analytic_sphere_kernel_exploratory_sandbox_v1_once",
    ):
        assert token in text

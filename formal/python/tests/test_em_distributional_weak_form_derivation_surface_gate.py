from __future__ import annotations

import json
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
DOC_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_EM_DISTRIBUTIONAL_WEAK_FORM_DERIVATION_SURFACE_20260325_v0.md"
)
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "em_distributional_weak_form_derivation_surface_20260325_v0.json"
PREV_ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "em_distributional_science_increment_20260325_v0.json"
ASSUMPTION_REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "ASSUMPTION_REGISTRY_v1.md"

EXPECTED_ASSUMPTIONS = {
    "ASM-EM-U1-PHY-SOURCE-01",
    "ASM-EM-U1-MATH-SMOOTH-01",
    "ASM-EM-U1-MATH-DISTRIB-01",
}

EXPECTED_IDENTITY = "<partial_mu J^mu, phi> = -<J^mu, partial_mu phi>"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _artifact() -> dict:
    return json.loads(_read(ARTIFACT_PATH))


def test_em_distributional_weak_form_derivation_surface_artifacts_exist() -> None:
    assert DOC_PATH.exists(), "Missing EM weak-form derivation surface doc."
    assert ARTIFACT_PATH.exists(), "Missing EM weak-form derivation surface artifact."
    assert PREV_ARTIFACT_PATH.exists(), "Missing predecessor EM distributional science increment artifact."


def test_em_distributional_weak_form_doc_has_required_markers() -> None:
    text = _read(DOC_PATH)
    required_tokens = [
        "DERIVATION_TARGET_EM_DISTRIBUTIONAL_WEAK_FORM_DERIVATION_SURFACE_20260325_v0",
        "TARGET-EM-DISTRIBUTIONAL-WEAK-FORM-DERIVATION-SURFACE-20260325-v0",
        "EM_DISTRIBUTIONAL_WEAK_FORM_DERIVATION_20260325_ADJUDICATION: NOT_YET_DISCHARGED",
        "EM_DISTRIBUTIONAL_WEAK_FORM_DERIVATION_STATUS_v0: BOUNDED_WEAK_FORM_DERIVATION_SURFACE_PINNED_NONCLAIM",
        "EM_DISTRIBUTIONAL_WEAK_FORM_IDENTITY_v0: PAIRING_DUALITY_INTEGRATION_BY_PARTS_SYMBOLIC_SURFACE",
        "EM_DISTRIBUTIONAL_WEAK_FORM_BOUNDARY_RULE_v0: COMPACT_SUPPORT_BOUNDARY_TERM_VANISHES",
        "EM_DISTRIBUTIONAL_WEAK_FORM_SOURCE_MODEL_v0: POINT_SOURCE_DELTA_SYMBOLIC_COMPATIBILITY",
        "formal/output/em_distributional_science_increment_20260325_v0.json",
        "formal/output/em_distributional_weak_form_derivation_surface_20260325_v0.json",
        "formal/python/tests/test_em_distributional_weak_form_derivation_surface_gate.py",
    ]
    missing = [tok for tok in required_tokens if tok not in text]
    assert not missing, "EM weak-form derivation doc is missing required token(s): " + ", ".join(missing)


def test_em_distributional_weak_form_derivation_artifact_schema_and_tieback() -> None:
    artifact = _artifact()
    assert artifact["artifact_id"] == "em_distributional_weak_form_derivation_surface_20260325_v0"
    assert artifact["status"] == "BOUNDED_WEAK_FORM_DERIVATION_SURFACE_PINNED_NONCLAIM"
    assert artifact["lane"] == "EM_U1_MICRO_DISTRIBUTIONAL"

    assert artifact["derived_from"]["artifact_path"] == "formal/output/em_distributional_science_increment_20260325_v0.json"
    assert artifact["derived_from"]["artifact_id"] == "em_distributional_science_increment_20260325_v0"
    assert artifact["doc_pointer"] == (
        "formal/docs/paper/DERIVATION_TARGET_EM_DISTRIBUTIONAL_WEAK_FORM_DERIVATION_SURFACE_20260325_v0.md"
    )


def test_em_distributional_weak_form_derivation_is_explicit_bounded_and_nonclaim() -> None:
    artifact = _artifact()
    weak_form = artifact["weak_form_derivation"]

    assert weak_form["test_function_space"] == "C_c^infinity(omega)"
    assert weak_form["identity"] == EXPECTED_IDENTITY
    assert weak_form["integration_by_parts_boundary_condition"] == "compact_support_boundary_term_zero"

    expected_steps = [
        "pairing_definition",
        "bounded_support_localization",
        "integration_by_parts",
        "boundary_term_vanishes",
        "symbolic_identity_conclusion",
    ]
    assert weak_form["steps"] == expected_steps

    witness = artifact["bounded_singular_source_witness"]
    assert witness["model"] == "1D_point_source"
    assert witness["distribution"] == "delta(x)"
    assert witness["pairing_left"] == "<delta, phi>"
    assert witness["pairing_right"] == "phi(0)"
    assert witness["symbolic_consistency"] is True

    bounded_scope = artifact["bounded_scope"]
    assert bounded_scope["theorem_discharge_claimed"] is False
    assert bounded_scope["curved_space_covariant_divergence_claimed"] is False
    assert bounded_scope["non_abelian_completion_claimed"] is False
    assert bounded_scope["external_truth_claimed"] is False


def test_em_distributional_weak_form_derivation_assumption_and_adjudication_tokens() -> None:
    artifact = _artifact()
    assumptions = set(artifact["assumption_ids"])
    assert EXPECTED_ASSUMPTIONS.issubset(assumptions)

    registry_text = _read(ASSUMPTION_REGISTRY_PATH)
    missing_registry = [aid for aid in EXPECTED_ASSUMPTIONS if aid not in registry_text]
    assert not missing_registry, "Assumption registry missing ID(s): " + ", ".join(missing_registry)

    adjudication = artifact["adjudication"]
    assert adjudication["token"] == "EM_DISTRIBUTIONAL_WEAK_FORM_DERIVATION_20260325_ADJUDICATION"
    assert adjudication["value"] == "NOT_YET_DISCHARGED"

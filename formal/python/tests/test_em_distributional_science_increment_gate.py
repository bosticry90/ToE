from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "em_distributional_science_increment_20260325_v0.json"
ASSUMPTION_REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "ASSUMPTION_REGISTRY_v1.md"


REQUIRED_ASSUMPTION_IDS = {
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


def test_em_distributional_science_increment_artifact_exists_and_is_typed() -> None:
    artifact = _artifact()
    assert artifact["artifact_id"] == "em_distributional_science_increment_20260325_v0"
    assert artifact["lane"] == "EM_U1_MICRO_DISTRIBUTIONAL"
    assert artifact["status"] == "BOUNDED_WEAK_FORM_SEMANTICS_PINNED_NONCLAIM"


def test_em_distributional_science_increment_assumption_ids_are_present_and_registered() -> None:
    artifact = _artifact()
    assumption_ids = set(artifact["assumption_ids"])
    assert REQUIRED_ASSUMPTION_IDS.issubset(assumption_ids)

    registry_text = _read(ASSUMPTION_REGISTRY_PATH)
    missing_from_registry = [aid for aid in REQUIRED_ASSUMPTION_IDS if aid not in registry_text]
    assert not missing_from_registry, (
        "Assumption registry is missing required EM distributional assumption ID(s): "
        + ", ".join(missing_from_registry)
    )


def test_em_distributional_weak_form_semantics_and_bounded_scope_are_explicit() -> None:
    artifact = _artifact()
    semantics = artifact["weak_form_semantics"]
    bounded_scope = artifact["bounded_scope"]

    assert semantics["test_function_space"] == "C_c^infinity(omega)"
    assert semantics["support_localization"] == "bounded_compact_support"
    assert semantics["distributional_continuity_identity"] == EXPECTED_IDENTITY
    assert semantics["singular_source_model"] == "point_source_q_delta_x"
    assert semantics["admissible_claim_scope"] == "semantic_mapping_and_bounded_pairing_only"

    assert bounded_scope["curved_space_covariant_divergence_claimed"] is False
    assert bounded_scope["theorem_discharge_claimed"] is False
    assert bounded_scope["non_abelian_completion_claimed"] is False
    assert bounded_scope["external_truth_claimed"] is False


def test_em_distributional_toy_pairing_witness_is_pairing_consistent() -> None:
    artifact = _artifact()
    witness = artifact["toy_pairing_witness"]

    lhs = Fraction(witness["lhs_pairing_partial_J_phi"])
    rhs = Fraction(witness["rhs_neg_pairing_J_partial_phi"])
    diff = Fraction(witness["difference"])

    assert lhs == rhs
    assert diff == 0


def test_em_distributional_adjudication_token_is_nonclaim() -> None:
    artifact = _artifact()
    adjudication = artifact["adjudication"]

    assert adjudication["token"] == "EM_DISTRIBUTIONAL_SCI_INCREMENT_20260325_ADJUDICATION"
    assert adjudication["value"] == "NOT_YET_DISCHARGED"

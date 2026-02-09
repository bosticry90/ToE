from __future__ import annotations

import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
MANIFEST_PATH = (
    REPO_ROOT
    / "formal"
    / "python"
    / "toe"
    / "comparators"
    / "comparator_rep_interpretability_manifest.json"
)


def test_cv03_manifest_entry_is_pinned_to_cross_rep_equivalent_with_proof():
    manifest = json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    comparators = manifest.get("comparators", {})

    cid = "cv03_ucff_dispersion_v1"
    assert cid in comparators, f"Missing comparator entry in manifest: {cid}"

    row = comparators[cid]
    assert row.get("rep_interpretability_claim") == "cross_rep_equivalent"
    assert row.get("policy_token") == "FN_REP_EQ_POLICY_V1"
    assert (
        row.get("proof_artifact")
        == "formal/toe_formal/ToeFormal/Variational/FNRep32Rep64Equivalence.lean"
    )
    assert (
        row.get("proof_build_guard_test")
        == "formal/python/tests/test_lean_fn_rep32_rep64_equivalence_build_guard.py"
    )

    proof_path = (REPO_ROOT / row["proof_artifact"]).resolve()
    assert proof_path.exists(), f"Proof artifact missing: {row['proof_artifact']}"
    assert proof_path.suffix == ".lean"

    guard_path = (REPO_ROOT / row["proof_build_guard_test"]).resolve()
    assert guard_path.exists(), f"Build-guard test missing: {row['proof_build_guard_test']}"
    assert guard_path.suffix == ".py"


def test_rl02_manifest_entry_is_pinned_within_rep_only():
    manifest = json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    comparators = manifest.get("comparators", {})

    cid = "rl02_nonrelativistic_nlse_v0"
    assert cid in comparators, f"Missing comparator entry in manifest: {cid}"

    row = comparators[cid]
    assert row.get("rep_interpretability_claim") == "within_rep_only"
    assert row.get("module") == "formal/python/toe/comparators/rl02_nonrelativistic_nlse_v0.py"

    module_path = (REPO_ROOT / row["module"]).resolve()
    assert module_path.exists(), f"Comparator module missing: {row['module']}"
    assert module_path.suffix == ".py"

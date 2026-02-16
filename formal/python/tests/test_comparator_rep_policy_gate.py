from __future__ import annotations

import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
COMPARATORS_DIR = REPO_ROOT / "formal" / "python" / "toe" / "comparators"
MANIFEST_PATH = COMPARATORS_DIR / "comparator_rep_interpretability_manifest.json"
POLICY_PATH = REPO_ROOT / "formal" / "python" / "toe" / "constraints" / "fn_rep_equivalence_policy.json"


def _load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _lean_module_from_path(artifact_path: str) -> str:
    path = Path(artifact_path).with_suffix("")
    parts = list(path.parts)
    if "ToeFormal" in parts:
        start = parts.index("ToeFormal")
        parts = parts[start:]
    return ".".join(parts)


def _tracked_comparator_modules() -> set[str]:
    # Canonical comparator surface on this branch includes cv* lanes plus
    # the two baseline RL comparators (rl01/rl02).
    modules = {p.name for p in COMPARATORS_DIR.glob("cv*_*.py")}
    modules |= {p.name for p in COMPARATORS_DIR.glob("rl01_*.py")}
    modules |= {p.name for p in COMPARATORS_DIR.glob("rl02_*.py")}
    return modules


def test_comparator_manifest_covers_all_comparator_modules():
    manifest = _load_json(MANIFEST_PATH)
    comparators = manifest.get("comparators", {})
    manifest_modules = {Path(v.get("module", "")).name for v in comparators.values()}
    fs_modules = _tracked_comparator_modules()
    assert manifest_modules == fs_modules, (
        "Comparator rep-interpretability manifest must cover all comparator modules.\n"
        f"Manifest modules: {sorted(manifest_modules)}\n"
        f"Filesystem modules: {sorted(fs_modules)}"
    )


def test_cross_rep_claims_require_pinned_policy_token():
    manifest = _load_json(MANIFEST_PATH)
    policy = _load_json(POLICY_PATH)

    assert manifest.get("schema") == "Toe/comparator_rep_interpretability_manifest/v2"
    assert policy.get("schema") == "Toe/fn_rep_equivalence_policy/v1"

    policy_token = policy.get("policy_token")
    required_token = manifest.get("policy_token_required_for_cross_rep")
    assert policy_token == required_token

    allowed_claims = {"within_rep_only", "cross_rep_equivalent"}
    for cid, row in manifest.get("comparators", {}).items():
        claim = row.get("rep_interpretability_claim")
        assert claim in allowed_claims, f"{cid}: invalid claim kind {claim!r}"
        claim_token = row.get("policy_token")
        proof_artifact = str(row.get("proof_artifact", "")).strip()
        proof_build_guard_test = str(row.get("proof_build_guard_test", "")).strip()
        if claim == "cross_rep_equivalent":
            assert claim_token == policy_token, (
                f"{cid}: cross-rep claim requires policy_token={policy_token!r}"
            )
            assert proof_artifact, f"{cid}: cross-rep claim must declare proof_artifact"
            proof_path = (REPO_ROOT / proof_artifact).resolve()
            assert proof_path.exists(), f"{cid}: proof_artifact not found: {proof_artifact}"
            assert proof_path.suffix == ".lean", (
                f"{cid}: proof_artifact must reference a Lean module (.lean), got: {proof_artifact}"
            )

            assert proof_build_guard_test, (
                f"{cid}: cross-rep claim must declare proof_build_guard_test (a pytest build-guard module)"
            )
            guard_path = (REPO_ROOT / proof_build_guard_test).resolve()
            assert guard_path.exists(), (
                f"{cid}: proof_build_guard_test not found: {proof_build_guard_test}"
            )
            assert guard_path.suffix == ".py", (
                f"{cid}: proof_build_guard_test must reference a python test module (.py), got: {proof_build_guard_test}"
            )
            assert guard_path.name.startswith("test_"), (
                f"{cid}: proof_build_guard_test should be a pytest test module (must start with 'test_'), got: {proof_build_guard_test}"
            )
            tests_root = (REPO_ROOT / "formal" / "python" / "tests").resolve()
            assert tests_root in guard_path.parents, (
                f"{cid}: proof_build_guard_test must live under formal/python/tests (got: {proof_build_guard_test})"
            )
            lean_module = _lean_module_from_path(proof_artifact)
            guard_text = guard_path.read_text(encoding="utf-8")
            assert lean_module in guard_text, (
                f"{cid}: proof_build_guard_test must reference Lean module {lean_module!r}"
            )
        else:
            assert not proof_artifact, (
                f"{cid}: within_rep_only must not declare proof_artifact (found {proof_artifact!r})"
            )
            assert not proof_build_guard_test, (
                f"{cid}: within_rep_only must not declare proof_build_guard_test (found {proof_build_guard_test!r})"
            )

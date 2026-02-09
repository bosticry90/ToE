from __future__ import annotations

import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
COMPARATORS_DIR = REPO_ROOT / "formal" / "python" / "toe" / "comparators"
MANIFEST_PATH = COMPARATORS_DIR / "comparator_rep_interpretability_manifest.json"
POLICY_PATH = REPO_ROOT / "formal" / "python" / "toe" / "constraints" / "fn_rep_equivalence_policy.json"


def _load_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _tracked_comparator_modules() -> set[str]:
    # Comparator lanes are cv*.py modules in the canonical comparators front door.
    return {p.name for p in COMPARATORS_DIR.glob("cv*_*.py")}


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

    assert manifest.get("schema") == "Toe/comparator_rep_interpretability_manifest/v1"
    assert policy.get("schema") == "Toe/fn_rep_equivalence_policy/v1"

    policy_token = policy.get("policy_token")
    required_token = manifest.get("policy_token_required_for_cross_rep")
    assert policy_token == required_token

    allowed_claims = {"within_rep_only", "cross_rep_equivalent"}
    for cid, row in manifest.get("comparators", {}).items():
        claim = row.get("rep_interpretability_claim")
        assert claim in allowed_claims, f"{cid}: invalid claim kind {claim!r}"
        claim_token = row.get("policy_token")
        if claim == "cross_rep_equivalent":
            assert claim_token == policy_token, (
                f"{cid}: cross-rep claim requires policy_token={policy_token!r}"
            )

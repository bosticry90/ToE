from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

from formal.python.tools.regen_canonical_locks import main as regen_main


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))


def _extract_json_block(md_text: str) -> dict[str, Any]:
    m = re.search(r"```json\s*(\{.*?\})\s*```", md_text, flags=re.DOTALL)
    if m is None:
        raise AssertionError("Missing JSON record block")
    return json.loads(m.group(1))


def _semantic_stability_key(locked: dict[str, Any]) -> str:
    """Prefer the record fingerprint (the semantic lock payload hash).

    Falls back to a deterministic hash of a filtered semantic subset if a
    particular record type ever omits the fingerprint.
    """

    fp = locked.get("fingerprint")
    if isinstance(fp, str) and fp:
        return fp

    # Fallback: hash a stable subset that should be semantic.
    subset = {
        "schema": locked.get("schema"),
        "observable_id": locked.get("observable_id"),
        "inputs": locked.get("inputs"),
        "selection": locked.get("selection"),
        "method": locked.get("method"),
        "results": locked.get("results"),
        "rows": locked.get("rows"),
        "units": locked.get("units"),
    }
    b = json.dumps(subset, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode("utf-8")
    # Re-use stdlib hashlib here to avoid importing anything heavy.
    import hashlib

    return hashlib.sha256(b).hexdigest()


def test_regen_bragg_only_override_is_stable_and_unblocked_for_key_records() -> None:
    override = REPO_ROOT / "formal" / "markdown locks" / "gates" / "admissibility_manifest_ENABLED_OVERRIDE.json"
    assert override.exists()

    lock_paths = [
        REPO_ROOT / "formal" / "markdown" / "locks" / "observables" / "OV-BR-04a_bragg_lowk_slope_conditionA_OVERRIDE.md",
        REPO_ROOT / "formal" / "markdown" / "locks" / "observables" / "OV-BR-04b_bragg_lowk_slope_conditionB_OVERRIDE.md",
        REPO_ROOT / "formal" / "markdown" / "locks" / "observables" / "OV-BR-05_bragg_lowk_slope_summary_OVERRIDE.md",
        REPO_ROOT / "formal" / "markdown" / "locks" / "observables" / "OV-DR-BR-01_candidate_pruning_table_OVERRIDE.md",
        REPO_ROOT / "formal" / "markdown" / "locks" / "observables" / "OV-FN-WT-01_fn01_weight_policy_pruning_table_OVERRIDE.md",
        REPO_ROOT / "formal" / "markdown" / "locks" / "observables" / "OV-FN-02_weighted_residual_audit_OVERRIDE.md",
    ]

    rc = regen_main(["--bragg-only", "--admissibility-manifest", str(override), "--report"])
    assert rc == 0

    after_1_keys: list[str] = []
    for p in lock_paths:
        locked = _extract_json_block(p.read_text(encoding="utf-8"))
        after_1_keys.append(_semantic_stability_key(locked))

    # Run twice: the first run may normalize legacy lock state; the second run
    # must be a fixed point.
    rc = regen_main(["--bragg-only", "--admissibility-manifest", str(override), "--report"])
    assert rc == 0

    after_2_keys: list[str] = []
    for p in lock_paths:
        locked = _extract_json_block(p.read_text(encoding="utf-8"))
        after_2_keys.append(_semantic_stability_key(locked))

    # Renderer/debug churn is allowed; semantic payload must be stable.
    assert after_2_keys == after_1_keys

    # Smoke invariants: correct manifest wiring + unblocked.
    for p in lock_paths:
        text = p.read_text(encoding="utf-8")
        locked = _extract_json_block(text)
        status = dict(locked.get("status") or {})
        assert status.get("blocked") is False

        manifest = dict(status.get("admissibility_manifest") or {})
        assert manifest.get("path") == "formal/markdown locks/gates/admissibility_manifest_ENABLED_OVERRIDE.json"
        assert manifest.get("version") == 5

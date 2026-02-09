from __future__ import annotations

import json
from pathlib import Path

import pytest

from formal.python.toe.observables.ovbr04a_bragg_lowk_slope_conditionA_record import (
    ovbr04a_bragg_lowk_slope_conditionA_record,
)


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def test_admissibility_manifest_override_blocks_ct01(monkeypatch: pytest.MonkeyPatch, tmp_path: Path):
    repo_root = _find_repo_root(Path(__file__))
    manifest_path = repo_root / "formal" / "markdown locks" / "gates" / "admissibility_manifest.json"
    assert manifest_path.exists(), f"Missing manifest: {manifest_path}"

    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    assert "gates" in manifest
    assert "CT01" in manifest["gates"]

    manifest["gates"]["CT01"]["enabled"] = False
    override_path = tmp_path / "admissibility_manifest_override.json"
    override_path.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    monkeypatch.setenv("TOE_ADMISSIBILITY_MANIFEST", str(override_path))

    rec = ovbr04a_bragg_lowk_slope_conditionA_record(date="2026-01-25")
    assert bool(rec.status.get("blocked")) is True
    reasons = rec.status.get("reasons", [])
    assert any(str(r).startswith("gate_disabled:CT01") for r in reasons)

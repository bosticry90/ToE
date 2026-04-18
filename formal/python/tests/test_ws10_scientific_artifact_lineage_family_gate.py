from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
STATE_CORE_PATH = REPO_ROOT / "formal" / "docs" / "release" / "state_core_v0.json"
RENDERER_PATH = REPO_ROOT / "formal" / "python" / "tools" / "render_state_core_mirrors.py"

TRACKER_SNIPPET = REPO_ROOT / "formal" / "output" / "state_core_generated" / "state_core_tracker_snippet_v0.md"
WS10_SNIPPET = REPO_ROOT / "formal" / "output" / "state_core_generated" / "state_core_ws10_snippet_v0.md"


def _run_renderer() -> None:
    cmd = [
        sys.executable,
        str(RENDERER_PATH),
        "--apply-mirrors",
        "--verify-mirrors",
    ]
    completed = subprocess.run(
        cmd,
        cwd=str(REPO_ROOT),
        check=False,
        capture_output=True,
        text=True,
    )
    assert completed.returncode == 0, (
        "Renderer apply/verify failed for WS-10 scientific artifact lineage family gate.\n"
        f"stdout:\n{completed.stdout}\n"
        f"stderr:\n{completed.stderr}"
    )


def test_ws10_scientific_artifact_lineage_family_contract() -> None:
    state_core = json.loads(STATE_CORE_PATH.read_text(encoding="utf-8"))
    tranche_ids = {tranche["id"] for tranche in state_core["tranches"]}

    family = state_core["ws10_scientific_artifact_lineage_family"]
    assert family["family_id"] == "WS10_SCIENTIFIC_ARTIFACT_LINEAGE_METADATA_v0"
    assert family["active_lineage_id"] == "WS10-L19"

    lineages = family["lineages"]
    assert len(lineages) >= 4

    lineage_ids = [entry["id"] for entry in lineages]
    assert lineage_ids[0] == "WS10-L10"
    assert lineage_ids[-1] == "WS10-L19"
    assert family["active_lineage_id"] in lineage_ids

    for entry in lineages:
        assert entry["tranche_id"] in tranche_ids
        assert entry["lane"] in {"QM_STAT", "COSMO_SR"}
        assert entry["cycle"].startswith("CYCLE")
        assert entry["lineage_role"]
        artifact = REPO_ROOT / entry["artifact"]
        assert artifact.exists(), f"Missing lineage artifact: {artifact}"


def test_ws10_scientific_artifact_lineage_family_renderer_surface_coverage() -> None:
    _run_renderer()

    tracker_text = TRACKER_SNIPPET.read_text(encoding="utf-8")
    ws10_text = WS10_SNIPPET.read_text(encoding="utf-8")

    assert "STATE_CORE_TRACKER_WS10_LINEAGE_ACTIVE_ID_v0: WS10-L19" in tracker_text
    assert "STATE_CORE_TRACKER_WS10_LINEAGE_ACTIVE_TRANCHE_v0: WS-10-T19" in tracker_text
    assert "STATE_CORE_TRACKER_WS10_LINEAGE_ENTRY_COUNT_v0: 4" in tracker_text

    assert "STATE_CORE_WS10_LINEAGE_ACTIVE_ID_v0: WS10-L19" in ws10_text
    assert "STATE_CORE_WS10_LINEAGE_ACTIVE_TRANCHE_v0: WS-10-T19" in ws10_text
    assert "STATE_CORE_WS10_LINEAGE_ENTRY_COUNT_v0: 4" in ws10_text
    assert "STATE_CORE_WS10_LINEAGE_CHAIN_v0: WS10-L10:WS-10-T10" in ws10_text

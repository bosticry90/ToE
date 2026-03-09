from __future__ import annotations

import json
import re
from pathlib import Path


DEFAULT_CADENCE = 10


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PILLAR_DEEP_MATURITY_REGISTRY_v0.json"
REPORT_GLOB = "sr_m5_quality_checkpoint_cycle*_v0.json"


def _read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _cycle_from_text(text: str) -> int:
    m = re.search(r"cycle(\d+)", text)
    assert m is not None, f"Could not parse cycle from `{text}`"
    return int(m.group(1))


def test_sr_m5_periodic_quality_checkpoint_gate() -> None:
    registry = _read_json(REGISTRY_PATH)

    active_gate = registry.get("sr_m5_theory_parity_gate_path")
    assert isinstance(active_gate, str) and active_gate
    active_cycle = _cycle_from_text(active_gate)

    policy_doc = REPO_ROOT / str(registry.get("sr_m5_archive_retention_policy_doc", ""))
    cadence = DEFAULT_CADENCE
    if policy_doc.exists():
        txt = policy_doc.read_text(encoding="utf-8")
        m = re.search(r"SR_M5_QUALITY_CHECKPOINT_CADENCE_v0\s*:\s*(\d+)", txt)
        if m is not None:
            cadence = int(m.group(1))

    out_dir = REPO_ROOT / "formal" / "output"
    reports = sorted(out_dir.glob(REPORT_GLOB))
    assert reports, "Missing SR M5 periodic quality checkpoint reports."

    latest_report = reports[-1]
    latest_cycle = _cycle_from_text(latest_report.name)
    payload = _read_json(latest_report)

    assert payload.get("active_cycle") == latest_cycle
    assert payload.get("artifact_count") >= latest_cycle
    assert payload.get("gate_count") >= latest_cycle
    assert payload.get("non_skipped_gate_count") == 1

    assert latest_cycle <= active_cycle, "Quality checkpoint cannot be ahead of active cycle."
    assert (active_cycle - latest_cycle) <= cadence, "Quality checkpoint is stale beyond configured cadence."

    pinned = registry.get("sr_m5_latest_quality_checkpoint_artifact_path")
    if isinstance(pinned, str) and pinned:
        assert (REPO_ROOT / pinned).exists(), "Pinned latest quality checkpoint artifact is missing."
        assert _cycle_from_text(pinned) == latest_cycle

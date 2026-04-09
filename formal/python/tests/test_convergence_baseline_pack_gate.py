from __future__ import annotations

import json
from pathlib import Path

from formal.python.tests._archived_history_sentinel import split_active_and_archived


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
CHECKLIST_PATH = REPO_ROOT / "Canonical Verification Checklist.md"
DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "CONVERGENCE_BASELINE_PACK_20260409_v0.md"
PACK_PATH = REPO_ROOT / "formal" / "output" / "reports" / "convergence_baseline_pack_20260409_v0.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _active_text(path: Path) -> str:
    active, _ = split_active_and_archived(_read(path), path)
    return active


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_convergence_baseline_pack_files_exist() -> None:
    assert DECLARATION_PATH.exists(), "Missing convergence baseline pack declaration."
    assert PACK_PATH.exists(), "Missing convergence baseline pack JSON."


def test_convergence_baseline_pack_required_metrics_shape() -> None:
    payload = _json(PACK_PATH)

    assert payload.get("schema_id") == "CONVERGENCE_BASELINE_PACK_20260409_v0"
    assert payload.get("status") == "DECLARED_BASELINE_PACK_NONLIVE_NONCLAIM"

    required_metrics = payload.get("required_metrics", {})
    assert isinstance(required_metrics, dict)
    assert len(required_metrics) == 5

    expected_keys = {
        "blocker_count_by_class",
        "theorem_depth_baseline",
        "redundant_registry_count",
        "checkpoint_count",
        "active_canonical_owners_list",
    }
    assert set(required_metrics.keys()) == expected_keys

    blocker_counts = required_metrics["blocker_count_by_class"].get("current", {})
    for key in [
        "THEOREM_GAP",
        "SEAM_INTEGRATION_GAP",
        "PARITY_DRIFT",
        "GOVERNANCE_GUARDRAIL",
        "EVIDENCE_ALIGNMENT_GAP",
    ]:
        assert key in blocker_counts
        assert isinstance(blocker_counts[key], int) and blocker_counts[key] >= 0

    theorem_depth = required_metrics["theorem_depth_baseline"]
    assert theorem_depth.get("score_name") == "THEOREM_DEPTH_QUEUE_ROW_COUNT"
    assert theorem_depth.get("value") == 3

    redundant_registry = required_metrics["redundant_registry_count"]
    assert isinstance(redundant_registry.get("value"), int)
    assert redundant_registry.get("value") >= 0

    checkpoint_count = required_metrics["checkpoint_count"]
    assert isinstance(checkpoint_count.get("value"), int)
    assert checkpoint_count.get("value") > 0

    owners = required_metrics["active_canonical_owners_list"]
    assert owners.get("count") == 5
    assert isinstance(owners.get("owners"), list)
    assert len(owners["owners"]) == 5
    for owner in owners["owners"]:
        assert isinstance(owner.get("token_family"), str) and owner["token_family"]
        assert isinstance(owner.get("owner_path"), str) and owner["owner_path"]


def test_convergence_baseline_pack_state_and_checklist_tokens_present() -> None:
    state_text = _active_text(STATE_PATH)
    checklist_text = _read(CHECKLIST_PATH)

    state_required = [
        "CONVERGENCE_BASELINE_PACK_DECLARATION_v0: formal/docs/release/CONVERGENCE_BASELINE_PACK_20260409_v0.md",
        "CONVERGENCE_BASELINE_PACK_JSON_v0: formal/output/reports/convergence_baseline_pack_20260409_v0.json",
        "CONVERGENCE_BASELINE_DELTA_RULE_v0: NO_PHASE_LEVEL_IMPROVEMENT_CLAIM_WITHOUT_BASELINE_PACK_DELTA_CITATION",
        "CONVERGENCE_BASELINE_GATE_v0: formal/python/tests/test_convergence_baseline_pack_gate.py",
    ]
    for token in state_required:
        assert token in state_text, f"Missing state token: {token}"

    checklist_required = [
        "Baseline pack pointer declared? YES / NO",
        "Blocker-count-by-class delta recorded? YES / NO",
        "Theorem-depth baseline delta recorded? YES / NO",
        "Redundant-registry count delta recorded? YES / NO",
        "Checkpoint-count delta recorded? YES / NO",
        "Active canonical owners delta recorded? YES / NO",
        "Discriminator threshold defined? YES / NO",
        "Blocker-reduction claim present? YES / NO",
        "Proof-debt movement recorded? YES / NO",
    ]
    for token in checklist_required:
        assert token in checklist_text, f"Missing checklist token: {token}"

from __future__ import annotations

import json
import re
from pathlib import Path


def _repo_root() -> Path:
    return Path(__file__).resolve().parents[3]


def _read_json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def _extract_rollup_count(text: str, name: str) -> int:
    match = re.search(rf"- `{re.escape(name)}`: (\d+)", text)
    assert match is not None, f"Missing inventory rollup marker: {name}"
    return int(match.group(1))


def _count_inventory_statuses(text: str) -> dict[str, int]:
    counts = {
        "VALIDATED": 0,
        "USED": 0,
        "OPEN_PROOF_DEBT": 0,
        "BOUNDED_NONCLAIM": 0,
    }

    in_table = False
    for line in text.splitlines():
        if line.strip() == "## 2) Mathematical inventory":
            in_table = True
            continue
        if in_table and line.strip() == "## 4) Validation status":
            break
        if not in_table or not line.startswith("| `INV-"):
            continue

        columns = [part.strip() for part in line.split("|")]
        if len(columns) < 10:
            continue
        status = columns[9].strip("`")
        if status in counts:
            counts[status] += 1

    return counts


def test_repo_status_audit_checkpoint_core_tokens() -> None:
    root = _repo_root()
    checkpoint_path = root / "formal/output/repo_status_audit_20260315_checkpoint_v0.json"
    payload = _read_json(checkpoint_path)

    assert payload["checkpoint_id"] == "repo_status_audit_20260315_checkpoint_v0"
    assert payload["status"] == "ACTIVE_v0_NONCLAIM"

    tokens = payload["status_tokens"]
    assert tokens["REPO_STATUS_AUDIT_DATE_v0"] == "2026-03-15"
    assert tokens["REPO_STATUS_TOE_COMPLETE_V1_v0"] == "TERMINAL_SATISFIED_v0_NONCLAIM"
    assert tokens["REPO_STATUS_SEAM_PHYSICS_COMPLETE_GLOBAL_v0"] == "NO"
    assert tokens["REPO_STATUS_PACKET41_v0"] == "HOLD_RETAINED_REVIEW_LAYER_FAILURE_CYCLE02_NUMERIC_EVALUATED"


def test_repo_status_audit_cross_surface_bindings_exist() -> None:
    root = _repo_root()
    checkpoint_path = root / "formal/output/repo_status_audit_20260315_checkpoint_v0.json"
    payload = _read_json(checkpoint_path)

    bindings = payload["bindings"]
    for rel_path in bindings.values():
        assert (root / rel_path).exists(), f"Missing binding target: {rel_path}"


def test_repo_status_audit_parity_in_state_and_roadmap() -> None:
    root = _repo_root()
    state = _read_text(root / "State_of_the_Theory.md")
    roadmap = _read_text(root / "formal/docs/paper/PHYSICS_ROADMAP_v0.md")

    required_lines = [
        "REPO_STATUS_AUDIT_DATE_v0: 2026-03-15",
        "REPO_STATUS_GOVERNANCE_v0: STRONG_BOUNDED_NONCLAIM",
        "REPO_STATUS_PHYSICS_v0: DISCRIMINATIVE_MIXED_PROGRESS",
        "REPO_STATUS_TOE_COMPLETE_V1_v0: TERMINAL_SATISFIED_v0_NONCLAIM",
        "REPO_STATUS_SEAM_PHYSICS_COMPLETE_GLOBAL_v0: NO",
        "REPO_STATUS_PACKET41_v0: HOLD_RETAINED_REVIEW_LAYER_FAILURE_CYCLE02_NUMERIC_EVALUATED",
        "REPO_STATUS_SCALAR_SUBMISSION_v0: READY_FOR_BOUNDED_PAPER1_SUBMISSION_PACKAGE",
        "formal/docs/release/REPO_STATUS_AUDIT_20260315_v0.md",
        "formal/output/repo_status_audit_20260315_checkpoint_v0.json",
        "formal/python/tests/test_repo_status_audit_20260315_gate.py",
    ]

    for line in required_lines:
        assert line in state, f"Missing state marker: {line}"
        assert line in roadmap, f"Missing roadmap marker: {line}"


def test_repo_status_audit_inventory_rollup_matches_row_statuses() -> None:
    root = _repo_root()
    inventory = _read_text(root / "formal/docs/paper/TOE_MATH_PHYSICS_INVENTORY_v0.md")

    counts = _count_inventory_statuses(inventory)

    assert _extract_rollup_count(inventory, "validated_rows") == counts["VALIDATED"]
    assert _extract_rollup_count(inventory, "used_rows") == counts["USED"]
    assert _extract_rollup_count(inventory, "open_proof_debt_rows") == counts["OPEN_PROOF_DEBT"]
    assert _extract_rollup_count(inventory, "bounded_nonclaim_rows") == counts["BOUNDED_NONCLAIM"]

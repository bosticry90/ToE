from __future__ import annotations

import json
import re
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PILLAR_STATUS_MATRIX_v1.json"
RESULTS_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "RESULTS_TABLE_v0.md"
THERMO_TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_THERMO_ENTROPY_OBJECT_v0.md"
STAT_PLAN_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_STAT_ENTROPY_PLAN_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _extract_single_token_value(text: str, token_name: str) -> str:
    matches = re.findall(rf"\b{re.escape(token_name)}\s*:\s*([^\n]+)", text)
    assert len(matches) == 1, f"Expected exactly one `{token_name}` definition, found {len(matches)}."
    return matches[0].strip().strip("`")


def _pillar_table_row(text: str, pillar_id: str) -> str:
    rows = [line for line in text.splitlines() if line.strip().startswith(f"| `{pillar_id}` |")]
    assert len(rows) == 1, f"Expected exactly one `{pillar_id}` row in roadmap table, found {len(rows)}."
    return rows[0]


def _extract_status_from_row(row: str) -> str:
    cols = [c.strip() for c in row.split("|") if c.strip()]
    assert len(cols) >= 2, f"Malformed pillar row: {row}"
    return cols[1].strip("`")


def _extract_prereqs_from_row(row: str) -> str:
    cols = [c.strip() for c in row.split("|") if c.strip()]
    assert len(cols) >= 5, f"Malformed pillar row: {row}"
    return cols[4].strip("`")


def _results_labels_by_claim(text: str) -> dict[str, str]:
    claim_to_label: dict[str, str] = {}
    pattern = re.compile(r"^\|\s*([^|]+?)\s*\|\s*`([^`]+)`\s*\|", re.MULTILINE)
    for claim, label in pattern.findall(text):
        claim_to_label[claim.strip()] = label.strip()
    return claim_to_label


def test_stat_unlock_prerequisite_integrity_gate() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    matrix = _read_json(MATRIX_PATH)
    results_text = _read(RESULTS_PATH)
    thermo_target_text = _read(THERMO_TARGET_PATH)
    stat_plan_text = _read(STAT_PLAN_PATH)

    stat_row = _pillar_table_row(roadmap_text, "PILLAR-STAT")
    stat_status = _extract_status_from_row(stat_row)
    assert stat_status in {"LOCKED", "ACTIVE"}, (
        "PILLAR-STAT prerequisite integrity gate expects either the historical LOCKED posture or the canonical ACTIVE posture."
    )
    assert "`TARGET-TH-ENTROPY-PLAN`" in stat_row
    assert "`TARGET-GR01-DERIV-CHECKLIST-PLAN`" in stat_row

    stat_matrix = matrix.get("pillars", {}).get("PILLAR-STAT")
    if stat_status == "ACTIVE":
        assert isinstance(stat_matrix, dict), "PILLAR-STAT matrix row must exist after activation."
        assert stat_matrix.get("matrix_status") == "ACTIVE", "PILLAR-STAT matrix status must be ACTIVE after activation."

    assert "`TOE-STAT-*` -> `TARGET-TH-ENTROPY-PLAN`" in roadmap_text

    gr_matrix = matrix.get("pillars", {}).get("PILLAR-GR")
    assert isinstance(gr_matrix, dict), "PILLAR-GR matrix row is missing."
    assert gr_matrix.get("matrix_status") == "CLOSED", "PILLAR-GR must remain CLOSED for STAT unlock readiness."

    required_rows_raw = _extract_single_token_value(roadmap_text, "REQUIRED_GR_CLOSURE_ROWS")
    required_rows = [token.strip().strip("`") for token in required_rows_raw.split(",") if token.strip()]
    assert required_rows, "REQUIRED_GR_CLOSURE_ROWS must not be empty."

    claim_labels = _results_labels_by_claim(results_text)
    for claim in required_rows:
        assert claim in claim_labels, f"Required prerequisite row `{claim}` missing in RESULTS_TABLE_v0.md."
        assert not claim_labels[claim].startswith("B-"), (
            f"Required prerequisite row `{claim}` is still blocker-labeled: `{claim_labels[claim]}`."
        )

    qft_row = _pillar_table_row(roadmap_text, "PILLAR-QFT")
    qft_prereqs = _extract_prereqs_from_row(qft_row)
    assert "TARGET-TH-ENTROPY-PLAN" not in qft_prereqs, (
        "QFT prerequisite set must not depend on STAT target during readiness lane."
    )

    assert "Target ID:\n- `TARGET-TH-ENTROPY-PLAN`" in thermo_target_text
    assert "Target ID:\n- `TARGET-TH-ENTROPY-PLAN`" in stat_plan_text

    assert "ASM-QM-" not in thermo_target_text
    assert "ASM-QFT-" not in thermo_target_text
    assert "ASM-QM-" not in stat_plan_text
    assert "ASM-QFT-" not in stat_plan_text

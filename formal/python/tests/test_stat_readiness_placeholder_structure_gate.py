from __future__ import annotations

import json
import re
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists() and (p / "README.md").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory and README.md).")


REPO_ROOT = find_repo_root(Path(__file__))
STAT_PLAN_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_STAT_ENTROPY_PLAN_v0.md"
RESULTS_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "RESULTS_TABLE_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PILLAR_STATUS_MATRIX_v1.json"
STAT_CYCLE01_ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "stat_evidence_checkpoint_cycle01_v0.json"
STAT_CYCLE01_COUPLING_GATE_PATH = (
    REPO_ROOT / "formal" / "python" / "tests" / "test_stat_evidence_checkpoint_coupling_cycle01_gate.py"
)
STAT_CYCLE01_ACCEPTANCE_GATE_PATH = (
    REPO_ROOT / "formal" / "python" / "tests" / "test_stat_evidence_checkpoint_cycle01_acceptance_gate.py"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def _read_json(path: Path) -> dict:
    assert path.exists(), f"Missing required file: {path}"
    return json.loads(path.read_text(encoding="utf-8"))


def _results_row_line(text: str, row_id: str) -> str:
    rows = [line for line in text.splitlines() if line.strip().startswith(f"| {row_id} |")]
    assert len(rows) == 1, f"Expected exactly one `{row_id}` row in RESULTS_TABLE_v0.md, found {len(rows)}."
    return rows[0]


def _results_row_columns(row_line: str) -> list[str]:
    cols = [c.strip() for c in row_line.split("|") if c.strip()]
    assert len(cols) >= 6, f"Malformed results row: {row_line}"
    return cols


def test_stat_readiness_placeholder_structure_gate() -> None:
    stat_plan_text = _read(STAT_PLAN_PATH)
    results_text = _read(RESULTS_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    matrix = _read_json(MATRIX_PATH)

    stat_matrix = matrix.get("pillars", {}).get("PILLAR-STAT")
    matrix_status = stat_matrix.get("matrix_status") if isinstance(stat_matrix, dict) else None

    stat_locked = "| `PILLAR-STAT` | `LOCKED` |" in roadmap_text
    stat_closed = "| `PILLAR-STAT` | `CLOSED` |" in roadmap_text
    if not stat_locked:
        assert "| `PILLAR-STAT` | `ACTIVE` |" in roadmap_text or stat_closed, (
            "STAT placeholder structure gate expects LOCKED, ACTIVE, or CLOSED posture."
        )

    # Reserved STAT closure rows must exist in both the STAT plan and results table before activation.
    for row_id in ("TOE-STAT-DER-01", "TOE-STAT-DER-02"):
        assert f"`{row_id}`" in stat_plan_text, f"STAT plan must reserve `{row_id}`."

        row_line = _results_row_line(results_text, row_id)
        cols = _results_row_columns(row_line)
        claim_label = cols[1].strip("`")
        statement = cols[2]
        evidence_pointer = cols[3]

        if stat_locked or ("| `PILLAR-STAT` | `ACTIVE` |" in roadmap_text and matrix_status != "CLOSED"):
            assert claim_label.startswith("B-"), f"`{row_id}` must remain `B-*` during ACTIVE readiness posture."
        else:
            assert not claim_label.startswith("B-"), f"`{row_id}` must be non-`B-*` during CLOSED discharge posture."
        assert "TARGET-TH-ENTROPY-PLAN" in statement, f"`{row_id}` must remain bound to STAT target."
        assert "DERIVATION_TARGET_STAT_ENTROPY_PLAN_v0.md" in evidence_pointer, (
            f"`{row_id}` must point to the STAT readiness plan document."
        )

    assert _extract_token(stat_plan_text, "STAT_EVIDENCE_CHECKPOINT_CYCLE01_ARTIFACT_v0") == (
        "stat_evidence_checkpoint_cycle01_v0"
    )
    assert _extract_token(stat_plan_text, "STAT_EVIDENCE_CHECKPOINT_CYCLE01_GATE_v0") == (
        "ARTIFACT_HASH_AND_CROSS_SURFACE_POINTERS_REQUIRED"
    )

    assert "formal/output/stat_evidence_checkpoint_cycle01_v0.json" in stat_plan_text
    assert "formal/python/tests/test_stat_evidence_checkpoint_coupling_cycle01_gate.py" in stat_plan_text

    if stat_locked:
        assert _extract_token(stat_plan_text, "STAT_EVIDENCE_CHECKPOINT_CYCLE01_ARTIFACT_SHA256_v0") == "NOT_PRESENT_v0"
        assert _extract_token(stat_plan_text, "STAT_EVIDENCE_CHECKPOINT_CYCLE01_COUPLING_GATE_PLACEHOLDER_v0") == (
            "RESERVED_TEST_PATH_NOT_YET_BOUND"
        )

        for field_name in (
            "artifact_id",
            "cycle_id",
            "target_id",
            "scope_boundary",
            "assumption_freeze_refs",
            "required_results_rows_refs",
            "cross_surface_pointers",
            "artifact_sha256",
        ):
            assert f"`{field_name}`" in stat_plan_text, (
                f"STAT Cycle01 placeholder schema must list `{field_name}`."
            )

        assert "no non-placeholder SHA256 token may be emitted until the artifact is actually produced." in stat_plan_text
        assert "must include a pinned SHA256 token and cross-surface pointers in the same change set." in stat_plan_text

        assert not STAT_CYCLE01_ARTIFACT_PATH.exists(), (
            "STAT Cycle01 artifact must not be produced during locked readiness placeholder stage."
        )
        assert not STAT_CYCLE01_COUPLING_GATE_PATH.exists(), (
            "STAT Cycle01 coupling gate path is reserved only; do not bind it before activation lane work."
        )
    else:
        assert _extract_token(stat_plan_text, "STAT_EVIDENCE_CHECKPOINT_CYCLE01_ARTIFACT_SHA256_v0") != "NOT_PRESENT_v0"
        assert _extract_token(stat_plan_text, "STAT_EVIDENCE_CHECKPOINT_CYCLE01_ACCEPTANCE_GATE_v0") == (
            "PAYLOAD_SCHEMA_SCOPE_POINTERS_ROWS_REQUIRED"
        )
        assert _extract_token(stat_plan_text, "STAT_EVIDENCE_CHECKPOINT_CYCLE01_COUPLING_GATE_BINDING_v0") == (
            "BOUND_TO_TEST_PATH_v0"
        )
        assert "acceptance criteria gate path: `formal/python/tests/test_stat_evidence_checkpoint_cycle01_acceptance_gate.py`" in stat_plan_text
        assert STAT_CYCLE01_ARTIFACT_PATH.exists(), "STAT Cycle01 artifact must exist after activation."
        assert STAT_CYCLE01_COUPLING_GATE_PATH.exists(), "STAT Cycle01 coupling gate must exist after activation."
        assert STAT_CYCLE01_ACCEPTANCE_GATE_PATH.exists(), "STAT Cycle01 acceptance gate must exist after activation."

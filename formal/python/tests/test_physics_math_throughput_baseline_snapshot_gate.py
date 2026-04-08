from __future__ import annotations

import json
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PHYS_MATH_THROUGHPUT_REMEDIATION_PROGRAM_v0.md"
DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "PHYS_MATH_THROUGHPUT_IMPLEMENTATION_TRANCHE_00_BASELINE_20260407_v0.md"
)
TOOL_PATH = REPO_ROOT / "formal" / "python" / "tools" / "physics_math_throughput_baseline_snapshot.py"
ARTIFACT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "physics_math_throughput_baseline_20260407_v0.json"
MANIFEST_PATH = REPO_ROOT / "formal" / "docs" / "release" / "GOVERNANCE_TEST_MANIFEST_v1.json"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_phase0_baseline_files_exist() -> None:
    assert PROGRAM_PATH.exists(), "Missing throughput remediation program doc."
    assert DECLARATION_PATH.exists(), "Missing throughput tranche declaration."
    assert TOOL_PATH.exists(), "Missing throughput baseline tool."
    assert ARTIFACT_PATH.exists(), "Missing throughput baseline artifact."


def test_phase0_program_tokens_present() -> None:
    text = _read(PROGRAM_PATH)
    required = [
        "PHYS_MATH_THROUGHPUT_PROGRAM_STATUS_v0: ACTIVE_PHASE0_BASELINE",
        "PHYS_MATH_THROUGHPUT_PROGRAM_HORIZON_v0: 24_WEEKS",
        "PHYS_MATH_THROUGHPUT_PROGRAM_RISK_POSTURE_v0: AGGRESSIVE",
        "PHYS_MATH_THROUGHPUT_PROGRAM_RETROACTIVE_SCOPE_v0: SELECTIVE_DOWNGRADES_ENABLED",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE0_ARTIFACT_v0: formal/output/reports/physics_math_throughput_baseline_20260407_v0.json",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE0_TOOL_v0: formal/python/tools/physics_math_throughput_baseline_snapshot.py",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE0_GATE_v0: formal/python/tests/test_physics_math_throughput_baseline_snapshot_gate.py",
        "PHYS_MATH_THROUGHPUT_PROGRAM_PHASE0_DECLARATION_v0: formal/docs/release/PHYS_MATH_THROUGHPUT_IMPLEMENTATION_TRANCHE_00_BASELINE_20260407_v0.md",
    ]
    missing = [token for token in required if token not in text]
    assert not missing, "Missing throughput program token(s): " + ", ".join(missing)


def test_phase0_baseline_artifact_schema() -> None:
    payload = _read_json(ARTIFACT_PATH)
    manifest = _read_json(MANIFEST_PATH)

    assert payload.get("schema_id") == "PHYS_MATH_THROUGHPUT_BASELINE_v0"
    assert payload.get("status") == "BASELINE_CAPTURED_NONCLAIM"

    counts = payload.get("counts", {})
    assert counts.get("total_test_files", 0) > 0
    assert counts.get("metadata_pattern_file_count", 0) >= 0
    assert counts.get("science_pattern_file_count", 0) >= 0

    listed = len(manifest.get("groups", {}).get("governance_pytests", {}).get("tests", []))
    expected = manifest.get("groups", {}).get("governance_pytests", {}).get("expected_count")
    assert counts.get("governance_manifest_listed_count") == listed
    assert counts.get("governance_manifest_expected_count") == expected

    ratios = payload.get("ratios", {})
    file_ratio = ratios.get("metadata_to_science_file_ratio")
    line_ratio = ratios.get("metadata_to_science_line_ratio")
    assert file_ratio is None or file_ratio >= 0
    assert line_ratio is None or line_ratio >= 0

    baseline_context = payload.get("baseline_context", {})
    assert "Measurement-only artifact" in baseline_context.get("nonclaim_boundary", "")

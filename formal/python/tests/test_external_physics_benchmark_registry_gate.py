from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
REGISTRY_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "lanes"
    / "EXTERNAL_PHYSICS_BENCHMARK_REGISTRY_v0.md"
)
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "external_physics_benchmark_registry_v0.json"
)

REQUIRED_BENCHMARK_IDS = [
    "QM-STAT-ACTION-DENSITY-BENCHMARK",
    "QFT-VACUUM-STRUCTURE-BENCHMARK",
    "COSMO-HUBBLE-TENSION-BENCHMARK",
    "AI-FORMALIZATION-GOVERNANCE-BENCHMARK",
    "QM-STAT-MEASUREMENT-TIME-BENCHMARK",
    "EM-QM-STAT-TRANSPORT-BENCHMARK",
    "GR-QM-MASSIVE-MOTION-BENCHMARK",
    "COSMO-DEFORMATION-WATCHLIST",
    "GR-QM-FIELD-EMISSION-BENCHMARK",
    "TIME-ONTOLOGY-CAUTION-NOTE",
]

REQUIRED_GLOBAL_TOKENS = [
    "EXTERNAL_PHYSICS_BENCHMARK_REGISTRY_STATUS_v0: ACTIVE_NONCLAIM",
    "EXTERNAL_PHYSICS_BENCHMARK_CLAIM_STATUS_v0: EXTERNAL_MOTIVATION_NONCLAIM",
    "EXTERNAL_PHYSICS_BENCHMARK_FORMAL_IMPACT_v0: NO_THEOREM_DISCHARGE",
    (
        "EXTERNAL_PHYSICS_BENCHMARK_OUTCOME_v0: "
        "EXTERNAL_BENCHMARKS_REGISTERED_NONCLAIM_NO_THEOREM_DISCHARGE"
    ),
]

PROHIBITED_PHRASES = [
    "proves the ToE",
    "confirms the ToE",
    "Phase 2 authorized",
    "theorem discharged",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required external benchmark file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _section_for(text: str, benchmark_id: str) -> str:
    header = f"## `{benchmark_id}`"
    start = text.index(header)
    next_header = text.find("\n## `", start + len(header))
    if next_header == -1:
        return text[start:]
    return text[start:next_header]


def test_external_benchmark_registry_and_report_exist() -> None:
    assert REGISTRY_PATH.exists()
    assert REPORT_PATH.exists()


def test_external_benchmark_registry_global_nonclaim_tokens() -> None:
    text = _read(REGISTRY_PATH)
    for token in REQUIRED_GLOBAL_TOKENS:
        assert token in text, f"Missing global registry token: {token}"


def test_external_benchmark_registry_has_exact_required_inventory() -> None:
    text = _read(REGISTRY_PATH)
    for benchmark_id in REQUIRED_BENCHMARK_IDS:
        assert text.count(benchmark_id) == 1, (
            f"Benchmark id `{benchmark_id}` must appear exactly once in registry."
        )


def test_each_external_benchmark_section_is_nonclaim_and_no_discharge() -> None:
    text = _read(REGISTRY_PATH)
    for benchmark_id in REQUIRED_BENCHMARK_IDS:
        section = _section_for(text, benchmark_id)
        assert "EXTERNAL_MOTIVATION_NONCLAIM" in section
        assert "NO_THEOREM_DISCHARGE" in section
        assert "Required future proof object:" in section
        assert "Overclaim warning:" in section


def test_external_benchmark_registry_avoids_prohibited_claim_language() -> None:
    combined_text = _read(REGISTRY_PATH) + "\n" + _read(REPORT_PATH)
    for phrase in PROHIBITED_PHRASES:
        assert phrase not in combined_text, f"Prohibited phrase present: {phrase}"


def test_external_benchmark_report_schema_and_nonclaim_status() -> None:
    payload = _read_json(REPORT_PATH)

    assert payload["report_id"] == "external_physics_benchmark_registry_v0"
    assert payload["report_status"] == "SUCCESS"
    assert payload["claim_status"] == "EXTERNAL_MOTIVATION_NONCLAIM"
    assert payload["formal_impact"] == "NO_THEOREM_DISCHARGE"
    assert (
        payload["outcome_id"]
        == "EXTERNAL_BENCHMARKS_REGISTERED_NONCLAIM_NO_THEOREM_DISCHARGE"
    )
    assert payload["registered_benchmark_count"] == 10
    assert payload["theorem_gap_movement_claimed"] is False
    assert payload["phase2_authorized"] is False
    assert payload["lean_theorem_surface_modified"] is False
    assert payload["blocker_status_changed"] is False
    assert payload["objective_completion_claimed"] is False

    report_ids = [row["benchmark_id"] for row in payload["registered_benchmarks"]]
    assert report_ids == REQUIRED_BENCHMARK_IDS

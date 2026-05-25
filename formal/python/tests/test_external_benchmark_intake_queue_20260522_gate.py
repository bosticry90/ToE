from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
QUEUE_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "lanes"
    / "EXTERNAL_BENCHMARK_INTAKE_QUEUE_20260522_v0.md"
)
LEDGER_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "lanes"
    / "EXTERNAL_BENCHMARK_SOURCE_VERIFICATION_LEDGER_20260522_v0.md"
)
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "external_benchmark_intake_queue_20260522_v0.json"
)
REGISTRY_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "lanes"
    / "EXTERNAL_PHYSICS_BENCHMARK_REGISTRY_v0.md"
)
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
INVENTORY_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_MATH_PHYSICS_INVENTORY_v0.md"
)

POLICY_SENTENCE = (
    "External science inputs may create benchmark pressure, caution notes, or future "
    "target categories, but they do not discharge theorem gaps, validate the master "
    "action, close seams, or promote ToE status without repo-local proof objects and "
    "verified primary sources."
)

REQUIRED_INTAKE_IDS = [
    "EXTERNAL_BENCHMARK_SWOT_FULL_FIELD_RESIDUALS_v0",
    "EXTERNAL_BENCHMARK_GR_SINGULARITY_HIDDEN_STRUCTURE_v0",
    "EXTERNAL_BENCHMARK_GR_QM_EM_ATOMIC_EMISSION_v0",
    "EXTERNAL_BENCHMARK_ANYON_EXCHANGE_STATISTICS_v0",
    "EXTERNAL_BENCHMARK_SYMMETRY_CONTROLLED_TRANSFER_v0",
    "EXTERNAL_BENCHMARK_B_MESON_RARE_DECAY_ANOMALY_v0",
    "EXTERNAL_BENCHMARK_VACUUM_STRUCTURE_ENERGY_ACCOUNTING_v0",
    "EXTERNAL_BENCHMARK_INTERFACE_TRANSPORT_CATALYSIS_v0",
    "EXTERNAL_BENCHMARK_GW_SCALAR_DARK_MATTER_ENVIRONMENT_v0",
    "EXTERNAL_BENCHMARK_QUANTUM_SENSOR_RESIDUALS_v0",
    "METHODOLOGICAL_BENCHMARK_FOUNDATIONAL_LANGUAGE_REBUILD_v0",
    "WORKFLOW_STANDARD_PUBLIC_SUBMISSION_AI_HYGIENE_v0",
    "WORKFLOW_STANDARD_AGENT_ORCHESTRATION_SCOPE_CONTROL_v0",
    "WORKFLOW_STANDARD_EXTERNAL_EVIDENCE_INTAKE_ASSISTANT_v0",
    "INFRASTRUCTURE_PILOT_LOCAL_RETRIEVAL_TURBOQUANT_v0",
]

EXISTING_REGISTRY_IDS = [
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

REQUIRED_ROW_TOKENS = [
    "NONCLAIM",
    "NO_THEOREM_DISCHARGE",
    "NO_MASTER_ACTION_PROMOTION",
    "NO_SEAM_CLOSURE",
    "NO_EMPIRICAL_VALIDATION",
]

SOURCE_STATUS_LABELS = [
    "PRIMARY_VERIFIED",
    "PREPRINT_PINNED",
    "SECONDARY_CONTEXT_ONLY",
    "NEEDS_PRIMARY",
    "HIGH_RISK_NONCLAIM",
    "OFFICIAL_WORKFLOW_SOURCE",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _row_for(text: str, intake_id: str) -> str:
    for line in text.splitlines():
        if f"`{intake_id}`" in line:
            return line
    raise AssertionError(f"Missing intake row for {intake_id}")


def test_external_benchmark_intake_files_exist() -> None:
    assert QUEUE_PATH.exists()
    assert LEDGER_PATH.exists()
    assert REPORT_PATH.exists()


def test_existing_external_benchmark_registry_remains_exact_count() -> None:
    text = _read(REGISTRY_PATH)
    for benchmark_id in EXISTING_REGISTRY_IDS:
        assert text.count(benchmark_id) == 1
    assert text.count("\n## `") == 10


def test_intake_queue_global_policy_and_count() -> None:
    text = _read(QUEUE_PATH)
    assert "EXTERNAL_BENCHMARK_INTAKE_QUEUE_ENTRY_COUNT_v0: 15" in text
    assert POLICY_SENTENCE in text
    for intake_id in REQUIRED_INTAKE_IDS:
        assert text.count(intake_id) == 1, f"{intake_id} must appear exactly once"


def test_each_intake_row_has_required_nonclaim_tokens() -> None:
    text = _read(QUEUE_PATH)
    for intake_id in REQUIRED_INTAKE_IDS:
        row = _row_for(text, intake_id)
        for token in REQUIRED_ROW_TOKENS:
            assert token in row, f"{intake_id} missing {token}"


def test_source_ledger_has_each_intake_and_explicit_status_labels() -> None:
    text = _read(LEDGER_PATH)
    for intake_id in REQUIRED_INTAKE_IDS:
        assert intake_id in text, f"Ledger missing {intake_id}"
    for line in text.splitlines():
        if line.startswith("| `"):
            assert any(label in line for label in SOURCE_STATUS_LABELS), (
                f"Ledger row lacks explicit source status: {line}"
            )


def test_intake_report_schema_and_nonclaim_boundaries() -> None:
    payload = _read_json(REPORT_PATH)
    assert payload["report_id"] == "external_benchmark_intake_queue_20260522_v0"
    assert payload["report_status"] == "SUCCESS"
    assert payload["claim_status"] == "NONCLAIM"
    assert payload["formal_impact"] == "NO_THEOREM_DISCHARGE"
    assert payload["registered_intake_count"] == 15
    assert payload["registered_intakes"] == REQUIRED_INTAKE_IDS
    assert payload["policy_sentence"] == POLICY_SENTENCE
    assert payload["roadmap_state_inventory_pointer_only"] is True

    for flag_value in payload["nonclaim_boundaries"].values():
        assert flag_value is False


def test_authority_surfaces_have_lightweight_pointers_only_and_live_target_unchanged() -> None:
    required_refs = [
        "EXTERNAL_BENCHMARK_INTAKE_QUEUE_20260522_v0",
        "PUBLIC_SUBMISSION_AI_HYGIENE_STANDARD_v0",
        "NONCLAIM_BENCHMARK_INTAKE_AND_PUBLIC_SUBMISSION_HYGIENE_TRANCHE_PREPARED_WITH_NO_THEOREM_DISCHARGE_OR_PROMOTION",
    ]
    expected_live = (
        "CURRENT_LIVE_NEXT_TARGET_v0: "
        "review_v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout_packet_result"
    )

    for path in [STATE_PATH, ROADMAP_PATH, INVENTORY_PATH]:
        text = _read(path)
        for ref in required_refs:
            assert ref in text, f"{path} missing lightweight pointer {ref}"
        assert expected_live in text, f"{path} changed or omits current live target"

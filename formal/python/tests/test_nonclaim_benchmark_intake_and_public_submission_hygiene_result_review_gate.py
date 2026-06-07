from __future__ import annotations

import json
import subprocess
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))

REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "NONCLAIM_BENCHMARK_INTAKE_AND_PUBLIC_SUBMISSION_HYGIENE_TRANCHE_RESULT_REVIEW_20260522_v0.json"
)
HYGIENE_STANDARD_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PUBLIC_SUBMISSION_AI_HYGIENE_STANDARD_v0.md"
)
HYGIENE_REPORT_PATH = (
    REPO_ROOT / "formal" / "output" / "reports" / "public_submission_ai_hygiene_v0.json"
)
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
INTAKE_REPORT_PATH = (
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

RESULT_REVIEW_TOKEN = (
    "NONCLAIM_BENCHMARK_INTAKE_AND_PUBLIC_SUBMISSION_HYGIENE_TRANCHE_RESULT_REVIEW_ACCEPTS_NONCLAIM_INTAKE_AND_HYGIENE_WITH_NO_LIVE_TARGET_CHANGE"
)
PREPARED_TOKEN = (
    "NONCLAIM_BENCHMARK_INTAKE_AND_PUBLIC_SUBMISSION_HYGIENE_TRANCHE_PREPARED_WITH_NO_THEOREM_DISCHARGE_OR_PROMOTION"
)
EXPECTED_LIVE_TARGET = (
    "CURRENT_LIVE_NEXT_TARGET_v0: "
    "prepare_qft_gr_renormalization_operator_domain_compatibility_assumption_reduction_packet"
)
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


def _git_ls_files(path: Path) -> str:
    rel = path.relative_to(REPO_ROOT).as_posix()
    completed = subprocess.run(
        ["git", "ls-files", "--", rel],
        cwd=REPO_ROOT,
        text=True,
        capture_output=True,
        check=True,
    )
    return completed.stdout.strip()


def test_result_review_artifact_schema_and_token() -> None:
    payload = _read_json(REVIEW_PATH)
    assert (
        payload["schema_id"]
        == "NONCLAIM_BENCHMARK_INTAKE_AND_PUBLIC_SUBMISSION_HYGIENE_TRANCHE_RESULT_REVIEW_20260522_v0"
    )
    assert payload["review_target"] == (
        "review_nonclaim_benchmark_intake_and_public_submission_hygiene_tranche_result"
    )
    assert payload["consumed_outcome_token"] == PREPARED_TOKEN
    assert payload["result_review_token"] == RESULT_REVIEW_TOKEN
    assert payload["classification"] == "P-POLICY/nonclaim"


def test_result_review_consumed_surfaces_exist() -> None:
    payload = _read_json(REVIEW_PATH)
    for rel_path in payload["consumed_surfaces"].values():
        assert (REPO_ROOT / rel_path).exists(), f"Consumed surface missing: {rel_path}"
    assert HYGIENE_STANDARD_PATH.exists()
    assert HYGIENE_REPORT_PATH.exists()
    assert QUEUE_PATH.exists()
    assert LEDGER_PATH.exists()
    assert INTAKE_REPORT_PATH.exists()


def test_new_output_reports_are_intentionally_tracked() -> None:
    assert _git_ls_files(HYGIENE_REPORT_PATH).endswith(
        "formal/output/reports/public_submission_ai_hygiene_v0.json"
    )
    assert _git_ls_files(INTAKE_REPORT_PATH).endswith(
        "formal/output/reports/external_benchmark_intake_queue_20260522_v0.json"
    )


def test_registry_and_intake_counts_are_preserved() -> None:
    registry_text = _read(REGISTRY_PATH)
    queue_text = _read(QUEUE_PATH)
    assert registry_text.count("\n## `") == 10
    assert "EXTERNAL_BENCHMARK_INTAKE_QUEUE_ENTRY_COUNT_v0: 15" in queue_text
    assert _read_json(INTAKE_REPORT_PATH)["registered_intake_count"] == 15


def test_intake_rows_and_source_ledger_keep_required_boundaries() -> None:
    queue_text = _read(QUEUE_PATH)
    for line in queue_text.splitlines():
        if line.startswith("| `") and "_v0`" in line:
            for token in REQUIRED_ROW_TOKENS:
                assert token in line, f"Intake row missing {token}: {line}"

    ledger_text = _read(LEDGER_PATH)
    for line in ledger_text.splitlines():
        if line.startswith("| `") and "_v0`" in line:
            assert any(label in line for label in SOURCE_STATUS_LABELS), (
                f"Source ledger row lacks explicit status: {line}"
            )


def test_no_promotion_or_live_target_change_is_recorded() -> None:
    payload = _read_json(REVIEW_PATH)
    for flag_value in payload["nonclaim_boundaries"].values():
        assert flag_value is False
    assert (
        payload["current_live_next_target_expected"]
        == "review_v01_alpha_dependency_remediation_tranche_006_release_policy_adjudication_packet_result"
    )

    for path in [STATE_PATH, ROADMAP_PATH, INVENTORY_PATH]:
        text = _read(path)
        assert EXPECTED_LIVE_TARGET in text
        assert PREPARED_TOKEN in text


def test_state_roadmap_inventory_have_only_lightweight_tranche_pointers() -> None:
    for path in [STATE_PATH, ROADMAP_PATH, INVENTORY_PATH]:
        text = _read(path)
        assert "PUBLIC_SUBMISSION_AI_HYGIENE_STANDARD_v0" in text
        assert "EXTERNAL_BENCHMARK_INTAKE_QUEUE_20260522_v0" in text
        assert PREPARED_TOKEN in text
        assert "NONCLAIM_BENCHMARK_INTAKE_AND_PUBLIC_SUBMISSION_HYGIENE_TRANCHE_RESULT_REVIEW_ACCEPTS_NONCLAIM_INTAKE_AND_HYGIENE_WITH_NO_LIVE_TARGET_CHANGE" not in text

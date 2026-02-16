from __future__ import annotations

from pathlib import Path


OUTDATED_STATUS_VALUES = (
    "governance suite green on 2026-02-10 (316 passed)",
    "governance suite green on 2026-02-11 (337 passed)",
)
EXPECTED_CURRENT_STATUS = "governance suite green on 2026-02-12 (383 passed)"


def _state_doc_path() -> Path:
    return Path(__file__).resolve().parents[3] / "State_of_the_Theory.md"


def test_state_doc_does_not_advertise_outdated_suite_status() -> None:
    text = _state_doc_path().read_text(encoding="utf-8")
    for outdated in OUTDATED_STATUS_VALUES:
        assert outdated not in text, (
            "State_of_the_Theory.md still advertises an outdated suite-status value."
        )


def test_state_doc_contains_current_suite_status_for_governance_notes() -> None:
    text = _state_doc_path().read_text(encoding="utf-8")
    assert EXPECTED_CURRENT_STATUS in text, (
        "State_of_the_Theory.md is missing the current governance suite-status value."
    )



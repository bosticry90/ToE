from __future__ import annotations

import importlib.util
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[3]
TOOL = ROOT / "formal" / "python" / "tools" / "governance_json.py"
SPEC = importlib.util.spec_from_file_location("governance_json", TOOL)
assert SPEC and SPEC.loader
subject = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(subject)

AUTHORITY = ROOT / "formal" / "docs" / "release" / "CURRENT_MAINTENANCE_AUTHORITY_v0.json"


def test_strict_current_authority_parser_accepts_repaired_single_selector() -> None:
    payload = subject.strict_current_authority_parse(AUTHORITY)
    assert payload["selector"] == {
        "path": (
            "formal/docs/release/"
            "POST_PILLAR_HISTORICAL_ARTIFACT_CURRENCY_ROLE_SEPARATION_"
            "REPAIR_BASELINE_REASSESSMENT_SELECTION_20260724_v0.json"
        ),
        "sha256": "18a36a738d11331f97c5354ffea22acfc879809880d29a65d2e017fe1032a63d",
    }


def test_forensic_reader_preserves_bytes_and_reports_both_selectors() -> None:
    raw = b'{"selector":{"path":"old"},"selector":{"path":"new"}}'
    report = subject.forensic_historical_parse_bytes(raw)
    assert report.raw_bytes == raw
    assert len(report.raw_sha256) == 64
    selector = [
        item
        for item in report.duplicates
        if item["json_path"] == "$" and item["key"] == "selector"
    ]
    assert len(selector) == 1
    assert selector[0]["occurrences"] == 2
    assert not hasattr(report, "authoritative_value")


def test_strict_parser_rejects_nested_duplicates() -> None:
    with pytest.raises(subject.DuplicateKeyError, match="x"):
        subject.strict_current_authority_loads(b'{"outer":{"x":1,"x":2}}')


def test_strict_parser_accepts_unambiguous_json() -> None:
    assert subject.strict_current_authority_loads(b'{"outer":{"x":1}}') == {
        "outer": {"x": 1}
    }

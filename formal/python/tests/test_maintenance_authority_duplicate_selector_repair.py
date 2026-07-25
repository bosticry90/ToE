from __future__ import annotations

import copy
import hashlib
import importlib.util
import json
import subprocess
import sys
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[3]
TOOLS = ROOT / "formal" / "python" / "tools"
sys.path.insert(0, str(TOOLS))
TOOL = TOOLS / "maintenance_authority_duplicate_selector_repair.py"
SPEC = importlib.util.spec_from_file_location(
    "maintenance_authority_duplicate_selector_repair", TOOL
)
assert SPEC and SPEC.loader
subject = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(subject)

AUTHORITY = ROOT / "formal" / "docs" / "release" / "CURRENT_MAINTENANCE_AUTHORITY_v0.json"


def _before_bytes() -> bytes:
    bootstrap = subject.load_bootstrap()
    completed = subprocess.run(
        [
            "git",
            "-C",
            str(ROOT),
            "show",
            (
                bootstrap["parent_recovery_state"]["commit"]
                + ":"
                + bootstrap["target"]["path"]
            ),
        ],
        check=True,
        capture_output=True,
    )
    return completed.stdout


def test_bootstrap_preview_is_exactly_one_deletion() -> None:
    bootstrap = subject.load_bootstrap()
    raw = _before_bytes()
    repaired, evidence = subject.validate_repair_bytes(
        raw,
        bootstrap,
        tool_bytes=TOOL.read_bytes(),
    )
    deletion = bootstrap["target"]["permitted_deletion"]
    start = deletion["start_byte"]
    end = deletion["end_byte_exclusive"]
    assert repaired == raw[:start] + raw[end:]
    assert evidence["removed_bytes"] == end - start == 218
    assert evidence["after_sha256"] == bootstrap["target"]["expected_after_sha256"]


def test_bootstrap_rejects_wrong_source_bytes() -> None:
    bootstrap = subject.load_bootstrap()
    with pytest.raises(subject.BootstrapRepairError, match="before-hash"):
        subject.validate_repair_bytes(
            _before_bytes() + b"\n",
            bootstrap,
            tool_bytes=TOOL.read_bytes(),
        )


def test_bootstrap_rejects_tool_tampering() -> None:
    bootstrap = subject.load_bootstrap()
    with pytest.raises(subject.BootstrapRepairError, match="tool hash"):
        subject.validate_repair_bytes(
            _before_bytes(),
            bootstrap,
            tool_bytes=TOOL.read_bytes() + b"\n",
        )


def test_bootstrap_rejects_expanded_deletion_range() -> None:
    bootstrap = copy.deepcopy(subject.load_bootstrap())
    bootstrap["target"]["permitted_deletion"]["end_byte_exclusive"] += 1
    with pytest.raises(subject.BootstrapRepairError, match="deletion bytes"):
        subject.validate_repair_bytes(
            _before_bytes(),
            bootstrap,
            tool_bytes=TOOL.read_bytes(),
        )


def test_repaired_document_has_only_authorized_selector() -> None:
    bootstrap = subject.load_bootstrap()
    repaired, _ = subject.validate_repair_bytes(
        _before_bytes(),
        bootstrap,
        tool_bytes=TOOL.read_bytes(),
    )
    assert repaired == AUTHORITY.read_bytes()
    parsed = subject.strict_current_authority_loads(repaired)
    assert parsed["selector"] == bootstrap["authorized_second_selector_value"]
    assert hashlib.sha256(repaired).hexdigest() == (
        "1d6604e25da32a886d1431c6eb3a92c16e4082d8b9ac5cda8bc16a469e99d224"
    )


def test_consumed_bootstrap_cannot_execute_again() -> None:
    with pytest.raises(subject.BootstrapRepairError, match="already been consumed"):
        subject.execute_once()

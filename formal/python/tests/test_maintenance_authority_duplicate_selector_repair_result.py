from __future__ import annotations

import hashlib
import importlib.util
import json
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
RELEASE = ROOT / "formal" / "docs" / "release"
RESULT = RELEASE / (
    "REPOSITORY_MAINTENANCE_AUTHORITY_DUPLICATE_SELECTOR_KEY_"
    "REPAIR_RESULT_20260725_v0.json"
)
AUTHORITY = RELEASE / "CURRENT_MAINTENANCE_AUTHORITY_v0.json"
BOOTSTRAP = RELEASE / (
    "MAINTENANCE_AUTHORITY_DUPLICATE_SELECTOR_KEY_REPAIR_BOOTSTRAP_20260725_v0.json"
)
CONSUMPTION = RELEASE / (
    "MAINTENANCE_AUTHORITY_DUPLICATE_SELECTOR_KEY_REPAIR_"
    "BOOTSTRAP_CONSUMPTION_20260725_v0.json"
)

GOVERNANCE_JSON = ROOT / "formal" / "python" / "tools" / "governance_json.py"
SPEC = importlib.util.spec_from_file_location("governance_json_result_guard", GOVERNANCE_JSON)
assert SPEC and SPEC.loader
strict_json = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(strict_json)


def _sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _parent_authority_bytes() -> bytes:
    bootstrap = strict_json.strict_current_authority_parse(BOOTSTRAP)
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


def test_result_binds_bootstrap_consumption_and_exact_authority_hashes() -> None:
    result = strict_json.strict_current_authority_parse(RESULT)
    assert _sha(BOOTSTRAP) == result["authorization"]["bootstrap"]["sha256"]
    assert _sha(CONSUMPTION) == result["authorization"]["consumption"]["sha256"]
    assert _sha(AUTHORITY) == result["authority_document"]["after"]["sha256"]
    assert result["authorization"]["consumption"]["execution_counter_consumed"] == 1
    assert (
        result["authorization"]["consumption"][
            "exceptional_bootstrap_authority_after"
        ]
        == "PERMANENTLY_EXPIRED"
    )


def test_authority_change_is_exactly_the_permitted_deletion() -> None:
    result = strict_json.strict_current_authority_parse(RESULT)
    before = _parent_authority_bytes()
    after = AUTHORITY.read_bytes()
    deletion = result["authority_document"]["minimal_byte_diff"]
    start = deletion["start_byte"]
    end = deletion["end_byte_exclusive"]
    assert after == before[:start] + before[end:]
    assert hashlib.sha256(before[start:end]).hexdigest() == deletion["removed_sha256"]
    assert deletion["all_other_bytes_unchanged"] is True


def test_current_authority_has_one_strict_interpretation() -> None:
    result = strict_json.strict_current_authority_parse(RESULT)
    strict = strict_json.strict_current_authority_parse(AUTHORITY)
    ordinary = json.loads(AUTHORITY.read_text(encoding="utf-8"))
    assert strict == ordinary
    assert strict["selector"] == result["authority_document"][
        "authorized_surviving_selector"
    ]
    assert result["parsing_contract"]["current_authority_interpretation"] == (
        "STRICT_CURRENT_AUTHORITY_PARSE_ONLY"
    )


def test_repair_preserves_scientific_and_successor_boundaries() -> None:
    result = strict_json.strict_current_authority_parse(RESULT)
    assert result["scope"]["scientific_content_changed"] is False
    assert result["scope"]["registry_rotated"] is False
    assert result["scope"]["v2_enrolled"] is False
    assert result["scope"]["pillar_v1_repair_performed"] is False
    assert result["scope"]["automatic_successor"] is False
    assert result["scientific_posture"] == "B-BLOCKED"

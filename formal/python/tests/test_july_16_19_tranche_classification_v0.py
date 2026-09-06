from __future__ import annotations

import importlib.util
import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
TOOL_PATH = (
    REPO_ROOT
    / "formal/python/tools/july_16_19_tranche_classification_v0.py"
)
OUTPUT_PATH = (
    REPO_ROOT
    / "formal/docs/release/"
    "JULY_16_19_DIRTY_CHECKOUT_TRANCHE_CLASSIFICATION_20260727_v0.json"
)


def _load_tool():
    spec = importlib.util.spec_from_file_location(
        "july_16_19_tranche_classification_v0", TOOL_PATH
    )
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_committed_classification_record_is_complete_and_bounded() -> None:
    tool = _load_tool()
    record = json.loads(OUTPUT_PATH.read_text(encoding="utf-8"))
    tool.validate_record(record)
    assert record["counts"]["inventory_rows"] == 629
    assert len(record["snapshot_inventory"]) == 629
    assert len(record["external_custody_only_rows"]) == 24


def test_external_bytes_are_not_misclassified_as_repository_artifacts() -> None:
    record = json.loads(OUTPUT_PATH.read_text(encoding="utf-8"))
    for row in record["external_custody_only_rows"]:
        assert row["licensing_and_redistribution"] == "UNRESOLVED_PER_FILE"
        assert row["repository_disposition"].startswith("INTENTIONALLY_IGNORED_")
        assert row["scientific_status"] == (
            "PRESERVED_EXTERNAL_CUSTODY_NOT_ADOPTED"
        )


def test_commitment_semantics_do_not_manufacture_scientific_authority() -> None:
    record = json.loads(OUTPUT_PATH.read_text(encoding="utf-8"))
    policy = record["classification_policy"]
    assert policy["commitment_semantics"] == (
        "BYTE_PRESERVATION_DOES_NOT_CONSTITUTE_SCIENTIFIC_ADOPTION"
    )
    assert policy["scientific_authority_rotation"] == "PROHIBITED"
    assert policy["new_physics"] == "PROHIBITED"
    assert policy["yukawa_rerun"] == "PROHIBITED"

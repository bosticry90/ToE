from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import (
    eotwash_2020_yukawa_primary_evidence_custody_acquisition_result_review_v0
    as review,
)
from formal.python.tools import (
    eotwash_2020_yukawa_primary_evidence_custody_acquisition_v0 as execution,
)
from formal.python.tools import (
    post_eotwash_2020_yukawa_primary_evidence_custody_acquisition_scientific_response_selection_v0
    as selection,
)


REPO_ROOT = find_repo_root(Path(__file__))
CLASSIFICATION_PATH = (
    REPO_ROOT
    / "formal/docs/release/"
    "JULY_16_19_DIRTY_CHECKOUT_TRANCHE_CLASSIFICATION_20260727_v0.json"
)


def _json(relative_path: str) -> dict[str, object]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def _sha256(relative_path: str) -> str:
    return hashlib.sha256((REPO_ROOT / relative_path).read_bytes()).hexdigest()


def test_committed_execution_and_review_match_frozen_downstream_hashes() -> None:
    assert _sha256(execution.REPORT_RELATIVE_PATH) == (
        review.EXECUTION_HASHES[execution.REPORT_RELATIVE_PATH]
    )
    assert _sha256(review.REPORT_RELATIVE_PATH) == (
        selection.AUTHORITY_HASHES[review.REPORT_RELATIVE_PATH]
    )


def test_external_custody_hash_ledger_matches_both_committed_records() -> None:
    execution_report = _json(execution.REPORT_RELATIVE_PATH)
    review_report = _json(review.REPORT_RELATIVE_PATH)
    classification = json.loads(CLASSIFICATION_PATH.read_text(encoding="utf-8"))
    classified = {
        row["path"]: row["sha256"]
        for row in classification["external_custody_only_rows"]
    }
    execution_hashes = execution.ACQUIRED_OBJECT_HASHES
    reviewed_hashes = {
        row["relative_path"]: row["sha256"]
        for row in review_report["authority"]["verified_raw_custody_objects"]
    }

    assert len(execution_hashes) == len(reviewed_hashes) == 13
    assert reviewed_hashes == execution_hashes
    assert all(classified[path] == digest for path, digest in execution_hashes.items())
    assert (
        execution_report["required_evidence_inventory"]["complete_item_count"]
        == 0
    )


def test_archive_integrity_preserves_custody_only_nonclaim_boundary() -> None:
    execution_report = _json(execution.REPORT_RELATIVE_PATH)
    review_report = _json(review.REPORT_RELATIVE_PATH)

    assert execution_report["principal_outcome"] == (
        "AUTHORS_OR_CUSTODIAN_CONTACT_REQUIRED"
    )
    assert review_report["verdict"] == review.VERDICT
    assert review_report["accepted_bounded_claim"]["evidence_components"] == (
        "0_OF_6_COMPLETE_6_OF_6_PARTIAL"
    )
    assert review_report["accepted_bounded_claim"][
        "scalar_allowance_or_exclusion_claim"
    ] is False

from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import pillar_v1_staging_identity_adjudication


REPO_ROOT = find_repo_root(Path(__file__))
RESULT_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "REPOSITORY_POST_PILLAR_V1_STAGING_IDENTITY_ADJUDICATION_"
    "RESULT_20260725_v0.json"
)
REVIEW_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "REPOSITORY_POST_PILLAR_V1_STAGING_IDENTITY_ADJUDICATION_"
    "RESULT_REVIEW_20260725_v0.json"
)


def _load(path: str) -> dict:
    return json.loads((REPO_ROOT / path).read_bytes())


def test_frozen_and_current_inventories_remain_distinct() -> None:
    result = json.loads(RESULT_PATH.read_bytes())
    frozen = _load(result["inventories"]["FROZEN_COMPARABILITY_INVENTORY"]["manifest"])
    current = _load(result["inventories"]["CURRENT_ACCEPTANCE_INVENTORY"]["manifest"])
    assert frozen["count"] == 13756
    assert frozen["purpose"] == "OUTCOME_COMPARABILITY_ONLY"
    assert frozen["acceptance_boundary"]["defines_current_acceptance_suite"] is False
    assert current["count"] == 13818
    assert current["collection"]["added_over_frozen_comparability"] == 62
    assert current["collection"]["removed_from_frozen_comparability"] == 0
    assert current["acceptance_boundary"]["dynamic_demotion_permitted"] is False


def test_result_maps_all_dependencies_and_preserves_the_accepted_mismatch() -> None:
    result = json.loads(RESULT_PATH.read_bytes())
    assert result["adjudication"]["staged_dependencies_individually_mapped"] == 23
    assert result["adjudication"]["provenance_blocked_dependencies"] == 0
    assert result["in_memory_causal_probe"]["persisted_substitutions"] == 0
    assert result["in_memory_causal_probe"]["historical_decisions"] == (
        "25 / 26 REPRODUCED"
    )
    assert result["in_memory_causal_probe"]["sole_failed_decision"] == (
        "supporting_sources_have_authorized_bounded_class"
    )
    assert result["in_memory_causal_probe"]["new_masked_roots_after_role_substitution"] == 0


def test_adjudication_is_repair_justified_but_authorizes_no_repair() -> None:
    result = json.loads(RESULT_PATH.read_bytes())
    assert result["terminal_outcome"] == (
        "PILLAR_V1_STAGING_IDENTITY_ROLE_SEPARATION_REPAIR_JUSTIFIED"
    )
    assert result["scope"]["staging_consumer_modified"] is False
    assert result["scope"]["persisted_hash_substitutions"] == 0
    assert result["authorization"]["successor_authority"] == "NONE"
    assert result["scientific_posture"] == "B-BLOCKED"
    assert result["v2_enrollment"] == "NOT_AUTHORIZED"


def test_machine_ledger_reproduces_the_same_exhaustive_counts() -> None:
    adjudication = pillar_v1_staging_identity_adjudication.build_adjudication()
    result = json.loads(RESULT_PATH.read_bytes())
    assert adjudication["dependency_count"] == result["adjudication"]["staged_dependencies"]
    assert adjudication["role_counts"] == result["adjudication"]["role_counts"]
    assert adjudication["representation_counts"] == result["adjudication"][
        "representation_counts"
    ]


def test_independent_review_accepts_adjudication_without_successor_authority() -> None:
    review = json.loads(REVIEW_PATH.read_bytes())
    assert review["accepted"] is True
    assert review["findings"]["all_dependencies_mapped"] is True
    assert review["findings"]["repair_justified"] is True
    assert review["scope"]["repair_performed"] is False
    assert review["successor_authority"] == "NONE"
    assert review["scientific_posture"] == "B-BLOCKED"

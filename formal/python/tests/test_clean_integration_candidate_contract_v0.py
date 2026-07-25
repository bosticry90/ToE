from __future__ import annotations

import json
from pathlib import Path

from formal.python.tools.governance_json import strict_current_authority_parse


ROOT = Path(__file__).resolve().parents[3]
RELEASE = ROOT / "formal/docs/release"
PROFILES = ROOT / "formal/output/validation_profiles"


def test_clean_candidate_imports_no_unapproved_dirty_main_path() -> None:
    selection = strict_current_authority_parse(
        RELEASE / "CLEAN_INTEGRATION_CANDIDATE_SELECTION_20260725_v0.json"
    )
    custody = strict_current_authority_parse(
        RELEASE
        / "DIRTY_MAIN_TERMINAL_CUSTODY_DISPOSITION_RESULT_REVIEW_20260725_v0.json"
    )
    assert selection["custody_import"]["approved_for_clean_integration"] == 0
    assert selection["custody_import"]["paths_to_import"] == 0
    assert selection["custody_import"]["dirty_main_wholesale_merge"] is False
    assert custody["findings"]["approved_for_clean_integration"] == 0
    assert custody["findings"]["manual_review_required_remaining"] == 0


def test_authority_fields_have_exactly_one_owner() -> None:
    contract = strict_current_authority_parse(
        RELEASE / "CURRENT_AUTHORITY_FIELD_OWNERSHIP_CONTRACT_20260725_v0.json"
    )
    fields = [row["field"] for row in contract["owners"]]
    assert len(fields) == len(set(fields)) == 8
    assert all(row["sole_owner"] for row in contract["owners"])
    assert contract["mirror_contract"]["independent_writers_per_field"] == 1
    assert contract["mirror_contract"]["mirror_disagreement"] == "BLOCKING"


def test_current_authority_uses_only_the_strict_interpreter() -> None:
    contract = strict_current_authority_parse(
        RELEASE / "CURRENT_AUTHORITY_FIELD_OWNERSHIP_CONTRACT_20260725_v0.json"
    )
    authority = strict_current_authority_parse(
        RELEASE / "CURRENT_MAINTENANCE_AUTHORITY_v0.json"
    )
    assert contract["strict_current_authority_interpretation"] == (
        "STRICT_CURRENT_AUTHORITY_PARSE_ONLY"
    )
    assert contract["mirror_contract"]["ordinary_json_parse_authoritative"] is False
    assert (
        contract["mirror_contract"]["forensic_historical_parse_authoritative"]
        is False
    )
    assert authority["selector"]


def test_scientific_state_remains_blocked_and_unenrolled() -> None:
    contract = strict_current_authority_parse(
        RELEASE / "CURRENT_AUTHORITY_FIELD_OWNERSHIP_CONTRACT_20260725_v0.json"
    )
    state = contract["current_state_boundary"]
    assert state == {
        "scientific_posture": "B-BLOCKED",
        "resolved_unit_or_seam_rows": "0 / 12",
        "qft_gr_seam": "OPEN",
        "v2_enrollment": "NOT_AUTHORIZED",
        "scientific_execution_permission": "NONE",
    }


def test_integration_profiles_exactly_partition_current_inventory() -> None:
    current = json.loads(
        (PROFILES / "CURRENT_CONTROL_PLANE_PROFILE_20260725_v5.json").read_bytes()
    )
    historical = json.loads(
        (PROFILES / "HISTORICAL_DEBT_PROFILE_20260725_v5.json").read_bytes()
    )
    reconciliation = json.loads(
        (
            PROFILES / "VALIDATION_PROFILE_RECONCILIATION_20260725_v5.json"
        ).read_bytes()
    )
    assert set(current["nodeids"]).isdisjoint(historical["nodeids"])
    assert current["nodeid_count"] + historical["nodeid_count"] == 13856
    assert reconciliation["exact_partition"] is True
    assert reconciliation["unknown_current_reachability_obligations"] == 0

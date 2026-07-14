from __future__ import annotations

import json

from formal.python.tools import (
    pillar_seam_unit_mapping_ledger_blocker_response_route_selection_v2 as v2,
)


def test_v2_artifacts_are_current() -> None:
    packet, manifest, report = v2.build_artifacts()
    assert v2.PACKET_PATH.read_bytes() == v2.canonical_json_bytes(packet)
    assert v2.MANIFEST_PATH.read_bytes() == v2.canonical_json_bytes(manifest)
    assert v2.REPORT_PATH.read_bytes() == v2.canonical_json_bytes(report)


def test_v2_repairs_authority_at_proposition_granularity() -> None:
    packet, _, _ = v2.build_artifacts()
    records = v2._record_map(packet)
    assert records
    assert all(set(record) == v2.RECORD_REQUIRED_FIELDS for record in records.values())
    for record in records.values():
        if record["source_id"] in v2.POLICY_SOURCE_IDS:
            assert record["source_declared_claim_label"] == "P-POLICY"
            assert record["authority_class"] == "BOUNDED_PLANNING_NONCLAIM"
        if record["source_id"] == "gr_bounded_surface":
            assert record["claim_label_context"] == "LEGACY_UNMIGRATED_NONRELEASE"
            assert record["authority_class"] == "BOUNDED_ACCEPTED_MATHEMATICAL_SURFACE"
        if record["source_id"] == "accepted_scalar_sandbox_review":
            assert record["evidence_role"] == "REPOSITORY_STATE_EVIDENCE"
            assert record["route_support_eligible"] is False
    assert all(
        record["authority_class"] != "BOUNDED_AUTHORITATIVE_SURFACE"
        for record in records.values()
    )


def test_v2_compatibility_matrix_is_closed_exhaustive_and_fail_closed() -> None:
    packet, _, _ = v2.build_artifacts()
    matrix = packet["compatibility_matrix"]
    assert matrix["row_count"] == (
        len(v2.SUPPORT_MODES) * len(v2.EVIDENCE_ROLES) * len(v2.ROUTE_TYPES)
    )
    assert matrix["default_for_unknown_combination"] == "INELIGIBLE"
    assert all(
        row["result"] == v2._compatibility_result(
            row["support_mode"], row["evidence_role"], row["route_type"]
        )
        for row in matrix["rows"]
    )


def test_v2_routes_are_recomputed_and_prerequisites_are_separate() -> None:
    packet, _, _ = v2.build_artifacts()
    ledger = json.loads((v2.REPO_ROOT / v2.v0.LEDGER_RELATIVE_PATH).read_text(encoding="utf-8"))
    assert v2.packet_validation_failures(packet, ledger) == []
    assert len(packet["route_selections"]) == 12
    assert all(isinstance(row["primary_route"], str) for row in packet["route_selections"])
    assert all(
        row["ordered_prerequisite_routes"] == []
        for row in packet["route_selections"]
        if row["row_kind"] == "pillar"
    )
    assert all(
        len(row["ordered_prerequisite_routes"]) == 2
        for row in packet["route_selections"]
        if row["row_kind"] == "seam"
    )
    assert packet["historical_route_counts_used_as_oracle"] is False
    assert packet["expected_route_stored_in_source_specification"] is False


def test_v2_runs_34_fresh_fixture_controls() -> None:
    ledger, _ = v2._load_inputs()
    controls = v2.run_negative_controls(ledger)
    assert len(controls) == 34
    assert len({item["control_id"] for item in controls}) == 34
    assert len({item["expected_diagnostic"] for item in controls}) == 34
    assert all(item["fresh_unmutated_fixture_rebuilt"] for item in controls)
    assert all(item["baseline_passed_immediately_before_mutation"] for item in controls)
    assert all(item["expected_diagnostic_observed"] for item in controls)
    assert all(item["no_unrelated_earlier_failure"] for item in controls)
    assert all(item["passed"] for item in controls)


def test_v2_emits_no_resolution_and_preserves_prompt() -> None:
    packet, _, report = v2.build_artifacts()
    assert all(row["proposed_unit_assignment"] is None for row in packet["route_selections"])
    assert all(row["restoration_rule"] is None for row in packet["route_selections"])
    assert packet["boundary"]["Maxwell_Dirac_selected"] is False
    assert report["packet_acceptance_authorized"] is False
    assert report["first_unit_selector_authorized"] is False
    assert v2.sha256_path(v2.REPO_ROOT / v2.PROMPT_RELATIVE_PATH) == v2.PROMPT_BASELINE_SHA256

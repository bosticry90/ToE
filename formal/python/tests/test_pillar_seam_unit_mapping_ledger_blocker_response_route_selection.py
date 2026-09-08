from __future__ import annotations

import copy
import json
import subprocess
import sys
from collections import Counter
from pathlib import Path

import pytest

from formal.python.tools import (
    pillar_seam_unit_mapping_ledger_blocker_response_route_selection as subject,
)


EXPECTED_ROUTES = {
    "PILLAR-QFT-units_and_dimensions-v0": "OBJECT_SEMANTICS_REFINEMENT",
    "PILLAR-GR-units_and_dimensions-v0": "EQUATION_BALANCE_DERIVATION",
    "PILLAR-QM-units_and_dimensions-v0": "OBJECT_SEMANTICS_REFINEMENT",
    "PILLAR-STAT-units_and_dimensions-v0": "OBJECT_SEMANTICS_REFINEMENT",
    "PILLAR-EM-units_and_dimensions-v0": "CONVENTION_AND_CONSTANT_RESTORATION",
    "PILLAR-SR-units_and_dimensions-v0": "CONVENTION_AND_CONSTANT_RESTORATION",
    "PILLAR-COSMO-units_and_dimensions-v0": "OBJECT_SEMANTICS_REFINEMENT",
    "SEAM-QFT-GR-unit_map-v0": "RESEARCH_BLOCKED",
    "SEAM-QM-STAT-unit_map-v0": "RESEARCH_BLOCKED",
    "SEAM-EM-QFT-unit_map-v0": "RESEARCH_BLOCKED",
    "SEAM-SR-COSMO-unit_map-v0": "RESEARCH_BLOCKED",
    "SEAM-GR-QM-unit_map-v0": "RESEARCH_BLOCKED",
}

EXPECTED_COUNTS = {
    "action_derivations_required": 0,
    "convention_restorations_required": 2,
    "empirical_calibrations_required": 0,
    "equation_balance_derivations_required": 1,
    "rows_rejected": 0,
    "research_blocked_routes_required": 5,
    "rows_remaining_blocked": 12,
    "seam_maps_required": 0,
    "semantic_clarifications_required": 4,
    "total_rows": 12,
}


def _artifacts() -> tuple[dict, dict, dict]:
    return subject.build_artifacts()


def test_frozen_inputs_are_byte_verified_and_review_authorizes_target() -> None:
    ledger, review = subject.load_inputs()
    assert subject.sha256_path(subject.LEDGER_PATH) == subject.LEDGER_SHA256
    assert (
        subject.sha256_path(subject.LEDGER_MANIFEST_PATH)
        == subject.LEDGER_MANIFEST_SHA256
    )
    assert (
        subject.sha256_path(subject.EXECUTION_REPORT_PATH)
        == subject.EXECUTION_REPORT_SHA256
    )
    assert (
        subject.sha256_path(subject.ACCEPTED_REVIEW_PATH)
        == subject.ACCEPTED_REVIEW_SHA256
    )
    assert ledger["total_row_count"] == 12
    assert review["accepted"] is True
    assert review["selected_next_target"] == subject.TARGET


def test_packet_routes_each_frozen_row_exactly_once() -> None:
    packet, _, _ = _artifacts()
    rows = packet["route_selections"]
    assert len(rows) == 12
    assert len({row["row_id"] for row in rows}) == 12
    assert {
        row["row_id"]: row["selected_response_route"] for row in rows
    } == EXPECTED_ROUTES
    assert all(set(row) == subject.ROW_REQUIRED_FIELDS for row in rows)
    assert all(isinstance(row["selected_response_route"], str) for row in rows)
    assert all(
        [item["criterion"] for item in row["selection_criteria_evaluation"]]
        == subject.ORDERED_SELECTION_CRITERIA
        for row in rows
    )


def test_packet_preserves_six_unknown_and_six_unresolved() -> None:
    packet, _, _ = _artifacts()
    statuses = Counter(row["current_status"] for row in packet["route_selections"])
    assert statuses == {"unit_unknown": 6, "unresolved": 6}
    assert all(
        row["claim_impact"].startswith("planning_only_")
        for row in packet["route_selections"]
    )


def test_route_counts_are_planning_counts_not_achievements() -> None:
    packet, _, report = _artifacts()
    assert packet["family_level_counts"] == EXPECTED_COUNTS
    assert report["family_level_counts"] == EXPECTED_COUNTS
    assert packet["boundary"]["route_selection_is_resolution"] is False
    assert packet["policy"]["route_selection_resolves_blocker"] is False


def test_seams_remain_blocked_until_both_internal_unit_systems_are_reviewed() -> None:
    packet, _, _ = _artifacts()
    seams = [row for row in packet["route_selections"] if row["row_kind"] == "seam"]
    assert len(seams) == 5
    assert {row["selected_response_route"] for row in seams} == {"RESEARCH_BLOCKED"}
    assert all("both participating pillars" in row["selection_reason"] for row in seams)
    assert all(
        row["seam_endpoint_readiness"]["applicable"] is True
        and row["seam_endpoint_readiness"]["both_internal_unit_systems_reviewed"]
        is False
        and len(row["seam_endpoint_readiness"]["endpoints"]) == 2
        for row in seams
    )
    assert packet["family_level_counts"]["seam_maps_required"] == 0


def test_no_unit_dimension_constant_calibration_or_mapping_is_emitted() -> None:
    packet, _, report = _artifacts()
    assert subject._contains_assignment_keys(packet) is False
    assert packet["boundary"]["unit_assignments_emitted"] == 0
    assert packet["boundary"]["dimension_vectors_emitted"] == 0
    assert packet["boundary"]["conversion_constants_emitted"] == 0
    assert packet["boundary"]["seam_mappings_emitted"] == 0
    assert "no unit, dimension, constant, calibration, or seam mapping is derived" in report[
        "claim"
    ].lower()


def test_all_prescribed_nonclaims_are_explicit() -> None:
    packet, _, report = _artifacts()
    assert packet["nonclaims"] == subject.NONCLAIMS
    assert report["nonclaims"] == subject.NONCLAIMS
    assert packet["boundary"] == subject.BOUNDARY
    assert packet["claim_ceiling_level"] == 3
    assert all(
        value is False
        for key, value in packet["boundary"].items()
        if key.endswith(("_claimed", "_authorized", "_promoted", "_resumed"))
    )


def test_selection_criteria_and_closed_eight_route_taxonomy_are_exact() -> None:
    packet, _, _ = _artifacts()
    assert packet["ordered_selection_criteria"] == subject.ORDERED_SELECTION_CRITERIA
    assert len(packet["ordered_selection_criteria"]) == 10
    assert packet["route_count"] == 8
    assert [entry["route"] for entry in packet["route_taxonomy"]] == list(
        subject.ROUTES
    )


def test_top_level_successor_is_independent_result_review() -> None:
    packet, manifest, report = _artifacts()
    for artifact in (packet, manifest, report):
        assert artifact["selected_next_target"] == subject.SUCCESSOR_TARGET
        assert artifact["selected_next_target_kind"] == subject.SUCCESSOR_TARGET_KIND
    assert report["verdict"] == "PREPARED_PENDING_INDEPENDENT_REVIEW"


def test_canonical_packet_passes_all_sixteen_decisions() -> None:
    ledger, _ = subject.load_inputs()
    packet = subject.build_packet(ledger)
    assert subject.packet_validation_failures(packet, ledger) == []
    _, _, report = _artifacts()
    assert report["decision_count"] == 16
    assert report["all_decisions_passed"] is True
    assert [entry["decision_id"] for entry in report["decisions"]] == subject.DECISION_IDS
    assert all(entry["passed"] for entry in report["decisions"])


def test_route_swap_preserving_family_counts_fails_exact_row_routing() -> None:
    ledger, _ = subject.load_inputs()
    packet = subject.build_packet(ledger)
    qft_route = packet["route_selections"][0]["selected_response_route"]
    gr_route = packet["route_selections"][1]["selected_response_route"]
    packet["route_selections"][0]["selected_response_route"] = gr_route
    packet["route_selections"][1]["selected_response_route"] = qft_route
    assert packet["family_level_counts"] == EXPECTED_COUNTS
    failures = subject.packet_validation_failures(packet, ledger)
    assert "each_row_selects_exactly_one_primary_route" in failures
    assert "exact_twelve_row_identity_status_and_evidence_bindings_preserved" in failures


def test_all_ten_prescribed_negative_controls_are_detected() -> None:
    ledger, _ = subject.load_inputs()
    packet = subject.build_packet(ledger)
    controls = subject.run_negative_controls(packet, ledger)
    assert len(controls) == 10
    assert all(control["fresh_deep_copy_used"] for control in controls)
    assert all(control["passed"] for control in controls)
    assert all(
        control["expected_failed_decision_id"]
        in control["observed_failed_decision_ids"]
        for control in controls
    )


@pytest.mark.parametrize(
    ("control_id", "expected_decision"),
    [
        (
            "assign_unit_to_unit_unknown_without_evidence",
            "unit_unknown_rows_cannot_receive_assignments_without_evidence",
        ),
        (
            "natural_units_mark_unresolved_resolved",
            "natural_units_do_not_resolve_unresolved_rows",
        ),
        (
            "dimensionless_coordinates_promoted_to_physical_distance",
            "dimensionless_coordinates_are_not_physical_distances",
        ),
        (
            "suppressed_constant_omitted",
            "suppressed_constants_require_explicit_restoration",
        ),
        (
            "two_incompatible_routes_assigned_without_priority",
            "each_row_selects_exactly_one_primary_route",
        ),
        (
            "seam_map_selected_with_incomplete_pillar_units",
            "seam_map_requires_two_reviewed_internal_unit_systems",
        ),
        (
            "candidate_master_action_used_as_self_evidence",
            "candidate_master_action_is_not_self_supporting_evidence",
        ),
        (
            "normalization_convention_promoted_to_empirical_scale",
            "normalization_conventions_are_not_empirical_scales",
        ),
        (
            "routed_blocker_promoted_to_dimensional_closure",
            "route_selection_does_not_promote_dimensional_closure",
        ),
        (
            "C_k_embedding_before_dimensions_known",
            "C_k_embedding_remains_forbidden_before_dimensions_are_known",
        ),
    ],
)
def test_each_control_reports_its_specific_decision(
    control_id: str, expected_decision: str
) -> None:
    _, _, report = _artifacts()
    control = next(
        item for item in report["negative_controls"] if item["control_id"] == control_id
    )
    assert control["expected_failed_decision_id"] == expected_decision
    assert expected_decision in control["observed_failed_decision_ids"]
    assert control["passed"] is True


def test_build_is_byte_deterministic() -> None:
    first = _artifacts()
    second = _artifacts()
    assert [subject.canonical_json_bytes(value) for value in first] == [
        subject.canonical_json_bytes(value) for value in second
    ]


def test_manifest_binds_packet_generator_and_accepted_inputs() -> None:
    packet, manifest, report = _artifacts()
    assert manifest["packet"]["sha256"] == subject.sha256_bytes(
        subject.canonical_json_bytes(packet)
    )
    assert manifest["generator"]["sha256"] == subject.HISTORICAL_SCRIPT_SHA256
    assert manifest["input_artifacts"] == subject._input_bindings()
    assert report["artifact_hashes"]["manifest_sha256"] == subject.sha256_bytes(
        subject.canonical_json_bytes(manifest)
    )


def test_all_route_evidence_hashes_and_imported_scalar_action_are_bound() -> None:
    packet, manifest, _ = _artifacts()
    contract = subject.qft_route_evidence_identity.load_contract()
    contract_by_path = {
        entry["path"]: entry for entry in contract["identities"]
    }
    resolved = subject.qft_route_evidence_identity.verify_route_evidence(
        [artifact["path"] for artifact in subject.ROUTE_EVIDENCE_ARTIFACTS],
        repo_root=subject.REPO_ROOT,
    )
    assert len(resolved) == 9
    for artifact in subject.ROUTE_EVIDENCE_ARTIFACTS:
        assert (
            contract_by_path[artifact["path"]]["historical_identity"]["sha256"]
            == artifact["sha256"]
        )
        assert artifact in packet["input_artifacts"]
        assert artifact in manifest["input_artifacts"]
    qft = packet["route_selections"][0]
    assert qft["supplemental_evidence_bindings"] == [
        subject.ROUTE_EVIDENCE_ARTIFACTS[-1]
    ]
    assert qft["authority_limit"] == (
        "accepted_imported_real_scalar_action_only_no_candidate_master_action_"
        "no_ToE_native_phi_no_wider_QFT_authority"
    )
    assert qft["successor_target"] == (
        "prepare_qft_pillar_unit_object_semantics_refinement_packet"
    )


def test_repository_artifacts_are_canonical_and_current() -> None:
    packet, manifest, report = _artifacts()
    assert subject.PACKET_PATH.read_bytes() == subject.canonical_json_bytes(packet)
    assert subject.MANIFEST_PATH.read_bytes() == subject.canonical_json_bytes(manifest)
    assert subject.REPORT_PATH.read_bytes() == subject.canonical_json_bytes(report)


def test_cli_check_succeeds() -> None:
    result = subprocess.run(
        [sys.executable, "-m", subject.__name__, "--check"],
        cwd=subject.REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0, result.stderr
    assert "16/16 decisions and 10/10 controls pass" in result.stdout


def test_tampered_accepted_ledger_is_rejected(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    tampered = json.loads(subject.LEDGER_PATH.read_text(encoding="utf-8"))
    tampered["total_row_count"] = 11
    tampered_path = tmp_path / "ledger.json"
    tampered_path.write_text(json.dumps(tampered), encoding="utf-8")
    monkeypatch.setattr(subject, "LEDGER_PATH", tampered_path)
    with pytest.raises(ValueError, match="input hash mismatch"):
        subject.load_inputs()


def test_mutating_canonical_packet_does_not_mutate_a_fresh_build() -> None:
    ledger, _ = subject.load_inputs()
    first = subject.build_packet(ledger)
    first["route_selections"][0]["available_evidence"].append("tamper")
    second = subject.build_packet(ledger)
    assert "tamper" not in second["route_selections"][0]["available_evidence"]

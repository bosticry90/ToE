from __future__ import annotations

import copy
from pathlib import Path

from formal.python.tools import (
    pillar_seam_unit_mapping_ledger_blocker_response_route_selection_packet_result_review
    as subject,
)


def report() -> dict:
    return subject.build_review_report(run_subprocesses=True)


def test_review_is_fail_closed_on_exact_three_source_attribution_defects() -> None:
    value = report()
    assert value["accepted"] is False
    assert value["verdict"] == "B-BLOCKED"
    assert value["primary_label"] == "B-BLOCKED"
    assert value["mismatch_codes"] == subject.MISMATCH_CODES
    assert value["status"] == "blocked_source_evidence_attribution_mismatch"


def test_review_binds_immutable_preparation_commit_and_parent() -> None:
    value = report()
    assert value["preparation_commit"] == subject.PREPARATION_COMMIT
    assert value["preparation_parent"] == subject.PREPARATION_PARENT
    assert value["failure_preservation"]["preparation_commit_remains_immutable"]
    assert value["failure_preservation"]["preparation_artifacts_amended_by_review"] is False


def test_all_frozen_hashes_match_without_trusting_preparation_flags() -> None:
    value = report()
    for relative, expected in subject.EXPECTED_HASHES.items():
        assert subject.resolved_expected_hash(relative, expected) == expected
    assert value["artifact_chain"]["expected_hashes"] == subject.EXPECTED_HASHES


def test_exact_twelve_routes_and_counts_are_independently_reproduced() -> None:
    value = report()
    route = value["route_reproduction"]
    assert route["route_map_reproduced"] is True
    assert route["expected_routes"] == subject.EXPECTED_ROUTES
    assert route["expected_route_counts"] == subject.EXPECTED_ROUTE_COUNTS
    assert route["unit_unknown_row_count"] == 6
    assert route["unresolved_row_count"] == 6
    assert route["rows_remaining_blocked"] == 12


def test_all_sixteen_preparation_decisions_are_recomputed() -> None:
    decisions = report()["implemented_decision_reproduction"]
    assert decisions["decision_count"] == 16
    assert decisions["all_implemented_decisions_reproduced"] is True
    assert decisions["failed_decision_ids"] == []
    assert [item["decision_id"] for item in decisions["decisions"]] == subject.DECISION_IDS
    assert all(item["passed"] for item in decisions["decisions"])


def test_all_ten_controls_are_replayed_from_fresh_copies() -> None:
    controls = report()["negative_control_reproduction"]
    assert controls["control_count"] == 10
    assert controls["all_controls_reproduced"] is True
    assert all(item["fresh_deep_copy_used"] for item in controls["controls"])
    assert all(item["passed"] for item in controls["controls"])
    assert all(
        item["expected_failed_decision_id"] in item["observed_failed_decision_ids"]
        for item in controls["controls"]
    )


def test_qft_bound_source_action_attribution_is_rejected_by_named_check() -> None:
    evidence = report()["source_evidence_review"]
    assert evidence["mismatch_checks"][
        "QFT_BOUND_SOURCE_ACTION_ATTRIBUTION_MISMATCH"
    ]
    assert evidence["positive_route_evidence_checks"][
        "qft_narrow_scalar_anti_promotion_preserved"
    ]


def test_qm_bound_source_hamiltonian_attribution_is_rejected() -> None:
    evidence = report()["source_evidence_review"]
    assert evidence["mismatch_checks"][
        "QM_BOUND_SOURCE_HAMILTONIAN_ATTRIBUTION_MISMATCH"
    ]
    assert evidence["positive_route_evidence_checks"][
        "qm_supported_surfaces_are_schrodinger_state_contract_and_unitarity"
    ]


def test_stat_probability_transport_attribution_is_rejected() -> None:
    evidence = report()["source_evidence_review"]
    assert evidence["mismatch_checks"][
        "STAT_BOUND_SOURCE_PROBABILITY_TRANSPORT_ATTRIBUTION_MISMATCH"
    ]
    assert evidence["positive_route_evidence_checks"][
        "stat_supported_surfaces_are_entropy_flux_balance_and_regime"
    ]


def test_gr_em_sr_positive_route_evidence_is_preserved_at_bounded_scope() -> None:
    checks = report()["source_evidence_review"]["positive_route_evidence_checks"]
    assert checks["gr_bounded_poisson_and_action_native_surface_supported"]
    assert checks["em_typed_objects_and_units_not_selected_supported"]
    assert checks["sr_interval_and_dimensional_structure_supported"]


def test_evidence_wording_correction_would_remove_only_named_mismatches() -> None:
    packet = subject.load_json(subject.PACKET_PATH)
    changed = copy.deepcopy(packet)
    rows = subject.row_map(changed)
    rows["PILLAR-QFT-units_and_dimensions-v0"]["available_evidence"][0] = (
        "The bound QFT source identifies canonical-momentum, Hamiltonian, "
        "unitarity, and normalization obligations."
    )
    rows["PILLAR-QM-units_and_dimensions-v0"]["available_evidence"][0] = (
        "The bound QM source identifies Schrodinger-form, state-evolution-contract, "
        "and unitary-consistency surfaces under explicit assumptions."
    )
    rows["PILLAR-STAT-units_and_dimensions-v0"]["available_evidence"][0] = (
        "The bound STAT source identifies entropy and entropy-production, "
        "flux and balance-law, and regime-assumption surfaces."
    )
    assert subject.source_evidence_audit(changed)["mismatch_codes"] == []
    assert subject.independent_decision_failures(
        changed, subject.load_json(subject.LEDGER_PATH)
    ) == []


def test_review_emits_and_authorizes_no_unit_or_resolution_content() -> None:
    boundary = report()["boundary"]
    assert boundary["unit_or_dimension_assignment_emitted"] is False
    assert boundary["dimensional_closure_claimed"] is False
    assert boundary["pillar_completion_claimed"] is False
    assert boundary["seam_admissibility_claimed"] is False
    assert boundary["physical_calibration_claimed"] is False
    assert boundary["cross_sector_coupling_validation_claimed"] is False
    assert boundary["C_k_action_embedding_authorized"] is False
    assert boundary["ccft_resumed"] is False
    assert boundary["master_action_promoted"] is False


def test_only_versioned_evidence_correction_is_selected() -> None:
    value = report()
    assert value["selected_next_target"] == subject.SELECTED_NEXT_TARGET
    assert value["selected_next_target_kind"] == subject.SELECTED_NEXT_TARGET_KIND
    assert value["authority_rotation"]["packet_acceptance_authorized"] is False
    assert value["authority_rotation"]["corrective_v1_preparation_authorized"] is True
    assert value["authority_rotation"][
        "first_blocker_resolution_guardrail_authorized"
    ] is False
    assert value["successor_boundary"]["first_resolution_guardrail_selected_now"] is False
    assert value["successor_boundary"][
        "would_be_first_resolution_guardrail_after_future_acceptance"
    ] == subject.FIRST_RESOLUTION_GUARDRAIL


def test_two_fresh_subprocess_regenerations_are_byte_exact_and_nonrewriting() -> None:
    regeneration = report()["regeneration"]
    assert regeneration["passed"] is True
    assert regeneration["fresh_subprocess_count"] == 2
    assert regeneration["return_codes"] == [0, 0]
    assert regeneration["subprocess_outputs_byte_identical"] is True
    assert regeneration["subprocess_report_matches_committed_report"] is True
    assert regeneration["preparation_artifact_hashes_unchanged"] is True


def test_registry_maintenance_remains_paused_and_irrelevant() -> None:
    boundary = report()["maintenance_boundary"]
    assert boundary == {
        "registry_maintenance_paused": True,
        "registry_monolith_remains_authoritative": True,
        "registry_v3_live": False,
        "stage_a_authorized": False,
        "stage_b_authorized": False,
    }


def test_committed_review_report_is_canonical_and_current() -> None:
    value = report()
    assert subject.REVIEW_REPORT_PATH.read_bytes() == subject.canonical_json_bytes(value)
    assert value["review_outcome"] == subject.REVIEW_OUTCOME
    assert value["strict_review_outcome"] == subject.STRICT_REVIEW_OUTCOME


def test_reviewer_does_not_import_preparation_validator_as_authority() -> None:
    source = Path(subject.__file__).read_text(encoding="utf-8")
    assert "from formal.python.tools.pillar_seam_unit_mapping_ledger_blocker" not in source
    assert "packet_validation_failures" not in source
    assert "run_negative_controls" not in source


def test_review_schema_and_diagnostic_target_are_exact() -> None:
    value = report()
    assert value["schema_id"].endswith("RESULT_REVIEW_20260712_v0")
    assert value["diagnostic_target"] == subject.DIAGNOSTIC_TARGET
    assert value["failure_preservation"]["versioned_successor_required"] is True

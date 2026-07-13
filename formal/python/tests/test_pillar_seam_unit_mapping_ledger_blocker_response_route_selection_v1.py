from __future__ import annotations

import subprocess
import sys
from collections import Counter

import pytest

from formal.python.tools import (
    pillar_seam_unit_mapping_ledger_blocker_response_route_selection_v1 as subject,
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
    "equation_balance_derivations_required": 1,
    "convention_restorations_required": 2,
    "seam_maps_required": 0,
    "empirical_calibrations_required": 0,
    "semantic_clarifications_required": 4,
    "research_blocked_routes_required": 5,
    "rows_remaining_blocked": 12,
    "rows_rejected": 0,
    "total_rows": 12,
}

EXPECTED_CONTROL_DECISIONS = {
    "assign_unit_to_unit_unknown_without_evidence":
        "unit_unknown_rows_cannot_receive_assignments_without_evidence",
    "natural_units_mark_unresolved_resolved":
        "natural_units_do_not_resolve_unresolved_rows",
    "dimensionless_coordinates_promoted_to_physical_distance":
        "dimensionless_coordinates_are_not_physical_distances",
    "suppressed_constant_omitted":
        "suppressed_constants_require_explicit_restoration",
    "two_incompatible_routes_assigned_without_priority":
        "each_row_selects_exactly_one_primary_route",
    "seam_map_selected_with_incomplete_pillar_units":
        "seam_map_requires_two_reviewed_internal_unit_systems",
    "candidate_master_action_used_as_self_evidence":
        "candidate_master_action_is_not_self_supporting_evidence",
    "normalization_convention_promoted_to_empirical_scale":
        "normalization_conventions_are_not_empirical_scales",
    "routed_blocker_promoted_to_dimensional_closure":
        "route_selection_does_not_promote_dimensional_closure",
    "C_k_embedding_before_dimensions_known":
        "C_k_embedding_remains_forbidden_before_dimensions_are_known",
    "qft_action_claimed_without_action":
        "explicit_propositions_are_source_anchored",
    "qm_hamiltonian_claimed_without_hamiltonian":
        "explicit_propositions_are_source_anchored",
    "stat_probability_claimed_without_probability_semantics":
        "explicit_propositions_are_source_anchored",
    "stat_transport_claimed_without_transport_law":
        "explicit_propositions_are_source_anchored",
    "narrow_scalar_evidence_promoted_to_full_qft":
        "narrow_scalar_evidence_is_not_promoted_to_full_qft",
    "absence_treated_as_positive_evidence":
        "inferred_and_absent_propositions_do_not_support_routes",
    "citation_hash_changed_without_rebinding":
        "source_path_hash_pairs_are_exactly_rebound",
    "route_rationale_object_missing_from_inventory":
        "route_rationale_objects_are_supported",
    "speculative_surface_treated_as_authoritative":
        "supporting_sources_have_authorized_bounded_class",
    "one_source_supports_conflicting_object_definitions":
        "source_object_definitions_are_nonconflicting",
}


def _artifacts() -> tuple[dict, dict, dict]:
    return subject.build_artifacts()


def _rows(packet: dict) -> dict[str, dict]:
    return {row["row_id"]: row for row in packet["route_selections"]}


def _props(row: dict) -> dict[str, dict]:
    return {
        prop["proposition_id"]: prop
        for prop in row["evidence_matrix"]["propositions"]
    }


def test_frozen_v0_preparation_and_b_blocked_review_authorize_only_v1() -> None:
    ledger, review = subject.load_inputs()
    assert ledger["total_row_count"] == 12
    assert review["accepted"] is False
    assert review["verdict"] == "B-BLOCKED"
    assert review["mismatch_codes"] == subject.CORRECTED_MISMATCH_CODES
    assert review["selected_next_target"] == subject.TARGET
    for binding in subject._frozen_inputs():
        path = subject.REPO_ROOT / binding["path"]
        assert subject.sha256_path(path) == binding["sha256"]


def test_v1_lineage_preserves_both_immutable_commits_and_hashes() -> None:
    packet, _, report = _artifacts()
    expected = {
        "v0_preparation_commit": subject.V0_PREPARATION_COMMIT,
        "v0_rejection_commit": subject.V0_REVIEW_COMMIT,
        "v0_preparation_packet_sha256": subject.V0_PACKET_SHA256,
        "v0_rejection_report_sha256": subject.V0_REVIEW_SHA256,
    }
    assert packet["lineage"] == expected
    assert report["lineage"] == expected
    assert packet["source_attribution_repair"] == {
        "correction_scope": "SOURCE_ATTRIBUTION_ONLY",
        "corrected_mismatch_codes": subject.CORRECTED_MISMATCH_CODES,
        "v0_route_map_treated_as_authority": False,
        "v1_route_map_changed_after_recomputation": False,
    }


def test_exactly_twelve_evidence_matrices_are_bound_once() -> None:
    packet, _, _ = _artifacts()
    rows = packet["route_selections"]
    assert len(rows) == 12
    assert len({row["row_id"] for row in rows}) == 12
    assert all(set(row) == subject.ROW_REQUIRED_FIELDS for row in rows)
    assert all(row["evidence_matrix"]["row_id"] == row["row_id"] for row in rows)
    assert all(row["route_recomputed_from_supported_evidence"] is True for row in rows)
    assert packet["route_map_recomputed_not_inherited"] is True


def test_route_map_is_recomputed_from_supported_propositions() -> None:
    packet, _, report = _artifacts()
    rows = _rows(packet)
    assert {
        row_id: row["selected_response_route"] for row_id, row in rows.items()
    } == EXPECTED_ROUTES
    assert report["route_map"] == EXPECTED_ROUTES
    for row in rows.values():
        matrix = row["evidence_matrix"]
        assert subject._select_route(matrix) == row["selected_response_route"]
        assert matrix["route_recomputed_not_inherited"] is True
        assert row["route_support_proposition_ids"] == matrix[
            "supported_proposition_ids"
        ]


def test_statuses_and_family_counts_remain_planning_only() -> None:
    packet, _, report = _artifacts()
    assert Counter(row["current_status"] for row in packet["route_selections"]) == {
        "unit_unknown": 6,
        "unresolved": 6,
    }
    assert packet["family_level_counts"] == EXPECTED_COUNTS
    assert report["family_level_counts"] == EXPECTED_COUNTS
    assert report["resolved_row_count"] == 0
    assert report["unit_unknown_row_count"] == 6
    assert report["unresolved_row_count"] == 6


def test_proposition_taxonomy_and_support_rules_are_closed() -> None:
    packet, _, _ = _artifacts()
    assert packet["evidence_classification_taxonomy"] == list(
        subject.CLASSIFICATIONS
    )
    for row in packet["route_selections"]:
        matrix = row["evidence_matrix"]
        propositions = _props(row)
        assert set(matrix["supported_proposition_ids"]) == {
            prop_id
            for prop_id, prop in propositions.items()
            if prop["supports_route"]
        }
        assert set(matrix["unsupported_proposition_ids"]) == {
            prop_id
            for prop_id, prop in propositions.items()
            if not prop["supports_route"]
        }
        for prop in propositions.values():
            assert prop["classification"] in subject.CLASSIFICATIONS
            if prop["supports_route"]:
                assert prop["classification"] in subject.SUPPORTING_CLASSIFICATIONS
            if prop["classification"] in {
                "INFERRED_NOT_ESTABLISHED",
                "ABSENT_FROM_SOURCE",
            }:
                assert prop["supports_route"] is False


def test_explicit_and_derived_propositions_are_reproducibly_anchored() -> None:
    packet, _, _ = _artifacts()
    for row in packet["route_selections"]:
        matrix = row["evidence_matrix"]
        bindings = {
            binding["source_id"]: binding
            for binding in matrix["source_bindings"]
        }
        propositions = _props(row)
        for binding in bindings.values():
            assert binding["authority_class"] in subject.SUPPORTING_AUTHORITY_CLASSES
            assert subject.sha256_path(subject.REPO_ROOT / binding["path"]) == binding[
                "sha256"
            ]
        for prop in propositions.values():
            if prop["classification"] == "EXPLICITLY_STATED_BY_SOURCE":
                assert prop["source_id"] in bindings
                if not prop.get("ledger_assertion"):
                    text = (
                        subject.REPO_ROOT / bindings[prop["source_id"]]["path"]
                    ).read_text(encoding="utf-8").casefold()
                    assert all(
                        anchor.casefold() in text
                        for anchor in prop["required_substrings"]
                    )
            if prop["classification"] == "DERIVED_FROM_SOURCE":
                assert prop["premise_ids"]
                assert all(
                    premise in propositions
                    and propositions[premise]["classification"]
                    in subject.SUPPORTING_CLASSIFICATIONS
                    for premise in prop["premise_ids"]
                )


def test_route_rationale_objects_are_covered_by_supported_inventory() -> None:
    packet, _, _ = _artifacts()
    for row in packet["route_selections"]:
        matrix = row["evidence_matrix"]
        supported_objects = {
            obj["object_id"]
            for prop in matrix["propositions"]
            if prop["supports_route"]
            for obj in prop["objects"]
        }
        assert set(matrix["rationale_object_ids"]) <= supported_objects
        assert set(row["rationale_object_ids"]) <= supported_objects


def test_qft_posture_removes_direct_action_attribution_and_bounds_scalar() -> None:
    packet, _, _ = _artifacts()
    row = _rows(packet)["PILLAR-QFT-units_and_dimensions-v0"]
    props = _props(row)
    assert props["qft_direct_scope_explicit"]["supports_route"] is True
    assert "canonical momentum" in props["qft_direct_scope_explicit"][
        "statement"
    ].lower()
    assert props["qft_direct_physical_action_absent"]["classification"] == (
        "ABSENT_FROM_SOURCE"
    )
    assert props["qft_direct_physical_action_absent"]["supports_route"] is False
    assert props["qft_scalar_sandbox_explicit"]["supports_route"] is True
    assert "qft_scalar_sandbox_explicit" in row[
        "route_support_proposition_ids"
    ]
    assert props["qft_scalar_sandbox_explicit"]["statement"] in row[
        "available_evidence"
    ]
    assert props["qft_scalar_sandbox_explicit"]["statement"] not in row[
        "missing_evidence"
    ]
    route_signal = props["PILLAR-QFT-units_and_dimensions-v0_route_signal"]
    assert "qft_scalar_sandbox_explicit" in route_signal["premise_ids"]
    assert row["evidence_matrix"]["scalar_evidence_scope"] == (
        "NARROW_CLASSICAL_REAL_SCALAR_ONLY"
    )
    assert row["selected_response_route"] == "OBJECT_SEMANTICS_REFINEMENT"


def test_each_seam_route_is_premised_on_exact_endpoint_readiness() -> None:
    ledger, _ = subject.load_inputs()
    packet = subject.build_packet(ledger)
    pillar_states = {
        row["pillar_id"]: row["guardrail_unit_state"]
        for row in ledger["pillar_rows"]
    }
    ledger_seams = {row["row_id"]: row for row in ledger["seam_rows"]}
    for row in packet["route_selections"]:
        if row["row_kind"] != "seam":
            continue
        props = _props(row)
        endpoint_id = f"{row['row_id']}_endpoint_readiness_explicit"
        route_id = f"{row['row_id']}_route_research_blocked"
        endpoint = props[endpoint_id]
        route = props[route_id]
        pillar_ids = ledger_seams[row["row_id"]]["pillar_ids"]
        exact_states = {pillar_id: pillar_states[pillar_id] for pillar_id in pillar_ids}
        assert endpoint["classification"] == "EXPLICITLY_STATED_BY_SOURCE"
        assert endpoint["source_id"] == subject.SOURCES["ledger"]["source_id"]
        assert endpoint["supports_route"] is True
        assert endpoint["ledger_assertion"] == {
            "assertion_type": "endpoint_readiness",
            "seam_row_id": row["row_id"],
            "pillar_ids": pillar_ids,
            "endpoint_states": exact_states,
        }
        assert endpoint_id in route["premise_ids"]
        assert route["derivation_rule"] == (
            "UNRESOLVED_ENDPOINTS_BLOCK_SEAM_CONVERSION"
        )
        assert route["derived_facts"]["endpoint_states"] == exact_states
        assert all(state in {"unit_unknown", "unresolved"} for state in exact_states.values())
        assert row["selected_response_route"] == "RESEARCH_BLOCKED"


def test_absent_qft_qm_stat_propositions_are_bound_and_machine_checked() -> None:
    packet, _, _ = _artifacts()
    cases = {
        ("PILLAR-QFT-units_and_dimensions-v0", "qft_direct_physical_action_absent"):
            {
                "kind": "regex",
                "pattern": r"(?<![-\w])action(?![-\w])",
                "flags": ["IGNORECASE"],
                "expected_match_count": 0,
            },
        ("PILLAR-QM-units_and_dimensions-v0", "qm_hamiltonian_absent"): {
            "kind": "casefold_substring",
            "substring": "Hamiltonian",
            "expected_match_count": 0,
        },
        ("PILLAR-STAT-units_and_dimensions-v0", "stat_probability_absent"): {
            "kind": "casefold_substring",
            "substring": "probability",
            "expected_match_count": 0,
        },
        ("PILLAR-STAT-units_and_dimensions-v0", "stat_transport_absent"): {
            "kind": "casefold_substring",
            "substring": "transport",
            "expected_match_count": 0,
        },
    }
    rows = _rows(packet)
    for (row_id, proposition_id), expected_check in cases.items():
        row = rows[row_id]
        matrix = row["evidence_matrix"]
        bindings = {
            binding["source_id"]: binding
            for binding in matrix["source_bindings"]
        }
        proposition = _props(row)[proposition_id]
        assert proposition["classification"] == "ABSENT_FROM_SOURCE"
        assert proposition["supports_route"] is False
        assert proposition["source_id"] in bindings
        assert proposition["absence_check"] == expected_check
        binding = bindings[proposition["source_id"]]
        assert subject.sha256_path(subject.REPO_ROOT / binding["path"]) == binding[
            "sha256"
        ]
        source_text = (subject.REPO_ROOT / binding["path"]).read_text(
            encoding="utf-8"
        )
        assert subject._absence_check_passes(source_text, expected_check) is True


def test_qm_posture_uses_supported_surfaces_and_marks_hamiltonian_absent() -> None:
    packet, _, _ = _artifacts()
    row = _rows(packet)["PILLAR-QM-units_and_dimensions-v0"]
    props = _props(row)
    direct = props["qm_direct_scope_explicit"]
    assert direct["supports_route"] is True
    assert all(
        token in direct["statement"].lower()
        for token in ("schrodinger", "state-evolution", "unitary")
    )
    assert props["qm_hamiltonian_absent"]["classification"] == "ABSENT_FROM_SOURCE"
    assert props["qm_hamiltonian_absent"]["supports_route"] is False
    assert row["selected_response_route"] == "OBJECT_SEMANTICS_REFINEMENT"


def test_stat_posture_is_entropy_flux_regime_only_without_probability_transport() -> None:
    packet, _, _ = _artifacts()
    row = _rows(packet)["PILLAR-STAT-units_and_dimensions-v0"]
    props = _props(row)
    direct = props["stat_direct_scope_explicit"]
    assert direct["supports_route"] is True
    assert all(
        token in direct["statement"].lower()
        for token in ("entropy", "flux", "regime")
    )
    for prop_id in ("stat_probability_absent", "stat_transport_absent"):
        assert props[prop_id]["classification"] == "ABSENT_FROM_SOURCE"
        assert props[prop_id]["supports_route"] is False
    assert row["selected_response_route"] == "OBJECT_SEMANTICS_REFINEMENT"


def test_canonical_packet_passes_all_twenty_six_decisions() -> None:
    ledger, _ = subject.load_inputs()
    packet = subject.build_packet(ledger)
    assert subject.packet_validation_failures(packet, ledger) == []
    _, manifest, report = _artifacts()
    assert len(subject.DECISION_IDS) == 26
    assert report["decision_count"] == 26
    assert manifest["decision_count"] == 26
    assert report["all_decisions_passed"] is True
    assert [item["decision_id"] for item in report["decisions"]] == (
        subject.DECISION_IDS
    )


def test_exact_twenty_negative_controls_are_rejected() -> None:
    ledger, _ = subject.load_inputs()
    controls = subject.run_negative_controls(subject.build_packet(ledger), ledger)
    assert len(controls) == 20
    assert {item["control_id"] for item in controls} == set(
        EXPECTED_CONTROL_DECISIONS
    )
    assert all(item["fresh_deep_copy_used"] for item in controls)
    assert all(item["passed"] for item in controls)


@pytest.mark.parametrize(
    ("control_id", "expected_decision"),
    list(EXPECTED_CONTROL_DECISIONS.items()),
)
def test_each_negative_control_reports_its_named_failure(
    control_id: str, expected_decision: str
) -> None:
    _, _, report = _artifacts()
    control = next(
        item for item in report["negative_controls"]
        if item["control_id"] == control_id
    )
    assert control["expected_failed_decision_id"] == expected_decision
    assert expected_decision in control["observed_failed_decision_ids"]
    assert control["passed"] is True


def test_manifest_hashes_generator_packet_and_all_frozen_inputs() -> None:
    packet, manifest, report = _artifacts()
    packet_raw = subject.canonical_json_bytes(packet)
    manifest_raw = subject.canonical_json_bytes(manifest)
    assert manifest["generator"] == {
        "path": subject.SCRIPT_RELATIVE_PATH,
        "sha256": subject.sha256_path(subject.SCRIPT_PATH),
    }
    assert manifest["input_artifacts"] == subject._frozen_inputs()
    assert manifest["packet"] == {
        "path": subject.PACKET_RELATIVE_PATH,
        "schema_id": subject.PACKET_SCHEMA_ID,
        "sha256": subject.sha256_bytes(packet_raw),
    }
    assert report["artifact_hashes"] == {
        "packet_sha256": subject.sha256_bytes(packet_raw),
        "manifest_sha256": subject.sha256_bytes(manifest_raw),
    }


def test_build_is_byte_deterministic_and_repository_artifacts_are_current() -> None:
    first = _artifacts()
    second = _artifacts()
    assert [subject.canonical_json_bytes(item) for item in first] == [
        subject.canonical_json_bytes(item) for item in second
    ]
    packet, manifest, report = first
    assert subject.PACKET_PATH.read_bytes() == subject.canonical_json_bytes(packet)
    assert subject.MANIFEST_PATH.read_bytes() == subject.canonical_json_bytes(manifest)
    assert subject.REPORT_PATH.read_bytes() == subject.canonical_json_bytes(report)


def test_nonclaims_and_independent_review_successor_remain_fail_closed() -> None:
    packet, manifest, report = _artifacts()
    assert packet["nonclaims"] == subject.v0.NONCLAIMS
    assert report["nonclaims"] == subject.v0.NONCLAIMS
    assert packet["boundary"] == subject.v0.BOUNDARY
    assert report["boundary"] == subject.v0.BOUNDARY
    assert report["resolved_row_count"] == 0
    assert report["packet_acceptance_authorized"] is False
    assert report["first_blocker_resolution_guardrail_authorized"] is False
    assert report["verdict"] == "PREPARED_PENDING_INDEPENDENT_REVIEW"
    for artifact in (packet, manifest, report):
        assert artifact["selected_next_target"] == subject.SUCCESSOR_TARGET
        assert artifact["selected_next_target_kind"] == subject.SUCCESSOR_TARGET_KIND


def test_cli_check_succeeds() -> None:
    result = subprocess.run(
        [sys.executable, "-m", subject.__name__, "--check"],
        cwd=subject.REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert result.returncode == 0, result.stderr
    assert "26/26 decisions and 20/20 controls pass" in result.stdout

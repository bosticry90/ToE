from __future__ import annotations

from formal.python.tools import post_dirac_maxwell_full_zero_mode_canonical_result_route_decision as decision


def test_post_result_route_decision_artifacts_are_current() -> None:
    packet, manifest, report = decision.build_artifacts()
    assert decision.PACKET_PATH.read_bytes() == decision.canonical_json_bytes(packet)
    assert decision.MANIFEST_PATH.read_bytes() == decision.canonical_json_bytes(manifest)
    assert decision.REPORT_PATH.read_bytes() == decision.canonical_json_bytes(report)


def test_exact_five_routes_receive_complete_frozen_scoring() -> None:
    packet, _, _ = decision.build_artifacts()
    assert [item["candidate_id"] for item in packet["scored_candidates"]] == decision.CANDIDATE_ORDER
    assert packet["criterion_weights"] == decision.CRITERION_WEIGHTS
    assert packet["selection_threshold"] == 44
    assert all(len(item["criterion_scores"]) == 8 for item in packet["scored_candidates"])
    assert sum(len(item["criterion_scores"]) for item in packet["scored_candidates"]) == 40


def test_scores_reproduce_without_recommendation_or_expected_winner_oracle() -> None:
    packet, _, _ = decision.build_artifacts()
    totals = {item["candidate_id"]: item["weighted_total"] for item in packet["scored_candidates"]}
    assert totals == {
        "DESCENDANT_NECESSITY_ROBUSTNESS": 56,
        "DIMENSIONAL_ASCENT_2P1": 36,
        "FIXED_CURVED_BACKGROUND_EXTENSION": 36,
        "DYNAMIC_EINSTEIN_SCALAR": 29,
        "NEXT_UNIT_PILLAR_TARGET": 34,
    }
    assert packet["canonical_selection"]["selected_candidate_id"] == "DESCENDANT_NECESSITY_ROBUSTNESS"
    assert packet["user_recommendation"]["used_as_score_input"] is False
    assert "expected_winner" not in packet
    assert "expected_selected_candidate" not in packet


def test_selection_is_stable_across_all_frozen_thresholds() -> None:
    packet, _, _ = decision.build_artifacts()
    assert packet["selection_stable_40_through_48"] is True
    assert {item["selected_candidate_id"] for item in packet["sensitivity_analysis"]} == {
        "DESCENDANT_NECESSITY_ROBUSTNESS"
    }


def test_every_score_binds_exact_eligible_propositions() -> None:
    packet, _, _ = decision.build_artifacts()
    proposition_ids = {item["proposition_id"] for item in packet["evidence_records"]}
    assert all(item["route_support_eligible"] is True for item in packet["evidence_records"])
    assert all(item["source_locator"]["locator_type"] == "JSON_POINTER" for item in packet["evidence_records"])
    for candidate in packet["scored_candidates"]:
        for row in candidate["criterion_scores"]:
            assert row["exact_supporting_proposition_ids"]
            assert set(row["exact_supporting_proposition_ids"]).issubset(proposition_ids)


def test_selected_route_is_bounded_and_does_not_reopen_canonical_work() -> None:
    packet, _, _ = decision.build_artifacts()
    selected = packet["selected_route_definition"]
    assert selected["route_id"] == "DESCENDANT_NECESSITY_ROBUSTNESS"
    assert selected["invalid_comparator_is_not_a_rival_physical_model"] is True
    assert len(selected["bounded_parameter_axes"]) == 5
    assert len(selected["required_outcome_classes"]) == 5
    assert packet["completed_tranches_reopened"] is False
    assert packet["canonical_rerun_authorized"] is False


def test_mutations_and_nonpromotion_boundaries_hold() -> None:
    packet, _, report = decision.build_artifacts()
    assert len(packet["mutation_controls"]) == 10
    assert all(item["passed"] for item in packet["mutation_controls"])
    assert report["mutation_controls_passed"] == 10
    assert packet["boundary"]["robustness_execution_authorized"] is False
    assert packet["boundary"]["pillar_completion_claimed"] is False
    assert packet["boundary"]["seam_admissibility_or_closure_claimed"] is False
    assert packet["boundary"]["C_k_audit_only"] is True
    assert packet["boundary"]["master_action_promoted"] is False


def test_prompt_is_preserved() -> None:
    assert decision.PROMPT_DEPENDENCY_ROLE == "DEMOTE_TO_NONBLOCKING_PROVENANCE"

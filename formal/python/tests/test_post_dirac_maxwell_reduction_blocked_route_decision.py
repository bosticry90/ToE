from __future__ import annotations

from formal.python.tools import post_dirac_maxwell_reduction_blocked_route_decision as decision


def test_route_decision_artifacts_are_current() -> None:
    packet, manifest, report = decision.build_artifacts()
    assert decision.PACKET_PATH.read_bytes() == decision.canonical_json_bytes(packet)
    assert decision.MANIFEST_PATH.read_bytes() == decision.canonical_json_bytes(manifest)
    assert decision.REPORT_PATH.read_bytes() == decision.canonical_json_bytes(report)


def test_exact_four_candidates_receive_complete_frozen_scoring() -> None:
    packet, _, _ = decision.build_artifacts()
    assert [item["candidate_id"] for item in packet["scored_candidates"]] == decision.CANDIDATE_ORDER
    assert packet["criterion_weights"] == decision.CRITERION_WEIGHTS
    assert packet["selection_threshold"] == 44
    assert all(len(item["criterion_scores"]) == 8 for item in packet["scored_candidates"])
    assert all(all(row["exact_supporting_proposition_ids"] for row in item["criterion_scores"]) for item in packet["scored_candidates"])


def test_scores_reproduce_and_repair_wins_without_oracle() -> None:
    packet, _, _ = decision.build_artifacts()
    totals = {item["candidate_id"]: item["weighted_total"] for item in packet["scored_candidates"]}
    assert totals == {
        "REPAIR_REDUCTION": 51,
        "ADOPT_NATIVE_1P1": 37,
        "MOVE_TO_2P1": 38,
        "CHANGE_MATTER_SECTOR": 31,
    }
    assert packet["canonical_selection"]["selected_candidate_id"] == "REPAIR_REDUCTION"
    assert "expected_winner" not in packet
    assert "expected_selected_candidate" not in packet


def test_selection_is_stable_and_context_is_nondecisive() -> None:
    packet, _, _ = decision.build_artifacts()
    assert packet["selection_stable_40_through_48"] is True
    assert {item["selected_candidate_id"] for item in packet["sensitivity_analysis"]} == {"REPAIR_REDUCTION"}
    assert packet["user_recommendation"]["used_as_score_input"] is False
    assert all(item["route_support_eligible"] is False for item in packet["external_context"])


def test_repair_is_full_zero_mode_not_tailored_sector_hunting() -> None:
    packet, _, _ = decision.build_artifacts()
    assert packet["restricted_spinor_sector_default_repair"] is False
    assert "Retain A2 and A3" in packet["repair_route_definition"]
    assert packet["post_acceptance_target"] == decision.POST_ACCEPTANCE_TARGET


def test_mutation_controls_and_authority_boundary_hold() -> None:
    packet, _, report = decision.build_artifacts()
    assert len(packet["mutation_controls"]) == 8
    assert all(item["passed"] for item in packet["mutation_controls"])
    assert report["mutation_controls_passed"] == 8
    assert packet["boundary"]["numerical_guardrail_authorized"] is False
    assert packet["boundary"]["execution_authorized"] is False


def test_prompt_is_preserved() -> None:
    assert decision.PROMPT_DEPENDENCY_ROLE == "DEMOTE_TO_NONBLOCKING_PROVENANCE"

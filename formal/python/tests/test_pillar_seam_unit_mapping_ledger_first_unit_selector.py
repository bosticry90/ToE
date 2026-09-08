from __future__ import annotations

from formal.python.tools import pillar_seam_unit_mapping_ledger_first_unit_selector as selector


def test_selector_artifacts_are_current() -> None:
    packet, manifest, report = selector.build_artifacts()
    assert selector.PACKET_PATH.read_bytes() == selector.canonical_json_bytes(packet)
    assert selector.MANIFEST_PATH.read_bytes() == selector.canonical_json_bytes(manifest)
    assert selector.REPORT_PATH.read_bytes() == selector.canonical_json_bytes(report)


def test_selector_scores_all_rows_and_criteria() -> None:
    packet, _, _ = selector.build_artifacts()
    assert len(packet["scored_rows"]) == 7
    assert packet["criterion_weights"] == selector.CRITERION_WEIGHTS
    assert packet["maximum_weighted_total"] == 62
    for row in packet["scored_rows"]:
        assert len(row["criterion_scores"]) == 8
        assert row["weighted_total"] == sum(item["weighted_score"] for item in row["criterion_scores"])
        assert all(item["exact_supporting_proposition_ids"] for item in row["criterion_scores"])
        assert all(item["eligibility_basis"] for item in row["criterion_scores"])
        assert all(item["missing_evidence_required_for_next_score"] for item in row["criterion_scores"])


def test_selector_selects_sr_stably_without_execution_readiness() -> None:
    packet, _, _ = selector.build_artifacts()
    selection = packet["canonical_selection"]
    assert selection["selected_row_id"] == "PILLAR-SR-units_and_dimensions-v0"
    assert selection["selected_weighted_total"] == 51
    assert packet["threshold_sensitive"] is False
    assert {item["threshold"]: item["selected_pillar_code"] for item in packet["sensitivity_analysis"]} == {
        40: "SR",
        42: "SR",
        44: "SR",
        46: "SR",
        48: "SR",
    }
    assert packet["selected_row_resolution_execution_ready"] is False


def test_selector_separates_target_and_execution_readiness() -> None:
    packet, _, _ = selector.build_artifacts()
    sr = next(row for row in packet["scored_rows"] if row["pillar_code"] == "SR")
    assert sr["target_selection_ready"] is True
    assert sr["resolution_execution_ready"] is False
    assert packet["selection_authorizes_preparation_only"] is True
    assert packet["unit_assignment_authorized"] is False
    assert packet["restoration_rule_authorized"] is False


def test_selector_preserves_candidate_and_prompt_boundaries() -> None:
    packet, _, _ = selector.build_artifacts()
    assert packet["Maxwell_Dirac_status"] == "PREFERRED_DOWNSTREAM_CANDIDATE_NOT_SELECTED_RESULT"
    assert packet["boundary"]["Maxwell_Dirac_selected"] is False
    assert packet["boundary"]["C_k_audit_only"] is True
    assert selector.PROMPT_DEPENDENCY_ROLE == "DEMOTE_TO_NONBLOCKING_PROVENANCE"

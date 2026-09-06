from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import (
    sr_pillar_coordinate_convention_and_constant_restoration_packet_review_v3 as review_v3,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / review_v3.REPORT_RELATIVE_PATH


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _review() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_review_regenerates_exactly_and_deterministically() -> None:
    first = review_v3.artifact_bytes()
    second = review_v3.artifact_bytes()
    assert first == second == REPORT_PATH.read_bytes()


def test_review_preserves_every_frozen_v3_input_byte() -> None:
    before = {path: _sha256(REPO_ROOT / path) for path in review_v3.FROZEN_INPUT_HASHES}
    review_v3.build_review()
    after = {path: _sha256(REPO_ROOT / path) for path in review_v3.FROZEN_INPUT_HASHES}
    assert before == after == review_v3.FROZEN_INPUT_HASHES


def test_review_blocks_v3_on_exact_first_lineage_diagnostic() -> None:
    review = _review()
    assert review["target"] == review_v3.CONSUMED_TARGET
    assert review["verdict"] == review_v3.VERDICT
    assert review["first_diagnostic"] == review_v3.FIRST_DIAGNOSTIC
    assert review["selected_next_target"] == review_v3.SELECTED_NEXT_TARGET
    assert review["hard_stop"]["lane_closed"] is True


def test_all_six_exact_source_bindings_remain_valid() -> None:
    audit = _review()["retained_results"]["exact_source_content_bindings_audit"]
    assert audit["required_count"] == audit["passed_count"] == 6
    assert audit["passed"] is True
    assert all(row["claim_class_increased"] is False for row in audit["rows"])


def test_operator_derivative_and_scalar_semantics_pass_all_ten_probes() -> None:
    audit = _review()["retained_results"]["operator_derivative_and_scalar_audit"]
    assert audit["required_count"] == audit["passed_count"] == 10
    assert audit["passed"] is True
    assert all(audit["checks"].values())
    for key in (
        "gamma_D_differs_from_D_gamma",
        "gamma_D_differs_from_D_of_gamma_psi",
        "generic_AB_differs_from_BA",
        "all_i_hbar_c_permutations_equal",
        "partial_nabla_spin_gauge_all_distinct",
        "derivative_scope_preserved",
    ):
        assert audit["checks"][key] is True


def test_all_six_production_paths_and_oracle_independence_pass() -> None:
    audit = _review()["retained_results"]["oracle_and_six_path_audit"]
    assert audit["six_path_required_count"] == audit["six_path_passed_count"] == 6
    assert audit["all_inverse_inputs_are_issued_forward_objects"] is True
    assert audit["all_six_passed"] is True
    assert audit["wrong_oracle_did_not_change_computed_ast"] is True
    assert audit["wrong_oracle_rejected"] is True
    assert audit["oracle_independence_passed"] is True


def test_lineage_rejects_copies_binding_convention_and_ast_changes() -> None:
    audit = _review()["issued_lineage_audit"]
    assert audit["result_dataclass_frozen"] is True
    assert audit["normal_public_assignment_rejected"] is True
    assert audit["valid_exact_issued_object_suppressed"] is True
    for key in (
        "manual_visible_field_and_capability_copy_diagnostic",
        "wrong_binding_diagnostic",
        "wrong_convention_diagnostic",
        "replaced_ast_copy_diagnostic",
        "replaced_trace_copy_diagnostic",
        "reflectively_modified_exact_object_ast_diagnostic",
    ):
        assert audit[key] == "LINEAGE_PROVENANCE_FAILURE"


def test_exact_issued_object_with_modified_trace_is_incorrectly_accepted() -> None:
    audit = _review()["issued_lineage_audit"]
    assert audit["issuance_registry_snapshots_provenance_trace"] is False
    assert audit["reflectively_modified_exact_object_trace_diagnostic"] == "NO_DIAGNOSTIC"
    assert audit["reflectively_modified_exact_object_trace_was_accepted"] is True


def test_only_one_of_three_positive_controls_uses_full_production_path() -> None:
    audit = _review()["control_path_and_atomicity_audit"]["positive_controls"]
    assert audit["reported_count"] == audit["passed_count"] == 3
    assert audit["full_production_path_count"] == 1
    assert audit["all_use_full_production_path"] is False
    assert [row["full_production_path"] for row in audit["rows"]] == [True, False, False]


def test_only_thirteen_of_fourteen_negative_controls_are_one_field_mutations() -> None:
    audit = _review()["control_path_and_atomicity_audit"]["atomic_negative_controls"]
    assert audit["reported_count"] == audit["exact_diagnostic_passed_count"] == 14
    assert audit["independently_atomic_count"] == 13
    assert audit["all_single_change"] is False
    map_row = next(row for row in audit["rows"] if row["mutation_id"] == "ADV_OBJECT_MAP_MUTATED")
    assert map_row["reported_changed_premise_count"] == 1
    assert map_row["independently_observed_changed_field_count"] == 2
    assert map_row["changed_fields"] == ["RewriteRule.target", "RewriteRule.meaning"]


def test_eight_convention_controls_remain_exact_and_preoutput() -> None:
    audit = _review()["control_path_and_atomicity_audit"]["convention_controls"]
    assert audit == {
        "all_failed_before_output": True,
        "passed_count": 8,
        "reported_count": 8,
    }


def test_exact_three_terminal_blocking_findings_are_confirmed() -> None:
    blocked = _review()["blocking_findings"]
    assert blocked["count"] == 3
    assert blocked["all_confirmed"] is True
    assert [row["finding_id"] for row in blocked["findings"]] == [
        "ISSUED_PROVENANCE_TRACE_MUTATION_NOT_REVALIDATED",
        "TWO_OF_THREE_POSITIVE_CONTROLS_BYPASS_FULL_PRODUCTION_PATH",
        "OBJECT_MAP_NEGATIVE_CONTROL_CHANGES_TARGET_AND_MEANING_FIELDS",
    ]


def test_terminal_closeout_retains_policy_but_defers_automated_restoration() -> None:
    closeout = _review()["terminal_lane_closeout"]
    assert closeout == {
        "lane": "SR_AUTOMATED_CONSTANT_RESTORATION_TOOLING",
        "status": "CLOSED",
        "classification": "BLOCKED_SR_RESTORATION_TOOLING_CONTRACT",
        "physical_convention_policy_retained": True,
        "automated_restoration_deferred": True,
        "v4_prepared": False,
        "v4_automatically_authorized": False,
        "fresh_full_project_priority_decision_required_for_v4": True,
        "authority_returned_to_full_project_priority_map": True,
    }


def test_review_authorizes_no_restoration_migration_or_v4() -> None:
    scope = _review()["scope_and_authorization"]
    assert scope["packet_v3_accepted"] is False
    assert scope["bounded_six_surface_restoration_authorized"] is False
    assert scope["authoritative_equation_restoration_executed"] is False
    assert scope["scientific_equation_migration_executed"] is False
    assert scope["automatic_v4_authorized"] is False
    assert scope["r13_reopened"] is False
    assert scope["automation_created"] is False
    assert scope["full_project_priority_selection_authorized"] is True
    assert _review()["hard_stop"]["automatic_successor_packet_authorized"] is False

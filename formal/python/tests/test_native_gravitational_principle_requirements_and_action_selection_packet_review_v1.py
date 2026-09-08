from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import (
    native_gravitational_principle_requirements_and_action_selection_packet_review_v1 as review,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / review.REPORT_RELATIVE_PATH


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _report() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_review_regenerates_exactly_and_deterministically() -> None:
    assert review.artifact_bytes() == review.artifact_bytes() == REPORT_PATH.read_bytes()


def test_review_preserves_every_frozen_v1_input_byte() -> None:
    before = {
        path: _sha256(REPO_ROOT / path)
        for path in review.AUTHORITY_AND_PACKET_HASHES
    }
    review.build_review()
    after = {
        path: _sha256(REPO_ROOT / path)
        for path in review.AUTHORITY_AND_PACKET_HASHES
    }
    assert before == after == review.AUTHORITY_AND_PACKET_HASHES


def test_review_blocks_v1_and_authorizes_only_v2_preparation() -> None:
    report = _report()
    assert report["target"] == review.TARGET
    assert report["verdict"] == review.VERDICT
    assert report["primary_diagnostic"] == review.PRIMARY_DIAGNOSTIC
    assert report["selected_next_target"] == review.SELECTED_NEXT_TARGET
    assert report["selected_next_target_kind"] == (
        "PREPARATION_ONLY_REQUIREMENTS_ACTION_SELECTION_PACKET_V2_REPAIR"
    )


def test_static_ten_row_class_inventory_is_retained() -> None:
    audit = _report()["static_statement_class_audit"]
    assert audit["status"] == "PASS"
    assert audit["requirement_count"] == 10
    assert audit["exact_static_class_count"] == 10
    assert audit["requirement_ids"] == review.EXPECTED_REQUIREMENT_IDS


def test_production_source_class_authority_can_be_spoofed() -> None:
    audit = _report()["production_statement_class_enforcement_audit"]
    assert audit["status"] == "FAIL"
    assert audit["diagnostic"] == (
        "STATEMENT_CLASS_AUTHORITY_BINDING_NOT_ENFORCED"
    )
    assert audit["expected"] == "PRECHECK_FAILURE_BEFORE_MATRIX_EVALUATION"
    assert audit["observed_status"] == "SCIENTIFIC_OUTCOME_COMPUTED"
    assert audit["observed_scientific_outcome"] == (
        "CURRENT_REQUIREMENTS_COLLAPSE_TO_STANDARD_GR"
    )
    assert audit["observed_supplied_exclusion_trace"] == [{
        "family_id": "F_EH",
        "requirement_id": "R4_DIFF_COVARIANCE",
    }]


def test_affirmative_and_equivalence_cells_need_no_bound_evidence() -> None:
    audit = _report()["matrix_cell_evidence_audit"]
    assert audit["status"] == "FAIL"
    assert audit["diagnostic"] == "MATRIX_CELL_EVIDENCE_BINDING_NOT_ENFORCED"
    assert audit["affirmative_observed_status"] == "SCIENTIFIC_OUTCOME_COMPUTED"
    assert audit["equivalence_observed_status"] == "SCIENTIFIC_OUTCOME_COMPUTED"
    assert audit["affirmative_observed_outcome"] == (
        "CURRENT_REQUIREMENTS_COLLAPSE_TO_STANDARD_GR"
    )
    assert audit["equivalence_observed_outcome"] == (
        "CURRENT_REQUIREMENTS_COLLAPSE_TO_STANDARD_GR"
    )


def test_forbidden_equivalence_proof_token_is_accepted() -> None:
    audit = _report()["equivalence_policy_audit"]
    assert audit["status"] == "FAIL"
    assert audit["diagnostic"] == "EQUIVALENCE_PROOF_POLICY_NOT_ENFORCED"
    assert audit["submitted_proof_class"] == (
        "FORBIDDEN_DIFFERENT_PROPAGATING_MODES"
    )
    assert audit["observed_status"] == "SCIENTIFIC_OUTCOME_COMPUTED"
    assert audit["observed_affirmative_classes"] == ["F_EH"]
    assert audit["observed_scientific_outcome"] == (
        "CURRENT_REQUIREMENTS_COLLAPSE_TO_STANDARD_GR"
    )


def test_undecidable_member_is_erased_at_equivalence_class_level() -> None:
    audit = _report()["undecidable_propagation_audit"]
    assert audit["status"] == "FAIL"
    assert audit["diagnostic"] == "UNDECIDABLE_EQUIVALENCE_CLASS_ERASED"
    assert audit["observed_unresolved_family_ids"] == ["F_FR"]
    assert audit["observed_unresolved_equivalence_classes"] == []
    assert audit["observed_scientific_outcome"] == (
        "CURRENT_REQUIREMENTS_COLLAPSE_TO_STANDARD_GR"
    )


def test_viable_distinctiveness_no_go_branch_is_unreachable() -> None:
    audit = _report()["terminal_no_go_audit"]
    assert audit["status"] == "FAIL"
    assert audit["diagnostic"] == (
        "VIABLE_DISTINCTIVENESS_NO_GO_BRANCH_UNREACHABLE"
    )
    assert audit["possible_equivalence_classes"] == ["F_FR"]
    assert audit["expected_scientific_outcome"] == (
        "NO_GO_UNDER_MINIMAL_METRIC_LOCAL_ASSUMPTIONS"
    )
    assert audit["observed_scientific_outcome"] == (
        "ACTION_FAMILY_UNDERDETERMINED"
    )


def test_existing_eight_controls_and_two_probes_still_share_production_path() -> None:
    audit = _report()["shared_path_control_audit"]
    assert audit["status"] == "PASS"
    assert audit["control_count"] == audit["control_pass_count"] == 8
    assert audit["boundary_probe_count"] == audit["boundary_probe_pass_count"] == 2
    assert audit["all_used_shared_entry_point"] is True
    assert audit["production_entry_point_id"] == "evaluate_analysis_v1"


def test_exactly_five_blocking_defect_classes_are_recorded() -> None:
    report = _report()
    findings = report["findings"]
    assert findings["finding_count"] == findings["blocking_count"] == 5
    assert [row["diagnostic"] for row in findings["rows"]] == [
        "STATEMENT_CLASS_AUTHORITY_BINDING_NOT_ENFORCED",
        "MATRIX_CELL_EVIDENCE_BINDING_NOT_ENFORCED",
        "EQUIVALENCE_PROOF_POLICY_NOT_ENFORCED",
        "UNDECIDABLE_EQUIVALENCE_CLASS_ERASED",
        "VIABLE_DISTINCTIVENESS_NO_GO_BRANCH_UNREACHABLE",
    ]
    gates = report["review_gates"]
    assert gates["gate_count"] == 11
    assert gates["pass_count"] == 6
    assert gates["failure_count"] == 5


def test_real_analysis_and_downstream_physics_remain_unexecuted() -> None:
    scope = _report()["scope"]
    assert scope["independent_v1_review_executed"] is True
    assert scope["v1_block_recorded"] is True
    assert scope["real_matrix_cells_computed"] == 0
    for key, value in scope.items():
        if key not in {
            "independent_v1_review_executed",
            "v1_block_recorded",
            "real_matrix_cells_computed",
        }:
            assert value is False, key
    retained = _report()["retained_results"]
    assert retained["real_matrix_cells"] == "0_OF_70"
    assert retained["native_candidate_readiness"] == (
        "BLOCKED_NO_NATIVE_GRAVITATIONAL_PRINCIPLE"
    )


def test_human_review_records_blockers_repair_boundary_and_nonclaims() -> None:
    text = (REPO_ROOT / review.REVIEW_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        review.VERDICT,
        "0 / 70",
        "STATEMENT_CLASS_AUTHORITY_BINDING_NOT_ENFORCED",
        "MATRIX_CELL_EVIDENCE_BINDING_NOT_ENFORCED",
        "EQUIVALENCE_PROOF_POLICY_NOT_ENFORCED",
        "UNDECIDABLE_EQUIVALENCE_CLASS_ERASED",
        "VIABLE_DISTINCTIVENESS_NO_GO_BRANCH_UNREACHABLE",
        "does not",
        "create V2 now",
        review.SELECTED_NEXT_TARGET,
    ):
        assert token in text

from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import (
    sr_pillar_coordinate_convention_and_constant_restoration_packet_review_v2 as review_v2,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / review_v2.REPORT_RELATIVE_PATH


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _review() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_review_regenerates_exactly_and_deterministically() -> None:
    first = review_v2.artifact_bytes()
    second = review_v2.artifact_bytes()
    assert first == second == REPORT_PATH.read_bytes()


def test_review_preserves_every_frozen_v2_input_byte() -> None:
    before = {path: _sha256(REPO_ROOT / path) for path in review_v2.FROZEN_INPUT_HASHES}
    review_v2.build_review()
    after = {path: _sha256(REPO_ROOT / path) for path in review_v2.FROZEN_INPUT_HASHES}
    assert before == after == review_v2.FROZEN_INPUT_HASHES


def test_review_blocks_v2_on_exact_first_canonicalization_diagnostic() -> None:
    review = _review()
    assert review["target"] == review_v2.CONSUMED_TARGET
    assert review["verdict"] == review_v2.VERDICT
    assert review["first_diagnostic"] == review_v2.FIRST_DIAGNOSTIC
    assert review["selected_next_target"] == review_v2.SELECTED_NEXT_TARGET
    assert review["hard_stop"]["packet_accepted"] is False


def test_all_six_exact_authoritative_source_bindings_still_match() -> None:
    audit = _review()["retained_findings"]["exact_source_content_bindings_audit"]
    assert audit["required_count"] == 6
    assert audit["passed_count"] == 6
    assert audit["passed"] is True
    assert all(row["claim_class_increased"] is False for row in audit["rows"])


def test_oracle_is_independent_and_wrong_target_fails() -> None:
    oracle = _review()["retained_findings"]["oracle_map_and_shared_path_audit"]["oracle_independence"]
    assert oracle == {
        "computed_ast_unchanged": True,
        "wrong_target_rejected": True,
    }


def test_missing_mutated_and_extra_maps_are_rejected() -> None:
    maps = _review()["retained_findings"]["oracle_map_and_shared_path_audit"]["map_enforcement"]
    assert maps["underapplication_rejected"] is True
    assert maps["mutation_rejected"] is True
    assert maps["overapplication_rejected"] is True


def test_six_valid_examples_and_eight_preflight_controls_use_production_paths() -> None:
    audit = _review()["retained_findings"]["oracle_map_and_shared_path_audit"]
    assert audit["actual_production_functions_called"] == ["restore", "suppress"]
    assert audit["valid_production_round_trips"] == {
        "all_use_forward_lineage": True,
        "passed_count": 6,
        "required_count": 6,
    }
    assert audit["convention_preflight_controls"] == {
        "all_failed_before_output": True,
        "passed_count": 8,
        "required_count": 8,
    }


def test_canonicalizer_preserves_only_five_of_six_required_semantics() -> None:
    audit = _review()["canonicalization_soundness_audit"]
    assert audit["required_count"] == 6
    assert audit["passed_count"] == 5
    assert audit["passed"] is False
    assert audit["raw_gamma_D_differs_from_raw_D_gamma"] is True
    assert audit["canonical_gamma_D_equals_canonical_D_gamma"] is True
    assert audit["safety_checks"]["operator_order_preserved"] is False
    assert all(
        value
        for key, value in audit["safety_checks"].items()
        if key != "operator_order_preserved"
    )


def test_manual_public_result_can_forge_forward_lineage_and_pass_suppression() -> None:
    audit = _review()["forward_lineage_origin_audit"]
    assert audit["forward_restore_called"] is False
    assert audit["public_transform_result_constructor_used"] is True
    assert audit["lineage_reconstructed_from_public_fields"] is True
    assert audit["manual_result_accepted_by_suppress"] is True
    assert audit["manual_result_inverse_passed"] is True
    assert audit["origin_authentication_passed"] is False


def test_only_eight_of_ten_reported_adversarial_rows_are_atomic_mutations() -> None:
    audit = _review()["adversarial_control_atomicity_audit"]
    assert audit["reported_control_count"] == 10
    assert audit["atomic_single_premise_count"] == 8
    assert audit["forced_summary_actual_changed_premises"] == 2
    assert audit["zero_mutation_positive_row_counted_as_adversarial"] is True
    assert audit["all_adversarial_controls_atomic"] is False


def test_exact_three_blocking_findings_are_reproduced() -> None:
    blocked = _review()["blocking_findings"]
    assert blocked["count"] == 3
    assert blocked["all_confirmed"] is True
    assert [row["finding_id"] for row in blocked["findings"]] == [
        "CANONICALIZER_ERASES_NONCOMMUTATIVE_OPERATOR_ORDER",
        "FORWARD_LINEAGE_FORGEABLE_FROM_PUBLIC_RESULT_FIELDS",
        "PRODUCTION_ADVERSARIAL_CONTROL_ATOMICITY_MISREPORTED",
    ]


def test_v3_contract_is_narrow_and_does_not_reopen_physical_conventions() -> None:
    review = _review()
    contract = review["v3_contract"]
    assert len(contract) == 5
    joined = "\n".join(contract)
    for token in (
        "operator order",
        "opaque restore-issued custody token",
        "one-premise mutation",
        "forced-summary",
        "without adding equations",
    ):
        assert token in joined
    assert review["scope_and_authorization"]["physical_convention_reopened"] is False


def test_review_authorizes_no_restoration_migration_or_adjacent_work() -> None:
    scope = _review()["scope_and_authorization"]
    assert scope == {
        "packet_v2_accepted": False,
        "bounded_six_surface_restoration_authorized": False,
        "authoritative_equation_restoration_executed": False,
        "scientific_equation_migration_executed": False,
        "historical_artifacts_modified": False,
        "repository_wide_migration_authorized": False,
        "physical_convention_reopened": False,
        "r13_reopened": False,
        "external_comparator_activated": False,
        "automation_created": False,
        "only_bounded_v3_packet_preparation_authorized": True,
    }

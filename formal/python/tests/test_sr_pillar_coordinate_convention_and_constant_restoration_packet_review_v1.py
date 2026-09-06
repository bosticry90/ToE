from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.tools import (
    sr_pillar_coordinate_convention_and_constant_restoration_packet_review_v1 as review_v1,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_PATH = REPO_ROOT / review_v1.REPORT_RELATIVE_PATH


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _review() -> dict[str, object]:
    value = json.loads(REPORT_PATH.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_review_regenerates_exactly_and_deterministically() -> None:
    first = review_v1.artifact_bytes()
    second = review_v1.artifact_bytes()
    assert first == second == REPORT_PATH.read_bytes()


def test_review_preserves_every_frozen_v1_input_byte() -> None:
    before = {
        path: _sha256(REPO_ROOT / path) for path in review_v1.FROZEN_INPUT_HASHES
    }
    review_v1.build_review()
    after = {
        path: _sha256(REPO_ROOT / path) for path in review_v1.FROZEN_INPUT_HASHES
    }
    assert before == after == review_v1.FROZEN_INPUT_HASHES


def test_review_blocks_v1_on_the_exact_first_production_diagnostic() -> None:
    review = _review()
    assert review["target"] == review_v1.CONSUMED_TARGET
    assert review["verdict"] == review_v1.VERDICT
    assert review["first_diagnostic"] == review_v1.FIRST_DIAGNOSTIC
    assert review["selected_next_target"] == review_v1.SELECTED_NEXT_TARGET
    assert review["hard_stop"]["packet_accepted"] is False


def test_independent_electromagnetic_derivation_passes_all_seven_checks() -> None:
    audit = _review()["independent_positive_findings"]["electromagnetic_audit"]
    assert audit["required_count"] == 7
    assert audit["passed_count"] == 7
    assert audit["passed"] is True
    assert all(audit["checks"].values())


def test_independent_quantum_gauge_sign_and_unit_audit_passes() -> None:
    audit = _review()["independent_positive_findings"][
        "quantum_gauge_sign_and_units_audit"
    ]
    assert audit["required_count"] == 7
    assert audit["passed_count"] == 7
    assert audit["passed"] is True
    assert "opposite phase-gradient term" in audit["gauge_covariance_derivation"]


def test_stress_component_and_flat_curved_adapter_scope_passes() -> None:
    audit = _review()["independent_positive_findings"][
        "stress_energy_and_derivative_adapter_audit"
    ]
    assert audit["required_count"] == 10
    assert audit["passed_count"] == 10
    assert audit["passed"] is True


def test_all_six_exact_source_content_bindings_independently_match() -> None:
    audit = _review()["independent_positive_findings"][
        "exact_source_content_bindings_audit"
    ]
    assert audit["required_count"] == 6
    assert audit["passed_count"] == 6
    assert audit["passed"] is True
    assert all(row["original_claim_class_preserved"] for row in audit["rows"])


def test_adversarial_probe_proves_round_trip_is_object_map_insensitive() -> None:
    probe = _review()["production_contract_audit"]["six_equation_probe"]
    assert probe["declared_object_map_used_by_restore"] is False
    assert probe["declared_object_map_used_by_suppress"] is False
    assert probe["invalid_object_map_mutation_ignored"] is True
    assert probe["deliberately_wrong_si_target_still_reports_round_trip_pass"] is True


def test_quantum_round_trip_is_self_assignment_not_a_transform() -> None:
    probe = _review()["production_contract_audit"]["quantum_probe"]
    assert probe["restored_assignment"] == "si"
    assert probe["suppressed_assignment"] == "natural"
    assert probe["passed_is_hardcoded_true"] is True
    assert probe["semantic_transform_function_called"] is False


def test_matter_exchange_round_trip_ast_is_not_the_exact_bound_source() -> None:
    alignment = _review()["production_contract_audit"]["bound_source_ast_alignment"]
    assert alignment["bound_source_tensor"] == "T_psi"
    assert alignment["round_trip_source_tensor"] == "T_matter"
    assert alignment["explicit_T_psi_to_T_matter_adapter_present"] is False
    assert alignment["exact_bound_source_ast_alignment_passed"] is False


def test_exact_four_blocking_findings_are_concrete_and_reproduced() -> None:
    blocked = _review()["blocking_findings"]
    assert blocked["count"] == 4
    assert blocked["all_confirmed"] is True
    assert [row["finding_id"] for row in blocked["findings"]] == [
        "RESTORATION_FUNCTIONS_DO_NOT_APPLY_DECLARED_OBJECT_MAPS",
        "QUANTUM_ROUND_TRIP_IS_SELF_ASSIGNMENT_WITH_HARDCODED_PASS",
        "MATTER_EXCHANGE_ROUND_TRIP_AST_NOT_EXACT_BOUND_SOURCE",
        "NEGATIVE_CONTROL_PREFLIGHT_NOT_ENFORCED_BY_RESTORATION_ENTRY_POINTS",
    ]


def test_v2_contract_is_limited_to_production_contract_repairs() -> None:
    review = _review()
    contract = review["v2_contract"]
    assert len(contract) == 5
    joined = "\n".join(contract)
    for token in (
        "actually consume the frozen object maps",
        "remove self-assignment",
        "T_psi",
        "validate-then-restore",
        "without adding equations",
    ):
        assert token in joined
    assert review["selected_next_target"].endswith("_packet_v2")


def test_review_authorizes_no_restoration_migration_or_adjacent_work() -> None:
    scope = _review()["scope_and_authorization"]
    assert scope == {
        "packet_v1_accepted": False,
        "bounded_six_surface_restoration_authorized": False,
        "authoritative_equation_restoration_executed": False,
        "scientific_equation_migration_executed": False,
        "historical_artifacts_modified": False,
        "repository_wide_migration_authorized": False,
        "r13_reopened": False,
        "external_comparator_activated": False,
        "automation_created": False,
        "only_bounded_v2_packet_preparation_authorized": True,
    }

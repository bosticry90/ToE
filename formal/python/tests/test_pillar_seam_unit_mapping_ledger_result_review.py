from __future__ import annotations

import ast
import copy
import hashlib
import json
import shutil
import subprocess
import sys
from collections import Counter
from pathlib import Path
from typing import Any

import pytest

from formal.python.tools import pillar_seam_unit_mapping_ledger_result_review as review


EXECUTION_COMMIT = "2d2617950437b7465e6f322b89463d6417d8cf35"
EXECUTION_PARENT = "cfa61bdbb0147a8759f7159ef2588fcaabca472a"
SUCCESS_TARGET = (
    "prepare_pillar_seam_unit_mapping_ledger_blocker_response_route_selection_packet"
)
SUCCESS_TARGET_KIND = (
    "pillar_seam_unit_mapping_ledger_blocker_response_route_selection_packet"
)
SUCCESS_OUTCOME = (
    "PILLAR_SEAM_UNIT_MAPPING_LEDGER_RESULT_REVIEW_ACCEPTS_REPRODUCIBLE_"
    "TWELVE_ROW_BLOCKER_PRESERVING_AUDIT_AND_AUTHORIZES_BLOCKER_RESPONSE_"
    "ROUTE_SELECTION_PACKET_PREPARATION_ONLY"
)
STRICT_OUTCOME = (
    "PILLAR_SEAM_UNIT_MAPPING_LEDGER_RESULT_REVIEW_ACCEPTS_AUDIT_ONLY_"
    "NO_UNIT_CLOSURE_NO_PILLAR_COMPLETION_NO_SEAM_ADMISSIBILITY_"
    "NO_LEVEL4OR5_NO_CK_ACTION_EMBEDDING_NO_CCFT_NO_MASTER_ACTION_PROMOTION"
)
FAILURE_TARGET = (
    "diagnose_pillar_seam_unit_mapping_ledger_v0_reproducibility_mismatch"
)

EXPECTED_EXECUTION_HASHES = {
    "guardrail_sha256": (
        "7fd4e988ea1a3c435247c2427686c2f3d3024a01c179d99fab30a4d027e364cf"
    ),
    "executor_sha256": (
        "c947d2211c0fa62e743dd3f3937473fc1e2671760059a28c332b2ebec4fef9b2"
    ),
    "ledger_sha256": (
        "a441b4764c9a27ba66df1eb9b94789b135db35d29aed5151b7bd4bc29c2de9b0"
    ),
    "manifest_sha256": (
        "7804844617dea99df2c875d144966b0b196b08bbc884c8aa28a4c441bc7836b1"
    ),
    "execution_report_sha256": (
        "9c32106d3220945094a32525ee7f626b32b71146c518a353955974bd386285ec"
    ),
}
EXPECTED_INPUT_HASHES = {
    "readiness_sha256": (
        "6a4273b3f95bca657bbc9dcdbab82d118a8223ab6de55a213374421b560838a1"
    ),
    "scalar_review_sha256": (
        "cca24f7a9d72d035b974a781213235dc7e8f0685a63bb5189ee465b1c3aa17a0"
    ),
    "compendium_sha256": (
        "7a7f9e564fd2e902b731b6ddceb7adb687e854d3a7970462c8ba29b51c05427e"
    ),
    "qcd_context_sha256": (
        "a6ca799b72fa3b1d0324f62bc9914a39e32c810584e86b3900776c05df6ca724"
    ),
}
EXPECTED_EXECUTION_CUSTODY_HASHES = {
    "registry_sha256": (
        "eda451133e8bbfe1ba0e815b29735f874e8b33e61d7fc5085999c4ba38df0543"
    ),
    "maintenance_authority_sha256": (
        "ada2c9c9c4622c64f0ab0fb7033b8e39b790d55a29ee492dd03fea06afc3695b"
    ),
    "maintenance_v2_review_sha256": (
        "5b1505fb722121329a3d0d08dc9fe8d10674ede0ccce9c1b7a2ffed1ef7d3cd6"
    ),
}

EXPECTED_PILLAR_ROWS = (
    ("PILLAR-QFT-units_and_dimensions-v0", "missing", "unit_unknown"),
    ("PILLAR-GR-units_and_dimensions-v0", "partial", "unresolved"),
    ("PILLAR-QM-units_and_dimensions-v0", "missing", "unit_unknown"),
    ("PILLAR-STAT-units_and_dimensions-v0", "missing", "unit_unknown"),
    ("PILLAR-EM-units_and_dimensions-v0", "partial", "unresolved"),
    ("PILLAR-SR-units_and_dimensions-v0", "partial", "unresolved"),
    ("PILLAR-COSMO-units_and_dimensions-v0", "partial", "unresolved"),
)
EXPECTED_SEAM_ROWS = (
    ("SEAM-QFT-GR-unit_map-v0", "missing", "unit_unknown"),
    ("SEAM-QM-STAT-unit_map-v0", "missing", "unit_unknown"),
    ("SEAM-EM-QFT-unit_map-v0", "partial", "unresolved"),
    ("SEAM-SR-COSMO-unit_map-v0", "partial", "unresolved"),
    ("SEAM-GR-QM-unit_map-v0", "missing", "unit_unknown"),
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    assert isinstance(payload, dict)
    return payload


def _copy_execution_chain(tmp_path: Path) -> dict[str, Path]:
    paths = {
        "guardrail_path": tmp_path / "guardrail.json",
        "executor_path": tmp_path / "execution.py",
        "ledger_path": tmp_path / "ledger.json",
        "manifest_path": tmp_path / "manifest.json",
        "execution_report_path": tmp_path / "execution-report.json",
        "readiness_path": tmp_path / "readiness.json",
        "scalar_review_path": tmp_path / "scalar-review.json",
        "compendium_path": tmp_path / "compendium.md",
        "qcd_context_path": tmp_path / "qcd-context.json",
    }
    sources = {
        "guardrail_path": review.GUARDRAIL_PATH,
        "executor_path": review.EXECUTOR_PATH,
        "ledger_path": review.LEDGER_PATH,
        "manifest_path": review.MANIFEST_PATH,
        "execution_report_path": review.EXECUTION_REPORT_PATH,
        "readiness_path": review.READINESS_PATH,
        "scalar_review_path": review.SCALAR_REVIEW_PATH,
        "compendium_path": review.COMPENDIUM_PATH,
        "qcd_context_path": review.QCD_CONTEXT_PATH,
    }
    for role, destination in paths.items():
        shutil.copyfile(sources[role], destination)
    return paths


def test_reviewer_has_no_executor_import_or_validator_dependency() -> None:
    source = review.SCRIPT_PATH.read_text(encoding="utf-8")
    tree = ast.parse(source)
    imported: list[str] = []
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            imported.extend(alias.name for alias in node.names)
        elif isinstance(node, ast.ImportFrom) and node.module:
            imported.append(node.module)
            imported.extend(f"{node.module}.{alias.name}" for alias in node.names)
    assert not any(
        name.endswith("pillar_seam_unit_mapping_ledger_execution")
        for name in imported
    )
    forbidden_helpers = {
        "ledger_validation_failures",
        "run_negative_controls",
        "build_artifacts",
        "validate_ledger",
        "validate_manifest",
        "validate_execution_report",
    }
    called_helpers: set[str] = set()
    for node in ast.walk(tree):
        if not isinstance(node, ast.Call):
            continue
        if isinstance(node.func, ast.Name):
            called_helpers.add(node.func.id)
        elif isinstance(node.func, ast.Attribute):
            called_helpers.add(node.func.attr)
    assert forbidden_helpers.isdisjoint(called_helpers)


def test_execution_commit_hashes_inputs_and_successor_are_strictly_frozen() -> None:
    assert review.EXECUTION_COMMIT == EXECUTION_COMMIT
    assert review.EXECUTION_PARENT == EXECUTION_PARENT
    assert review.EXPECTED_EXECUTION_HASHES == EXPECTED_EXECUTION_HASHES
    assert review.EXPECTED_INPUT_HASHES == EXPECTED_INPUT_HASHES
    assert review.EXPECTED_EXECUTION_CUSTODY_HASHES == (
        EXPECTED_EXECUTION_CUSTODY_HASHES
    )
    assert review.SUCCESS_TARGET == SUCCESS_TARGET
    assert review.SUCCESS_TARGET_KIND == SUCCESS_TARGET_KIND
    assert review.REVIEW_OUTCOME == SUCCESS_OUTCOME
    assert review.REVIEW_STRICT_OUTCOME == STRICT_OUTCOME
    assert review.FAILURE_TARGET == FAILURE_TARGET
    actual = {
        "guardrail_sha256": _sha256(review.GUARDRAIL_PATH),
        "executor_sha256": _sha256(review.EXECUTOR_PATH),
        "ledger_sha256": _sha256(review.LEDGER_PATH),
        "manifest_sha256": _sha256(review.MANIFEST_PATH),
        "execution_report_sha256": _sha256(review.EXECUTION_REPORT_PATH),
    }
    assert actual == EXPECTED_EXECUTION_HASHES


def test_independent_reconstruction_derives_exact_rows_states_and_blockers() -> None:
    reconstructed = review.independent_reconstruct_source_rows()
    pillar_rows = reconstructed["pillar_rows"]
    seam_rows = reconstructed["seam_rows"]
    assert [
        (row["row_id"], row["source_status"], row["guardrail_unit_state"])
        for row in pillar_rows
    ] == list(EXPECTED_PILLAR_ROWS)
    assert [
        (row["row_id"], row["source_status"], row["guardrail_unit_state"])
        for row in seam_rows
    ] == list(EXPECTED_SEAM_ROWS)
    assert reconstructed["pillar_row_count"] == 7
    assert reconstructed["seam_row_count"] == 5
    assert reconstructed["total_row_count"] == 12
    all_rows = pillar_rows + seam_rows
    assert len({row["row_id"] for row in all_rows}) == 12
    assert Counter(row["source_status"] for row in all_rows) == {
        "missing": 6,
        "partial": 6,
    }
    assert Counter(row["guardrail_unit_state"] for row in all_rows) == {
        "unit_unknown": 6,
        "unresolved": 6,
    }
    for row in all_rows:
        state = row["guardrail_unit_state"]
        assert len(row["unresolved_items"]) == 1
        blocker = row["unresolved_items"][0]
        assert blocker["blocker_id"] == f"{row['row_id']}-{state}-blocker"
        assert blocker["state"] == state
        assert blocker["evidence_pointer"] == row["evidence_pointer"]
        assert blocker["reason"]
        assert blocker["required_resolution"]


def test_independent_reconstruction_proves_zero_inventions_explicitly() -> None:
    reconstructed = review.independent_reconstruct_source_rows()
    assert reconstructed["invention_counts"] == {
        "quantity_rows": 0,
        "mapping_rows": 0,
        "nonnull_unit_conventions": 0,
        "dimension_vectors": 0,
        "declared_units": 0,
        "conversion_assumptions": 0,
        "conversion_constants": 0,
        "conversion_maps": 0,
        "restoration_maps": 0,
        "physical_calibrations": 0,
    }
    for row in reconstructed["pillar_rows"]:
        assert row["unit_convention"] is None
        assert row["quantity_rows"] == []
        assert row["conversion_assumptions"] == []
        assert row["adjudication_status"] == (
            f"blocked_{row['guardrail_unit_state']}"
        )
    for row in reconstructed["seam_rows"]:
        assert row["mapping_rows"] == []
        assert row["conversion_constants"] == []
        assert row["compatibility_status"] == (
            f"blocked_{row['guardrail_unit_state']}"
        )


def test_all_sixteen_decisions_are_recomputed_independently() -> None:
    reconstructed = review.independent_reconstruct_source_rows()
    decisions = review.independently_adjudicate(reconstructed)
    assert [row["decision_number"] for row in decisions] == list(range(1, 17))
    assert [row["decision_id"] for row in decisions] == list(review.DECISION_IDS)
    assert len(set(review.DECISION_IDS)) == 16
    assert all(row["passed"] is True for row in decisions)
    assert all(row["source"] == "independent_result_review" for row in decisions)
    # The zero-row schema decisions pass honestly over an empty assignment domain;
    # they do not silently become dimensional-closure evidence.
    vacuous = {
        row["decision_id"]: row["assignment_domain_count"]
        for row in decisions
        if "assignment_domain_count" in row
    }
    assert vacuous
    assert set(vacuous.values()) == {0}


@pytest.mark.parametrize(
    "control_id",
    list(review.CONTROL_EXPECTATIONS),
)
def test_each_of_eight_controls_uses_a_fresh_copy_and_detects_its_defect(
    control_id: str,
) -> None:
    baseline = review.independent_reconstruct_source_rows()
    preserved = copy.deepcopy(baseline)
    result = review.independently_run_one_control(control_id, baseline)
    committed = {
        row["control_id"]: row
        for row in _load(review.LEDGER_PATH)["negative_control_results"]
    }[control_id]
    assert baseline == preserved
    assert result["control_id"] == control_id
    assert result["fresh_deep_copy_used"] is True
    assert result["detected"] is True
    assert result["expected_failure"] == committed["expected_failure"]
    assert result["expected_failed_decision_ids"] == committed[
        "expected_failed_decision_ids"
    ]
    assert result["observed_failed_decision_ids"] == committed[
        "observed_failed_decision_ids"
    ]
    if control_id == "dropped_source_row":
        assert result["subcases"] == committed["subcases"]


def test_all_eight_controls_are_complete_deterministic_and_nonleaking() -> None:
    baseline = review.independent_reconstruct_source_rows()
    preserved = copy.deepcopy(baseline)
    first = review.independently_run_negative_controls(baseline)
    second = review.independently_run_negative_controls(baseline)
    assert baseline == preserved
    assert first == second
    assert len(first) == 8
    assert [row["control_id"] for row in first] == list(
        review.CONTROL_EXPECTATIONS
    )
    assert all(row["fresh_deep_copy_used"] is True for row in first)
    assert all(row["detected"] is True for row in first)
    committed = _load(review.LEDGER_PATH)["negative_control_results"]
    for independent, recorded in zip(first, committed, strict=True):
        assert independent["control_id"] == recorded["control_id"]
        assert independent["expected_failure"] == recorded["expected_failure"]
        assert independent["expected_failed_decision_ids"] == recorded[
            "expected_failed_decision_ids"
        ]
        assert independent["observed_failed_decision_ids"] == recorded[
            "observed_failed_decision_ids"
        ]
        assert independent["fresh_deep_copy_used"] == recorded[
            "fresh_deep_copy_used"
        ]
        assert independent["detected"] == recorded["passed"]


@pytest.mark.parametrize(
    "control_id",
    list(review.CONTROL_EXPECTATIONS),
)
def test_control_mutations_reproduce_the_frozen_schema_exactly(
    monkeypatch: pytest.MonkeyPatch, control_id: str
) -> None:
    baseline = review.independent_reconstruct_source_rows()
    captured: list[dict[str, Any]] = []
    adjudicate = review.independently_adjudicate

    def capture(candidate: dict[str, Any]) -> list[dict[str, Any]]:
        captured.append(copy.deepcopy(candidate))
        return adjudicate(candidate)

    monkeypatch.setattr(review, "independently_adjudicate", capture)
    result = review.independently_run_one_control(control_id, baseline)
    assert result["detected"] is True
    if control_id == "dropped_source_row":
        assert len(captured) == 2
        assert len(captured[0]["pillar_rows"]) == 6
        assert len(captured[0]["seam_rows"]) == 5
        assert len(captured[1]["pillar_rows"]) == 7
        assert len(captured[1]["seam_rows"]) == 4
        assert [row["mutation"] for row in result["subcases"]] == [
            "drop one row from pillar_rows",
            "drop one row from seam_rows",
        ]
        return

    assert len(captured) == 1
    mutated = captured[0]
    if control_id == "duplicate_source_row_id":
        assert mutated["seam_rows"][0]["row_id"] == (
            baseline["pillar_rows"][0]["row_id"]
        )
    elif control_id == "source_status_promotion":
        assert mutated["pillar_rows"][0]["source_status"] == "resolved"
        assert mutated["pillar_rows"][0]["guardrail_unit_state"] == (
            baseline["pillar_rows"][0]["guardrail_unit_state"]
        )
    elif control_id == "missing_evidence_pointer":
        assert mutated["seam_rows"][0]["evidence_pointer"] == ""
        assert mutated["pillar_rows"][0] == baseline["pillar_rows"][0]
    elif control_id == "implicit_natural_unit_conversion":
        assert mutated["pillar_rows"][1]["quantity_rows"] == [
            {
                "assignment_status": "unresolved",
                "declared_unit": "synthetic_negative_control_only",
                "dimension_vector": [0, 0, 0, 0, 0, 0, 0],
                "natural_unit_constants": [],
                "physical_role": "negative-control mutation only",
                "quantity_id": "negative-control-quantity",
                "restoration_map": None,
                "source_pointer": "negative-control://fresh-deep-copy",
                "symbol": "q_control",
                "unit_convention": (
                    "declared_natural_units_with_explicit_constant_restoration_map"
                ),
            }
        ]
    elif control_id == (
        "dimensionless_test_value_promoted_to_physical_calibration"
    ):
        assert mutated["pillar_rows"][1]["quantity_rows"] == [
            {
                "assignment_status": "unresolved",
                "declared_unit": "synthetic_negative_control_only",
                "dimension_vector": [0, 0, 0, 0, 0, 0, 0],
                "physical_calibration_claimed": True,
                "physical_role": "negative-control mutation only",
                "quantity_id": "negative-control-quantity",
                "scale_binding_status": "promoted_to_physical_calibration",
                "source_pointer": "negative-control://fresh-deep-copy",
                "symbol": "q_control",
                "unit_convention": (
                    "dimensionless_numerical_test_units_with_explicit_"
                    "scale_binding_status"
                ),
            }
        ]
    elif control_id == "dimension_vector_mismatch_marked_compatible":
        assert mutated["seam_rows"][2]["mapping_rows"] == [
            {
                "conversion_map": {"kind": "identity_negative_control"},
                "converted_dimensions_match": True,
                "mapping_status": "unresolved",
                "source_dimension_vector": [1, 0, 0, 0, 0, 0, 0],
                "source_quantity_id": "negative-control-source",
                "target_dimension_vector": [0, 1, 0, 0, 0, 0, 0],
                "target_quantity_id": "negative-control-target",
            }
        ]
    elif control_id == "unresolved_assignment_silently_filled":
        assert mutated["pillar_rows"][0]["unresolved_items"] == []
        assert mutated["pillar_rows"][0]["adjudication_status"] == "resolved"


def test_cross_convention_decision_uses_source_and_target_conventions() -> None:
    candidate = review.independent_reconstruct_source_rows()
    candidate["seam_rows"][0]["mapping_rows"] = [
        {
            "conversion_map": None,
            "converted_dimensions_match": False,
            "mapping_status": "unresolved",
            "source_dimension_vector": [1, 0, 0, 0, 0, 0, 0],
            "source_quantity_id": "source-control",
            "source_unit_convention": "SI_base_dimensions",
            "target_dimension_vector": [1, 0, 0, 0, 0, 0, 0],
            "target_quantity_id": "target-control",
            "target_unit_convention": (
                "declared_natural_units_with_explicit_constant_restoration_map"
            ),
        }
    ]
    decisions = {
        row["decision_id"]: row["passed"]
        for row in review.independently_adjudicate(candidate)
    }
    assert decisions[
        "cross_convention_equalities_require_explicit_conversion_maps"
    ] is False


def test_strict_json_and_canonical_execution_bytes() -> None:
    for path in (
        review.GUARDRAIL_PATH,
        review.LEDGER_PATH,
        review.MANIFEST_PATH,
        review.EXECUTION_REPORT_PATH,
    ):
        payload = review.load_strict_json_object(path, style="canonical")
        assert path.read_bytes() == review.canonical_json_bytes(payload)


def test_canonical_and_report_serializers_use_sorted_keys() -> None:
    payload = {
        "z_last": {"z_nested": 2, "a_nested": 1},
        "a_first": 0,
    }
    expected = (
        json.dumps(
            payload,
            indent=2,
            sort_keys=True,
            ensure_ascii=True,
            allow_nan=False,
        )
        + "\n"
    ).encode("utf-8")
    assert review.canonical_json_bytes(payload) == expected
    assert review.report_json_bytes(payload) == expected


def test_strict_parser_rejects_duplicate_nonfinite_bom_and_noncanonical(
    tmp_path: Path,
) -> None:
    duplicate = tmp_path / "duplicate.json"
    duplicate.write_bytes(b'{"a":1,"a":2}\n')
    with pytest.raises(review.DuplicateKeyError):
        review.load_strict_json_object(duplicate, style="canonical")
    nonfinite = tmp_path / "nonfinite.json"
    nonfinite.write_bytes(b'{"a":NaN}\n')
    with pytest.raises(review.NonFiniteJSONError):
        review.load_strict_json_object(nonfinite, style="canonical")
    bom = tmp_path / "bom.json"
    bom.write_bytes(b"\xef\xbb\xbf{}\n")
    with pytest.raises(ValueError, match="BOM"):
        review.load_strict_json_object(bom, style="canonical")
    noncanonical = tmp_path / "noncanonical.json"
    noncanonical.write_bytes(b'{ "a": 1 }\n')
    with pytest.raises(ValueError, match="canonical"):
        review.load_strict_json_object(noncanonical, style="canonical")
    unsorted = tmp_path / "unsorted.json"
    unsorted.write_bytes(
        (json.dumps({"z": 1, "a": 2}, indent=2, sort_keys=False) + "\n").encode(
            "utf-8"
        )
    )
    with pytest.raises(ValueError, match="canonical"):
        review.load_strict_json_object(unsorted, style="canonical")


def test_independent_semantics_reject_invention_even_if_executor_flags_are_true() -> None:
    reconstructed = review.independent_reconstruct_source_rows()
    tampered = copy.deepcopy(reconstructed)
    tampered["all_guardrail_decisions_passed"] = True
    tampered["all_negative_controls_passed"] = True
    tampered["pillar_rows"][0]["quantity_rows"].append(
        {
            "assignment_status": "resolved",
            "declared_unit": "invented",
            "dimension_vector": [0, 0, 0, 0, 0, 0, 0],
            "physical_role": "invented",
            "quantity_id": "invented",
            "source_pointer": "invented",
            "symbol": "invented",
            "unit_convention": "SI_base_dimensions",
        }
    )
    tampered["pillar_rows"][0]["unresolved_items"] = []
    tampered["pillar_rows"][0]["adjudication_status"] = "resolved"
    failed = {
        row["decision_id"]
        for row in review.independently_adjudicate(tampered)
        if row["passed"] is False
    }
    assert "unresolved_unit_assignments_remain_explicit_blockers" in failed


def test_frozen_chain_is_accepted_with_two_fresh_isolated_reproductions() -> None:
    verification = review.verify_execution_result()
    assert verification["accepted"] is True
    assert verification["mismatch_codes"] == []
    assert verification["execution_self_adjudication_trusted"] is False
    assert verification["all_five_execution_hashes_match"] is True
    assert verification["all_four_input_hashes_match"] is True
    assert verification["all_sixteen_independent_decisions_pass"] is True
    assert verification["all_eight_independent_controls_detected"] is True
    fresh = verification["fresh_subprocess_reproduction"]
    assert fresh["run_count"] == 2
    assert fresh["distinct_temporary_directories"] is True
    assert fresh["both_runs_byte_identical"] is True
    assert fresh["fresh_runs_match_repository_artifacts"] is True
    assert fresh["all_frozen_inputs_unchanged"] is True
    assert fresh["repository_execution_artifacts_unchanged"] is True


def test_execution_time_registry_and_maintenance_custody_are_unchanged() -> None:
    verification = review.verify_execution_result(run_subprocesses=False)
    custody = verification["execution_time_custody"]
    assert custody["execution_commit"] == EXECUTION_COMMIT
    assert custody["execution_parent"] == EXECUTION_PARENT
    assert custody["registry_unchanged_from_parent"] is True
    assert custody["maintenance_authority_unchanged_from_parent"] is True
    assert custody["maintenance_v2_review_unchanged_from_parent"] is True
    authority_binding = review.review_time_authority_binding()
    assert authority_binding["role"] == "REVIEW_TIME_AUTHORITY"
    assert authority_binding["current_successor_role"] == "CURRENT_LIVE_AUTHORITY"
    assert authority_binding["equality_with_current_live_authority_required"] is False
    assert custody["registry_sha256"] == (
        EXPECTED_EXECUTION_CUSTODY_HASHES["registry_sha256"]
    )
    assert custody["maintenance_authority_sha256"] == (
        EXPECTED_EXECUTION_CUSTODY_HASHES["maintenance_authority_sha256"]
    )
    assert custody["maintenance_v2_review_sha256"] == (
        EXPECTED_EXECUTION_CUSTODY_HASHES["maintenance_v2_review_sha256"]
    )
    assert custody["maintenance_v2_status"].startswith("B_BLOCKED")
    assert custody["stage_a_authorized"] is False
    assert custody["stage_b_authorized"] is False
    assert custody["prototype_execution_authorized"] is False
    assert custody["versioned_v3_successor_required"] is True


def test_accept_report_freezes_successor_outcomes_and_every_nonclaim() -> None:
    payload = review.build_review_report()
    assert payload["status"] == "accepted_bounded_unit_mapping_ledger"
    assert payload["primary_label"] == "ACCEPT"
    assert payload["accepted"] is True
    assert payload["review_outcome"] == SUCCESS_OUTCOME
    assert payload["strict_review_outcome"] == STRICT_OUTCOME
    assert payload["selected_next_target"] == SUCCESS_TARGET
    assert payload["selected_next_target_kind"] == SUCCESS_TARGET_KIND
    assert payload["execution_commit"] == EXECUTION_COMMIT
    assert payload["verification"]["execution_self_adjudication_trusted"] is False
    assert payload["claim"]["claim_ceiling_level"] == 3
    boundary = payload["boundary"]
    for key in (
        "unit_closure_claimed",
        "dimensional_closure_claimed",
        "pillar_completion_claimed",
        "seam_admissibility_claimed",
        "seam_closure_claimed",
        "physical_calibration_authorized",
        "cross_sector_coupling_claim_authorized",
        "level_4_or_level_5_authorized",
        "C_k_action_embedding_authorized",
        "ccft_resumed",
        "master_action_promoted",
    ):
        assert boundary[key] is False
    assert payload["authority_rotation"]["execution_time_rotation_performed"] is False
    assert payload["authority_rotation"]["review_time_rotation_authorized"] is True


def test_skipped_reproduction_is_blocking_and_preserves_execution() -> None:
    verification = review.verify_execution_result(run_subprocesses=False)
    assert verification["accepted"] is False
    assert "fresh_subprocess_verification_not_run" in verification["mismatch_codes"]
    report = review.build_review_report(run_subprocesses=False)
    assert report["status"] == "blocked_reproducibility_mismatch"
    assert report["primary_label"] == "B-BLOCKED"
    assert report["accepted"] is False
    assert report["selected_next_target"] == FAILURE_TARGET
    assert report["failure_preservation"]["execution_commit_remains_immutable"] is True
    assert report["failure_preservation"]["authority_rotation_authorized"] is False


@pytest.mark.parametrize(
    ("artifact", "expected_code"),
    [
        ("guardrail_path", "guardrail_hash_mismatch"),
        ("executor_path", "executor_hash_mismatch"),
        ("ledger_path", "ledger_hash_mismatch"),
        ("manifest_path", "manifest_hash_mismatch"),
        ("execution_report_path", "execution_report_hash_mismatch"),
    ],
)
def test_each_execution_artifact_is_individually_tamper_evident(
    tmp_path: Path, artifact: str, expected_code: str
) -> None:
    paths = _copy_execution_chain(tmp_path)
    paths[artifact].write_bytes(paths[artifact].read_bytes() + b"tamper")
    verification = review.verify_execution_result(
        **paths, run_subprocesses=False
    )
    assert verification["accepted"] is False
    assert expected_code in verification["mismatch_codes"]


@pytest.mark.parametrize(
    ("artifact", "expected_code"),
    [
        ("readiness_path", "readiness_hash_mismatch"),
        ("scalar_review_path", "scalar_review_hash_mismatch"),
        ("compendium_path", "compendium_hash_mismatch"),
        ("qcd_context_path", "qcd_context_hash_mismatch"),
    ],
)
def test_each_input_hash_tamper_fails_decision_one_and_the_sixteen_aggregate(
    tmp_path: Path, artifact: str, expected_code: str
) -> None:
    paths = _copy_execution_chain(tmp_path)
    path = paths[artifact]
    if path.suffix == ".json":
        payload = _load(path)
        payload["independent_review_negative_control"] = True
        path.write_bytes(review.canonical_json_bytes(payload))
    else:
        path.write_bytes(path.read_bytes() + b"\nindependent-review-negative-control\n")
    verification = review.verify_execution_result(
        **paths, run_subprocesses=False
    )
    decisions = {
        row["decision_id"]: row["passed"]
        for row in verification["independent_decisions"]
    }
    assert verification["accepted"] is False
    assert expected_code in verification["mismatch_codes"]
    assert verification["all_four_input_hashes_match"] is False
    assert decisions["all_four_input_artifact_hashes_match"] is False
    assert verification["all_sixteen_independent_decisions_pass"] is False


def test_semantic_tamper_is_not_masked_by_combined_pass_flags(
    tmp_path: Path,
) -> None:
    paths = _copy_execution_chain(tmp_path)
    ledger = _load(paths["ledger_path"])
    ledger["all_guardrail_decisions_passed"] = True
    ledger["negative_control_results"] = copy.deepcopy(
        _load(review.LEDGER_PATH)["negative_control_results"]
    )
    ledger["pillar_rows"][0]["unresolved_items"] = []
    ledger["pillar_rows"][0]["adjudication_status"] = "resolved"
    paths["ledger_path"].write_bytes(review.canonical_json_bytes(ledger))
    verification = review.verify_execution_result(
        **paths, run_subprocesses=False
    )
    assert verification["accepted"] is False
    assert "independent_row_or_blocker_reconstruction_mismatch" in (
        verification["mismatch_codes"]
    )
    assert verification["execution_self_adjudication_trusted"] is False


def test_review_report_is_canonical_deterministic_and_cli_check_passes() -> None:
    first = review.build_review_report()
    second = review.build_review_report()
    assert first == second
    assert review.report_json_bytes(first) == review.report_json_bytes(second)
    assert review.REVIEW_REPORT_PATH.read_bytes() == review.report_json_bytes(first)
    completed = subprocess.run(
        [
            sys.executable,
            "-m",
            "formal.python.tools.pillar_seam_unit_mapping_ledger_result_review",
            "--check",
        ],
        cwd=review.REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    assert completed.returncode == 0, completed.stderr

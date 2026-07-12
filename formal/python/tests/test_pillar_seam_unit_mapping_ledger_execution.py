from __future__ import annotations

import copy
import hashlib
import json
import subprocess
import sys
from pathlib import Path

import pytest

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import pillar_seam_unit_mapping_ledger_execution as execution
from formal.python.tools import pillar_seam_unit_mapping_ledger_reports as guardrail_reports


REPO_ROOT = find_repo_root(Path(__file__))


def _guardrail() -> dict:
    return json.loads(guardrail_reports.GUARDRAIL_PATH.read_text(encoding="utf-8"))


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _canonical(payload: dict) -> bytes:
    return guardrail_reports.canonical_json_bytes(payload)


def test_ledger_binds_exactly_seven_pillar_and_five_seam_rows() -> None:
    guardrail = _guardrail()
    ledger = execution.build_ledger(guardrail)
    source = guardrail["source_baseline"]

    assert ledger["pillar_row_count"] == 7
    assert ledger["seam_row_count"] == 5
    assert ledger["total_row_count"] == 12
    assert len(ledger["pillar_rows"]) == 7
    assert len(ledger["seam_rows"]) == 5

    expected_pillars = [
        (
            row["row_id"],
            row["pillar_id"],
            row["status"],
            row["evidence_pointer"],
        )
        for row in source["pillar_rows"]
    ]
    observed_pillars = [
        (
            row["row_id"],
            row["pillar_id"],
            row["source_status"],
            row["evidence_pointer"],
        )
        for row in ledger["pillar_rows"]
    ]
    expected_seams = [
        (
            row["row_id"],
            row["seam_id"],
            row["status"],
            row["evidence_pointer"],
        )
        for row in source["seam_rows"]
    ]
    observed_seams = [
        (
            row["row_id"],
            row["seam_id"],
            row["source_status"],
            row["evidence_pointer"],
        )
        for row in ledger["seam_rows"]
    ]

    assert observed_pillars == expected_pillars
    assert observed_seams == expected_seams
    assert {row["source_status"] for row in ledger["pillar_rows"]} == {
        "missing",
        "partial",
    }
    assert {row["source_status"] for row in ledger["seam_rows"]} == {
        "missing",
        "partial",
    }
    assert len(
        {row["row_id"] for row in ledger["pillar_rows"] + ledger["seam_rows"]}
    ) == 12


def test_ledger_invents_no_quantities_or_maps_and_keeps_explicit_blockers() -> None:
    ledger = execution.build_ledger(_guardrail())

    for row in ledger["pillar_rows"]:
        expected_state = (
            "unit_unknown" if row["source_status"] == "missing" else "unresolved"
        )
        assert row["quantity_rows"] == []
        assert row["conversion_assumptions"] == []
        assert row["unit_convention"] is None
        assert row["guardrail_unit_state"] == expected_state
        assert len(row["unresolved_items"]) == 1
        assert row["unresolved_items"][0]["state"] == expected_state
        assert row["unresolved_items"][0]["evidence_pointer"] == row[
            "evidence_pointer"
        ]
        assert row["adjudication_status"] == f"blocked_{expected_state}"
        assert row["evidence_pointer"]

    for row in ledger["seam_rows"]:
        expected_state = (
            "unit_unknown" if row["source_status"] == "missing" else "unresolved"
        )
        assert row["mapping_rows"] == []
        assert row["conversion_constants"] == []
        assert row["guardrail_unit_state"] == expected_state
        assert len(row["unresolved_items"]) == 1
        assert row["unresolved_items"][0]["state"] == expected_state
        assert row["unresolved_items"][0]["evidence_pointer"] == row[
            "evidence_pointer"
        ]
        assert row["compatibility_status"] == f"blocked_{expected_state}"
        assert row["evidence_pointer"]


def test_validator_accepts_the_inventory_and_fails_closed_on_promotion() -> None:
    guardrail = _guardrail()
    ledger = execution.build_ledger(guardrail)

    assert execution.ledger_validation_failures(ledger, guardrail) == []
    assert execution.validate_ledger(ledger, guardrail) is None

    promoted = copy.deepcopy(ledger)
    promoted["pillar_rows"][0]["source_status"] = "resolved"
    failures = execution.ledger_validation_failures(promoted, guardrail)
    assert "source_missing_partial_or_blocked_statuses_are_not_promoted" in failures
    with pytest.raises(ValueError):
        execution.validate_ledger(promoted, guardrail)

    missing_evidence = copy.deepcopy(ledger)
    missing_evidence["seam_rows"][0]["evidence_pointer"] = ""
    failures = execution.ledger_validation_failures(missing_evidence, guardrail)
    assert "all_source_evidence_pointers_are_retained" in failures
    with pytest.raises(ValueError):
        execution.validate_ledger(missing_evidence, guardrail)


def test_ledger_retains_all_sixteen_guardrail_decisions() -> None:
    guardrail = _guardrail()
    ledger = execution.build_ledger(guardrail)

    assert len(ledger["guardrail_decisions"]) == 16
    assert [row["decision_id"] for row in ledger["guardrail_decisions"]] == [
        row["decision_id"] for row in guardrail["guardrail_decisions"]
    ]
    assert {row["decision_id"] for row in ledger["guardrail_decisions"]} == set(
        guardrail_reports.GUARDRAIL_DECISIONS
    )
    assert all(row["required"] is True for row in ledger["guardrail_decisions"])
    assert all(row["passed"] is True for row in ledger["guardrail_decisions"])
    assert ledger["all_guardrail_decisions_passed"] is True


def test_ledger_preserves_every_forbidden_boundary_and_does_not_rotate_target() -> None:
    guardrail = _guardrail()
    ledger = execution.build_ledger(guardrail)

    assert ledger["boundary"] == guardrail["boundary"]
    assert ledger["boundary"]
    assert all(value is False for value in ledger["boundary"].values())
    assert ledger["boundary"]["unit_closure_claimed"] is False
    assert ledger["boundary"]["pillar_completion_claimed"] is False
    assert ledger["boundary"]["seam_admissibility_claimed"] is False
    assert ledger["boundary"]["level_4_or_level_5_authorized"] is False
    assert ledger["boundary"]["C_k_action_embedding_authorized"] is False
    assert ledger["boundary"]["ccft_resumed"] is False
    assert ledger["boundary"]["master_action_promoted"] is False
    assert ledger["selected_next_target"] is None
    assert ledger["selected_next_target_kind"] is None
    assert ledger["successor_selection_status"] == (
        "not_authorized_by_guardrail"
    )
    assert ledger["authority_rotation_executed"] is False
    assert ledger["status"] == (
        "executed_guardrail_passed_with_explicit_unit_blockers"
    )
    assert ledger["ledger_status"] == (
        "complete_bounded_inventory_unit_closure_blocked"
    )
    assert ledger["unit_closure_claimed"] is False
    assert ledger["dimensional_closure_claimed"] is False
    assert ledger["guardrail_decision_count"] == 16
    assert ledger["negative_control_count"] == 8
    assert len(ledger["execution_schema_decisions"]) == 5


def test_all_eight_negative_controls_run_independently_and_detect_mutations() -> None:
    guardrail = _guardrail()
    ledger = execution.build_ledger(guardrail)
    pristine = copy.deepcopy(ledger)

    results = execution.run_negative_controls(ledger, guardrail)

    assert ledger == pristine
    assert results == ledger["negative_control_results"]
    assert len(results) == 8
    assert [row["control_id"] for row in results] == [
        row["control_id"] for row in guardrail["negative_controls"]
    ]
    assert [row["expected_failure"] for row in results] == [
        row["expected_failure"] for row in guardrail["negative_controls"]
    ]
    assert all(row["fresh_deep_copy_used"] is True for row in results)
    assert all(row["passed"] is True for row in results)
    for row in results:
        assert set(row["expected_failed_decision_ids"]) <= set(
            row["observed_failed_decision_ids"]
        )

    dropped = results[0]
    assert len(dropped["subcases"]) == 2
    assert all(row["fresh_deep_copy_used"] is True for row in dropped["subcases"])
    assert all(row["passed"] is True for row in dropped["subcases"])
    assert {
        row["expected_failed_decision_id"] for row in dropped["subcases"]
    } == {
        "exactly_seven_pillar_unit_rows_are_bound",
        "exactly_five_seam_unit_map_rows_are_bound",
    }


def test_builders_are_canonical_deterministic_and_form_an_acyclic_hash_chain() -> None:
    first = execution.build_artifacts()
    second = execution.build_artifacts()

    assert first == second
    ledger, manifest, report = first
    ledger_bytes = _canonical(ledger)
    manifest_bytes = _canonical(manifest)
    report_bytes = _canonical(report)
    assert json.loads(ledger_bytes) == ledger
    assert json.loads(manifest_bytes) == manifest
    assert json.loads(report_bytes) == report

    assert manifest["guardrail_sha256"] == execution.GUARDRAIL_SHA256
    assert manifest["ledger_sha256"] == _sha256(ledger_bytes)
    assert manifest["executor_sha256"] == execution.sha256_path(
        execution.SCRIPT_PATH
    )
    assert len(manifest["input_artifacts"]) == 4
    assert all(row["verified"] is True for row in manifest["input_artifacts"])
    assert report["guardrail_sha256"] == execution.GUARDRAIL_SHA256
    assert report["ledger_sha256"] == _sha256(ledger_bytes)
    assert report["manifest_sha256"] == _sha256(manifest_bytes)
    assert report["executor_sha256"] == manifest["executor_sha256"]

    assert "ledger_sha256" not in ledger
    assert "manifest_sha256" not in ledger
    assert "execution_report_sha256" not in ledger
    assert "manifest_sha256" not in manifest
    assert "execution_report_sha256" not in manifest
    assert "execution_report_sha256" not in report


def test_write_artifacts_uses_exactly_three_authorized_paths(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    observed_paths: list[Path] = []
    monkeypatch.setattr(
        execution,
        "_write_bytes",
        lambda path, raw: observed_paths.append(path),
    )

    ledger, manifest, report = execution.write_artifacts()

    assert observed_paths == [
        execution.LEDGER_PATH,
        execution.MANIFEST_PATH,
        execution.EXECUTION_REPORT_PATH,
    ]
    assert _canonical(ledger)
    assert _canonical(manifest)
    assert _canonical(report)
    assert _guardrail()["outputs_authorized"] == {
        "execution_report": execution.EXECUTION_REPORT_RELATIVE_PATH,
        "ledger": execution.LEDGER_RELATIVE_PATH,
        "manifest": execution.MANIFEST_RELATIVE_PATH,
    }


def test_output_allowlist_rejects_custom_duplicate_and_external_paths(
    tmp_path: Path,
) -> None:
    custom = (
        tmp_path / "ledger.json",
        tmp_path / "manifest.json",
        tmp_path / "report.json",
    )
    with pytest.raises(ValueError, match="allowlist"):
        execution._validate_authorized_output_paths(custom)
    with pytest.raises(ValueError, match="distinct"):
        execution._validate_authorized_output_paths(
            (execution.LEDGER_PATH, execution.LEDGER_PATH, execution.LEDGER_PATH)
        )


def test_report_preserves_decisions_boundaries_and_absent_successor() -> None:
    ledger, manifest, report = execution.build_artifacts()

    assert report["guardrail_decisions"] == ledger["guardrail_decisions"]
    assert len(report["guardrail_decisions"]) == 16
    assert report["all_guardrail_decisions_passed"] is True
    assert report["negative_control_results"] == ledger["negative_control_results"]
    assert report["all_negative_controls_passed"] is True
    assert report["boundary"] == ledger["boundary"]
    assert all(value is False for value in report["boundary"].values())
    assert report["selected_next_target"] is None
    assert report["selected_next_target_kind"] is None
    assert report["successor_selection_status"] == (
        "not_authorized_by_guardrail"
    )
    assert report["authority_rotation_executed"] is False
    assert manifest["selected_next_target"] is None
    assert manifest["selected_next_target_kind"] is None
    assert manifest["authority_rotation_executed"] is False


def test_cli_checks_canonical_paths_and_rejects_output_overrides(
    tmp_path: Path,
) -> None:
    checked = subprocess.run(
        [
            sys.executable,
            "-m",
            "formal.python.tools.pillar_seam_unit_mapping_ledger_execution",
            "--check",
        ],
        cwd=REPO_ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    assert checked.returncode == 0, checked.stdout + checked.stderr

    rejected = subprocess.run(
        [
            sys.executable,
            "-m",
            "formal.python.tools.pillar_seam_unit_mapping_ledger_execution",
            "--ledger-output",
            str(tmp_path / "forbidden.json"),
        ],
        cwd=REPO_ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    assert rejected.returncode == 2
    assert list(tmp_path.iterdir()) == []


def test_main_preflight_failure_writes_nothing(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    before = {
        path: path.read_bytes()
        for path in (
            execution.LEDGER_PATH,
            execution.MANIFEST_PATH,
            execution.EXECUTION_REPORT_PATH,
        )
    }
    monkeypatch.setattr(
        execution,
        "load_guardrail",
        lambda: (_ for _ in ()).throw(ValueError("synthetic preflight failure")),
    )
    assert execution.main([]) == 2
    diagnostic = json.loads(capsys.readouterr().err)
    assert diagnostic["canonical_outputs_written"] is False
    assert diagnostic["selected_next_target"] == guardrail_reports.FAILURE_TARGET
    assert {path: path.read_bytes() for path in before} == before


def test_mid_write_failure_rolls_back_all_canonical_outputs(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    paths = (
        execution.LEDGER_PATH,
        execution.MANIFEST_PATH,
        execution.EXECUTION_REPORT_PATH,
    )
    before = {path: path.read_bytes() for path in paths}
    calls = 0

    def fail_second(path: Path, raw: bytes) -> None:
        nonlocal calls
        calls += 1
        if calls == 1:
            path.write_bytes(b"synthetic partial write")
            return
        raise OSError("synthetic second-write failure")

    monkeypatch.setattr(execution, "_write_bytes", fail_second)
    observed: dict[Path, bytes] = {}
    try:
        with pytest.raises(OSError, match="synthetic second-write failure"):
            execution.write_artifacts()
        observed = {path: path.read_bytes() for path in paths}
    finally:
        for path, raw in before.items():
            path.write_bytes(raw)
    assert observed == before


@pytest.mark.parametrize(
    "mutation",
    [
        lambda p: p.__setitem__("schema_id", "invented"),
        lambda p: p.__setitem__("status", "closed"),
        lambda p: p.__setitem__("ledger_status", "unit_closed"),
        lambda p: p.__setitem__("execution_target", "invented_target"),
        lambda p: p.__setitem__("failure_target", "ignore_mismatch"),
        lambda p: p.__setitem__("packet_result", "promoted"),
        lambda p: p.__setitem__("strict_packet_result", "promoted"),
        lambda p: p.__setitem__("total_row_count", 999),
        lambda p: p.__setitem__("result_review", {"status": "accepted"}),
        lambda p: p.__setitem__("unit_schema", {}),
        lambda p: p["guardrail"].__setitem__("sha256", "0" * 64),
        lambda p: p["pillar_rows"][0]["unresolved_items"][0].__setitem__(
            "state", "resolved"
        ),
        lambda p: p["pillar_rows"][0]["quantity_rows"].append(
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
        ),
        lambda p: p["seam_rows"][0]["mapping_rows"].append(
            {
                "conversion_map": {"kind": "invented"},
                "converted_dimensions_match": True,
                "mapping_status": "resolved",
                "source_dimension_vector": [0, 0, 0, 0, 0, 0, 0],
                "source_quantity_id": "invented-source",
                "target_dimension_vector": [0, 0, 0, 0, 0, 0, 0],
                "target_quantity_id": "invented-target",
            }
        ),
    ],
)
def test_closed_ledger_validator_rejects_metadata_and_science_tampering(
    mutation: object,
) -> None:
    guardrail = _guardrail()
    tampered = copy.deepcopy(execution.build_ledger(guardrail))
    mutation(tampered)  # type: ignore[operator]
    assert execution.ledger_validation_failures(tampered, guardrail)
    with pytest.raises(ValueError):
        execution.validate_ledger(tampered, guardrail)


def test_negative_control_evidence_must_match_fresh_deterministic_rerun() -> None:
    guardrail = _guardrail()
    tampered = execution.build_ledger(guardrail)
    tampered["negative_control_results"][0]["fresh_deep_copy_used"] = False
    with pytest.raises(ValueError, match="fresh deterministic rerun"):
        execution.validate_ledger(tampered, guardrail)


def test_manifest_and_report_validators_reject_closed_schema_tampering() -> None:
    ledger, manifest, report = execution.build_artifacts()
    bad_manifest = copy.deepcopy(manifest)
    bad_manifest["ledger_sha256"] = "0" * 64
    with pytest.raises(ValueError, match="manifest differs"):
        execution.validate_manifest(bad_manifest, ledger)

    bad_report = copy.deepcopy(report)
    bad_report["selected_next_target"] = "invented_review_target"
    with pytest.raises(ValueError, match="execution report differs"):
        execution.validate_execution_report(bad_report, ledger, manifest)


def test_input_hash_tampering_is_rejected_by_the_frozen_decision() -> None:
    guardrail = _guardrail()
    tampered = execution.build_ledger(guardrail)
    tampered["input_artifacts"][0]["actual_sha256"] = "0" * 64
    assert execution.ledger_validation_failures(tampered, guardrail) == [
        "all_four_input_artifact_hashes_match"
    ]
    with pytest.raises(ValueError, match="all_four_input_artifact_hashes_match"):
        execution.validate_ledger(tampered, guardrail)

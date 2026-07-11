from __future__ import annotations

import copy
import json
import shutil
from pathlib import Path
from typing import Any

import pytest

from formal.python.tools import scalar_multi_background_robustness_result_review as review


def _execution_chain_is_frozen() -> bool:
    return (
        all(
            value != review.UNFROZEN_HASH_SENTINEL
            for value in review.EXPECTED_EXECUTION_HASHES.values()
        )
        and all(
            path.is_file()
            for path in (
                review.GUARDRAIL_PATH,
                review.SCRIPT_PATH,
                review.OUTPUT_PATH,
                review.MANIFEST_PATH,
                review.EXECUTION_REPORT_PATH,
            )
        )
    )


def _copy_execution_chain(tmp_path: Path) -> dict[str, Path]:
    paths = {
        "guardrail_path": tmp_path / "guardrail.json",
        "script_path": tmp_path / "calculation.py",
        "output_path": tmp_path / "result.json",
        "manifest_path": tmp_path / "manifest.json",
        "execution_report_path": tmp_path / "execution.json",
    }
    sources = {
        "guardrail_path": review.GUARDRAIL_PATH,
        "script_path": review.SCRIPT_PATH,
        "output_path": review.OUTPUT_PATH,
        "manifest_path": review.MANIFEST_PATH,
        "execution_report_path": review.EXECUTION_REPORT_PATH,
    }
    for key, destination in paths.items():
        shutil.copyfile(sources[key], destination)
    return paths


def _load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _write(path: Path, payload: dict[str, Any], *, compact: bool) -> None:
    encoder = review.canonical_json_bytes if compact else review.report_json_bytes
    path.write_bytes(encoder(payload))


def test_review_local_source_reconstruction_rederives_exact_family() -> None:
    family = review.independent_reconstruct_source_family()
    assert family["source_chain_count"] == 4
    assert family["bound_artifact_count"] == 24
    assert len(family["background_comparison_rows"]) == 4
    assert len(family["comparable_rows"]) == 5
    assert len(family["qualified_source_decisions"]) == 37
    assert len(family["source_local_on_shell_policy_rows"]) == 4
    assert len(family["control_instances"]) == 10
    assert {row["mechanism_class"] for row in family["control_instances"]} == (
        review.CONTROL_MECHANISMS
    )
    assert family["family_minimum_p_min"] == pytest.approx(
        1.9916550282637009
    )
    assert family["family_maximum_off_shell_relative_error"] == pytest.approx(
        0.004010933857743127
    )
    assert family["warped_2plus1_degeneracy_language_isolated"] is True


def test_review_local_adjudication_passes_exactly_sixteen_decisions() -> None:
    decisions = review.independently_adjudicate(
        review.independent_reconstruct_source_family()
    )
    assert [row["decision_number"] for row in decisions] == list(range(1, 17))
    assert [row["decision_id"] for row in decisions] == list(review.DECISION_IDS)
    assert all(row["passed"] is True for row in decisions)


@pytest.mark.parametrize(
    ("control_id", "expected_failed_decision"),
    list(review.TAMPER_EXPECTATIONS.items()),
)
def test_each_review_local_tamper_control_is_isolated_and_detected(
    control_id: str, expected_failed_decision: str
) -> None:
    family = review.independent_reconstruct_source_family()
    candidate = copy.deepcopy(family)
    review._apply_tamper(control_id, candidate)
    decisions = review.independently_adjudicate(candidate)
    failed = [row["decision_id"] for row in decisions if row["passed"] is False]
    assert expected_failed_decision in failed
    assert family != candidate


def test_all_fourteen_review_local_tamper_records_are_deterministic() -> None:
    family = review.independent_reconstruct_source_family()
    first = review.independently_run_tamper_controls(family)
    second = review.independently_run_tamper_controls(family)
    assert first == second
    assert len(first) == 14
    assert [row["control_id"] for row in first] == list(
        review.TAMPER_EXPECTATIONS
    )
    assert all(row["detected"] is True for row in first)


def test_strict_parser_rejects_duplicate_nonfinite_bom_and_noncanonical_bytes(
    tmp_path: Path,
) -> None:
    duplicate = tmp_path / "duplicate.json"
    duplicate.write_bytes(b'{"a":1,"a":2}\n')
    with pytest.raises(review.DuplicateKeyError):
        review.load_strict_json_object(duplicate, style="compact")
    nonfinite = tmp_path / "nonfinite.json"
    nonfinite.write_bytes(b'{"a":NaN}\n')
    with pytest.raises(review.NonFiniteJSONError):
        review.load_strict_json_object(nonfinite, style="compact")
    overflow = tmp_path / "overflow.json"
    overflow.write_bytes(b'{"a":1e999}\n')
    with pytest.raises(review.NonFiniteJSONError):
        review.load_strict_json_object(overflow, style="compact")
    bom = tmp_path / "bom.json"
    bom.write_bytes(b"\xef\xbb\xbf{}\n")
    with pytest.raises(ValueError, match="BOM"):
        review.load_strict_json_object(bom, style="compact")
    noncanonical = tmp_path / "noncanonical.json"
    noncanonical.write_bytes(b'{ "a": 1 }\n')
    with pytest.raises(ValueError, match="canonical"):
        review.load_strict_json_object(noncanonical, style="compact")


def test_unfrozen_hash_sentinel_forces_preserved_blocked_review(tmp_path: Path) -> None:
    if _execution_chain_is_frozen():
        pytest.skip("execution chain has been frozen; sentinel branch is no longer live")
    verification = review.verify_calculation_result(run_subprocesses=False)
    assert verification["accepted"] is False
    assert "expected_execution_hash_not_frozen" in verification["mismatch_codes"]
    payload = review.build_review_report(run_subprocesses=False)
    repeated = review.build_review_report(run_subprocesses=False)
    assert review.report_json_bytes(payload) == review.report_json_bytes(repeated)
    out = tmp_path / "blocked-review.json"
    review.write_review_report(out, payload)
    persisted = review.load_strict_json_object(out, style="report")
    assert persisted["status"] == "blocked_reproducibility_mismatch"
    assert persisted["primary_label"] == "B-BLOCKED"
    assert persisted["accepted_e_repro"] is False
    assert persisted["mismatch_codes"]
    assert persisted["selected_next_target"] == review.FAILURE_TARGET
    assert persisted["failure_preservation"]["execution_commit_remains_immutable"] is True


def test_success_target_and_selection_basis_are_frozen() -> None:
    assert review.SUCCESS_TARGET == (
        "prepare_pillar_seam_unit_mapping_ledger_guardrail_packet"
    )
    assert review.SUCCESS_SELECTION_BASIS == (
        "unit mapping is a hard gate before Level 4/5, physical calibration, "
        "cross-sector coupling, or C_k action embedding"
    )
    assert review.EXECUTION_COMMIT == (
        "f733587fedf78cfa4c2fc3a6ce8c7f63f1885b49"
    )
    assert review.FAILURE_TARGET == (
        "diagnose_calc_scalar_stress_energy_covariant_divergence_identity_multi_"
        "background_robustness_v0_reproducibility_mismatch"
    )
    assert review.EXPECTED_EXECUTION_HASHES["guardrail_sha256"] == (
        "be308d23673273bf2533f25c58280e92845da146b128dc74a7aad345557c5b95"
    )


@pytest.mark.skipif(
    not _execution_chain_is_frozen(), reason="execution commit hashes not frozen yet"
)
def test_independent_review_accepts_frozen_chain_and_two_fresh_runs() -> None:
    verification = review.verify_calculation_result()
    assert verification["accepted"] is True
    assert verification["mismatch_codes"] == []
    assert verification["all_five_artifact_hashes_match"] is True
    assert all(verification["independent_section_matches"].values())
    assert all(
        verification["execution_report_independent_section_matches"].values()
    )
    assert verification["twenty_four_scientific_input_links_match"] is True
    assert verification["execution_self_adjudication_trusted"] is False
    assert verification["all_sixteen_independent_synthesis_decisions_pass"] is True
    assert verification["all_fourteen_independent_tamper_controls_detected"] is True
    summary = verification["independent_summary"]
    assert summary["source_chain_count"] == 4
    assert summary["bound_artifact_count"] == 24
    assert summary["qualified_source_decision_count"] == 37
    assert summary["control_instance_count"] == 10
    assert summary["control_mechanism_count"] == 8
    assert summary["synthesis_decision_count"] == 16
    assert summary["synthesis_tamper_control_count"] == 14
    fresh = verification["fresh_subprocess_reproduction"]
    assert fresh["run_count"] == 2
    assert fresh["distinct_temporary_directories"] is True
    assert fresh["both_runs_byte_identical"] is True
    assert fresh["fresh_runs_match_repository_artifacts"] is True
    assert fresh["all_twenty_four_source_artifacts_unchanged"] is True
    assert fresh["repository_execution_artifacts_unchanged"] is True


@pytest.mark.skipif(
    not _execution_chain_is_frozen(), reason="execution commit hashes not frozen yet"
)
def test_accepted_review_uses_level3_claim_and_unit_ledger_target() -> None:
    payload = review.build_review_report()
    assert payload["status"] == "accepted_level_3_scoped_e_repro"
    assert payload["primary_label"] == "E-REPRO"
    assert payload["accepted_e_repro"] is True
    assert payload["selected_next_target"] == review.SUCCESS_TARGET
    assert payload["selection_basis"] == review.SUCCESS_SELECTION_BASIS
    assert payload["claim"]["claim_ceiling_level"] == 3
    assert payload["claim"]["not_a_theorem"] is True
    assert payload["claim"]["not_a_statistical_generalization"] is True
    assert payload["boundary"]["level_4_or_level_5_claimed"] is False
    assert payload["boundary"]["unit_ledger_status_during_review"] == (
        "queued_non_live_hard_gate"
    )


@pytest.mark.skipif(
    not _execution_chain_is_frozen(), reason="execution commit hashes not frozen yet"
)
@pytest.mark.parametrize(
    ("artifact", "expected_code"),
    [
        ("guardrail_path", "guardrail_hash_mismatch"),
        ("script_path", "calculation_script_hash_mismatch"),
        ("output_path", "calculation_output_hash_mismatch"),
        ("manifest_path", "calculation_manifest_hash_mismatch"),
        ("execution_report_path", "execution_report_hash_mismatch"),
    ],
)
def test_each_execution_artifact_hash_is_individually_tamper_evident(
    tmp_path: Path, artifact: str, expected_code: str
) -> None:
    paths = _copy_execution_chain(tmp_path)
    paths[artifact].write_bytes(paths[artifact].read_bytes() + b"tamper")
    verification = review.verify_calculation_result(
        **paths, run_subprocesses=False
    )
    assert verification["accepted"] is False
    assert expected_code in verification["mismatch_codes"]


@pytest.mark.skipif(
    not _execution_chain_is_frozen(), reason="execution commit hashes not frozen yet"
)
def test_result_decision_and_claim_tamper_cannot_be_masked(tmp_path: Path) -> None:
    paths = _copy_execution_chain(tmp_path)
    payload = _load(paths["output_path"])
    payload["synthesis_decisions"][0]["passed"] = False
    payload["all_decisions_passed"] = True
    payload["claim"]["claim_ceiling_level"] = 4
    _write(paths["output_path"], payload, compact=True)
    verification = review.verify_calculation_result(
        **paths, run_subprocesses=False
    )
    assert "sixteen_synthesis_decision_mismatch" in verification["mismatch_codes"]
    assert (
        "execution_lifecycle_or_claim_boundary_mismatch"
        in verification["mismatch_codes"]
    )


@pytest.mark.skipif(
    not _execution_chain_is_frozen(), reason="execution commit hashes not frozen yet"
)
def test_zero_fill_and_removed_control_are_semantically_rejected(tmp_path: Path) -> None:
    paths = _copy_execution_chain(tmp_path)
    payload = _load(paths["output_path"])
    for row in payload["applicability_typed_local_check_rows"]:
        raw_checks = row["checks"]
        checks = raw_checks.values() if isinstance(raw_checks, dict) else raw_checks
        for check in checks:
            if check["status"] == "not_applicable":
                check["status"] = "passed"
                check["value"] = 0
                break
        else:
            continue
        break
    instances = payload["control_coverage"].get(
        "instances", payload["control_coverage"].get("control_instances")
    )
    instances.pop()
    _write(paths["output_path"], payload, compact=True)
    verification = review.verify_calculation_result(
        **paths, run_subprocesses=False
    )
    assert "applicability_typing_mismatch" in verification["mismatch_codes"]
    assert "control_coverage_or_masking_mismatch" in verification["mismatch_codes"]


@pytest.mark.skipif(
    not _execution_chain_is_frozen(), reason="execution commit hashes not frozen yet"
)
def test_disabling_fresh_process_reproduction_is_blocking() -> None:
    verification = review.verify_calculation_result(run_subprocesses=False)
    assert verification["accepted"] is False
    assert "fresh_subprocess_verification_not_run" in verification["mismatch_codes"]
    report = review.build_review_report(run_subprocesses=False)
    assert report["status"] == "blocked_reproducibility_mismatch"
    assert report["selected_next_target"] == review.FAILURE_TARGET

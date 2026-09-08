from __future__ import annotations

from formal.python.tools import dirac_maxwell_full_zero_mode_pilot_implementation_repair as repair


def test_repair_artifacts_are_current() -> None:
    packet, manifest, report = repair.build_artifacts()
    assert repair.PACKET_PATH.read_bytes() == repair.canonical_json_bytes(packet)
    assert repair.MANIFEST_PATH.read_bytes() == repair.canonical_json_bytes(manifest)
    assert repair.REPORT_PATH.read_bytes() == repair.canonical_json_bytes(report)


def test_repair_is_exactly_the_authorized_identity_defect() -> None:
    packet, _, _ = repair.build_artifacts()
    assert packet["target"] == repair.TARGET
    assert packet["defect"]["diagnostic"] == "REGISTERED_RUN_IDENTITIES_NOT_UNIQUE"
    assert packet["defect"]["scientific_or_numerical_defect"] is False
    assert packet["defect"]["evidence_identity_defect"] is True


def test_role_qualified_records_are_closed_and_unique() -> None:
    packet, _, _ = repair.build_artifacts()
    records = packet["repaired_identity_preview"]
    assert len(records) == len(repair.CALIBRATION_ROLES) == 13
    assert [record["calibration_role"] for record in records] == repair.CALIBRATION_ROLES
    assert len({record["run_record_id"] for record in records}) == len(records)
    assert all(record["run_record_id"] == f"{record['calibration_role']}:{record['execution_id']}" for record in records)
    assert packet["baseline_diagnostics"] == []


def test_four_identity_mutations_are_independently_diagnosed() -> None:
    packet, _, _ = repair.build_artifacts()
    controls = packet["mutation_controls"]
    assert len(controls) == 4
    assert all(control["passed"] for control in controls)
    assert len({control["expected_diagnostic"] for control in controls}) == 4


def test_scientific_and_numerical_surfaces_are_immutable() -> None:
    packet, _, report = repair.build_artifacts()
    unchanged = packet["repair_scope"]["unchanged"]
    assert "all numerical arrays" in unchanged
    assert "all pilot values" in unchanged
    assert "all 12 positive controls" in unchanged
    assert "all 27 negative controls" in unchanged
    assert report["verdict"] == "PREPARED_PENDING_INDEPENDENT_REVIEW"


def test_only_repair_review_is_authorized() -> None:
    packet, _, _ = repair.build_artifacts()
    assert packet["selected_next_target"] == repair.REVIEW_TARGET
    assert packet["post_acceptance_target"] == repair.POST_ACCEPTANCE_TARGET
    assert all(value is False for value in packet["boundary"].values())


def test_prompt_is_preserved() -> None:
    assert repair.PROMPT_DEPENDENCY_ROLE == "DEMOTE_TO_NONBLOCKING_PROVENANCE"

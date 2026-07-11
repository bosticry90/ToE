from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import pillar_seam_unit_mapping_ledger_reports as reports


REPO_ROOT = find_repo_root(Path(__file__))


def _json(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def test_qcd_literature_pressure_records_primary_result_without_promotion() -> None:
    payload = _json(reports.QCD_PRESSURE_PATH)
    source = payload["primary_source"]
    result = payload["measured_result"]

    assert payload["schema_id"] == (
        "QCD_VACUUM_TO_HADRON_SPIN_INFORMATION_TRANSPORT_"
        "LITERATURE_PRESSURE_20260710_v0"
    )
    assert payload["concept_id"] == "qcd_vacuum_to_hadron_spin_information_transport"
    assert payload["provenance_status"] == "primary_article_verified_20260710"
    assert source["doi"] == "10.1038/s41586-025-09920-0"
    assert source["arxiv_id"] == "2506.05499"
    assert result["relative_polarization"] == 0.181
    assert result["statistical_uncertainty"] == 0.035
    assert result["systematic_uncertainty"] == 0.022
    assert result["significance_standard_deviations"] == 4.4
    assert payload["claim_upgrade"] is False
    assert payload["active_lane_interrupted"] is False
    assert payload["selected_as_current_target"] is False
    assert payload["current_live_target_before_intake"] == reports.CURRENT_TARGET
    assert payload["current_live_target_after_intake"] == reports.CURRENT_TARGET
    assert payload["non_authorizing_context_for_unit_ledger"] == {
        "role": "external seam-transport context only",
        "unit_assignments_imported": False,
        "unit_ledger_scope_changed": False,
        "unit_mapping_rows_authorized_by_this_source": 0,
    }


def test_frozen_input_hashes_match_guardrail_constants() -> None:
    assert reports.sha256_path(reports.READINESS_PATH) == reports.EXPECTED_READINESS_SHA256
    assert reports.sha256_path(reports.REVIEW_PATH) == reports.EXPECTED_REVIEW_SHA256
    assert reports.sha256_path(reports.COMPENDIUM_PATH) == reports.EXPECTED_COMPENDIUM_SHA256
    assert reports.sha256_path(reports.QCD_PRESSURE_PATH) == (
        reports.EXPECTED_QCD_PRESSURE_SHA256
    )


def test_guardrail_artifact_is_deterministic_and_canonical() -> None:
    persisted = _json(reports.GUARDRAIL_PATH)
    generated = reports.build_guardrail_packet()

    assert persisted == generated
    assert reports.GUARDRAIL_PATH.read_bytes() == reports.canonical_json_bytes(generated)
    assert persisted["schema_id"] == reports.SCHEMA_ID
    assert persisted["packet_id"] == reports.PACKET_ID
    assert persisted["packet_result"] == reports.PACKET_RESULT
    assert persisted["strict_packet_result"] == reports.STRICT_PACKET_RESULT
    assert persisted["status"] == "prepared_guardrail_only_execution_not_run"


def test_guardrail_binds_exactly_seven_pillar_and_five_seam_rows() -> None:
    payload = _json(reports.GUARDRAIL_PATH)
    baseline = payload["source_baseline"]
    pillar_rows = baseline["pillar_rows"]
    seam_rows = baseline["seam_rows"]

    assert baseline["pillar_row_count"] == 7
    assert baseline["seam_row_count"] == 5
    assert baseline["total_bound_row_count"] == 12
    assert baseline["pillar_status_counts"] == {"missing": 3, "partial": 4}
    assert baseline["seam_status_counts"] == {"missing": 3, "partial": 2}
    assert [
        (row["row_id"], row["pillar_id"], row["status"]) for row in pillar_rows
    ] == list(reports.PILLAR_EXPECTATIONS)
    assert [
        (row["row_id"], row["seam_id"], row["status"]) for row in seam_rows
    ] == list(reports.SEAM_EXPECTATIONS)
    assert len({row["row_id"] for row in pillar_rows + seam_rows}) == 12
    assert all(row["evidence_pointer"] for row in pillar_rows + seam_rows)
    assert all(
        row["guardrail_unit_state"] == (
            "unit_unknown" if row["status"] == "missing" else "unresolved"
        )
        for row in pillar_rows + seam_rows
    )


def test_guardrail_requires_explicit_conventions_dimensions_and_conversions() -> None:
    payload = _json(reports.GUARDRAIL_PATH)
    schema = payload["ledger_schema_contract"]

    assert schema["allowed_unit_conventions"] == [
        "SI_base_dimensions",
        "declared_natural_units_with_explicit_constant_restoration_map",
        "dimensionless_numerical_test_units_with_explicit_scale_binding_status",
    ]
    assert schema["canonical_SI_dimension_basis"] == [
        "mass",
        "length",
        "time",
        "electric_current",
        "temperature",
        "amount_of_substance",
        "luminous_intensity",
    ]
    assert "dimension_vector" in schema["quantity_row_required_fields"]
    assert "conversion_assumptions" in schema["pillar_row_required_fields"]
    assert "conversion_map" in schema["mapping_row_required_fields"]
    assert "converted_dimensions_match" in schema["mapping_row_required_fields"]
    assert [row["state"] for row in schema["typed_unit_states"]] == [
        "resolved",
        "unit_unknown",
        "unresolved",
    ]
    assert "may not be invented" in schema["typed_unit_states"][1]["value_policy"]
    assert "restoration requirements" in schema["typed_unit_states"][2]["value_policy"]
    assert "unresolved" in schema["unresolved_policy"].lower()
    assert "may not invent units" in schema["unresolved_policy"]


def test_guardrail_freezes_sixteen_decisions_and_eight_negative_controls() -> None:
    payload = _json(reports.GUARDRAIL_PATH)
    decisions = payload["guardrail_decisions"]
    controls = payload["negative_controls"]

    assert payload["guardrail_decision_count"] == 16
    assert payload["negative_control_count"] == 8
    assert [row["decision_id"] for row in decisions] == list(
        reports.GUARDRAIL_DECISIONS
    )
    assert all(row["required"] is True for row in decisions)
    assert len({row["control_id"] for row in controls}) == 8
    assert controls == list(reports.NEGATIVE_CONTROLS)


def test_guardrail_rotates_only_to_bounded_ledger_execution() -> None:
    payload = _json(reports.GUARDRAIL_PATH)
    authorization = payload["authorization"]

    assert authorization["consumed_target"] == reports.CURRENT_TARGET
    assert authorization["execution_target"] == reports.EXECUTION_TARGET
    assert authorization["execution_target_kind"] == reports.EXECUTION_TARGET_KIND
    assert payload["selected_next_target"] == reports.EXECUTION_TARGET
    assert payload["selected_next_target_kind"] == reports.EXECUTION_TARGET_KIND
    assert authorization["claim_ceiling_level_retained"] == 3
    assert payload["outputs_authorized"] == {
        "execution_report": (
            "formal/docs/release/PILLAR_SEAM_UNIT_MAPPING_LEDGER_"
            "EXECUTION_20260710_v0.json"
        ),
        "ledger": "formal/output/PILLAR-SEAM-UNIT-MAPPING-LEDGER-v0.json",
        "manifest": "formal/output/PILLAR-SEAM-UNIT-MAPPING-LEDGER-MANIFEST-v0.json",
    }


def test_guardrail_preserves_all_nonpromotion_boundaries() -> None:
    boundary = _json(reports.GUARDRAIL_PATH)["boundary"]
    assert boundary
    assert all(value is False for value in boundary.values())
    assert boundary["unit_closure_claimed"] is False
    assert boundary["pillar_completion_claimed"] is False
    assert boundary["seam_admissibility_claimed"] is False
    assert boundary["seam_closure_claimed"] is False
    assert boundary["qcd_equations_or_parameters_adopted"] is False
    assert boundary["level_4_or_level_5_authorized"] is False
    assert boundary["master_action_promoted"] is False


def test_guardrail_cli_check_succeeds() -> None:
    completed = subprocess.run(
        [
            sys.executable,
            "-m",
            "formal.python.tools.pillar_seam_unit_mapping_ledger_reports",
            "--check",
        ],
        cwd=REPO_ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    assert completed.returncode == 0, completed.stdout + completed.stderr

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
READINESS_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0.json"
)
REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_"
    "MULTI_BACKGROUND_ROBUSTNESS_CALCULATION_RESULT_REVIEW_20260710_v0.json"
)
COMPENDIUM_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "TOE_MATH_PHYSICS_WORK_AND_EQUATIONS_COMPENDIUM_v0.md"
)
QCD_PRESSURE_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QCD_VACUUM_TO_HADRON_SPIN_INFORMATION_TRANSPORT_"
    "LITERATURE_PRESSURE_20260710_v0.json"
)
GUARDRAIL_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PILLAR_SEAM_UNIT_MAPPING_LEDGER_GUARDRAIL_PACKET_20260710_v0.json"
)

EXPECTED_READINESS_SHA256 = (
    "6a4273b3f95bca657bbc9dcdbab82d118a8223ab6de55a213374421b560838a1"
)
EXPECTED_REVIEW_SHA256 = (
    "cca24f7a9d72d035b974a781213235dc7e8f0685a63bb5189ee465b1c3aa17a0"
)
EXPECTED_COMPENDIUM_SHA256 = (
    "7a7f9e564fd2e902b731b6ddceb7adb687e854d3a7970462c8ba29b51c05427e"
)
EXPECTED_QCD_PRESSURE_SHA256 = (
    "a6ca799b72fa3b1d0324f62bc9914a39e32c810584e86b3900776c05df6ca724"
)

SCHEMA_ID = "PILLAR_SEAM_UNIT_MAPPING_LEDGER_GUARDRAIL_PACKET_20260710_v0"
PACKET_ID = "PILLAR_SEAM_UNIT_MAPPING_LEDGER_GUARDRAIL_PACKET_v0"
CURRENT_TARGET = "prepare_pillar_seam_unit_mapping_ledger_guardrail_packet"
EXECUTION_TARGET = "execute_pillar_seam_unit_mapping_ledger_v0"
EXECUTION_TARGET_KIND = "pillar_seam_unit_mapping_ledger_execution"
FAILURE_TARGET = "diagnose_pillar_seam_unit_mapping_ledger_v0_input_or_schema_mismatch"
PACKET_RESULT = (
    "PILLAR_SEAM_UNIT_MAPPING_LEDGER_GUARDRAIL_PACKET_PREPARED_"
    "AUTHORIZES_BOUNDED_TWELVE_ROW_UNIT_MAPPING_LEDGER_CONSTRUCTION_ONLY"
)
STRICT_PACKET_RESULT = (
    "PILLAR_SEAM_UNIT_MAPPING_LEDGER_GUARDRAIL_PACKET_PREPARED_AUDIT_ONLY_"
    "NO_UNIT_CLOSURE_NO_PILLAR_OR_SEAM_ADMISSIBILITY_NO_LEVEL4_OR5_"
    "NO_CK_ACTION_EMBEDDING_NO_MASTER_ACTION_PROMOTION"
)

PILLAR_EXPECTATIONS = (
    ("PILLAR-QFT-units_and_dimensions-v0", "PILLAR-QFT", "missing"),
    ("PILLAR-GR-units_and_dimensions-v0", "PILLAR-GR", "partial"),
    ("PILLAR-QM-units_and_dimensions-v0", "PILLAR-QM", "missing"),
    ("PILLAR-STAT-units_and_dimensions-v0", "PILLAR-STAT", "missing"),
    ("PILLAR-EM-units_and_dimensions-v0", "PILLAR-EM", "partial"),
    ("PILLAR-SR-units_and_dimensions-v0", "PILLAR-SR", "partial"),
    ("PILLAR-COSMO-units_and_dimensions-v0", "PILLAR-COSMO", "partial"),
)
SEAM_EXPECTATIONS = (
    ("SEAM-QFT-GR-unit_map-v0", "SEAM-QFT-GR", "missing"),
    ("SEAM-QM-STAT-unit_map-v0", "SEAM-QM-STAT", "missing"),
    ("SEAM-EM-QFT-unit_map-v0", "SEAM-EM-QFT", "partial"),
    ("SEAM-SR-COSMO-unit_map-v0", "SEAM-SR-COSMO", "partial"),
    ("SEAM-GR-QM-unit_map-v0", "SEAM-GR-QM", "missing"),
)

GUARDRAIL_DECISIONS = (
    "all_four_input_artifact_hashes_match",
    "readiness_authority_schema_and_status_are_preserved",
    "exactly_seven_pillar_unit_rows_are_bound",
    "exactly_five_seam_unit_map_rows_are_bound",
    "all_twelve_source_row_ids_are_unique",
    "all_source_evidence_pointers_are_retained",
    "source_missing_partial_or_blocked_statuses_are_not_promoted",
    "every_quantity_declares_a_unit_convention",
    "every_dimensional_quantity_uses_an_explicit_dimension_vector",
    "natural_unit_reductions_name_constants_and_restoration_maps",
    "dimensionless_numerical_units_are_not_physical_calibration",
    "cross_convention_equalities_require_explicit_conversion_maps",
    "seam_compatibility_requires_matching_converted_dimensions",
    "unresolved_unit_assignments_remain_explicit_blockers",
    "qcd_literature_pressure_remains_non_authorizing_context",
    "all_claim_ceiling_and_nonpromotion_boundaries_are_preserved",
)

NEGATIVE_CONTROLS = (
    {
        "control_id": "dropped_source_row",
        "expected_failure": "exactly_seven_pillar_or_five_seam_rows_bound",
    },
    {
        "control_id": "duplicate_source_row_id",
        "expected_failure": "all_twelve_source_row_ids_are_unique",
    },
    {
        "control_id": "source_status_promotion",
        "expected_failure": "source_statuses_are_not_promoted",
    },
    {
        "control_id": "missing_evidence_pointer",
        "expected_failure": "all_source_evidence_pointers_are_retained",
    },
    {
        "control_id": "implicit_natural_unit_conversion",
        "expected_failure": "natural_unit_restoration_map_required",
    },
    {
        "control_id": "dimensionless_test_value_promoted_to_physical_calibration",
        "expected_failure": "dimensionless_numerical_units_are_noncalibrating",
    },
    {
        "control_id": "dimension_vector_mismatch_marked_compatible",
        "expected_failure": "converted_source_and_target_dimensions_must_match",
    },
    {
        "control_id": "unresolved_assignment_silently_filled",
        "expected_failure": "unresolved_unit_assignments_remain_blocked",
    },
)


def sha256_path(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load_json(path: Path) -> dict[str, Any]:
    with path.open("r", encoding="utf-8") as handle:
        payload = json.load(handle)
    if not isinstance(payload, dict):
        raise ValueError(f"Expected a JSON object: {path}")
    return payload


def canonical_json_bytes(payload: dict[str, Any]) -> bytes:
    return (
        json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=True) + "\n"
    ).encode("utf-8")


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(canonical_json_bytes(payload))


def _verify_frozen_inputs() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    expected = {
        READINESS_PATH: EXPECTED_READINESS_SHA256,
        REVIEW_PATH: EXPECTED_REVIEW_SHA256,
        COMPENDIUM_PATH: EXPECTED_COMPENDIUM_SHA256,
        QCD_PRESSURE_PATH: EXPECTED_QCD_PRESSURE_SHA256,
    }
    mismatches = [
        str(path.relative_to(REPO_ROOT))
        for path, digest in expected.items()
        if not path.exists() or sha256_path(path) != digest
    ]
    if mismatches:
        raise ValueError("Frozen input hash mismatch: " + ", ".join(mismatches))

    readiness = load_json(READINESS_PATH)
    review = load_json(REVIEW_PATH)
    qcd_pressure = load_json(QCD_PRESSURE_PATH)
    if readiness.get("schema_id") != "SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0":
        raise ValueError("Unexpected readiness schema")
    if review.get("selected_next_target") != CURRENT_TARGET:
        raise ValueError("Review does not authorize the current guardrail target")
    if qcd_pressure.get("selected_as_current_target") is not False:
        raise ValueError("QCD literature pressure must remain non-live")
    return readiness, review, qcd_pressure


def _select_rows(
    rows: list[dict[str, Any]],
    expectations: tuple[tuple[str, str, str], ...],
    identity_key: str,
) -> list[dict[str, Any]]:
    by_id = {row["row_id"]: row for row in rows}
    selected: list[dict[str, Any]] = []
    for row_id, identity, status in expectations:
        row = by_id.get(row_id)
        if row is None:
            raise ValueError(f"Missing frozen readiness row: {row_id}")
        if row.get(identity_key) != identity or row.get("status") != status:
            raise ValueError(f"Frozen readiness row changed: {row_id}")
        selected_row = dict(row)
        selected_row["guardrail_unit_state"] = (
            "unit_unknown" if status == "missing" else "unresolved"
        )
        selected.append(selected_row)
    return selected


def build_guardrail_packet() -> dict[str, Any]:
    readiness, review, qcd_pressure = _verify_frozen_inputs()
    pillar_rows = _select_rows(
        readiness["pillar_readiness_rows"], PILLAR_EXPECTATIONS, "pillar_id"
    )
    seam_rows = _select_rows(
        readiness["seam_readiness_rows"], SEAM_EXPECTATIONS, "seam_id"
    )
    all_rows = pillar_rows + seam_rows
    if len({row["row_id"] for row in all_rows}) != 12:
        raise ValueError("The twelve frozen source row ids must be unique")

    return {
        "authorization": {
            "claim_ceiling_level_retained": 3,
            "consumed_target": CURRENT_TARGET,
            "execution_target": EXECUTION_TARGET,
            "execution_target_kind": EXECUTION_TARGET_KIND,
            "failure_target": FAILURE_TARGET,
            "selection_basis": (
                "unit mapping is a hard gate before Level 4/5, physical "
                "calibration, cross-sector coupling, or C_k action embedding"
            ),
        },
        "boundary": {
            "C_k_action_embedding_authorized": False,
            "arbitrary_missing_unit_assignments_authorized": False,
            "ccft_resumed": False,
            "cross_sector_coupling_claim_authorized": False,
            "dimensionless_numerical_values_physically_calibrated": False,
            "level_4_or_level_5_authorized": False,
            "master_action_promoted": False,
            "physical_calibration_authorized": False,
            "pillar_completion_claimed": False,
            "qcd_equations_or_parameters_adopted": False,
            "seam_admissibility_claimed": False,
            "seam_closure_claimed": False,
            "unit_closure_claimed": False,
        },
        "captured_at_utc": "2026-07-10T00:00:00Z",
        "determinism_contract": {
            "canonical_json": "UTF-8, sorted keys, indent=2, terminal newline",
            "execution_must_emit_manifest": True,
            "execution_must_preserve_all_input_hashes": True,
            "execution_must_run_each_negative_control_independently": True,
            "execution_must_write_only_declared_outputs": True,
        },
        "guardrail_decision_count": len(GUARDRAIL_DECISIONS),
        "guardrail_decisions": [
            {"decision_id": decision_id, "required": True}
            for decision_id in GUARDRAIL_DECISIONS
        ],
        "input_artifacts": [
            {
                "artifact_id": "SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0",
                "path": str(READINESS_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
                "role": "frozen pillar and seam readiness row authority",
                "sha256": EXPECTED_READINESS_SHA256,
            },
            {
                "artifact_id": review["review_id"],
                "path": str(REVIEW_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
                "role": "authorization and retained Level 3 claim ceiling",
                "sha256": EXPECTED_REVIEW_SHA256,
            },
            {
                "artifact_id": "TOE_MATH_PHYSICS_WORK_AND_EQUATIONS_COMPENDIUM_v0",
                "path": str(COMPENDIUM_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
                "role": "read-only equation inventory; no equation or unit adoption",
                "sha256": EXPECTED_COMPENDIUM_SHA256,
            },
            {
                "artifact_id": qcd_pressure["concept_id"],
                "path": str(QCD_PRESSURE_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
                "role": "non-authorizing external seam-transport context only",
                "sha256": EXPECTED_QCD_PRESSURE_SHA256,
            },
        ],
        "ledger_schema_contract": {
            "allowed_unit_conventions": [
                "SI_base_dimensions",
                "declared_natural_units_with_explicit_constant_restoration_map",
                "dimensionless_numerical_test_units_with_explicit_scale_binding_status",
            ],
            "canonical_SI_dimension_basis": [
                "mass",
                "length",
                "time",
                "electric_current",
                "temperature",
                "amount_of_substance",
                "luminous_intensity",
            ],
            "pillar_row_required_fields": [
                "row_id",
                "pillar_id",
                "source_status",
                "evidence_pointer",
                "unit_convention",
                "quantity_rows",
                "conversion_assumptions",
                "unresolved_items",
                "adjudication_status",
            ],
            "quantity_row_required_fields": [
                "quantity_id",
                "symbol",
                "physical_role",
                "unit_convention",
                "dimension_vector",
                "declared_unit",
                "source_pointer",
                "assignment_status",
            ],
            "seam_row_required_fields": [
                "row_id",
                "seam_id",
                "pillar_ids",
                "source_status",
                "evidence_pointer",
                "mapping_rows",
                "conversion_constants",
                "unresolved_items",
                "compatibility_status",
            ],
            "mapping_row_required_fields": [
                "source_quantity_id",
                "target_quantity_id",
                "source_dimension_vector",
                "target_dimension_vector",
                "conversion_map",
                "converted_dimensions_match",
                "mapping_status",
            ],
            "typed_unit_states": [
                {
                    "state": "resolved",
                    "value_policy": (
                        "declared unit and dimension vector must be supported by an "
                        "evidence pointer and an explicit convention"
                    ),
                },
                {
                    "state": "unit_unknown",
                    "value_policy": (
                        "source evidence supplies no supported unit assignment; a "
                        "declared unit or dimension vector may not be invented"
                    ),
                },
                {
                    "state": "unresolved",
                    "value_policy": (
                        "available evidence is partial or conversion-dependent; an "
                        "unresolved reason and restoration requirements remain required"
                    ),
                },
            ],
            "unresolved_policy": (
                "Missing, partial, or otherwise unresolved source status must remain "
                "explicit. The execution "
                "may inventory, classify, and expose blockers but may not invent units, "
                "silently set c or hbar to one, or promote readiness."
            ),
        },
        "negative_control_count": len(NEGATIVE_CONTROLS),
        "negative_controls": list(NEGATIVE_CONTROLS),
        "outputs_authorized": {
            "execution_report": (
                "formal/docs/release/PILLAR_SEAM_UNIT_MAPPING_LEDGER_"
                "EXECUTION_20260710_v0.json"
            ),
            "ledger": "formal/output/PILLAR-SEAM-UNIT-MAPPING-LEDGER-v0.json",
            "manifest": (
                "formal/output/PILLAR-SEAM-UNIT-MAPPING-LEDGER-MANIFEST-v0.json"
            ),
        },
        "packet_id": PACKET_ID,
        "packet_result": PACKET_RESULT,
        "schema_id": SCHEMA_ID,
        "selected_next_target": EXECUTION_TARGET,
        "selected_next_target_kind": EXECUTION_TARGET_KIND,
        "source_baseline": {
            "pillar_row_count": len(pillar_rows),
            "pillar_rows": pillar_rows,
            "pillar_status_counts": dict(
                sorted(Counter(row["status"] for row in pillar_rows).items())
            ),
            "seam_row_count": len(seam_rows),
            "seam_rows": seam_rows,
            "seam_status_counts": dict(
                sorted(Counter(row["status"] for row in seam_rows).items())
            ),
            "total_bound_row_count": len(all_rows),
        },
        "status": "prepared_guardrail_only_execution_not_run",
        "strict_packet_result": STRICT_PACKET_RESULT,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=GUARDRAIL_PATH)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)

    payload = build_guardrail_packet()
    expected = canonical_json_bytes(payload)
    if args.check:
        if not args.output.exists() or args.output.read_bytes() != expected:
            raise SystemExit("guardrail artifact is missing or not deterministic")
    else:
        write_json(args.output, payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

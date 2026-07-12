from __future__ import annotations

import argparse
import copy
import hashlib
import json
import sys
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import pillar_seam_unit_mapping_ledger_reports as contract


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_RELATIVE_PATH = (
    "formal/python/tools/pillar_seam_unit_mapping_ledger_execution.py"
)
LEDGER_RELATIVE_PATH = "formal/output/PILLAR-SEAM-UNIT-MAPPING-LEDGER-v0.json"
MANIFEST_RELATIVE_PATH = (
    "formal/output/PILLAR-SEAM-UNIT-MAPPING-LEDGER-MANIFEST-v0.json"
)
EXECUTION_REPORT_RELATIVE_PATH = (
    "formal/docs/release/PILLAR_SEAM_UNIT_MAPPING_LEDGER_"
    "EXECUTION_20260710_v0.json"
)
LEDGER_PATH = REPO_ROOT / LEDGER_RELATIVE_PATH
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH
EXECUTION_REPORT_PATH = REPO_ROOT / EXECUTION_REPORT_RELATIVE_PATH

GUARDRAIL_SHA256 = (
    "7fd4e988ea1a3c435247c2427686c2f3d3024a01c179d99fab30a4d027e364cf"
)
CAPTURED_AT_UTC = "2026-07-12T00:00:00Z"
LEDGER_SCHEMA_ID = "PILLAR_SEAM_UNIT_MAPPING_LEDGER_v0"
MANIFEST_SCHEMA_ID = "PILLAR_SEAM_UNIT_MAPPING_LEDGER_MANIFEST_v0"
EXECUTION_REPORT_SCHEMA_ID = (
    "PILLAR_SEAM_UNIT_MAPPING_LEDGER_EXECUTION_20260710_v0"
)
EXECUTION_ID = "PILLAR_SEAM_UNIT_MAPPING_LEDGER_EXECUTION_v0"
STATUS = "executed_guardrail_passed_with_explicit_unit_blockers"
LEDGER_STATUS = "complete_bounded_inventory_unit_closure_blocked"
SUCCESSOR_SELECTION_STATUS = "not_authorized_by_guardrail"
PACKET_RESULT = (
    "PILLAR_SEAM_UNIT_MAPPING_LEDGER_EXECUTED_TWELVE_ROW_"
    "BLOCKER_PRESERVING_AUDIT_PENDING_INDEPENDENT_REVIEW"
)
STRICT_PACKET_RESULT = (
    "PILLAR_SEAM_UNIT_MAPPING_LEDGER_EXECUTED_AUDIT_ONLY_"
    "NO_UNIT_CLOSURE_NO_PILLAR_COMPLETION_NO_SEAM_ADMISSIBILITY_"
    "NO_LEVEL4_OR5_NO_CK_ACTION_EMBEDDING_NO_CCFT_"
    "NO_MASTER_ACTION_PROMOTION"
)

PILLAR_REQUIRED_FIELDS = {
    "row_id",
    "pillar_id",
    "source_status",
    "evidence_pointer",
    "unit_convention",
    "quantity_rows",
    "conversion_assumptions",
    "unresolved_items",
    "adjudication_status",
}
QUANTITY_REQUIRED_FIELDS = {
    "quantity_id",
    "symbol",
    "physical_role",
    "unit_convention",
    "dimension_vector",
    "declared_unit",
    "source_pointer",
    "assignment_status",
}
SEAM_REQUIRED_FIELDS = {
    "row_id",
    "seam_id",
    "pillar_ids",
    "source_status",
    "evidence_pointer",
    "mapping_rows",
    "conversion_constants",
    "unresolved_items",
    "compatibility_status",
}
MAPPING_REQUIRED_FIELDS = {
    "source_quantity_id",
    "target_quantity_id",
    "source_dimension_vector",
    "target_dimension_vector",
    "conversion_map",
    "converted_dimensions_match",
    "mapping_status",
}

CONTROL_DECISIONS = {
    "duplicate_source_row_id": ("all_twelve_source_row_ids_are_unique",),
    "source_status_promotion": (
        "source_missing_partial_or_blocked_statuses_are_not_promoted",
    ),
    "missing_evidence_pointer": ("all_source_evidence_pointers_are_retained",),
    "implicit_natural_unit_conversion": (
        "natural_unit_reductions_name_constants_and_restoration_maps",
    ),
    "dimensionless_test_value_promoted_to_physical_calibration": (
        "dimensionless_numerical_units_are_not_physical_calibration",
    ),
    "dimension_vector_mismatch_marked_compatible": (
        "seam_compatibility_requires_matching_converted_dimensions",
    ),
    "unresolved_assignment_silently_filled": (
        "unresolved_unit_assignments_remain_explicit_blockers",
    ),
}

EXECUTION_SCHEMA_DECISIONS = [
    {
        "decision_id": "closed_top_level_schema",
        "choice": (
            "The v0 guardrail leaves output top-level schemas open; this executor "
            "freezes the exact deterministic ledger, manifest, and report schemas "
            "implemented here for this execution tranche only."
        ),
    },
    {
        "decision_id": "unknown_value_encoding",
        "choice": (
            "A missing or partial source uses a null row-level unit convention, an "
            "empty quantity or mapping array, and one exact explicit blocker; no "
            "zero vector, identity conversion, or unit label is inferred."
        ),
    },
    {
        "decision_id": "quantity_and_mapping_minimum",
        "choice": (
            "The guardrail sets no nonzero minimum. Because no bound source supports "
            "a general unit assignment or seam map, all quantity and mapping arrays "
            "remain empty in the canonical audit."
        ),
    },
    {
        "decision_id": "dimension_vector_encoding",
        "choice": (
            "Any future supported dimension vector must contain exactly seven integer "
            "exponents in the guardrail's ordered SI basis; this execution emits none."
        ),
    },
    {
        "decision_id": "successor_selection",
        "choice": (
            "The guardrail names no success successor, so the review remains pending "
            "without a selected target and no authority rotation is executed."
        ),
    },
]

QCD_CONTEXT = {
    "equations_or_parameters_adopted": False,
    "role": "external seam-transport context only",
    "selected_as_current_target": False,
    "unit_assignments_imported": False,
    "unit_mapping_rows_authorized": 0,
}

RESULT_REVIEW = {
    "status": "pending_independent_review_target_not_selected",
    "target": None,
    "target_selection_authorized": False,
}

LEDGER_ROOT_KEYS = {
    "all_guardrail_decisions_passed",
    "authority_rotation_executed",
    "boundary",
    "captured_at_utc",
    "claim_ceiling_level",
    "dimensional_closure_claimed",
    "execution_id",
    "execution_schema_decisions",
    "execution_target",
    "failure_target",
    "guardrail",
    "guardrail_decision_count",
    "guardrail_decisions",
    "input_artifacts",
    "ledger_status",
    "negative_control_count",
    "negative_control_results",
    "packet_result",
    "pillar_row_count",
    "pillar_rows",
    "qcd_context",
    "readiness_schema_id",
    "result_review",
    "schema_id",
    "seam_row_count",
    "seam_rows",
    "selected_next_target",
    "selected_next_target_kind",
    "source_baseline_status_counts",
    "status",
    "strict_packet_result",
    "successor_selection_status",
    "total_row_count",
    "unit_closure_claimed",
    "unit_schema",
}


def canonical_json_bytes(payload: dict[str, Any]) -> bytes:
    return contract.canonical_json_bytes(payload)


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha256_path(path: Path) -> str:
    return contract.sha256_path(path)


def _relative_path(path: Path) -> str:
    try:
        return path.resolve().relative_to(REPO_ROOT.resolve()).as_posix()
    except ValueError:
        return path.name


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def load_guardrail() -> dict[str, Any]:
    """Load and byte-verify the frozen execution contract and all four inputs."""

    generated = contract.build_guardrail_packet()
    path = contract.GUARDRAIL_PATH
    _require(path.is_file(), "guardrail artifact is missing")
    raw = path.read_bytes()
    _require(
        sha256_bytes(raw) == GUARDRAIL_SHA256,
        "guardrail SHA-256 differs from the frozen execution contract",
    )
    _require(
        raw == canonical_json_bytes(generated),
        "guardrail bytes differ from the deterministic frozen contract",
    )
    _require(
        generated.get("status") == "prepared_guardrail_only_execution_not_run",
        "guardrail lifecycle status is not the authorized preparation status",
    )
    _require(
        generated.get("selected_next_target") == contract.EXECUTION_TARGET,
        "guardrail does not authorize the unit-ledger execution target",
    )
    _require(
        generated.get("outputs_authorized")
        == {
            "execution_report": EXECUTION_REPORT_RELATIVE_PATH,
            "ledger": LEDGER_RELATIVE_PATH,
            "manifest": MANIFEST_RELATIVE_PATH,
        },
        "guardrail output allowlist differs from the three frozen paths",
    )
    for artifact in generated["input_artifacts"]:
        input_path = REPO_ROOT / artifact["path"]
        _require(input_path.is_file(), f"frozen input is missing: {artifact['path']}")
        _require(
            sha256_path(input_path) == artifact["sha256"],
            f"frozen input hash mismatch: {artifact['path']}",
        )
    return generated


def _unit_state(source_status: str) -> str:
    if source_status == "missing":
        return "unit_unknown"
    if source_status == "partial":
        return "unresolved"
    raise ValueError(f"unsupported frozen source status: {source_status}")


def _blocker(source_row: dict[str, Any], *, row_kind: str) -> dict[str, Any]:
    state = _unit_state(source_row["status"])
    if row_kind == "pillar":
        absent = "unit convention, declared units, and dimension vectors"
        required = (
            "supply source-backed quantity rows with an explicit allowed convention, "
            "declared units, seven-component SI-basis dimension vectors, and any "
            "required constant-restoration maps"
        )
    else:
        absent = "source-to-target quantity pairing and converted dimension evidence"
        required = (
            "supply source-backed quantity pairs, explicit conversion constants and "
            "maps, and matching converted seven-component dimension vectors"
        )
    return {
        "blocker_id": f"{source_row['row_id']}-{state}-blocker",
        "evidence_pointer": source_row["evidence_pointer"],
        "reason": (
            f"Frozen source status is {source_row['status']}; the bound evidence "
            f"does not support {absent}."
        ),
        "required_resolution": required,
        "state": state,
    }


def _pillar_row(source_row: dict[str, Any]) -> dict[str, Any]:
    state = _unit_state(source_row["status"])
    return {
        "adjudication_status": f"blocked_{state}",
        "conversion_assumptions": [],
        "evidence_pointer": source_row["evidence_pointer"],
        "guardrail_unit_state": state,
        "pillar_id": source_row["pillar_id"],
        "quantity_rows": [],
        "row_id": source_row["row_id"],
        "source_status": source_row["status"],
        "unit_convention": None,
        "unresolved_items": [_blocker(source_row, row_kind="pillar")],
    }


def _seam_row(source_row: dict[str, Any]) -> dict[str, Any]:
    state = _unit_state(source_row["status"])
    return {
        "compatibility_status": f"blocked_{state}",
        "conversion_constants": [],
        "evidence_pointer": source_row["evidence_pointer"],
        "guardrail_unit_state": state,
        "mapping_rows": [],
        "pillar_ids": copy.deepcopy(source_row["pillar_ids"]),
        "row_id": source_row["row_id"],
        "seam_id": source_row["seam_id"],
        "source_status": source_row["status"],
        "unresolved_items": [_blocker(source_row, row_kind="seam")],
    }


def _input_bindings(guardrail: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        {
            **copy.deepcopy(artifact),
            "actual_sha256": sha256_path(REPO_ROOT / artifact["path"]),
            "verified": True,
        }
        for artifact in guardrail["input_artifacts"]
    ]


def _expected_source_rows(
    guardrail: dict[str, Any], key: str, identity_key: str
) -> dict[str, dict[str, Any]]:
    return {
        row[identity_key]: row for row in guardrail["source_baseline"][key]
    }


def _valid_dimension_vector(value: Any) -> bool:
    return (
        isinstance(value, list)
        and len(value) == 7
        and all(isinstance(item, int) and not isinstance(item, bool) for item in value)
    )


def ledger_validation_failures(
    ledger: dict[str, Any], guardrail: dict[str, Any]
) -> list[str]:
    """Return failed frozen decision IDs in the guardrail's canonical order."""

    failed: set[str] = set()
    pillar_rows = ledger.get("pillar_rows")
    seam_rows = ledger.get("seam_rows")
    if not isinstance(pillar_rows, list):
        pillar_rows = []
    if not isinstance(seam_rows, list):
        seam_rows = []

    expected_guardrail_binding = {
        "path": _relative_path(contract.GUARDRAIL_PATH),
        "schema_id": guardrail["schema_id"],
        "sha256": GUARDRAIL_SHA256,
    }
    if ledger.get("guardrail") != expected_guardrail_binding:
        failed.add("all_four_input_artifact_hashes_match")

    lifecycle_ok = (
        set(ledger) == LEDGER_ROOT_KEYS
        and ledger.get("schema_id") == LEDGER_SCHEMA_ID
        and ledger.get("captured_at_utc") == CAPTURED_AT_UTC
        and ledger.get("execution_id") == EXECUTION_ID
        and ledger.get("execution_target") == contract.EXECUTION_TARGET
        and ledger.get("failure_target") == contract.FAILURE_TARGET
        and ledger.get("status") == STATUS
        and ledger.get("ledger_status") == LEDGER_STATUS
        and ledger.get("packet_result") == PACKET_RESULT
        and ledger.get("strict_packet_result") == STRICT_PACKET_RESULT
        and ledger.get("result_review") == RESULT_REVIEW
        and ledger.get("execution_schema_decisions")
        == EXECUTION_SCHEMA_DECISIONS
        and ledger.get("guardrail_decision_count") == 16
        and ledger.get("negative_control_count") == 8
        and ledger.get("all_guardrail_decisions_passed") is True
    )
    if not lifecycle_ok:
        failed.add("all_claim_ceiling_and_nonpromotion_boundaries_are_preserved")

    if ledger.get("unit_schema") != guardrail["ledger_schema_contract"]:
        failed.update(
            {
                "every_quantity_declares_a_unit_convention",
                "every_dimensional_quantity_uses_an_explicit_dimension_vector",
                "natural_unit_reductions_name_constants_and_restoration_maps",
                "cross_convention_equalities_require_explicit_conversion_maps",
                "seam_compatibility_requires_matching_converted_dimensions",
            }
        )

    expected_inputs = guardrail["input_artifacts"]
    bindings = ledger.get("input_artifacts")
    input_ok = isinstance(bindings, list) and len(bindings) == 4
    if input_ok:
        for expected, observed in zip(expected_inputs, bindings, strict=True):
            path = REPO_ROOT / expected["path"]
            if not (
                isinstance(observed, dict)
                and observed.get("artifact_id") == expected["artifact_id"]
                and observed.get("path") == expected["path"]
                and observed.get("sha256") == expected["sha256"]
                and observed.get("actual_sha256") == expected["sha256"]
                and observed.get("verified") is True
                and path.is_file()
                and sha256_path(path) == expected["sha256"]
            ):
                input_ok = False
                break
    if not input_ok:
        failed.add("all_four_input_artifact_hashes_match")

    expected_pillars = _expected_source_rows(
        guardrail, "pillar_rows", "pillar_id"
    )
    expected_seams = _expected_source_rows(guardrail, "seam_rows", "seam_id")
    readiness_ok = (
        ledger.get("readiness_schema_id")
        == "SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0"
        and ledger.get("source_baseline_status_counts")
        == {
            "pillar": guardrail["source_baseline"]["pillar_status_counts"],
            "seam": guardrail["source_baseline"]["seam_status_counts"],
        }
    )
    if not readiness_ok:
        failed.add("readiness_authority_schema_and_status_are_preserved")

    if (
        len(pillar_rows) != 7
        or ledger.get("pillar_row_count") != 7
        or ledger.get("total_row_count") != 12
    ):
        failed.add("exactly_seven_pillar_unit_rows_are_bound")
    if (
        len(seam_rows) != 5
        or ledger.get("seam_row_count") != 5
        or ledger.get("total_row_count") != 12
    ):
        failed.add("exactly_five_seam_unit_map_rows_are_bound")
    all_rows = pillar_rows + seam_rows
    row_ids = [row.get("row_id") for row in all_rows if isinstance(row, dict)]
    row_ids_are_unique = (
        len(row_ids) == len(all_rows)
        and all(isinstance(row_id, str) for row_id in row_ids)
        and len(row_ids) == len(set(row_ids))
    )
    if not row_ids_are_unique:
        failed.add("all_twelve_source_row_ids_are_unique")

    evidence_ok = True
    status_ok = True
    unresolved_ok = True
    quantity_conventions_ok = True
    dimensional_quantities_ok = True
    natural_units_ok = True
    dimensionless_ok = True

    for row in pillar_rows:
        if not isinstance(row, dict) or set(row) != (
            PILLAR_REQUIRED_FIELDS | {"guardrail_unit_state"}
        ):
            evidence_ok = status_ok = unresolved_ok = False
            continue
        pillar_id = row.get("pillar_id")
        expected = (
            expected_pillars.get(pillar_id) if isinstance(pillar_id, str) else None
        )
        if expected is None:
            status_ok = False
            evidence_ok = False
        else:
            if row.get("evidence_pointer") != expected["evidence_pointer"]:
                evidence_ok = False
            state = _unit_state(expected["status"])
            if not (
                row.get("pillar_id") == expected["pillar_id"]
                and row.get("source_status") == expected["status"]
                and row.get("guardrail_unit_state") == state
                and (
                    row.get("row_id") == expected["row_id"]
                    or not row_ids_are_unique
                )
            ):
                status_ok = False
            if not (
                row.get("adjudication_status") == f"blocked_{state}"
                and row.get("unresolved_items")
                == [_blocker(expected, row_kind="pillar")]
                and row.get("unit_convention") is None
                and row.get("conversion_assumptions") == []
                and row.get("quantity_rows") == []
            ):
                unresolved_ok = False
        quantities = row.get("quantity_rows")
        if not isinstance(quantities, list):
            quantity_conventions_ok = dimensional_quantities_ok = False
            continue
        if quantities:
            unresolved_ok = False
        for quantity in quantities:
            if not isinstance(quantity, dict) or not QUANTITY_REQUIRED_FIELDS <= set(
                quantity
            ):
                quantity_conventions_ok = dimensional_quantities_ok = False
                continue
            convention = quantity.get("unit_convention")
            if convention not in guardrail["ledger_schema_contract"][
                "allowed_unit_conventions"
            ]:
                quantity_conventions_ok = False
            if not _valid_dimension_vector(quantity.get("dimension_vector")):
                dimensional_quantities_ok = False
            if convention == (
                "declared_natural_units_with_explicit_constant_restoration_map"
            ) and not (
                quantity.get("natural_unit_constants")
                and quantity.get("restoration_map")
            ):
                natural_units_ok = False
            if convention == (
                "dimensionless_numerical_test_units_with_explicit_scale_binding_status"
            ) and (
                quantity.get("physical_calibration_claimed") is not False
                or quantity.get("scale_binding_status")
                in {None, "physical_calibration", "promoted_to_physical_calibration"}
            ):
                dimensionless_ok = False

    cross_convention_ok = True
    seam_dimensions_ok = True
    for row in seam_rows:
        if not isinstance(row, dict) or set(row) != (
            SEAM_REQUIRED_FIELDS | {"guardrail_unit_state"}
        ):
            evidence_ok = status_ok = unresolved_ok = False
            continue
        seam_id = row.get("seam_id")
        expected = expected_seams.get(seam_id) if isinstance(seam_id, str) else None
        if expected is None:
            status_ok = False
            evidence_ok = False
        else:
            if row.get("evidence_pointer") != expected["evidence_pointer"]:
                evidence_ok = False
            state = _unit_state(expected["status"])
            if not (
                row.get("seam_id") == expected["seam_id"]
                and row.get("pillar_ids") == expected["pillar_ids"]
                and row.get("source_status") == expected["status"]
                and row.get("guardrail_unit_state") == state
                and (
                    row.get("row_id") == expected["row_id"]
                    or not row_ids_are_unique
                )
            ):
                status_ok = False
            if not (
                row.get("compatibility_status") == f"blocked_{state}"
                and row.get("unresolved_items")
                == [_blocker(expected, row_kind="seam")]
                and row.get("conversion_constants") == []
                and row.get("mapping_rows") == []
            ):
                unresolved_ok = False
        mappings = row.get("mapping_rows")
        if not isinstance(mappings, list):
            cross_convention_ok = seam_dimensions_ok = False
            continue
        if mappings:
            unresolved_ok = False
        for mapping in mappings:
            if not isinstance(mapping, dict) or not MAPPING_REQUIRED_FIELDS <= set(
                mapping
            ):
                cross_convention_ok = seam_dimensions_ok = False
                continue
            source_convention = mapping.get("source_unit_convention")
            target_convention = mapping.get("target_unit_convention")
            if (
                source_convention
                and target_convention
                and source_convention != target_convention
                and not mapping.get("conversion_map")
            ):
                cross_convention_ok = False
            source_vector = mapping.get("source_dimension_vector")
            target_vector = mapping.get("target_dimension_vector")
            if mapping.get("converted_dimensions_match") is True and not (
                _valid_dimension_vector(source_vector)
                and _valid_dimension_vector(target_vector)
                and source_vector == target_vector
            ):
                seam_dimensions_ok = False
            if row.get("compatibility_status") == "compatible" and not (
                mappings
                and all(item.get("converted_dimensions_match") is True for item in mappings)
            ):
                seam_dimensions_ok = False

    if not evidence_ok:
        failed.add("all_source_evidence_pointers_are_retained")
    if not status_ok:
        failed.add("source_missing_partial_or_blocked_statuses_are_not_promoted")
    if not quantity_conventions_ok:
        failed.add("every_quantity_declares_a_unit_convention")
    if not dimensional_quantities_ok:
        failed.add("every_dimensional_quantity_uses_an_explicit_dimension_vector")
    if not natural_units_ok:
        failed.add("natural_unit_reductions_name_constants_and_restoration_maps")
    if not dimensionless_ok:
        failed.add("dimensionless_numerical_units_are_not_physical_calibration")
    if not cross_convention_ok:
        failed.add("cross_convention_equalities_require_explicit_conversion_maps")
    if not seam_dimensions_ok:
        failed.add("seam_compatibility_requires_matching_converted_dimensions")
    if not unresolved_ok:
        failed.add("unresolved_unit_assignments_remain_explicit_blockers")

    qcd = ledger.get("qcd_context")
    if qcd != QCD_CONTEXT:
        failed.add("qcd_literature_pressure_remains_non_authorizing_context")

    boundary = ledger.get("boundary")
    boundary_ok = (
        boundary == guardrail["boundary"]
        and all(value is False for value in boundary.values())
        and ledger.get("claim_ceiling_level") == 3
        and ledger.get("selected_next_target") is None
        and ledger.get("selected_next_target_kind") is None
        and ledger.get("successor_selection_status") == SUCCESSOR_SELECTION_STATUS
        and ledger.get("authority_rotation_executed") is False
        and ledger.get("unit_closure_claimed") is False
        and ledger.get("dimensional_closure_claimed") is False
    )
    if not boundary_ok:
        failed.add("all_claim_ceiling_and_nonpromotion_boundaries_are_preserved")

    decision_order = [row["decision_id"] for row in guardrail["guardrail_decisions"]]
    return [decision_id for decision_id in decision_order if decision_id in failed]


def validate_ledger(ledger: dict[str, Any], guardrail: dict[str, Any]) -> None:
    failures = ledger_validation_failures(ledger, guardrail)
    if failures:
        raise ValueError("ledger failed frozen decisions: " + ", ".join(failures))
    _require(
        set(ledger) == LEDGER_ROOT_KEYS,
        "ledger root schema contains missing or undeclared fields",
    )
    expected_decisions = [
        {"decision_id": row["decision_id"], "passed": True, "required": True}
        for row in guardrail["guardrail_decisions"]
    ]
    _require(
        ledger.get("guardrail_decisions") == expected_decisions,
        "serialized guardrail decision ledger is incomplete or reordered",
    )
    _require(
        ledger.get("guardrail_decision_count") == 16,
        "serialized guardrail decision count differs from the frozen contract",
    )
    _require(ledger.get("all_guardrail_decisions_passed") is True, "pass flag false")
    controls = ledger.get("negative_control_results")
    expected_controls = run_negative_controls(ledger, guardrail)
    _require(
        isinstance(controls, list)
        and len(controls) == 8
        and controls == expected_controls,
        "negative-control evidence differs from a fresh deterministic rerun",
    )
    _require(
        ledger.get("negative_control_count") == 8,
        "serialized negative-control count differs from the frozen contract",
    )


def _synthetic_quantity(convention: str) -> dict[str, Any]:
    return {
        "assignment_status": "unresolved",
        "declared_unit": "synthetic_negative_control_only",
        "dimension_vector": [0, 0, 0, 0, 0, 0, 0],
        "physical_role": "negative-control mutation only",
        "quantity_id": "negative-control-quantity",
        "source_pointer": "negative-control://fresh-deep-copy",
        "symbol": "q_control",
        "unit_convention": convention,
    }


def run_negative_controls(
    baseline: dict[str, Any], guardrail: dict[str, Any]
) -> list[dict[str, Any]]:
    results: list[dict[str, Any]] = []
    control_specs = {row["control_id"]: row for row in guardrail["negative_controls"]}
    for control_id in [row["control_id"] for row in guardrail["negative_controls"]]:
        spec = control_specs[control_id]
        if control_id == "dropped_source_row":
            subcases = []
            for collection, expected in (
                ("pillar_rows", "exactly_seven_pillar_unit_rows_are_bound"),
                ("seam_rows", "exactly_five_seam_unit_map_rows_are_bound"),
            ):
                mutated = copy.deepcopy(baseline)
                mutated[collection].pop()
                observed = ledger_validation_failures(mutated, guardrail)
                subcases.append(
                    {
                        "expected_failed_decision_id": expected,
                        "fresh_deep_copy_used": True,
                        "mutation": f"drop one row from {collection}",
                        "observed_failed_decision_ids": observed,
                        "passed": expected in observed,
                    }
                )
            observed_union = list(
                dict.fromkeys(
                    decision
                    for subcase in subcases
                    for decision in subcase["observed_failed_decision_ids"]
                )
            )
            result = {
                "control_id": control_id,
                "expected_failure": spec["expected_failure"],
                "expected_failed_decision_ids": [
                    "exactly_seven_pillar_unit_rows_are_bound",
                    "exactly_five_seam_unit_map_rows_are_bound",
                ],
                "fresh_deep_copy_used": True,
                "observed_failed_decision_ids": observed_union,
                "passed": all(row["passed"] for row in subcases),
                "subcases": subcases,
            }
            results.append(result)
            continue

        mutated = copy.deepcopy(baseline)
        if control_id == "duplicate_source_row_id":
            mutated["seam_rows"][0]["row_id"] = mutated["pillar_rows"][0]["row_id"]
        elif control_id == "source_status_promotion":
            mutated["pillar_rows"][0]["source_status"] = "resolved"
        elif control_id == "missing_evidence_pointer":
            mutated["seam_rows"][0]["evidence_pointer"] = ""
        elif control_id == "implicit_natural_unit_conversion":
            quantity = _synthetic_quantity(
                "declared_natural_units_with_explicit_constant_restoration_map"
            )
            quantity["natural_unit_constants"] = []
            quantity["restoration_map"] = None
            mutated["pillar_rows"][1]["quantity_rows"].append(quantity)
        elif control_id == (
            "dimensionless_test_value_promoted_to_physical_calibration"
        ):
            quantity = _synthetic_quantity(
                "dimensionless_numerical_test_units_with_explicit_scale_binding_status"
            )
            quantity["physical_calibration_claimed"] = True
            quantity["scale_binding_status"] = "promoted_to_physical_calibration"
            mutated["pillar_rows"][1]["quantity_rows"].append(quantity)
        elif control_id == "dimension_vector_mismatch_marked_compatible":
            mutated["seam_rows"][2]["mapping_rows"].append(
                {
                    "conversion_map": {"kind": "identity_negative_control"},
                    "converted_dimensions_match": True,
                    "mapping_status": "unresolved",
                    "source_dimension_vector": [1, 0, 0, 0, 0, 0, 0],
                    "source_quantity_id": "negative-control-source",
                    "target_dimension_vector": [0, 1, 0, 0, 0, 0, 0],
                    "target_quantity_id": "negative-control-target",
                }
            )
        elif control_id == "unresolved_assignment_silently_filled":
            mutated["pillar_rows"][0]["unresolved_items"] = []
            mutated["pillar_rows"][0]["adjudication_status"] = "resolved"
        else:
            raise ValueError(f"unimplemented frozen negative control: {control_id}")
        observed = ledger_validation_failures(mutated, guardrail)
        expected = list(CONTROL_DECISIONS[control_id])
        results.append(
            {
                "control_id": control_id,
                "expected_failure": spec["expected_failure"],
                "expected_failed_decision_ids": expected,
                "fresh_deep_copy_used": True,
                "observed_failed_decision_ids": observed,
                "passed": all(decision in observed for decision in expected),
            }
        )
    return results


def build_ledger(guardrail: dict[str, Any] | None = None) -> dict[str, Any]:
    packet = load_guardrail() if guardrail is None else copy.deepcopy(guardrail)
    baseline = packet["source_baseline"]
    ledger: dict[str, Any] = {
        "all_guardrail_decisions_passed": True,
        "authority_rotation_executed": False,
        "boundary": copy.deepcopy(packet["boundary"]),
        "captured_at_utc": CAPTURED_AT_UTC,
        "claim_ceiling_level": 3,
        "dimensional_closure_claimed": False,
        "execution_schema_decisions": copy.deepcopy(EXECUTION_SCHEMA_DECISIONS),
        "execution_id": EXECUTION_ID,
        "execution_target": contract.EXECUTION_TARGET,
        "failure_target": contract.FAILURE_TARGET,
        "guardrail": {
            "path": _relative_path(contract.GUARDRAIL_PATH),
            "schema_id": packet["schema_id"],
            "sha256": GUARDRAIL_SHA256,
        },
        "guardrail_decisions": [
            {"decision_id": row["decision_id"], "passed": True, "required": True}
            for row in packet["guardrail_decisions"]
        ],
        "guardrail_decision_count": 16,
        "input_artifacts": _input_bindings(packet),
        "ledger_status": LEDGER_STATUS,
        "negative_control_results": [],
        "negative_control_count": 8,
        "packet_result": PACKET_RESULT,
        "pillar_row_count": 7,
        "pillar_rows": [_pillar_row(row) for row in baseline["pillar_rows"]],
        "qcd_context": copy.deepcopy(QCD_CONTEXT),
        "readiness_schema_id": "SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0",
        "result_review": copy.deepcopy(RESULT_REVIEW),
        "schema_id": LEDGER_SCHEMA_ID,
        "seam_row_count": 5,
        "seam_rows": [_seam_row(row) for row in baseline["seam_rows"]],
        "selected_next_target": None,
        "selected_next_target_kind": None,
        "source_baseline_status_counts": {
            "pillar": copy.deepcopy(baseline["pillar_status_counts"]),
            "seam": copy.deepcopy(baseline["seam_status_counts"]),
        },
        "status": STATUS,
        "strict_packet_result": STRICT_PACKET_RESULT,
        "successor_selection_status": SUCCESSOR_SELECTION_STATUS,
        "total_row_count": 12,
        "unit_closure_claimed": False,
        "unit_schema": copy.deepcopy(packet["ledger_schema_contract"]),
    }
    failures = ledger_validation_failures(ledger, packet)
    _require(not failures, "baseline ledger failed decisions: " + ", ".join(failures))
    ledger["negative_control_results"] = run_negative_controls(ledger, packet)
    validate_ledger(ledger, packet)
    return ledger


def build_manifest(
    ledger: dict[str, Any],
    *,
    ledger_path: Path = LEDGER_PATH,
    report_path: Path = EXECUTION_REPORT_PATH,
) -> dict[str, Any]:
    return {
        "ambient_repository_state_serialized": False,
        "authority_rotation_executed": False,
        "captured_at_utc": CAPTURED_AT_UTC,
        "execution_id": EXECUTION_ID,
        "execution_report_path": _relative_path(report_path),
        "execution_target": contract.EXECUTION_TARGET,
        "executor_path": SCRIPT_RELATIVE_PATH,
        "executor_sha256": sha256_path(SCRIPT_PATH),
        "guardrail_path": _relative_path(contract.GUARDRAIL_PATH),
        "guardrail_sha256": GUARDRAIL_SHA256,
        "input_artifacts": copy.deepcopy(ledger["input_artifacts"]),
        "ledger_path": _relative_path(ledger_path),
        "ledger_sha256": sha256_bytes(canonical_json_bytes(ledger)),
        "result_review_status": "pending_independent_review_target_not_selected",
        "schema_id": MANIFEST_SCHEMA_ID,
        "selected_next_target": None,
        "selected_next_target_kind": None,
        "status": STATUS,
        "successor_selection_status": SUCCESSOR_SELECTION_STATUS,
    }


def build_execution_report(
    ledger: dict[str, Any],
    manifest: dict[str, Any],
    *,
    ledger_path: Path = LEDGER_PATH,
    manifest_path: Path = MANIFEST_PATH,
    report_path: Path = EXECUTION_REPORT_PATH,
) -> dict[str, Any]:
    return {
        "all_guardrail_decisions_passed": True,
        "all_negative_controls_passed": True,
        "authority_rotation_executed": False,
        "boundary": copy.deepcopy(ledger["boundary"]),
        "captured_at_utc": CAPTURED_AT_UTC,
        "claim_ceiling_level": 3,
        "dimensional_closure_claimed": False,
        "execution_id": EXECUTION_ID,
        "execution_schema_decisions": copy.deepcopy(
            ledger["execution_schema_decisions"]
        ),
        "execution_report_path": _relative_path(report_path),
        "execution_target": contract.EXECUTION_TARGET,
        "executor_path": SCRIPT_RELATIVE_PATH,
        "executor_sha256": sha256_path(SCRIPT_PATH),
        "failure_target": contract.FAILURE_TARGET,
        "guardrail_decisions": copy.deepcopy(ledger["guardrail_decisions"]),
        "guardrail_decision_count": 16,
        "guardrail_path": _relative_path(contract.GUARDRAIL_PATH),
        "guardrail_sha256": GUARDRAIL_SHA256,
        "ledger_path": _relative_path(ledger_path),
        "ledger_sha256": sha256_bytes(canonical_json_bytes(ledger)),
        "ledger_status": LEDGER_STATUS,
        "manifest_path": _relative_path(manifest_path),
        "manifest_sha256": sha256_bytes(canonical_json_bytes(manifest)),
        "negative_control_results": copy.deepcopy(
            ledger["negative_control_results"]
        ),
        "negative_control_count": 8,
        "packet_result": PACKET_RESULT,
        "result_review": copy.deepcopy(ledger["result_review"]),
        "schema_id": EXECUTION_REPORT_SCHEMA_ID,
        "selected_next_target": None,
        "selected_next_target_kind": None,
        "status": STATUS,
        "strict_packet_result": STRICT_PACKET_RESULT,
        "successor_selection_status": SUCCESSOR_SELECTION_STATUS,
        "twelve_row_summary": {
            "pillar_rows": 7,
            "seam_rows": 5,
            "source_missing_rows": 6,
            "source_partial_rows": 6,
            "unit_unknown_rows": 6,
            "unresolved_rows": 6,
        },
        "unit_closure_claimed": False,
    }


def validate_manifest(
    manifest: dict[str, Any],
    ledger: dict[str, Any],
    *,
    ledger_path: Path = LEDGER_PATH,
    report_path: Path = EXECUTION_REPORT_PATH,
) -> None:
    validate_ledger(ledger, load_guardrail())
    expected = build_manifest(
        ledger, ledger_path=ledger_path, report_path=report_path
    )
    _require(
        manifest == expected,
        "manifest differs from the exact closed schema and hash bindings",
    )


def validate_execution_report(
    report: dict[str, Any],
    ledger: dict[str, Any],
    manifest: dict[str, Any],
    *,
    ledger_path: Path = LEDGER_PATH,
    manifest_path: Path = MANIFEST_PATH,
    report_path: Path = EXECUTION_REPORT_PATH,
) -> None:
    validate_ledger(ledger, load_guardrail())
    validate_manifest(
        manifest,
        ledger,
        ledger_path=ledger_path,
        report_path=report_path,
    )
    expected = build_execution_report(
        ledger,
        manifest,
        ledger_path=ledger_path,
        manifest_path=manifest_path,
        report_path=report_path,
    )
    _require(
        report == expected,
        "execution report differs from the exact closed schema and hash bindings",
    )


def build_artifacts(
    *,
    ledger_path: Path = LEDGER_PATH,
    manifest_path: Path = MANIFEST_PATH,
    report_path: Path = EXECUTION_REPORT_PATH,
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    guardrail = load_guardrail()
    ledger = build_ledger(guardrail)
    manifest = build_manifest(
        ledger, ledger_path=ledger_path, report_path=report_path
    )
    validate_manifest(
        manifest,
        ledger,
        ledger_path=ledger_path,
        report_path=report_path,
    )
    report = build_execution_report(
        ledger,
        manifest,
        ledger_path=ledger_path,
        manifest_path=manifest_path,
        report_path=report_path,
    )
    validate_execution_report(
        report,
        ledger,
        manifest,
        ledger_path=ledger_path,
        manifest_path=manifest_path,
        report_path=report_path,
    )
    return ledger, manifest, report


def _validate_authorized_output_paths(paths: tuple[Path, Path, Path]) -> None:
    authorized = (
        REPO_ROOT / LEDGER_RELATIVE_PATH,
        REPO_ROOT / MANIFEST_RELATIVE_PATH,
        REPO_ROOT / EXECUTION_REPORT_RELATIVE_PATH,
    )
    _require(len(set(paths)) == 3, "the three output roles must use distinct paths")
    root = REPO_ROOT.resolve()
    for path, expected in zip(paths, authorized, strict=True):
        _require(
            path.absolute() == expected.absolute(),
            "runtime output path is outside the exact guardrail allowlist",
        )
        _require(not path.is_symlink(), "runtime output path may not be a symlink")
        _require(
            not path.exists() or path.is_file(),
            "runtime output path exists but is not a regular file",
        )
        _require(path.parent.is_dir(), "runtime output parent directory is missing")
        _require(
            path.parent.resolve().is_relative_to(root),
            "runtime output parent resolves outside the repository",
        )


def _write_bytes(path: Path, raw: bytes) -> None:
    path.write_bytes(raw)


def write_artifacts() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    """Build all payloads before writing exactly the three declared artifact roles."""

    paths = (LEDGER_PATH, MANIFEST_PATH, EXECUTION_REPORT_PATH)
    _validate_authorized_output_paths(paths)
    ledger, manifest, report = build_artifacts()
    payloads = (
        (LEDGER_PATH, canonical_json_bytes(ledger)),
        (MANIFEST_PATH, canonical_json_bytes(manifest)),
        (EXECUTION_REPORT_PATH, canonical_json_bytes(report)),
    )
    prior_bytes = {
        path: path.read_bytes() if path.is_file() else None for path, _ in payloads
    }
    try:
        for path, raw in payloads:
            _write_bytes(path, raw)
    except OSError:
        rollback_errors: list[str] = []
        for path, prior in prior_bytes.items():
            try:
                if prior is None:
                    if path.exists():
                        path.unlink()
                else:
                    path.write_bytes(prior)
            except OSError as rollback_error:
                rollback_errors.append(f"{path}: {rollback_error}")
        if rollback_errors:
            raise OSError(
                "artifact write failed and rollback was incomplete: "
                + "; ".join(rollback_errors)
            )
        raise
    return ledger, manifest, report


def check_artifacts() -> None:
    paths = (LEDGER_PATH, MANIFEST_PATH, EXECUTION_REPORT_PATH)
    _validate_authorized_output_paths(paths)
    expected = build_artifacts()
    for path, payload in zip(
        paths, expected, strict=True
    ):
        _require(path.is_file(), f"execution artifact is missing: {path}")
        _require(
            path.read_bytes() == canonical_json_bytes(payload),
            f"execution artifact is not byte-exact: {path}",
        )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    try:
        if args.check:
            check_artifacts()
        else:
            write_artifacts()
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print(
            json.dumps(
                {
                    "canonical_outputs_written": False,
                    "error": str(exc),
                    "selected_next_target": contract.FAILURE_TARGET,
                    "status": "preflight_input_or_schema_mismatch",
                },
                sort_keys=True,
            ),
            file=sys.stderr,
        )
        return 2
    print(
        json.dumps(
            {
                "authority_rotation_executed": False,
                "ledger_status": LEDGER_STATUS,
                "row_count": 12,
                "selected_next_target": None,
                "status": STATUS,
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

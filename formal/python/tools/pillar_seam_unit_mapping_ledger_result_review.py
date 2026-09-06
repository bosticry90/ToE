from __future__ import annotations

import argparse
import copy
import functools
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
from collections import Counter
from pathlib import Path
from typing import Any, Callable

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.historical_artifact_currency_identity import (
    historical_compendium_sha256_for_path,
    verify_binding,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
GUARDRAIL_PATH = (
    REPO_ROOT
    / "formal/docs/release/PILLAR_SEAM_UNIT_MAPPING_LEDGER_GUARDRAIL_PACKET_20260710_v0.json"
)
EXECUTOR_PATH = (
    REPO_ROOT / "formal/python/tools/pillar_seam_unit_mapping_ledger_execution.py"
)
LEDGER_PATH = REPO_ROOT / "formal/output/PILLAR-SEAM-UNIT-MAPPING-LEDGER-v0.json"
MANIFEST_PATH = (
    REPO_ROOT / "formal/output/PILLAR-SEAM-UNIT-MAPPING-LEDGER-MANIFEST-v0.json"
)
EXECUTION_REPORT_PATH = (
    REPO_ROOT
    / "formal/docs/release/PILLAR_SEAM_UNIT_MAPPING_LEDGER_EXECUTION_20260710_v0.json"
)
READINESS_PATH = (
    REPO_ROOT / "formal/docs/release/SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0.json"
)
SCALAR_REVIEW_PATH = (
    REPO_ROOT
    / "formal/docs/release/SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_MULTI_BACKGROUND_ROBUSTNESS_CALCULATION_RESULT_REVIEW_20260710_v0.json"
)
COMPENDIUM_PATH = (
    REPO_ROOT
    / "formal/docs/paper/TOE_MATH_PHYSICS_WORK_AND_EQUATIONS_COMPENDIUM_v0.md"
)
QCD_CONTEXT_PATH = (
    REPO_ROOT
    / "formal/docs/release/QCD_VACUUM_TO_HADRON_SPIN_INFORMATION_TRANSPORT_LITERATURE_PRESSURE_20260710_v0.json"
)
REGISTRY_PATH = REPO_ROOT / "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"
MAINTENANCE_AUTHORITY_PATH = (
    REPO_ROOT / "formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_v0.json"
)
MAINTENANCE_V2_REVIEW_PATH = (
    REPO_ROOT
    / "formal/docs/release/LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_PROTOTYPE_EXECUTION_PACKET_INDEPENDENT_REVIEW_20260712_v2.json"
)
REVIEW_REPORT_PATH = (
    REPO_ROOT
    / "formal/docs/release/PILLAR_SEAM_UNIT_MAPPING_LEDGER_RESULT_REVIEW_20260712_v0.json"
)

EXECUTION_COMMIT = "2d2617950437b7465e6f322b89463d6417d8cf35"
EXECUTION_PARENT = "cfa61bdbb0147a8759f7159ef2588fcaabca472a"
REVIEW_ID = "PILLAR_SEAM_UNIT_MAPPING_LEDGER_RESULT_REVIEW_v0"
CAPTURED_AT_UTC = "2026-07-12T00:00:00Z"
CONSUMED_TARGET = "execute_pillar_seam_unit_mapping_ledger_v0"
SUCCESS_TARGET = (
    "prepare_pillar_seam_unit_mapping_ledger_blocker_response_route_selection_packet"
)
SUCCESS_TARGET_KIND = (
    "pillar_seam_unit_mapping_ledger_blocker_response_route_selection_packet"
)
FAILURE_TARGET = "diagnose_pillar_seam_unit_mapping_ledger_v0_reproducibility_mismatch"
REVIEW_OUTCOME = (
    "PILLAR_SEAM_UNIT_MAPPING_LEDGER_RESULT_REVIEW_ACCEPTS_REPRODUCIBLE_"
    "TWELVE_ROW_BLOCKER_PRESERVING_AUDIT_AND_AUTHORIZES_BLOCKER_RESPONSE_"
    "ROUTE_SELECTION_PACKET_PREPARATION_ONLY"
)
REVIEW_STRICT_OUTCOME = (
    "PILLAR_SEAM_UNIT_MAPPING_LEDGER_RESULT_REVIEW_ACCEPTS_AUDIT_ONLY_"
    "NO_UNIT_CLOSURE_NO_PILLAR_COMPLETION_NO_SEAM_ADMISSIBILITY_"
    "NO_LEVEL4OR5_NO_CK_ACTION_EMBEDDING_NO_CCFT_NO_MASTER_ACTION_PROMOTION"
)
SELECTION_BASIS = (
    "all twelve audited rows retain typed blockers, so a bounded source-backed "
    "blocker-response route must be selected before any unit assignment or "
    "readiness promotion"
)

EXPECTED_EXECUTION_HASHES = {
    "guardrail_sha256": "7fd4e988ea1a3c435247c2427686c2f3d3024a01c179d99fab30a4d027e364cf",
    "executor_sha256": "c947d2211c0fa62e743dd3f3937473fc1e2671760059a28c332b2ebec4fef9b2",
    "ledger_sha256": "a441b4764c9a27ba66df1eb9b94789b135db35d29aed5151b7bd4bc29c2de9b0",
    "manifest_sha256": "7804844617dea99df2c875d144966b0b196b08bbc884c8aa28a4c441bc7836b1",
    "execution_report_sha256": "9c32106d3220945094a32525ee7f626b32b71146c518a353955974bd386285ec",
}
EXPECTED_INPUT_HASHES = {
    "readiness_sha256": "6a4273b3f95bca657bbc9dcdbab82d118a8223ab6de55a213374421b560838a1",
    "scalar_review_sha256": "cca24f7a9d72d035b974a781213235dc7e8f0685a63bb5189ee465b1c3aa17a0",
    "compendium_sha256": "7a7f9e564fd2e902b731b6ddceb7adb687e854d3a7970462c8ba29b51c05427e",
    "qcd_context_sha256": "a6ca799b72fa3b1d0324f62bc9914a39e32c810584e86b3900776c05df6ca724",
}
EXPECTED_EXECUTION_CUSTODY_HASHES = {
    "registry_sha256": "eda451133e8bbfe1ba0e815b29735f874e8b33e61d7fc5085999c4ba38df0543",
    "maintenance_authority_sha256": "ada2c9c9c4622c64f0ab0fb7033b8e39b790d55a29ee492dd03fea06afc3695b",
    "maintenance_v2_review_sha256": "5b1505fb722121329a3d0d08dc9fe8d10674ede0ccce9c1b7a2ffed1ef7d3cd6",
}

DECISION_IDS = (
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
CONTROL_EXPECTATIONS = {
    "dropped_source_row": "exactly_seven_pillar_unit_rows_are_bound",
    "duplicate_source_row_id": "all_twelve_source_row_ids_are_unique",
    "source_status_promotion": "source_missing_partial_or_blocked_statuses_are_not_promoted",
    "missing_evidence_pointer": "all_source_evidence_pointers_are_retained",
    "implicit_natural_unit_conversion": "natural_unit_reductions_name_constants_and_restoration_maps",
    "dimensionless_test_value_promoted_to_physical_calibration": "dimensionless_numerical_units_are_not_physical_calibration",
    "dimension_vector_mismatch_marked_compatible": "seam_compatibility_requires_matching_converted_dimensions",
    "unresolved_assignment_silently_filled": "unresolved_unit_assignments_remain_explicit_blockers",
}
CONTROL_DECISION_EXPECTATIONS = {
    "dropped_source_row": (
        "exactly_seven_pillar_unit_rows_are_bound",
        "exactly_five_seam_unit_map_rows_are_bound",
    ),
    **{
        control_id: (decision_id,)
        for control_id, decision_id in CONTROL_EXPECTATIONS.items()
        if control_id != "dropped_source_row"
    },
}
CONTROL_FAILURE_TOKENS = {
    "dropped_source_row": "exactly_seven_pillar_or_five_seam_rows_bound",
    "duplicate_source_row_id": "all_twelve_source_row_ids_are_unique",
    "source_status_promotion": "source_statuses_are_not_promoted",
    "missing_evidence_pointer": "all_source_evidence_pointers_are_retained",
    "implicit_natural_unit_conversion": "natural_unit_restoration_map_required",
    "dimensionless_test_value_promoted_to_physical_calibration": "dimensionless_numerical_units_are_noncalibrating",
    "dimension_vector_mismatch_marked_compatible": "converted_source_and_target_dimensions_must_match",
    "unresolved_assignment_silently_filled": "unresolved_unit_assignments_remain_blocked",
}
ALLOWED_UNIT_CONVENTIONS = {
    "SI_base_dimensions",
    "declared_natural_units_with_explicit_constant_restoration_map",
    "dimensionless_numerical_test_units_with_explicit_scale_binding_status",
}


class DuplicateKeyError(ValueError):
    pass


class NonFiniteJSONError(ValueError):
    pass


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _sha256_path(path: Path) -> str:
    return _sha256(path.read_bytes())


def _historical_input_sha256(role: str, path: Path) -> str:
    if role == "compendium":
        return historical_compendium_sha256_for_path(
            path,
            expected_historical_sha256=EXPECTED_INPUT_HASHES[
                "compendium_sha256"
            ],
        )
    return _sha256_path(path)


def canonical_json_bytes(payload: dict[str, Any]) -> bytes:
    return (
        json.dumps(
            payload,
            indent=2,
            ensure_ascii=True,
            allow_nan=False,
            sort_keys=True,
        )
        + "\n"
    ).encode("utf-8")


def report_json_bytes(payload: dict[str, Any]) -> bytes:
    return canonical_json_bytes(payload)


def _reject_duplicate_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise DuplicateKeyError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _reject_nonfinite(token: str) -> Any:
    raise NonFiniteJSONError(f"nonfinite JSON value: {token}")


def load_strict_json_object(
    path: Path, *, style: str = "canonical"
) -> dict[str, Any]:
    raw = path.read_bytes()
    if raw.startswith(b"\xef\xbb\xbf"):
        raise ValueError(f"UTF-8 BOM is forbidden: {path}")
    text = raw.decode("utf-8", errors="strict")
    payload = json.loads(
        text,
        object_pairs_hook=_reject_duplicate_pairs,
        parse_constant=_reject_nonfinite,
    )
    if not isinstance(payload, dict):
        raise ValueError(f"top-level JSON value must be an object: {path}")
    if style == "canonical" and raw != canonical_json_bytes(payload):
        raise ValueError(f"JSON bytes are not canonical: {path}")
    if style not in {"canonical", "any"}:
        raise ValueError(f"unknown JSON style: {style}")
    return payload


def _unit_state(source_status: str) -> str:
    if source_status == "missing":
        return "unit_unknown"
    if source_status == "partial":
        return "unresolved"
    raise ValueError(f"unsupported frozen unit-readiness status: {source_status}")


def _blocker(
    *, row_id: str, state: str, source_status: str, evidence_pointer: str, seam: bool
) -> dict[str, Any]:
    if seam:
        subject = "source-to-target quantity pairing and converted dimension evidence"
        resolution = (
            "supply source-backed quantity pairs, explicit conversion constants and "
            "maps, and matching converted seven-component dimension vectors"
        )
    else:
        subject = "unit convention, declared units, and dimension vectors"
        resolution = (
            "supply source-backed quantity rows with an explicit allowed convention, "
            "declared units, seven-component SI-basis dimension vectors, and any "
            "required constant-restoration maps"
        )
    return {
        "blocker_id": f"{row_id}-{state}-blocker",
        "evidence_pointer": evidence_pointer,
        "reason": (
            f"Frozen source status is {source_status}; the bound evidence does not "
            f"support {subject}."
        ),
        "required_resolution": resolution,
        "state": state,
    }


def _invention_counts(payload: dict[str, Any]) -> dict[str, int]:
    pillars = payload.get("pillar_rows", [])
    seams = payload.get("seam_rows", [])
    quantities = [q for row in pillars for q in row.get("quantity_rows", [])]
    mappings = [m for row in seams for m in row.get("mapping_rows", [])]
    assumptions = [
        a for row in pillars for a in row.get("conversion_assumptions", [])
    ]
    constants = [c for row in seams for c in row.get("conversion_constants", [])]
    return {
        "quantity_rows": len(quantities),
        "mapping_rows": len(mappings),
        "nonnull_unit_conventions": sum(
            row.get("unit_convention") is not None for row in pillars
        ),
        "dimension_vectors": sum(q.get("dimension_vector") is not None for q in quantities)
        + sum(
            m.get(key) is not None
            for m in mappings
            for key in ("source_dimension_vector", "target_dimension_vector")
        ),
        "declared_units": sum(q.get("declared_unit") is not None for q in quantities),
        "conversion_assumptions": len(assumptions),
        "conversion_constants": len(constants),
        "conversion_maps": sum(m.get("conversion_map") is not None for m in mappings),
        "restoration_maps": sum(a.get("restoration_map") is not None for a in assumptions),
        "physical_calibrations": sum(
            q.get("physical_calibration") is True for q in quantities
        ),
    }


def independent_reconstruct_source_rows(
    *,
    readiness_path: Path = READINESS_PATH,
    scalar_review_path: Path = SCALAR_REVIEW_PATH,
    compendium_path: Path = COMPENDIUM_PATH,
    qcd_context_path: Path = QCD_CONTEXT_PATH,
) -> dict[str, Any]:
    readiness = load_strict_json_object(readiness_path, style="any")
    qcd = load_strict_json_object(qcd_context_path, style="any")
    pillar_sources = [
        row
        for row in readiness.get("pillar_readiness_rows", [])
        if row.get("criterion_id") == "units_and_dimensions"
    ]
    seam_sources = [
        row
        for row in readiness.get("seam_readiness_rows", [])
        if row.get("criterion_id") == "unit_map"
    ]
    pillar_rows: list[dict[str, Any]] = []
    for source in pillar_sources:
        status = source["status"]
        state = _unit_state(status)
        row_id = source["row_id"]
        evidence = source["evidence_pointer"]
        pillar_rows.append(
            {
                "adjudication_status": f"blocked_{state}",
                "conversion_assumptions": [],
                "evidence_pointer": evidence,
                "guardrail_unit_state": state,
                "pillar_id": source["pillar_id"],
                "quantity_rows": [],
                "row_id": row_id,
                "source_status": status,
                "unit_convention": None,
                "unresolved_items": [
                    _blocker(
                        row_id=row_id,
                        state=state,
                        source_status=status,
                        evidence_pointer=evidence,
                        seam=False,
                    )
                ],
            }
        )
    seam_rows: list[dict[str, Any]] = []
    for source in seam_sources:
        status = source["status"]
        state = _unit_state(status)
        row_id = source["row_id"]
        evidence = source["evidence_pointer"]
        seam_rows.append(
            {
                "compatibility_status": f"blocked_{state}",
                "conversion_constants": [],
                "evidence_pointer": evidence,
                "guardrail_unit_state": state,
                "mapping_rows": [],
                "pillar_ids": source["pillar_ids"],
                "row_id": row_id,
                "seam_id": source["seam_id"],
                "source_status": status,
                "unresolved_items": [
                    _blocker(
                        row_id=row_id,
                        state=state,
                        source_status=status,
                        evidence_pointer=evidence,
                        seam=True,
                    )
                ],
            }
        )
    context = qcd.get("non_authorizing_context_for_unit_ledger", {})
    result: dict[str, Any] = {
        "readiness_schema_id": readiness.get("artifact_id"),
        "readiness_status": readiness.get("status"),
        "pillar_rows": pillar_rows,
        "seam_rows": seam_rows,
        "pillar_row_count": len(pillar_rows),
        "seam_row_count": len(seam_rows),
        "total_row_count": len(pillar_rows) + len(seam_rows),
        "input_hashes_match": (
            _sha256_path(readiness_path)
            == EXPECTED_INPUT_HASHES["readiness_sha256"]
            and _sha256_path(scalar_review_path)
            == EXPECTED_INPUT_HASHES["scalar_review_sha256"]
            and _historical_input_sha256("compendium", compendium_path)
            == EXPECTED_INPUT_HASHES["compendium_sha256"]
            and _sha256_path(qcd_context_path)
            == EXPECTED_INPUT_HASHES["qcd_context_sha256"]
        ),
        "claim_ceiling_level": 3,
        "boundary": {
            "C_k_action_embedding_authorized": False,
            "ccft_resumed": False,
            "cross_sector_coupling_claim_authorized": False,
            "level_4_or_level_5_authorized": False,
            "master_action_promoted": False,
            "physical_calibration_authorized": False,
            "pillar_completion_claimed": False,
            "seam_admissibility_claimed": False,
            "seam_closure_claimed": False,
            "unit_closure_claimed": False,
            "dimensional_closure_claimed": False,
        },
        "qcd_context": {
            "claim_upgrade": qcd.get("claim_upgrade"),
            "selected_as_current_target": qcd.get("selected_as_current_target"),
            "unit_assignments_imported": context.get("unit_assignments_imported"),
            "unit_ledger_scope_changed": context.get("unit_ledger_scope_changed"),
            "unit_mapping_rows_authorized": context.get(
                "unit_mapping_rows_authorized_by_this_source"
            ),
        },
    }
    result["invention_counts"] = _invention_counts(result)
    return result


def _valid_vector(value: Any) -> bool:
    return (
        isinstance(value, list)
        and len(value) == 7
        and all(isinstance(item, int) and not isinstance(item, bool) for item in value)
    )


def independently_adjudicate(reconstructed: dict[str, Any]) -> list[dict[str, Any]]:
    pillars = reconstructed.get("pillar_rows", [])
    seams = reconstructed.get("seam_rows", [])
    rows = pillars + seams
    quantities = [q for row in pillars for q in row.get("quantity_rows", [])]
    mappings = [m for row in seams for m in row.get("mapping_rows", [])]
    inventions = _invention_counts(reconstructed)

    pointers_retained = all(
        isinstance(row.get("evidence_pointer"), str)
        and bool(row["evidence_pointer"])
        and all(
            item.get("evidence_pointer") == row["evidence_pointer"]
            for item in row.get("unresolved_items", [])
        )
        for row in rows
    )
    statuses_unpromoted = all(
        row.get("source_status") in {"missing", "partial"}
        and row.get("guardrail_unit_state")
        == ("unit_unknown" if row.get("source_status") == "missing" else "unresolved")
        for row in rows
    )
    natural_units_closed = all(
        quantity.get("unit_convention")
        != "declared_natural_units_with_explicit_constant_restoration_map"
        or bool(quantity.get("natural_unit_constants"))
        and bool(quantity.get("restoration_map"))
        for quantity in quantities
    )
    dimensionless_noncalibrating = all(
        quantity.get("unit_convention")
        != "dimensionless_numerical_test_units_with_explicit_scale_binding_status"
        or (
            quantity.get("physical_calibration_claimed") is False
            and quantity.get("scale_binding_status")
            not in {None, "physical_calibration", "promoted_to_physical_calibration"}
        )
        for quantity in quantities
    )
    conversions_explicit = all(
        not (
            mapping.get("source_unit_convention")
            and mapping.get("target_unit_convention")
            and mapping.get("source_unit_convention")
            != mapping.get("target_unit_convention")
        )
        or bool(mapping.get("conversion_map"))
        for mapping in mappings
    )
    converted_dimensions_match = all(
        not mapping.get("converted_dimensions_match")
        or mapping.get("source_dimension_vector")
        == mapping.get("target_dimension_vector")
        for mapping in mappings
    )
    blockers_explicit = True
    for row in rows:
        state = row.get("guardrail_unit_state")
        blockers = row.get("unresolved_items", [])
        expected_status = f"blocked_{state}"
        status_field = (
            "adjudication_status" if "pillar_id" in row else "compatibility_status"
        )
        assignments = (
            row.get("quantity_rows", []) if "pillar_id" in row else row.get("mapping_rows", [])
        )
        expected_row_id = (
            f"{row.get('pillar_id')}-units_and_dimensions-v0"
            if "pillar_id" in row
            else f"{row.get('seam_id')}-unit_map-v0"
        )
        blockers_explicit = blockers_explicit and (
            len(blockers) == 1
            and blockers[0].get("state") == state
            and blockers[0].get("blocker_id")
            == f"{expected_row_id}-{state}-blocker"
            and bool(blockers[0].get("reason"))
            and bool(blockers[0].get("required_resolution"))
            and row.get(status_field) == expected_status
            and assignments == []
        )
    qcd = reconstructed.get("qcd_context", {})
    qcd_non_authorizing = (
        qcd.get("claim_upgrade") is False
        and qcd.get("selected_as_current_target") is False
        and qcd.get("unit_assignments_imported") is False
        and qcd.get("unit_ledger_scope_changed") is False
        and qcd.get("unit_mapping_rows_authorized") == 0
    )
    boundaries = reconstructed.get("boundary", {})
    boundaries_preserved = (
        reconstructed.get("claim_ceiling_level") == 3
        and boundaries
        and all(value is False for value in boundaries.values())
        and inventions["physical_calibrations"] == 0
    )
    passed = (
        reconstructed.get("input_hashes_match") is True,
        reconstructed.get("readiness_schema_id") == "SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0"
        and reconstructed.get("readiness_status")
        == "accepted_current_science_sprint_readiness_authority",
        len(pillars) == 7,
        len(seams) == 5,
        len({row.get("row_id") for row in rows}) == len(rows)
        and all(isinstance(row.get("row_id"), str) for row in rows),
        pointers_retained,
        statuses_unpromoted,
        all(
            quantity.get("unit_convention") in ALLOWED_UNIT_CONVENTIONS
            for quantity in quantities
        ),
        all(_valid_vector(quantity.get("dimension_vector")) for quantity in quantities),
        natural_units_closed,
        dimensionless_noncalibrating,
        conversions_explicit,
        converted_dimensions_match,
        blockers_explicit,
        qcd_non_authorizing,
        boundaries_preserved,
    )
    assignment_domains = {
        7: len(quantities),
        8: len(quantities),
        9: len(quantities),
        10: len(quantities),
        11: len(mappings),
        12: len(mappings),
    }
    decisions: list[dict[str, Any]] = []
    for index, (decision_id, decision_passed) in enumerate(
        zip(DECISION_IDS, passed, strict=True), start=1
    ):
        row: dict[str, Any] = {
            "decision_number": index,
            "decision_id": decision_id,
            "passed": bool(decision_passed),
            "source": "independent_result_review",
        }
        if index - 1 in assignment_domains:
            row["assignment_domain_count"] = assignment_domains[index - 1]
        decisions.append(row)
    return decisions


def _sample_quantity(convention: str) -> dict[str, Any]:
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


def independently_run_one_control(
    control_id: str, baseline: dict[str, Any]
) -> dict[str, Any]:
    if control_id not in CONTROL_EXPECTATIONS:
        raise KeyError(f"unknown negative control: {control_id}")
    if control_id == "dropped_source_row":
        subcases: list[dict[str, Any]] = []
        observed_union: set[str] = set()
        for collection, expected in (
            ("pillar_rows", "exactly_seven_pillar_unit_rows_are_bound"),
            ("seam_rows", "exactly_five_seam_unit_map_rows_are_bound"),
        ):
            mutated = copy.deepcopy(baseline)
            mutated[collection].pop()
            observed = [
                row["decision_id"]
                for row in independently_adjudicate(mutated)
                if not row["passed"]
            ]
            observed_union.update(observed)
            subcases.append(
                {
                    "expected_failed_decision_id": expected,
                    "fresh_deep_copy_used": True,
                    "mutation": f"drop one row from {collection}",
                    "observed_failed_decision_ids": observed,
                    "passed": expected in observed,
                }
            )
        observed = [
            decision_id for decision_id in DECISION_IDS if decision_id in observed_union
        ]
        expected_all = list(CONTROL_DECISION_EXPECTATIONS[control_id])
        return {
            "control_id": control_id,
            "expected_failure": CONTROL_FAILURE_TOKENS[control_id],
            "expected_failed_decision_id": CONTROL_EXPECTATIONS[control_id],
            "expected_failed_decision_ids": expected_all,
            "observed_failed_decision_ids": observed,
            "fresh_deep_copy_used": True,
            "subcases": subcases,
            "passed": all(row["passed"] for row in subcases),
            "detected": all(row["passed"] for row in subcases),
        }
    mutated = copy.deepcopy(baseline)
    if control_id == "duplicate_source_row_id":
        mutated["seam_rows"][0]["row_id"] = mutated["pillar_rows"][0]["row_id"]
    elif control_id == "source_status_promotion":
        mutated["pillar_rows"][0]["source_status"] = "resolved"
    elif control_id == "missing_evidence_pointer":
        mutated["seam_rows"][0]["evidence_pointer"] = ""
    elif control_id == "implicit_natural_unit_conversion":
        quantity = _sample_quantity(
            "declared_natural_units_with_explicit_constant_restoration_map"
        )
        quantity["natural_unit_constants"] = []
        quantity["restoration_map"] = None
        mutated["pillar_rows"][1]["quantity_rows"].append(quantity)
    elif control_id == "dimensionless_test_value_promoted_to_physical_calibration":
        quantity = _sample_quantity(
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
    decisions = independently_adjudicate(mutated)
    failed = [row["decision_id"] for row in decisions if not row["passed"]]
    expected = CONTROL_EXPECTATIONS[control_id]
    expected_all = list(CONTROL_DECISION_EXPECTATIONS[control_id])
    detected = all(decision_id in failed for decision_id in expected_all)
    return {
        "control_id": control_id,
        "expected_failure": CONTROL_FAILURE_TOKENS[control_id],
        "expected_failed_decision_id": expected,
        "expected_failed_decision_ids": expected_all,
        "observed_failed_decision_ids": failed,
        "fresh_deep_copy_used": mutated is not baseline,
        "passed": detected,
        "detected": detected,
    }


def independently_run_negative_controls(
    baseline: dict[str, Any]
) -> list[dict[str, Any]]:
    return [
        independently_run_one_control(control_id, baseline)
        for control_id in CONTROL_EXPECTATIONS
    ]


def _committed_control_projection(result: dict[str, Any]) -> dict[str, Any]:
    projected = {
        "control_id": result["control_id"],
        "expected_failed_decision_ids": result["expected_failed_decision_ids"],
        "expected_failure": result["expected_failure"],
        "fresh_deep_copy_used": result["fresh_deep_copy_used"],
        "observed_failed_decision_ids": result["observed_failed_decision_ids"],
        "passed": result["passed"],
    }
    if "subcases" in result:
        projected["subcases"] = result["subcases"]
    return projected


def _git_bytes(commit: str, relative_path: str) -> bytes:
    completed = subprocess.run(
        ["git", "show", f"{commit}:{relative_path}"],
        cwd=REPO_ROOT,
        capture_output=True,
        check=False,
    )
    if completed.returncode:
        raise RuntimeError(completed.stderr.decode("utf-8", errors="replace"))
    return completed.stdout


@functools.lru_cache(maxsize=1)
def review_time_authority_binding() -> dict[str, Any]:
    return verify_binding(
        "PAC-017",
        expected_path="formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_v0.json",
        expected_sha256=EXPECTED_EXECUTION_CUSTODY_HASHES[
            "maintenance_authority_sha256"
        ],
    )


@functools.lru_cache(maxsize=1)
def _execution_time_custody() -> dict[str, Any]:
    paths = {
        "registry": "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json",
        "maintenance_authority": "formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_v0.json",
        "maintenance_v2_review": (
            "formal/docs/release/LOOP_CONTROL_REGISTRY_SHARDING_READ_ONLY_"
            "PROTOTYPE_EXECUTION_PACKET_INDEPENDENT_REVIEW_20260712_v2.json"
        ),
    }
    current = {name: _git_bytes(EXECUTION_COMMIT, path) for name, path in paths.items()}
    parent = {name: _git_bytes(EXECUTION_PARENT, path) for name, path in paths.items()}
    v2 = json.loads(current["maintenance_v2_review"].decode("utf-8"))
    authorization = v2["authorization"]
    review_time_authority = review_time_authority_binding()
    return {
        "execution_commit": EXECUTION_COMMIT,
        "execution_parent": EXECUTION_PARENT,
        "registry_sha256": _sha256(current["registry"]),
        "maintenance_authority_sha256": _sha256(current["maintenance_authority"]),
        "maintenance_v2_review_sha256": _sha256(current["maintenance_v2_review"]),
        "registry_unchanged_from_parent": current["registry"] == parent["registry"],
        "maintenance_authority_unchanged_from_parent": (
            current["maintenance_authority"] == parent["maintenance_authority"]
        ),
        "maintenance_v2_review_unchanged_from_parent": (
            current["maintenance_v2_review"] == parent["maintenance_v2_review"]
        ),
        "maintenance_v2_status": v2["status"],
        "stage_a_authorized": authorization["stage_a_authorized"],
        "stage_b_authorized": authorization["stage_b_authorized"],
        "prototype_execution_authorized": authorization[
            "prototype_execution_authorized"
        ],
        "versioned_v3_successor_required": authorization[
            "versioned_v3_successor_required"
        ],
        "review_time_maintenance_authority_unchanged": (
            review_time_authority["sha256"]
            == EXPECTED_EXECUTION_CUSTODY_HASHES["maintenance_authority_sha256"]
        ),
        "review_time_maintenance_v2_evidence_unchanged": (
            _sha256_path(MAINTENANCE_V2_REVIEW_PATH)
            == EXPECTED_EXECUTION_CUSTODY_HASHES["maintenance_v2_review_sha256"]
        ),
    }


_REPRO_SOURCE_PATHS = (
    "State_of_the_Theory.md",
    "formal/python/meta/repo_environment.py",
    "formal/python/tools/equation_compendium_identity.py",
    "formal/python/tools/pillar_seam_unit_mapping_ledger_reports.py",
    "formal/python/tools/pillar_seam_unit_mapping_ledger_execution.py",
    "formal/docs/release/EQUATION_COMPENDIUM_IDENTITY_DOMAIN_CONTRACT_20260724_v0.json",
    "formal/docs/release/PILLAR_SEAM_UNIT_MAPPING_LEDGER_GUARDRAIL_PACKET_20260710_v0.json",
    "formal/docs/release/SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0.json",
    "formal/docs/release/SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_MULTI_BACKGROUND_ROBUSTNESS_CALCULATION_RESULT_REVIEW_20260710_v0.json",
    "formal/docs/paper/TOE_MATH_PHYSICS_WORK_AND_EQUATIONS_COMPENDIUM_v0.md",
    "formal/docs/release/QCD_VACUUM_TO_HADRON_SPIN_INFORMATION_TRANSPORT_LITERATURE_PRESSURE_20260710_v0.json",
)
_REPRO_OUTPUT_PATHS = (
    "formal/output/PILLAR-SEAM-UNIT-MAPPING-LEDGER-v0.json",
    "formal/output/PILLAR-SEAM-UNIT-MAPPING-LEDGER-MANIFEST-v0.json",
    "formal/docs/release/PILLAR_SEAM_UNIT_MAPPING_LEDGER_EXECUTION_20260710_v0.json",
)


def _stage_and_run_reproduction(root: Path) -> tuple[dict[str, bytes], str]:
    for relative in _REPRO_SOURCE_PATHS:
        destination = root / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(REPO_ROOT / relative, destination)
    for relative in _REPRO_OUTPUT_PATHS:
        (root / relative).parent.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env["PYTHONPATH"] = str(root)
    env["PYTHONNOUSERSITE"] = "1"
    env["GIT_DIR"] = subprocess.run(
        ["git", "rev-parse", "--absolute-git-dir"],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    env["GIT_WORK_TREE"] = str(root)
    completed = subprocess.run(
        [
            sys.executable,
            "-m",
            "formal.python.tools.pillar_seam_unit_mapping_ledger_execution",
        ],
        cwd=root,
        env=env,
        capture_output=True,
        text=True,
        check=False,
        timeout=180,
    )
    if completed.returncode:
        raise RuntimeError(completed.stderr.strip() or completed.stdout.strip())
    return ({relative: (root / relative).read_bytes() for relative in _REPRO_OUTPUT_PATHS}, completed.stdout.strip())


def _fresh_reproduction() -> dict[str, Any]:
    frozen = {
        str(path.relative_to(REPO_ROOT)).replace("\\", "/"): path.read_bytes()
        for path in (
            GUARDRAIL_PATH,
            EXECUTOR_PATH,
            READINESS_PATH,
            SCALAR_REVIEW_PATH,
            COMPENDIUM_PATH,
            QCD_CONTEXT_PATH,
            LEDGER_PATH,
            MANIFEST_PATH,
            EXECUTION_REPORT_PATH,
        )
    }
    runs: list[dict[str, bytes]] = []
    stdout_rows: list[str] = []
    temp_names: list[str] = []
    try:
        for _ in range(2):
            with tempfile.TemporaryDirectory(prefix="toe-unit-ledger-review-") as name:
                temp_names.append(name)
                outputs, stdout = _stage_and_run_reproduction(Path(name))
                runs.append(outputs)
                stdout_rows.append(stdout)
        repository_outputs = {
            relative: (REPO_ROOT / relative).read_bytes()
            for relative in _REPRO_OUTPUT_PATHS
        }
        after = {
            relative: (REPO_ROOT / relative).read_bytes() for relative in frozen
        }
        return {
            "run_count": 2,
            "distinct_temporary_directories": len(set(temp_names)) == 2,
            "both_runs_byte_identical": runs[0] == runs[1],
            "fresh_runs_match_repository_artifacts": (
                runs[0] == repository_outputs and runs[1] == repository_outputs
            ),
            "all_frozen_inputs_unchanged": after == frozen,
            "repository_execution_artifacts_unchanged": all(
                after[relative] == frozen[relative] for relative in _REPRO_OUTPUT_PATHS
            ),
            "subprocess_stdout_byte_identical": stdout_rows[0] == stdout_rows[1],
            "failure": None,
        }
    except (OSError, RuntimeError, subprocess.SubprocessError) as exc:
        return {
            "run_count": len(runs),
            "distinct_temporary_directories": len(set(temp_names)) == len(temp_names),
            "both_runs_byte_identical": False,
            "fresh_runs_match_repository_artifacts": False,
            "all_frozen_inputs_unchanged": all(
                (REPO_ROOT / relative).read_bytes() == raw
                for relative, raw in frozen.items()
            ),
            "repository_execution_artifacts_unchanged": all(
                (REPO_ROOT / relative).read_bytes() == frozen[relative]
                for relative in _REPRO_OUTPUT_PATHS
            ),
            "subprocess_stdout_byte_identical": False,
            "failure": str(exc),
        }


def _append_once(codes: list[str], code: str) -> None:
    if code not in codes:
        codes.append(code)


def _verify_execution_result(
    *,
    guardrail_path: Path,
    executor_path: Path,
    ledger_path: Path,
    manifest_path: Path,
    execution_report_path: Path,
    readiness_path: Path,
    scalar_review_path: Path,
    compendium_path: Path,
    qcd_context_path: Path,
    run_subprocesses: bool,
) -> dict[str, Any]:
    codes: list[str] = []
    execution_paths = {
        "guardrail": guardrail_path,
        "executor": executor_path,
        "ledger": ledger_path,
        "manifest": manifest_path,
        "execution_report": execution_report_path,
    }
    actual_execution_hashes: dict[str, str | None] = {}
    for role, path in execution_paths.items():
        key = f"{role}_sha256"
        try:
            actual = _sha256_path(path)
        except OSError:
            actual = None
        actual_execution_hashes[key] = actual
        if actual != EXPECTED_EXECUTION_HASHES[key]:
            _append_once(codes, f"{role}_hash_mismatch")
    input_paths = {
        "readiness": readiness_path,
        "scalar_review": scalar_review_path,
        "compendium": compendium_path,
        "qcd_context": qcd_context_path,
    }
    actual_input_hashes: dict[str, str | None] = {}
    for role, path in input_paths.items():
        key = f"{role}_sha256"
        try:
            actual = _historical_input_sha256(role, path)
        except OSError:
            actual = None
        actual_input_hashes[key] = actual
        if actual != EXPECTED_INPUT_HASHES[key]:
            _append_once(codes, f"{role}_hash_mismatch")

    parsed: dict[str, dict[str, Any]] = {}
    for role, path in {
        "guardrail": guardrail_path,
        "ledger": ledger_path,
        "manifest": manifest_path,
        "execution_report": execution_report_path,
    }.items():
        try:
            parsed[role] = load_strict_json_object(path)
        except (OSError, ValueError, json.JSONDecodeError):
            _append_once(codes, f"{role}_canonical_or_parse_mismatch")

    reconstructed: dict[str, Any] | None = None
    decisions: list[dict[str, Any]] = []
    controls: list[dict[str, Any]] = []
    try:
        reconstructed = independent_reconstruct_source_rows(
            readiness_path=readiness_path,
            scalar_review_path=scalar_review_path,
            compendium_path=compendium_path,
            qcd_context_path=qcd_context_path,
        )
        decisions = independently_adjudicate(reconstructed)
        controls = independently_run_negative_controls(reconstructed)
    except (OSError, ValueError, KeyError, TypeError, json.JSONDecodeError):
        _append_once(codes, "independent_source_reconstruction_failed")
    ledger = parsed.get("ledger")
    if reconstructed is not None and ledger is not None:
        if (
            ledger.get("pillar_rows") != reconstructed["pillar_rows"]
            or ledger.get("seam_rows") != reconstructed["seam_rows"]
        ):
            _append_once(codes, "independent_row_or_blocker_reconstruction_mismatch")
        committed_decisions = ledger.get("guardrail_decisions", [])
        if [row.get("decision_id") for row in committed_decisions] != list(DECISION_IDS):
            _append_once(codes, "committed_decision_record_mismatch")
        committed_controls = ledger.get("negative_control_results", [])
        if [row.get("control_id") for row in committed_controls] != list(
            CONTROL_EXPECTATIONS
        ):
            _append_once(codes, "committed_control_record_mismatch")
        elif controls and [
            _committed_control_projection(row) for row in controls
        ] != committed_controls:
            _append_once(codes, "committed_control_evidence_mismatch")
        if ledger.get("selected_next_target") is not None or ledger.get(
            "authority_rotation_executed"
        ) is not False:
            _append_once(codes, "execution_lifecycle_boundary_mismatch")
        boundaries = ledger.get("boundary", {})
        if not boundaries or not all(value is False for value in boundaries.values()):
            _append_once(codes, "execution_nonclaim_boundary_mismatch")
    if decisions and not all(row["passed"] for row in decisions):
        _append_once(codes, "independent_decision_failure")
    if controls and not all(row["detected"] for row in controls):
        _append_once(codes, "independent_negative_control_failure")

    manifest = parsed.get("manifest")
    report = parsed.get("execution_report")
    if manifest is not None and (
        manifest.get("ledger_sha256") != actual_execution_hashes["ledger_sha256"]
        or manifest.get("executor_sha256") != actual_execution_hashes["executor_sha256"]
        or manifest.get("guardrail_sha256") != actual_execution_hashes["guardrail_sha256"]
    ):
        _append_once(codes, "manifest_artifact_chain_mismatch")
    if report is not None and (
        report.get("ledger_sha256") != actual_execution_hashes["ledger_sha256"]
        or report.get("manifest_sha256") != actual_execution_hashes["manifest_sha256"]
        or report.get("executor_sha256") != actual_execution_hashes["executor_sha256"]
        or report.get("guardrail_sha256") != actual_execution_hashes["guardrail_sha256"]
    ):
        _append_once(codes, "execution_report_artifact_chain_mismatch")

    custody = _execution_time_custody()
    for role, expected in EXPECTED_EXECUTION_CUSTODY_HASHES.items():
        if custody.get(role) != expected:
            _append_once(codes, f"execution_time_{role}_mismatch")
    if not all(
        custody[key]
        for key in (
            "registry_unchanged_from_parent",
            "maintenance_authority_unchanged_from_parent",
            "maintenance_v2_review_unchanged_from_parent",
            "review_time_maintenance_authority_unchanged",
            "review_time_maintenance_v2_evidence_unchanged",
        )
    ):
        _append_once(codes, "maintenance_or_execution_custody_mismatch")

    if run_subprocesses:
        fresh = _fresh_reproduction()
        if not all(
            fresh[key]
            for key in (
                "run_count",
                "distinct_temporary_directories",
                "both_runs_byte_identical",
                "fresh_runs_match_repository_artifacts",
                "all_frozen_inputs_unchanged",
                "repository_execution_artifacts_unchanged",
            )
        ) or fresh["run_count"] != 2:
            _append_once(codes, "fresh_subprocess_reproduction_mismatch")
    else:
        fresh = {
            "run_count": 0,
            "distinct_temporary_directories": False,
            "both_runs_byte_identical": False,
            "fresh_runs_match_repository_artifacts": False,
            "all_frozen_inputs_unchanged": True,
            "repository_execution_artifacts_unchanged": True,
            "subprocess_stdout_byte_identical": False,
            "failure": "not_run",
        }
        _append_once(codes, "fresh_subprocess_verification_not_run")
    return {
        "accepted": not codes,
        "mismatch_codes": codes,
        "execution_self_adjudication_trusted": False,
        "actual_execution_hashes": actual_execution_hashes,
        "actual_input_hashes": actual_input_hashes,
        "all_five_execution_hashes_match": actual_execution_hashes
        == EXPECTED_EXECUTION_HASHES,
        "all_four_input_hashes_match": actual_input_hashes == EXPECTED_INPUT_HASHES,
        "independent_reconstruction": reconstructed,
        "independent_decisions": decisions,
        "independent_negative_controls": controls,
        "all_sixteen_independent_decisions_pass": len(decisions) == 16
        and all(row["passed"] for row in decisions),
        "all_eight_independent_controls_detected": len(controls) == 8
        and all(row["detected"] for row in controls),
        "fresh_subprocess_reproduction": fresh,
        "execution_time_custody": custody,
    }


@functools.lru_cache(maxsize=1)
def _default_verification_cached() -> dict[str, Any]:
    return _verify_execution_result(
        guardrail_path=GUARDRAIL_PATH,
        executor_path=EXECUTOR_PATH,
        ledger_path=LEDGER_PATH,
        manifest_path=MANIFEST_PATH,
        execution_report_path=EXECUTION_REPORT_PATH,
        readiness_path=READINESS_PATH,
        scalar_review_path=SCALAR_REVIEW_PATH,
        compendium_path=COMPENDIUM_PATH,
        qcd_context_path=QCD_CONTEXT_PATH,
        run_subprocesses=True,
    )


def verify_execution_result(
    *,
    guardrail_path: Path = GUARDRAIL_PATH,
    executor_path: Path = EXECUTOR_PATH,
    ledger_path: Path = LEDGER_PATH,
    manifest_path: Path = MANIFEST_PATH,
    execution_report_path: Path = EXECUTION_REPORT_PATH,
    readiness_path: Path = READINESS_PATH,
    scalar_review_path: Path = SCALAR_REVIEW_PATH,
    compendium_path: Path = COMPENDIUM_PATH,
    qcd_context_path: Path = QCD_CONTEXT_PATH,
    run_subprocesses: bool = True,
) -> dict[str, Any]:
    defaults = (
        guardrail_path == GUARDRAIL_PATH
        and executor_path == EXECUTOR_PATH
        and ledger_path == LEDGER_PATH
        and manifest_path == MANIFEST_PATH
        and execution_report_path == EXECUTION_REPORT_PATH
        and readiness_path == READINESS_PATH
        and scalar_review_path == SCALAR_REVIEW_PATH
        and compendium_path == COMPENDIUM_PATH
        and qcd_context_path == QCD_CONTEXT_PATH
    )
    if defaults and run_subprocesses:
        return copy.deepcopy(_default_verification_cached())
    return _verify_execution_result(
        guardrail_path=guardrail_path,
        executor_path=executor_path,
        ledger_path=ledger_path,
        manifest_path=manifest_path,
        execution_report_path=execution_report_path,
        readiness_path=readiness_path,
        scalar_review_path=scalar_review_path,
        compendium_path=compendium_path,
        qcd_context_path=qcd_context_path,
        run_subprocesses=run_subprocesses,
    )


def build_review_report(*, run_subprocesses: bool = True) -> dict[str, Any]:
    verification = verify_execution_result(run_subprocesses=run_subprocesses)
    accepted = verification["accepted"]
    boundary = {
        "C_k_action_embedding_authorized": False,
        "ccft_resumed": False,
        "cross_sector_coupling_claim_authorized": False,
        "dimensional_closure_claimed": False,
        "level_4_or_level_5_authorized": False,
        "master_action_promoted": False,
        "physical_calibration_authorized": False,
        "pillar_completion_claimed": False,
        "seam_admissibility_claimed": False,
        "seam_closure_claimed": False,
        "unit_closure_claimed": False,
    }
    return {
        "accepted": accepted,
        "artifact_chain": {
            "expected_execution_hashes": EXPECTED_EXECUTION_HASHES,
            "expected_input_hashes": EXPECTED_INPUT_HASHES,
            "ledger_path": str(LEDGER_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "manifest_path": str(MANIFEST_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
            "execution_report_path": str(
                EXECUTION_REPORT_PATH.relative_to(REPO_ROOT)
            ).replace("\\", "/"),
        },
        "authority_rotation": {
            "execution_time_rotation_performed": False,
            "review_time_rotation_authorized": accepted,
            "maintenance_authority_rotation_authorized": False,
        },
        "boundary": boundary,
        "captured_at_utc": CAPTURED_AT_UTC,
        "claim": {
            "claim_ceiling_level": 3,
            "claim_scope": (
                "reproducible reconstruction, classification, and adversarial testing "
                "of the exact twelve frozen pillar and seam unit-readiness rows"
            ),
            "pillar_unit_row_count": 7,
            "seam_unit_map_row_count": 5,
            "total_row_count": 12,
            "unit_unknown_row_count": 6,
            "unresolved_row_count": 6,
            "invented_quantity_or_mapping_count": 0,
        },
        "consumed_target": CONSUMED_TARGET,
        "determinism": {
            "canonical_json": True,
            "fresh_subprocess_count_required": 2,
            "report_contains_no_ambient_repository_state": True,
        },
        "execution_commit": EXECUTION_COMMIT,
        "execution_parent": EXECUTION_PARENT,
        "failure_preservation": {
            "authority_rotation_authorized": accepted,
            "execution_commit_remains_immutable": True,
            "source_or_execution_artifacts_amended_by_review": False,
            "failure_target": FAILURE_TARGET,
        },
        "maintenance_boundary": {
            "maintenance_authority_unchanged": verification[
                "execution_time_custody"
            ]["review_time_maintenance_authority_unchanged"],
            "registry_maintenance_paused": True,
            "registry_monolith_remains_authoritative": True,
            "registry_v3_live": False,
            "stage_a_authorized": False,
            "stage_b_authorized": False,
        },
        "mismatch_codes": verification["mismatch_codes"],
        "primary_label": "ACCEPT" if accepted else "B-BLOCKED",
        "review_id": REVIEW_ID,
        "review_outcome": REVIEW_OUTCOME if accepted else "B_BLOCKED",
        "schema_id": "PILLAR_SEAM_UNIT_MAPPING_LEDGER_RESULT_REVIEW_20260712_v0",
        "selected_next_target": SUCCESS_TARGET if accepted else FAILURE_TARGET,
        "selected_next_target_kind": (
            SUCCESS_TARGET_KIND if accepted else "diagnostic_reproducibility_mismatch"
        ),
        "selection_basis": SELECTION_BASIS if accepted else "fail_closed_on_review_mismatch",
        "status": (
            "accepted_bounded_unit_mapping_ledger"
            if accepted
            else "blocked_reproducibility_mismatch"
        ),
        "strict_review_outcome": REVIEW_STRICT_OUTCOME if accepted else "B_BLOCKED",
        "successor_selection": {
            "direct_unit_assignment_authorized": False,
            "readiness_promotion_authorized": False,
            "selected_target": SUCCESS_TARGET if accepted else FAILURE_TARGET,
            "selected_target_kind": (
                SUCCESS_TARGET_KIND if accepted else "diagnostic_reproducibility_mismatch"
            ),
        },
        "verification": verification,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--output", type=Path, default=REVIEW_REPORT_PATH)
    args = parser.parse_args(argv)
    try:
        report = build_review_report()
        raw = report_json_bytes(report)
        if not report["accepted"]:
            print(json.dumps({"mismatch_codes": report["mismatch_codes"], "status": report["status"]}), file=sys.stderr)
            return 2
        if args.check:
            if not args.output.is_file() or args.output.read_bytes() != raw:
                print("review report is missing or not byte-exact", file=sys.stderr)
                return 1
        else:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_bytes(raw)
    except (OSError, ValueError, KeyError, TypeError, RuntimeError) as exc:
        print(str(exc), file=sys.stderr)
        return 2
    print(
        json.dumps(
            {
                "accepted": True,
                "review_id": REVIEW_ID,
                "selected_next_target": SUCCESS_TARGET,
                "status": "accepted_bounded_unit_mapping_ledger",
            },
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

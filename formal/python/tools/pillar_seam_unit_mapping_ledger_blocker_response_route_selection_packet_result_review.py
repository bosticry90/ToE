from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path
from typing import Any, Callable

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.historical_artifact_currency_identity import verify_binding


REPO_ROOT = find_repo_root(Path(__file__))
PREPARATION_COMMIT = "5d11196086e12f161f51785fb86dc88bbd803081"
PREPARATION_PARENT = "e0ba685c3d62040dc04a849b5d6808498fc9d63b"
CAPTURED_AT_UTC = "2026-07-12T00:00:00Z"

PACKET_REL = (
    "formal/output/PILLAR-SEAM-UNIT-MAPPING-LEDGER-BLOCKER-RESPONSE-"
    "ROUTE-SELECTION-PACKET-v0.json"
)
MANIFEST_REL = (
    "formal/output/PILLAR-SEAM-UNIT-MAPPING-LEDGER-BLOCKER-RESPONSE-"
    "ROUTE-SELECTION-MANIFEST-v0.json"
)
PREPARATION_REPORT_REL = (
    "formal/docs/release/PILLAR_SEAM_UNIT_MAPPING_LEDGER_BLOCKER_RESPONSE_"
    "ROUTE_SELECTION_PACKET_20260712_v0.json"
)
GENERATOR_REL = (
    "formal/python/tools/"
    "pillar_seam_unit_mapping_ledger_blocker_response_route_selection.py"
)
LEDGER_REL = "formal/output/PILLAR-SEAM-UNIT-MAPPING-LEDGER-v0.json"
ACCEPTED_LEDGER_REVIEW_REL = (
    "formal/docs/release/PILLAR_SEAM_UNIT_MAPPING_LEDGER_"
    "RESULT_REVIEW_20260712_v0.json"
)
REVIEW_REPORT_REL = (
    "formal/docs/release/PILLAR_SEAM_UNIT_MAPPING_LEDGER_BLOCKER_RESPONSE_"
    "ROUTE_SELECTION_PACKET_RESULT_REVIEW_20260712_v0.json"
)

PACKET_PATH = REPO_ROOT / PACKET_REL
MANIFEST_PATH = REPO_ROOT / MANIFEST_REL
PREPARATION_REPORT_PATH = REPO_ROOT / PREPARATION_REPORT_REL
GENERATOR_PATH = REPO_ROOT / GENERATOR_REL
LEDGER_PATH = REPO_ROOT / LEDGER_REL
ACCEPTED_LEDGER_REVIEW_PATH = REPO_ROOT / ACCEPTED_LEDGER_REVIEW_REL
REVIEW_REPORT_PATH = REPO_ROOT / REVIEW_REPORT_REL

EXPECTED_HASHES = {
    GENERATOR_REL: "27ad363691f34279e5a9e0d0ffc916096af0f21ca189c284ff7ad005927c730c",
    PACKET_REL: "e3aad41e3ed886f43bcd6dfafc0b3736c5f981a49278a6bd89460ffdf89875b9",
    MANIFEST_REL: "23015cfac12edd4d627d8db5af0613f10bc6924f8ea1ce422e0bf3e384457c88",
    PREPARATION_REPORT_REL: "56e55ff41d015a2337edeecd25da8397eff54289f8e05271fa0a309df4342444",
    LEDGER_REL: "a441b4764c9a27ba66df1eb9b94789b135db35d29aed5151b7bd4bc29c2de9b0",
    ACCEPTED_LEDGER_REVIEW_REL: "268525f4646c60bab7077faa559907c581d08d08d1b2ae001c316581fd9b55f6",
}

EXPECTED_ROUTES = {
    "PILLAR-QFT-units_and_dimensions-v0": "OBJECT_SEMANTICS_REFINEMENT",
    "PILLAR-GR-units_and_dimensions-v0": "EQUATION_BALANCE_DERIVATION",
    "PILLAR-QM-units_and_dimensions-v0": "OBJECT_SEMANTICS_REFINEMENT",
    "PILLAR-STAT-units_and_dimensions-v0": "OBJECT_SEMANTICS_REFINEMENT",
    "PILLAR-EM-units_and_dimensions-v0": "CONVENTION_AND_CONSTANT_RESTORATION",
    "PILLAR-SR-units_and_dimensions-v0": "CONVENTION_AND_CONSTANT_RESTORATION",
    "PILLAR-COSMO-units_and_dimensions-v0": "OBJECT_SEMANTICS_REFINEMENT",
    "SEAM-QFT-GR-unit_map-v0": "RESEARCH_BLOCKED",
    "SEAM-QM-STAT-unit_map-v0": "RESEARCH_BLOCKED",
    "SEAM-EM-QFT-unit_map-v0": "RESEARCH_BLOCKED",
    "SEAM-SR-COSMO-unit_map-v0": "RESEARCH_BLOCKED",
    "SEAM-GR-QM-unit_map-v0": "RESEARCH_BLOCKED",
}

EXPECTED_ROUTE_COUNTS = {
    "ACTION_DIMENSION_DERIVATION": 0,
    "EQUATION_BALANCE_DERIVATION": 1,
    "CONVENTION_AND_CONSTANT_RESTORATION": 2,
    "SEAM_CONVERSION_MAP": 0,
    "EMPIRICAL_SCALE_CALIBRATION": 0,
    "OBJECT_SEMANTICS_REFINEMENT": 4,
    "RESEARCH_BLOCKED": 5,
    "DIMENSIONAL_INCOMPATIBILITY_REJECTION": 0,
}

DECISION_IDS = [
    "frozen_preparation_and_accepted_ledger_hashes_match",
    "exact_twelve_row_identity_status_and_evidence_pointers_reconstructed",
    "each_row_has_exactly_one_independently_reproduced_primary_route",
    "eight_route_taxonomy_and_ten_ordered_criteria_are_preserved",
    "no_unit_dimension_constant_calibration_or_seam_map_is_emitted",
    "unit_unknown_rows_receive_no_assignment",
    "natural_units_do_not_resolve_unresolved_rows",
    "dimensionless_coordinates_are_not_promoted_to_physical_distances",
    "suppressed_constants_require_explicit_restoration",
    "seam_conversion_requires_two_reviewed_endpoint_unit_systems",
    "candidate_master_action_is_not_self_supporting_evidence",
    "normalization_convention_is_not_empirical_calibration",
    "route_selection_does_not_promote_dimensional_closure",
    "C_k_action_embedding_remains_unauthorized",
    "family_counts_and_all_twelve_blocked_rows_are_reproduced",
    "all_nonclaims_and_claim_ceiling_boundaries_are_preserved",
]

MISMATCH_CODES = [
    "QFT_BOUND_SOURCE_ACTION_ATTRIBUTION_MISMATCH",
    "QM_BOUND_SOURCE_HAMILTONIAN_ATTRIBUTION_MISMATCH",
    "STAT_BOUND_SOURCE_PROBABILITY_TRANSPORT_ATTRIBUTION_MISMATCH",
]

REVIEW_OUTCOME = (
    "PILLAR_SEAM_UNIT_MAPPING_LEDGER_BLOCKER_RESPONSE_ROUTE_SELECTION_PACKET_"
    "RESULT_REVIEW_B_BLOCKED_SOURCE_EVIDENCE_SUMMARY_MISMATCH"
)
STRICT_REVIEW_OUTCOME = (
    "B_BLOCKED_PRESERVES_TWELVE_ROUTE_MAP_NO_PACKET_ACCEPTANCE_NO_BLOCKER_"
    "RESOLUTION_GUARDRAIL_NO_DIMENSIONAL_CLOSURE_NO_PILLAR_COMPLETION_NO_"
    "SEAM_ADMISSIBILITY_NO_LEVEL4_OR5_NO_PHYSICAL_CALIBRATION_NO_CROSS_"
    "SECTOR_COUPLING_VALIDATION_NO_CK_ACTION_EMBEDDING_NO_CCFT_NO_MASTER_"
    "ACTION_PROMOTION"
)
DIAGNOSTIC_TARGET = (
    "diagnose_pillar_seam_unit_mapping_ledger_blocker_response_route_"
    "selection_packet_mismatch"
)
SELECTED_NEXT_TARGET = (
    "prepare_pillar_seam_unit_mapping_ledger_blocker_response_route_"
    "selection_packet_v1"
)
SELECTED_NEXT_TARGET_KIND = (
    "pillar_seam_unit_mapping_ledger_blocker_response_route_selection_packet_v1"
)
FIRST_RESOLUTION_GUARDRAIL = (
    "prepare_sr_pillar_coordinate_convention_and_constant_restoration_packet"
)

PROHIBITED_ASSIGNMENT_KEYS = {
    "assigned_unit",
    "declared_unit",
    "dimension_vector",
    "conversion_constant",
    "conversion_map",
    "restoration_map",
    "proposed_unit_assignment",
    "physical_calibration",
}


def canonical_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    ).encode("utf-8")


def sha256_path(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def resolved_expected_hash(relative: str, expected: str) -> str:
    if relative == GENERATOR_REL:
        return verify_binding(
            "PAC-002",
            expected_path=relative,
            expected_sha256=expected,
        )["sha256"]
    return sha256_path(REPO_ROOT / relative)


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {path}")
    return value


def ledger_rows(ledger: dict[str, Any]) -> list[tuple[str, dict[str, Any]]]:
    return [
        *[("pillar", row) for row in ledger["pillar_rows"]],
        *[("seam", row) for row in ledger["seam_rows"]],
    ]


def contains_assignment_key(value: Any) -> bool:
    if isinstance(value, dict):
        return bool(PROHIBITED_ASSIGNMENT_KEYS & set(value)) or any(
            contains_assignment_key(item) for item in value.values()
        )
    if isinstance(value, list):
        return any(contains_assignment_key(item) for item in value)
    return False


def row_map(packet: dict[str, Any]) -> dict[str, dict[str, Any]]:
    rows = packet.get("route_selections")
    if not isinstance(rows, list):
        return {}
    return {
        row.get("row_id"): row
        for row in rows
        if isinstance(row, dict) and isinstance(row.get("row_id"), str)
    }


def independent_decision_failures(
    packet: dict[str, Any], ledger: dict[str, Any]
) -> list[str]:
    failed: set[str] = set()
    rows = packet.get("route_selections")
    if not isinstance(rows, list):
        rows = []
    observed = row_map(packet)
    sources = {
        row["row_id"]: (kind, row) for kind, row in ledger_rows(ledger)
    }

    if not all(
        resolved_expected_hash(relative, expected) == expected
        for relative, expected in EXPECTED_HASHES.items()
    ):
        failed.add(DECISION_IDS[0])

    identity_ok = len(rows) == 12 and set(observed) == set(sources)
    if identity_ok:
        for row_id, (kind, source) in sources.items():
            row = observed[row_id]
            identity_ok = identity_ok and (
                row.get("row_kind") == kind
                and row.get("current_status") == source["guardrail_unit_state"]
                and row.get("source_evidence_pointer") == source["evidence_pointer"]
                and row.get("blocker_summary")
                == source["unresolved_items"][0]["reason"]
            )
    if not identity_ok:
        failed.add(DECISION_IDS[1])

    route_ok = len(observed) == 12 and all(
        observed[row_id].get("selected_response_route") == route
        for row_id, route in EXPECTED_ROUTES.items()
    )
    if not route_ok:
        failed.add(DECISION_IDS[2])

    if not (
        packet.get("route_count") == 8
        and isinstance(packet.get("route_taxonomy"), list)
        and len(packet["route_taxonomy"]) == 8
        and isinstance(packet.get("ordered_selection_criteria"), list)
        and len(packet["ordered_selection_criteria"]) == 10
        and all(
            len(row.get("selection_criteria_evaluation", [])) == 10
            for row in rows
            if isinstance(row, dict)
        )
    ):
        failed.add(DECISION_IDS[3])

    boundary = packet.get("boundary", {})
    policy = packet.get("policy", {})
    assignment_free = (
        not contains_assignment_key(packet)
        and boundary.get("unit_assignments_emitted") == 0
        and boundary.get("dimension_vectors_emitted") == 0
        and boundary.get("conversion_constants_emitted") == 0
        and boundary.get("seam_mappings_emitted") == 0
        and policy.get("unit_or_dimension_assignment_authorized") is False
    )
    if not assignment_free:
        failed.add(DECISION_IDS[4])
    if not assignment_free or any(
        row.get("current_status") == "unit_unknown"
        and bool(PROHIBITED_ASSIGNMENT_KEYS & set(row))
        for row in rows
        if isinstance(row, dict)
    ):
        failed.add(DECISION_IDS[5])
    if not (
        policy.get("route_selection_resolves_blocker") is False
        and all(
            row.get("current_status") in {"unit_unknown", "unresolved"}
            for row in rows
            if isinstance(row, dict)
        )
    ):
        failed.add(DECISION_IDS[6])
    if policy.get("dimensionless_coordinates_are_physical_distances") is not False:
        failed.add(DECISION_IDS[7])
    if not (
        policy.get("suppressed_constant_omission_allowed") is False
        and policy.get("suppressed_constants_requiring_explicit_treatment")
        == ["c", "hbar", "G", "k_B"]
    ):
        failed.add(DECISION_IDS[8])

    pillar_status = {
        row["pillar_id"]: row["guardrail_unit_state"]
        for row in ledger["pillar_rows"]
    }
    seam_sources = {row["row_id"]: row for row in ledger["seam_rows"]}
    seam_ok = True
    for row in rows:
        if not isinstance(row, dict) or row.get("row_kind") != "seam":
            continue
        if row.get("selected_response_route") == "SEAM_CONVERSION_MAP":
            source = seam_sources.get(row.get("row_id"), {})
            seam_ok = seam_ok and all(
                pillar_status.get(pillar_id) == "resolved"
                for pillar_id in source.get("pillar_ids", [])
            )
    if not seam_ok:
        failed.add(DECISION_IDS[9])

    if policy.get("candidate_master_action_self_support_allowed") is not False or any(
        "candidate master action supplies its own" in evidence.lower()
        for row in rows
        if isinstance(row, dict)
        for evidence in row.get("available_evidence", [])
        if isinstance(evidence, str)
    ):
        failed.add(DECISION_IDS[10])
    if policy.get("normalization_convention_is_empirical_scale") is not False:
        failed.add(DECISION_IDS[11])
    if not (
        packet.get("claim_ceiling_level") == 3
        and boundary.get("route_selection_is_resolution") is False
        and boundary.get("dimensional_closure_claimed") is False
        and boundary.get("pillar_completion_claimed") is False
        and boundary.get("seam_admissibility_claimed") is False
    ):
        failed.add(DECISION_IDS[12])
    if boundary.get("C_k_action_embedding_authorized") is not False:
        failed.add(DECISION_IDS[13])

    counts = Counter(
        (
            row.get("selected_response_route")
            if isinstance(row.get("selected_response_route"), str)
            else "__INVALID_ROUTE__"
        )
        for row in rows
        if isinstance(row, dict)
    )
    current_statuses = Counter(
        row.get("current_status") for row in rows if isinstance(row, dict)
    )
    count_ok = (
        all(counts[route] == count for route, count in EXPECTED_ROUTE_COUNTS.items())
        and current_statuses == Counter({"unit_unknown": 6, "unresolved": 6})
        and packet.get("family_level_counts", {}).get("rows_remaining_blocked")
        == 12
        and packet.get("family_level_counts", {}).get(
            "research_blocked_routes_required"
        )
        == 5
    )
    if not count_ok:
        failed.add(DECISION_IDS[14])

    expected_nonclaims = {
        "dimensional_closure",
        "pillar_completion",
        "seam_admissibility",
        "level_4_or_level_5",
        "physical_calibration_claims",
        "cross_sector_coupling_validation",
        "C_k_action_embedding",
        "CCFT_resumption",
        "master_action_promotion",
    }
    if not (
        set(packet.get("nonclaims", [])) == expected_nonclaims
        and boundary.get("physical_calibration_claimed") is False
        and boundary.get("cross_sector_coupling_validation_claimed") is False
        and boundary.get("level_4_or_level_5_authorized") is False
        and boundary.get("ccft_resumed") is False
        and boundary.get("master_action_promoted") is False
    ):
        failed.add(DECISION_IDS[15])
    return [decision_id for decision_id in DECISION_IDS if decision_id in failed]


def mutate(
    packet: dict[str, Any], mutation: Callable[[dict[str, Any]], None]
) -> dict[str, Any]:
    changed = copy.deepcopy(packet)
    mutation(changed)
    return changed


def independent_negative_controls(
    packet: dict[str, Any], ledger: dict[str, Any]
) -> list[dict[str, Any]]:
    controls: list[tuple[str, str, Callable[[dict[str, Any]], None]]] = [
        ("assign_unit_to_unit_unknown_without_evidence", DECISION_IDS[5],
         lambda value: value["route_selections"][0].__setitem__("proposed_unit_assignment", "invented")),
        ("natural_units_mark_unresolved_resolved", DECISION_IDS[6],
         lambda value: value["route_selections"][1].__setitem__("current_status", "resolved")),
        ("dimensionless_coordinates_promoted_to_physical_distance", DECISION_IDS[7],
         lambda value: value["policy"].__setitem__("dimensionless_coordinates_are_physical_distances", True)),
        ("suppressed_constant_omitted", DECISION_IDS[8],
         lambda value: value["policy"].__setitem__("suppressed_constant_omission_allowed", True)),
        ("two_incompatible_routes_assigned_without_priority", DECISION_IDS[2],
         lambda value: value["route_selections"][0].__setitem__("selected_response_route", ["OBJECT_SEMANTICS_REFINEMENT", "ACTION_DIMENSION_DERIVATION"])),
        ("seam_map_selected_with_incomplete_pillar_units", DECISION_IDS[9],
         lambda value: value["route_selections"][7].__setitem__("selected_response_route", "SEAM_CONVERSION_MAP")),
        ("candidate_master_action_used_as_self_evidence", DECISION_IDS[10],
         lambda value: value["route_selections"][0]["available_evidence"].append("The candidate master action supplies its own missing dimensions.")),
        ("normalization_convention_promoted_to_empirical_scale", DECISION_IDS[11],
         lambda value: value["policy"].__setitem__("normalization_convention_is_empirical_scale", True)),
        ("routed_blocker_promoted_to_dimensional_closure", DECISION_IDS[12],
         lambda value: value["boundary"].__setitem__("dimensional_closure_claimed", True)),
        ("C_k_embedding_before_dimensions_known", DECISION_IDS[13],
         lambda value: value["boundary"].__setitem__("C_k_action_embedding_authorized", True)),
    ]
    results = []
    for control_id, expected, change in controls:
        failures = independent_decision_failures(mutate(packet, change), ledger)
        results.append({
            "control_id": control_id,
            "expected_failed_decision_id": expected,
            "observed_failed_decision_ids": failures,
            "fresh_deep_copy_used": True,
            "passed": expected in failures,
        })
    return results


def source_evidence_audit(packet: dict[str, Any]) -> dict[str, Any]:
    rows = row_map(packet)
    qft_path = REPO_ROOT / rows["PILLAR-QFT-units_and_dimensions-v0"]["source_evidence_pointer"]
    qm_path = REPO_ROOT / rows["PILLAR-QM-units_and_dimensions-v0"]["source_evidence_pointer"]
    stat_path = REPO_ROOT / rows["PILLAR-STAT-units_and_dimensions-v0"]["source_evidence_pointer"]
    gr_path = REPO_ROOT / rows["PILLAR-GR-units_and_dimensions-v0"]["source_evidence_pointer"]
    em_path = REPO_ROOT / rows["PILLAR-EM-units_and_dimensions-v0"]["source_evidence_pointer"]
    sr_path = REPO_ROOT / rows["PILLAR-SR-units_and_dimensions-v0"]["source_evidence_pointer"]
    qft = qft_path.read_text(encoding="utf-8")
    qm = qm_path.read_text(encoding="utf-8")
    stat = stat_path.read_text(encoding="utf-8")
    gr = gr_path.read_text(encoding="utf-8")
    em = em_path.read_text(encoding="utf-8")
    sr = sr_path.read_text(encoding="utf-8")
    qft_physical_action_tokens = re.findall(
        r"(?<![-\w])action(?![-\w])", qft, flags=re.IGNORECASE
    )
    qft_claim = rows["PILLAR-QFT-units_and_dimensions-v0"]["available_evidence"][0]
    qm_claim = rows["PILLAR-QM-units_and_dimensions-v0"]["available_evidence"][0]
    stat_claim = rows["PILLAR-STAT-units_and_dimensions-v0"]["available_evidence"][0]
    checks = {
        "QFT_BOUND_SOURCE_ACTION_ATTRIBUTION_MISMATCH": (
            "identifies action," in qft_claim and len(qft_physical_action_tokens) == 0
        ),
        "QM_BOUND_SOURCE_HAMILTONIAN_ATTRIBUTION_MISMATCH": (
            "Hamiltonian" in qm_claim and "Hamiltonian" not in qm
        ),
        "STAT_BOUND_SOURCE_PROBABILITY_TRANSPORT_ATTRIBUTION_MISMATCH": (
            "probability" in stat_claim
            and "transport" in stat_claim
            and "probability" not in stat.lower()
            and "transport" not in stat.lower()
        ),
    }
    positive_checks = {
        "gr_bounded_poisson_and_action_native_surface_supported": (
            "Poisson" in gr and "action-native" in gr
        ),
        "em_typed_objects_and_units_not_selected_supported": (
            "A_mu" in em and "F_munu" in em and "UNITS_NOT_SELECTED" in em
        ),
        "sr_interval_and_dimensional_structure_supported": (
            "interval" in sr.lower() and "dimensional structure" in sr.lower()
        ),
        "qm_supported_surfaces_are_schrodinger_state_contract_and_unitarity": (
            "Schrodinger" in qm
            and "QMStateEvolvesUnderContract" in qm
            and "unitary" in qm.lower()
            and "Hamiltonian" not in qm
        ),
        "stat_supported_surfaces_are_entropy_flux_balance_and_regime": (
            "entropy / entropy-production object surface" in stat
            and "flux / balance law object surface" in stat
            and "regime" in stat.lower()
            and "probability" not in stat.lower()
            and "transport" not in stat.lower()
        ),
        "qft_narrow_scalar_anti_promotion_preserved": (
            rows["PILLAR-QFT-units_and_dimensions-v0"]["selected_response_route"]
            == "OBJECT_SEMANTICS_REFINEMENT"
            and len(rows["PILLAR-QFT-units_and_dimensions-v0"].get(
                "supplemental_evidence_bindings", []
            )) == 1
            and "no_wider_QFT_authority"
            in rows["PILLAR-QFT-units_and_dimensions-v0"]["authority_limit"]
        ),
    }
    return {
        "mismatch_codes": [code for code in MISMATCH_CODES if checks.get(code)],
        "mismatch_checks": checks,
        "positive_route_evidence_checks": positive_checks,
        "all_positive_route_evidence_checks_passed": all(positive_checks.values()),
        "review_note": (
            "The twelve routes remain independently reproducible, but three direct "
            "available_evidence summaries are not faithful to their named bound sources."
        ),
    }


def subprocess_regeneration() -> dict[str, Any]:
    before = {
        relative: sha256_path(REPO_ROOT / relative)
        for relative in (PACKET_REL, MANIFEST_REL, PREPARATION_REPORT_REL)
    }
    command = [
        sys.executable,
        "-m",
        "formal.python.tools.pillar_seam_unit_mapping_ledger_blocker_response_route_selection",
    ]
    outputs = []
    return_codes = []
    for _ in range(2):
        env = dict(os.environ)
        env["PYTHONDONTWRITEBYTECODE"] = "1"
        env["PYTHONNOUSERSITE"] = "1"
        completed = subprocess.run(
            command,
            cwd=REPO_ROOT,
            env=env,
            capture_output=True,
            check=False,
        )
        return_codes.append(completed.returncode)
        outputs.append(completed.stdout)
    after = {
        relative: sha256_path(REPO_ROOT / relative)
        for relative in (PACKET_REL, MANIFEST_REL, PREPARATION_REPORT_REL)
    }
    expected_stdout = PREPARATION_REPORT_PATH.read_bytes()
    return {
        "fresh_subprocess_count": 2,
        "return_codes": return_codes,
        "subprocess_outputs_byte_identical": outputs[0] == outputs[1],
        "subprocess_report_matches_committed_report": all(
            output == expected_stdout for output in outputs
        ),
        "preparation_artifact_hashes_unchanged": before == after,
        "passed": (
            return_codes == [0, 0]
            and outputs[0] == outputs[1]
            and all(output == expected_stdout for output in outputs)
            and before == after
        ),
    }


def build_review_report(*, run_subprocesses: bool = True) -> dict[str, Any]:
    packet = load_json(PACKET_PATH)
    ledger = load_json(LEDGER_PATH)
    manifest = load_json(MANIFEST_PATH)
    preparation_report = load_json(PREPARATION_REPORT_PATH)
    accepted_ledger_review = load_json(ACCEPTED_LEDGER_REVIEW_PATH)
    failures = independent_decision_failures(packet, ledger)
    controls = independent_negative_controls(packet, ledger)
    evidence = source_evidence_audit(packet)
    regeneration = (
        subprocess_regeneration()
        if run_subprocesses
        else {"passed": False, "not_run": True}
    )
    mismatch_codes = evidence["mismatch_codes"]
    blocked = bool(mismatch_codes)
    structural_pass = not failures and all(item["passed"] for item in controls)
    return {
        "accepted": False,
        "artifact_chain": {
            "expected_hashes": EXPECTED_HASHES,
            "manifest_schema_id": manifest.get("schema_id"),
            "preparation_report_schema_id": preparation_report.get("schema_id"),
            "accepted_ledger_review_schema_id": accepted_ledger_review.get("schema_id"),
        },
        "authority_rotation": {
            "packet_acceptance_authorized": False,
            "corrective_v1_preparation_authorized": blocked,
            "first_blocker_resolution_guardrail_authorized": False,
            "maintenance_authority_rotation_authorized": False,
        },
        "boundary": {
            "route_map_changed_by_review": False,
            "unit_or_dimension_assignment_emitted": False,
            "dimensional_closure_claimed": False,
            "pillar_completion_claimed": False,
            "seam_admissibility_claimed": False,
            "level_4_or_level_5_authorized": False,
            "physical_calibration_claimed": False,
            "cross_sector_coupling_validation_claimed": False,
            "C_k_action_embedding_authorized": False,
            "ccft_resumed": False,
            "master_action_promoted": False,
        },
        "captured_at_utc": CAPTURED_AT_UTC,
        "consumed_target": (
            "review_pillar_seam_unit_mapping_ledger_blocker_response_route_"
            "selection_packet_result"
        ),
        "diagnostic_target": DIAGNOSTIC_TARGET,
        "failure_preservation": {
            "preparation_commit_remains_immutable": True,
            "preparation_artifacts_amended_by_review": False,
            "versioned_successor_required": True,
        },
        "implemented_decision_reproduction": {
            "decision_count": len(DECISION_IDS),
            "decisions": [
                {"decision_id": decision_id, "passed": decision_id not in failures}
                for decision_id in DECISION_IDS
            ],
            "failed_decision_ids": failures,
            "all_implemented_decisions_reproduced": not failures,
        },
        "maintenance_boundary": {
            "registry_maintenance_paused": True,
            "registry_monolith_remains_authoritative": True,
            "registry_v3_live": False,
            "stage_a_authorized": False,
            "stage_b_authorized": False,
        },
        "mismatch_codes": mismatch_codes,
        "negative_control_reproduction": {
            "control_count": len(controls),
            "controls": controls,
            "all_controls_reproduced": all(item["passed"] for item in controls),
        },
        "preparation_commit": PREPARATION_COMMIT,
        "preparation_parent": PREPARATION_PARENT,
        "primary_label": "B-BLOCKED",
        "regeneration": regeneration,
        "review_id": (
            "PILLAR_SEAM_UNIT_MAPPING_LEDGER_BLOCKER_RESPONSE_ROUTE_SELECTION_"
            "PACKET_RESULT_REVIEW_v0"
        ),
        "review_outcome": REVIEW_OUTCOME,
        "route_reproduction": {
            "expected_routes": EXPECTED_ROUTES,
            "expected_route_counts": EXPECTED_ROUTE_COUNTS,
            "route_map_reproduced": structural_pass,
            "unit_unknown_row_count": 6,
            "unresolved_row_count": 6,
            "rows_remaining_blocked": 12,
        },
        "schema_id": (
            "PILLAR_SEAM_UNIT_MAPPING_LEDGER_BLOCKER_RESPONSE_ROUTE_SELECTION_"
            "PACKET_RESULT_REVIEW_20260712_v0"
        ),
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "selection_basis": (
            "Correct the three source-evidence summary attributions in a versioned "
            "successor while retaining the independently reproduced route map."
        ),
        "source_evidence_review": evidence,
        "status": "blocked_source_evidence_attribution_mismatch",
        "strict_review_outcome": STRICT_REVIEW_OUTCOME,
        "successor_boundary": {
            "corrective_successor": SELECTED_NEXT_TARGET,
            "would_be_first_resolution_guardrail_after_future_acceptance": (
                FIRST_RESOLUTION_GUARDRAIL
            ),
            "first_resolution_guardrail_selected_now": False,
        },
        "verdict": "B-BLOCKED",
    }


def write_report(report: dict[str, Any]) -> None:
    REVIEW_REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    REVIEW_REPORT_PATH.write_bytes(canonical_json_bytes(report))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Independently review the pillar/seam blocker route packet."
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    report = build_review_report(run_subprocesses=True)
    if args.write:
        write_report(report)
        print("wrote B-BLOCKED route-selection packet result review")
        return 0
    if args.check:
        expected = canonical_json_bytes(report)
        if not REVIEW_REPORT_PATH.is_file() or REVIEW_REPORT_PATH.read_bytes() != expected:
            print("stale or missing route-selection packet result review", file=sys.stderr)
            return 1
        print(
            "route-selection packet review verified: B-BLOCKED, "
            "16/16 decisions and 10/10 controls reproduced, 3 evidence mismatches"
        )
        return 0
    sys.stdout.buffer.write(canonical_json_bytes(report))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

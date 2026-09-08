from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parents[3]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from formal.python.tools import (
    native_gravitational_principle_requirements_and_action_selection_packet_v0 as packet,
)


REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_ACTION_SELECTION_PACKET_"
    "REVIEW_20260718_v0.json"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_native_gravitational_principle_requirements_and_action_selection_packet_review_v0.py"
)
REVIEW_RELATIVE_PATH = (
    "formal/docs/lanes/"
    "NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_ACTION_SELECTION_PACKET_"
    "REVIEW_20260718_v0.md"
)
TARGET = (
    "review_native_gravitational_principle_requirements_and_action_selection_packet_v0_result"
)
VERDICT = "BLOCKED_REQUIREMENTS_ACTION_SELECTION_CONTRACT_INCOMPLETE"
PRIMARY_DIAGNOSTIC = "REQUIREMENT_STATEMENT_CLASS_BINDING_MISSING"
SELECTED_NEXT_TARGET = (
    "prepare_native_gravitational_principle_requirements_and_action_selection_packet_v1"
)

AUTHORITY_AND_PACKET_HASHES = {
    "formal/docs/lanes/NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_ACTION_SELECTION_PACKET_20260718_v0.md":
        "b74f94c30298d81671157213845bf761631fb9cc39a8d102b93c236e8199056f",
    "formal/docs/release/NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_ACTION_SELECTION_PACKET_20260718_v0.json":
        "9dcc6df5a5844aecfff6e50c6ad8b67e7f8bac9411bd8c282f5d876d2ac44634",
    "formal/python/tools/native_gravitational_principle_requirements_and_action_selection_packet_v0.py":
        "d25634e5ad6bd59ec85dd25e321bda5ffeff7529557c1419634185d87efc3f9b",
    "formal/python/tests/test_native_gravitational_principle_requirements_and_action_selection_packet_v0.py":
        "5282518d483a33aed986a3babf37061058f8e4a680dcaf3ad8882c3d69ae5c3b",
    "formal/toe_formal/ToeFormal/Derivation/NativeGravitationalPrincipleRequirementsAndActionSelectionPacketV0.lean":
        "40c6e0b41d37ee977d4836c437bc7116efb7150056c95853e833b2a82cce0371",
    "formal/docs/release/NATIVE_GRAVITATIONAL_PRINCIPLE_RESPONSE_SELECTION_20260718_v0.json":
        "e2468ea98384383654efe73dd054f5149beb6d4a62db45123109d962999dea66",
    REVIEW_RELATIVE_PATH:
        "7c17a967d719f0dabf887cf5fb98b7ccaf1d3dbc34f19d8b5f6368d66f2ac7ea",
}

EXPECTED_REQUIREMENT_IDS = [
    "R1_DIMENSION",
    "R2_METRIC_ONLY",
    "R3_LOCALITY",
    "R4_DIFF_COVARIANCE",
    "R5_CK_FIREWALL",
    "R6_LOCAL_VARIATION",
    "R7_SOURCE_COMPATIBILITY",
    "R8_NEWTON_POISSON",
    "R9_MOMENTUM_CURRENT",
    "R10_STABILITY_NO_FIT",
]

FINDINGS = [
    {
        "order": 1,
        "diagnostic": "REQUIREMENT_STATEMENT_CLASS_BINDING_MISSING",
        "severity": "BLOCKING",
        "finding": (
            "All ten requirement rows omit statement_class; authority_status values "
            "are not members of, and have no total frozen mapping to, the declared "
            "three-way statement-class vocabulary."
        ),
    },
    {
        "order": 2,
        "diagnostic": "MATRIX_UNDECIDABLE_STATE_MISSING",
        "severity": "BLOCKING",
        "finding": (
            "The matrix cannot distinguish a completed but epistemically undecidable "
            "comparison from NOT_EVALUATED or an affirmative SURVIVES result."
        ),
    },
    {
        "order": 3,
        "diagnostic": "OUTCOME_PREDICATE_OVERLAP",
        "severity": "BLOCKING",
        "finding": (
            "A unique nondistinctive F_EH survivor selected without supplied uniqueness "
            "premises satisfies both native-selection and standard-GR-collapse gates; "
            "the earlier gate makes the intended collapse classification unreachable."
        ),
    },
    {
        "order": 4,
        "diagnostic": "CONTROL_ANALYSIS_PATH_NOT_EXECUTABLE",
        "severity": "BLOCKING",
        "finding": (
            "The packet module exposes construction and static validation but no shared "
            "matrix classifier, decision evaluator, or control entry point through which "
            "the eight promised mutations can execute end to end."
        ),
    },
]

REVIEW_GATES = [
    {"order": 1, "gate": "custody and deterministic reproduction", "status": "PASS"},
    {"order": 2, "gate": "ten requirement source bindings", "status": "PASS"},
    {"order": 3, "gate": "three-way statement class bound per row", "status": "FAIL"},
    {"order": 4, "gate": "bounded comparison-family adequacy", "status": "PASS"},
    {"order": 5, "gate": "matrix epistemic-state completeness", "status": "FAIL"},
    {"order": 6, "gate": "local-bulk equivalence conservatism", "status": "PASS"},
    {"order": 7, "gate": "independence and redundancy vocabulary", "status": "PASS"},
    {"order": 8, "gate": "standard-GR oracle isolation", "status": "PASS"},
    {"order": 9, "gate": "six-outcome mutual exclusivity", "status": "FAIL"},
    {"order": 10, "gate": "eight end-to-end atomic controls", "status": "FAIL"},
]

REVIEW_CONTROLS = [
    {
        "control_id": "REVIEW_DROP_AUTHORITY_STATUS_AND_QUERY_STATEMENT_CLASS",
        "mutation_count": 1,
        "observed_diagnostic": "REQUIREMENT_STATEMENT_CLASS_BINDING_MISSING",
    },
    {
        "control_id": "REVIEW_REQUIRE_COMPLETED_UNDECIDABLE_MATRIX_CELL",
        "mutation_count": 1,
        "observed_diagnostic": "MATRIX_UNDECIDABLE_STATE_MISSING",
    },
    {
        "control_id": "REVIEW_UNIQUE_NONDISTINCTIVE_EH_WITNESS",
        "mutation_count": 1,
        "observed_diagnostic": "OUTCOME_PREDICATE_OVERLAP",
    },
    {
        "control_id": "REVIEW_LOCATE_SHARED_CONTROL_ANALYSIS_ENTRY_POINT",
        "mutation_count": 1,
        "observed_diagnostic": "CONTROL_ANALYSIS_PATH_NOT_EXECUTABLE",
    },
]


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _validate_custody() -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for relative_path, expected_hash in AUTHORITY_AND_PACKET_HASHES.items():
        observed = _sha256((REPO_ROOT / relative_path).read_bytes())
        if observed != expected_hash:
            raise ValueError(f"requirements packet review hash mismatch: {relative_path}")
        rows.append({"relative_path": relative_path, "sha256": observed})

    packet_report = json.loads(
        (REPO_ROOT / packet.REPORT_RELATIVE_PATH).read_text(encoding="utf-8")
    )
    if packet_report.get("target") != packet.TARGET:
        raise ValueError("reviewed packet target mismatch")
    if packet_report.get("selected_next_target") != TARGET:
        raise ValueError("reviewed packet did not authorize this independent review")
    if packet_report.get("verdict") != "PREPARED_PENDING_INDEPENDENT_REVIEW":
        raise ValueError("reviewed packet preparation verdict mismatch")
    if packet_report["scope"].get("requirements_selection_analysis_executed") is not False:
        raise ValueError("packet unexpectedly executed the scientific analysis")

    for frozen in packet_report["authority"]["frozen_inputs"]:
        relative_path = frozen["relative_path"]
        observed = _sha256((REPO_ROOT / relative_path).read_bytes())
        if observed != frozen["sha256"]:
            raise ValueError(f"packet frozen input changed: {relative_path}")
    return rows


def _audit_requirement_sources(report: dict[str, Any]) -> list[dict[str, Any]]:
    rows = report["requirement_inventory"]["rows"]
    if [row["requirement_id"] for row in rows] != EXPECTED_REQUIREMENT_IDS:
        raise ValueError("requirement inventory identity or order mismatch")
    frozen_paths = {
        row["relative_path"] for row in report["authority"]["frozen_inputs"]
    }
    audit: list[dict[str, Any]] = []
    for row in rows:
        bindings = row.get("source_bindings", [])
        if not bindings or not set(bindings).issubset(frozen_paths):
            raise ValueError(f"unbound requirement source: {row['requirement_id']}")
        audit.append({
            "requirement_id": row["requirement_id"],
            "source_binding_count": len(bindings),
            "scope_boundary_present": bool(row.get("initial_boundary")),
            "status": "PASS",
        })
    return audit


def _audit_statement_classes(report: dict[str, Any]) -> dict[str, Any]:
    declared = set(report["statement_provenance_contract"]["classes"])
    rows = report["requirement_inventory"]["rows"]
    bound = [row.get("statement_class") for row in rows]
    valid_count = sum(value in declared for value in bound)
    return {
        "declared_classes": sorted(declared),
        "requirement_count": len(rows),
        "valid_bound_statement_class_count": valid_count,
        "missing_statement_class_count": sum(value is None for value in bound),
        "authority_status_is_statement_class": all(
            row.get("authority_status") in declared for row in rows
        ),
        "status": "PASS" if valid_count == len(rows) else "FAIL",
        "diagnostic": "REQUIREMENT_STATEMENT_CLASS_BINDING_MISSING",
    }


def _audit_matrix_vocabulary(report: dict[str, Any]) -> dict[str, Any]:
    values = report["survival_elimination_matrix_contract"]["cell_values"]
    required = "NOT_DECIDABLE_FROM_REQUIREMENT"
    return {
        "current_values": values,
        "required_completed_analysis_state": required,
        "required_state_present": required in values,
        "not_evaluated_is_equivalent_to_undecidable": False,
        "survives_is_equivalent_to_undecidable": False,
        "status": "PASS" if required in values else "FAIL",
        "diagnostic": "MATRIX_UNDECIDABLE_STATE_MISSING",
    }


def _audit_outcome_overlap(report: dict[str, Any]) -> dict[str, Any]:
    outcomes = {
        row["outcome"]: row["precondition"]
        for row in report["outcome_contract"]["decision_order"]
    }
    native = outcomes["NATIVE_PRINCIPLE_SET_SELECTS_ACTION_FAMILY"]
    collapse = outcomes["CURRENT_REQUIREMENTS_COLLAPSE_TO_STANDARD_GR"]
    native_excludes_eh_only = "exclude" in native.lower() and "einstein" in native.lower()
    collapse_requires_eh = "Einstein-Hilbert" in collapse
    matching = [
        "NATIVE_PRINCIPLE_SET_SELECTS_ACTION_FAMILY",
        "CURRENT_REQUIREMENTS_COLLAPSE_TO_STANDARD_GR",
    ] if collapse_requires_eh and not native_excludes_eh_only else []
    return {
        "witness": {
            "consistent": True,
            "unique_survivor": "F_EH",
            "supplied_uniqueness_assumption_used": False,
            "project_specific_distinctiveness_demonstrated": False,
        },
        "matching_outcomes": matching,
        "matching_outcome_count": len(matching),
        "first_match_result_under_v0_order": matching[0] if matching else None,
        "intended_specific_classification": "CURRENT_REQUIREMENTS_COLLAPSE_TO_STANDARD_GR",
        "status": "PASS" if len(matching) <= 1 else "FAIL",
        "diagnostic": "OUTCOME_PREDICATE_OVERLAP",
    }


def _audit_control_path() -> dict[str, Any]:
    public_callables = sorted(
        name
        for name, value in vars(packet).items()
        if callable(value) and not name.startswith("_") and getattr(value, "__module__", None) == packet.__name__
    )
    analysis_names = {
        "analyze",
        "classify_matrix",
        "evaluate_outcome",
        "run_control",
        "execute_analysis",
    }
    found = sorted(set(public_callables).intersection(analysis_names))
    return {
        "public_packet_callables": public_callables,
        "recognized_analysis_entry_points": found,
        "declared_control_count": len(packet.ATOMIC_CONTROLS),
        "end_to_end_control_count": 0 if not found else len(packet.ATOMIC_CONTROLS),
        "status": "FAIL" if not found else "PASS",
        "diagnostic": "CONTROL_ANALYSIS_PATH_NOT_EXECUTABLE",
    }


def build_review() -> dict[str, Any]:
    custody = _validate_custody()
    source_report = json.loads(
        (REPO_ROOT / packet.REPORT_RELATIVE_PATH).read_text(encoding="utf-8")
    )
    source_audit = _audit_requirement_sources(source_report)
    class_audit = _audit_statement_classes(source_report)
    matrix_audit = _audit_matrix_vocabulary(source_report)
    overlap_audit = _audit_outcome_overlap(source_report)
    control_audit = _audit_control_path()
    if class_audit["status"] != "FAIL":
        raise ValueError("review expected missing per-row statement classes")
    if matrix_audit["status"] != "FAIL":
        raise ValueError("review expected missing undecidable matrix state")
    if overlap_audit["matching_outcome_count"] != 2:
        raise ValueError("review outcome-overlap witness did not reproduce")
    if control_audit["status"] != "FAIL":
        raise ValueError("review unexpectedly found executable control path")
    if [row["order"] for row in FINDINGS] != [1, 2, 3, 4]:
        raise ValueError("review finding order mismatch")
    if len(REVIEW_CONTROLS) != 4 or not all(
        row["mutation_count"] == 1 for row in REVIEW_CONTROLS
    ):
        raise ValueError("review control contract mismatch")
    tool_path = Path(__file__).resolve()
    test_path = REPO_ROOT / TEST_RELATIVE_PATH
    if not test_path.exists():
        raise ValueError("requirements packet review focused test missing")

    return {
        "schema_id": (
            "NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_ACTION_SELECTION_"
            "PACKET_REVIEW_20260718_v0"
        ),
        "captured_at_utc": "2026-07-18T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "primary_diagnostic": PRIMARY_DIAGNOSTIC,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": (
            "PREPARATION_ONLY_REQUIREMENTS_ACTION_SELECTION_PACKET_V1_REPAIR"
        ),
        "authority": {
            "reviewed_packet_verdict": "PREPARED_PENDING_INDEPENDENT_REVIEW",
            "frozen_inputs": custody,
            "generator": {
                "relative_path": tool_path.relative_to(REPO_ROOT).as_posix(),
                "sha256": _sha256(tool_path.read_bytes()),
            },
            "test": {
                "relative_path": TEST_RELATIVE_PATH,
                "sha256": _sha256(test_path.read_bytes()),
            },
        },
        "review_answer": (
            "The ten requirement sources and seven-family comparison envelope are "
            "retained, but v0 is not executable as a safe action-selection analysis. "
            "Requirement rows do not bind the declared statement class; the matrix "
            "lacks an epistemic-undecidability state; native-selection and standard-GR "
            "collapse predicates overlap; and the controls have no shared executable "
            "analysis path."
        ),
        "review_gates": {
            "gate_count": len(REVIEW_GATES),
            "pass_count": sum(row["status"] == "PASS" for row in REVIEW_GATES),
            "failure_count": sum(row["status"] == "FAIL" for row in REVIEW_GATES),
            "rows": REVIEW_GATES,
        },
        "requirement_source_audit": {
            "requirement_count": len(source_audit),
            "pass_count": sum(row["status"] == "PASS" for row in source_audit),
            "rows": source_audit,
        },
        "statement_class_audit": class_audit,
        "family_envelope_audit": {
            "family_count": source_report["comparison_family_envelope"]["family_count"],
            "bounded_catalog": True,
            "adequate_for_first_selection_power_test": True,
            "exhaustive_claimed": False,
            "family_adopted_count": 0,
            "status": "PASS",
        },
        "matrix_vocabulary_audit": matrix_audit,
        "equivalence_audit": {
            "allowed_rule_count": source_report["equivalence_contract"]["allowed_rule_count"],
            "forbidden_rule_count": source_report["equivalence_contract"]["forbidden_rule_count"],
            "local_bulk_scope_preserved": True,
            "physically_distinct_dynamics_merged": False,
            "status": "PASS",
        },
        "standard_GR_isolation_audit": {
            "oracle_role": source_report["standard_GR_isolation"]["Einstein_Hilbert_role"],
            "Einstein_equation_used_as_selection_premise": False,
            "supplied_second_order_assumption_counted_native": False,
            "comparator_activated": False,
            "status": "PASS",
        },
        "outcome_overlap_audit": overlap_audit,
        "control_path_audit": control_audit,
        "findings": {
            "finding_count": len(FINDINGS),
            "blocking_count": sum(row["severity"] == "BLOCKING" for row in FINDINGS),
            "rows": FINDINGS,
        },
        "review_controls": {
            "control_count": len(REVIEW_CONTROLS),
            "all_single_mutation": True,
            "rows": REVIEW_CONTROLS,
        },
        "required_v1_repairs": [
            "bind one exact three-way statement_class to every requirement and optional premise",
            "add a completed-analysis NOT_DECIDABLE_FROM_REQUIREMENT matrix state",
            "make all six outcome predicates disjoint and test zero overlap",
            "provide one bounded table-analysis entry point shared by valid analysis and all eight controls",
            "preserve all ten sources seven families standard-GR isolation equivalence rules and nonclaims",
        ],
        "retained_results": {
            "requirement_source_bindings": "10_OF_10_RETAINED",
            "comparison_family_envelope": "7_OF_7_RETAINED",
            "standard_GR_isolation": "RETAINED",
            "local_bulk_equivalence_scope": "RETAINED",
            "minimal_gravitational_contract": "ACCEPTED",
            "native_candidate_readiness": "BLOCKED_NO_NATIVE_GRAVITATIONAL_PRINCIPLE",
        },
        "scope": {
            "independent_review_executed": True,
            "packet_block_recorded": True,
            "v1_packet_prepared_now": False,
            "requirements_selection_analysis_executed": False,
            "survivor_matrix_computed": False,
            "scientific_outcome_selected": False,
            "native_gravitational_principle_identified": False,
            "new_postulate_authorized": False,
            "gravitational_action_proposed_or_selected": False,
            "action_family_eliminated_or_adopted": False,
            "standard_GR_comparator_activated": False,
            "matter_sector_selected": False,
            "metric_or_tetrad_variation_executed": False,
            "stress_energy_derived": False,
            "tensor_field_equation_derived": False,
            "gravitomagnetic_route_reopened": False,
            "C_k_embedded_or_varied": False,
            "general_symbolic_or_theory_enumeration_tooling_created": False,
            "simulation_executed": False,
            "empirical_analysis_executed": False,
            "master_action_promoted": False,
            "GR_pillar_completed": False,
            "seam_closed": False,
            "automation_created": False,
        },
        "claim_ceiling": (
            "Independent packet review only. Ten source bindings, seven comparison "
            "families, standard-GR isolation, and conservative local-bulk equivalence "
            "are retained. V0 is blocked by missing per-row statement classes, a missing "
            "epistemic-undecidability matrix state, overlapping native-selection and "
            "standard-GR-collapse predicates, and no executable shared control path. "
            "No survivor analysis, family judgment, principle, postulate, action, matter "
            "sector, variation, GR result, tooling lane, or automation is created."
        ),
    }


def artifact_bytes() -> bytes:
    return (
        json.dumps(build_review(), indent=2, sort_keys=True, ensure_ascii=True) + "\n"
    ).encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    report_path = REPO_ROOT / REPORT_RELATIVE_PATH
    raw = artifact_bytes()
    if args.check:
        if not report_path.exists() or report_path.read_bytes() != raw:
            raise SystemExit("native-principle packet review is stale or missing")
        report = json.loads(raw)
        print(json.dumps({
            "failures": report["review_gates"]["failure_count"],
            "findings": report["findings"]["finding_count"],
            "source_bindings": report["requirement_source_audit"]["pass_count"],
            "status": "CHECKED",
            "verdict": report["verdict"],
        }, sort_keys=True))
        return 0
    report_path.write_bytes(raw)
    print(report_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

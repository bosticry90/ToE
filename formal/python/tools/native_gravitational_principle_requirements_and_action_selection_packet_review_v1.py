from __future__ import annotations

import argparse
import copy
import hashlib
import json
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from formal.python.tools import (  # noqa: E402
    native_gravitational_principle_requirements_and_action_selection_packet_v1 as packet,
)


REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_ACTION_SELECTION_PACKET_"
    "REVIEW_20260718_v1.json"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_native_gravitational_principle_requirements_and_action_selection_packet_review_v1.py"
)
REVIEW_RELATIVE_PATH = (
    "formal/docs/lanes/"
    "NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_ACTION_SELECTION_PACKET_"
    "REVIEW_20260718_v1.md"
)
TARGET = (
    "review_native_gravitational_principle_requirements_and_action_selection_"
    "packet_v1_result"
)
VERDICT = "BLOCKED_REQUIREMENTS_ACTION_SELECTION_PRODUCTION_SEMANTICS_INCOMPLETE"
PRIMARY_DIAGNOSTIC = "STATEMENT_CLASS_AUTHORITY_BINDING_NOT_ENFORCED"
SELECTED_NEXT_TARGET = (
    "prepare_native_gravitational_principle_requirements_and_action_selection_"
    "packet_v2"
)

AUTHORITY_AND_PACKET_HASHES = {
    "formal/docs/lanes/NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_ACTION_SELECTION_PACKET_20260718_v1.md":
        "4ed85fe1318a9923d55aa9c657a875336ebc78298cb9384659cf860fcfa48363",
    "formal/docs/release/NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_ACTION_SELECTION_PACKET_20260718_v1.json":
        "4121be7c310fde29a6a34e11b07817d410c7bfb0ae1a5a9996cb288efedc3ba1",
    "formal/python/tools/native_gravitational_principle_requirements_and_action_selection_packet_v1.py":
        "fffd0f6bfd38b57d913bb2f4aa13a402bd22495c47b27c03312e1be137d6b06e",
    "formal/python/tests/test_native_gravitational_principle_requirements_and_action_selection_packet_v1.py":
        "1acbc061344e1c7a78c14ef1af9ca1e2e6a82400ed6f8907534fe2f334f7ad96",
    "formal/toe_formal/ToeFormal/Derivation/NativeGravitationalPrincipleRequirementsAndActionSelectionPacketV1.lean":
        "9e2a5fe395f4154a5e132f703273fe90235147362f8245fb9339c638fc19f45d",
    REVIEW_RELATIVE_PATH:
        "66322dff48e73303dbcdd803cd50519efb9ccf667870721e8d10bfac2cb795aa",
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
        "diagnostic": "STATEMENT_CLASS_AUTHORITY_BINDING_NOT_ENFORCED",
        "severity": "BLOCKING",
        "finding": (
            "The production preflight compares two caller-supplied class fields rather "
            "than a frozen canonical authority record, so relabeling both fields "
            "changes native-selection behavior without a pre-matrix failure."
        ),
    },
    {
        "order": 2,
        "diagnostic": "MATRIX_CELL_EVIDENCE_BINDING_NOT_ENFORCED",
        "severity": "BLOCKING",
        "finding": (
            "Affirmative and local-bulk-equivalence cell strings count as satisfaction "
            "without a typed evidence record, proof identity, or source binding."
        ),
    },
    {
        "order": 3,
        "diagnostic": "EQUIVALENCE_PROOF_POLICY_NOT_ENFORCED",
        "severity": "BLOCKING",
        "finding": (
            "The equivalence preflight checks only member/representative pair presence; "
            "an unknown proof class can merge F_FR into F_EH and manufacture standard-GR "
            "collapse."
        ),
    },
    {
        "order": 4,
        "diagnostic": "UNDECIDABLE_EQUIVALENCE_CLASS_ERASED",
        "severity": "BLOCKING",
        "finding": (
            "The reducer subtracts an unresolved representative whenever the same "
            "representative is affirmative elsewhere, allowing a class with an "
            "unresolved member to be classified as uniquely complete."
        ),
    },
    {
        "order": 5,
        "diagnostic": "VIABLE_DISTINCTIVENESS_NO_GO_BRANCH_UNREACHABLE",
        "severity": "BLOCKING",
        "finding": (
            "The distinctiveness-no-go flag is inspected only for an empty possible set, "
            "so viable gravity with proved impossibility of distinctiveness returns "
            "underdetermination instead of the frozen no-go outcome."
        ),
    },
]


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _validate_custody() -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for relative_path, expected_hash in AUTHORITY_AND_PACKET_HASHES.items():
        observed = _sha256((REPO_ROOT / relative_path).read_bytes())
        if observed != expected_hash:
            raise ValueError(f"requirements v1 review hash mismatch: {relative_path}")
        rows.append({"relative_path": relative_path, "sha256": observed})

    report = json.loads(
        (REPO_ROOT / packet.REPORT_RELATIVE_PATH).read_text(encoding="utf-8")
    )
    if report.get("target") != packet.TARGET:
        raise ValueError("reviewed v1 packet target mismatch")
    if report.get("selected_next_target") != TARGET:
        raise ValueError("reviewed v1 packet did not authorize this review")
    if report.get("verdict") != "PREPARED_PENDING_INDEPENDENT_REVIEW":
        raise ValueError("reviewed v1 packet verdict mismatch")
    if report["scope"].get("real_requirements_family_analysis_executed") is not False:
        raise ValueError("reviewed v1 packet unexpectedly executed real analysis")
    if report["matrix_contract"].get("real_matrix_cells_supplied_by_preparation") != 0:
        raise ValueError("reviewed v1 packet contains real matrix cells")
    return rows


def _audit_static_statement_rows() -> dict[str, Any]:
    rows = packet.REPAIRED_REQUIREMENTS
    ids = [row["requirement_id"] for row in rows]
    exact = (
        ids == EXPECTED_REQUIREMENT_IDS
        and all(
            row["statement_class"] == "PROJECT_BOUND_NATIVE_REQUIREMENT"
            and row["statement_class"] == row["source_class_expected"]
            and row["class_binding_immutable"] is True
            for row in rows
        )
    )
    return {
        "requirement_count": len(rows),
        "requirement_ids": ids,
        "exact_static_class_count": sum(
            row["statement_class"] == "PROJECT_BOUND_NATIVE_REQUIREMENT"
            and row["statement_class"] == row["source_class_expected"]
            for row in rows
        ),
        "status": "PASS" if exact else "FAIL",
    }


def _audit_source_class_enforcement() -> dict[str, Any]:
    affirmative = "AFFIRMATIVELY_SATISFIES_REQUIREMENT"
    eliminated = "ELIMINATED"
    row = copy.deepcopy(
        next(
            item
            for item in packet.REPAIRED_REQUIREMENTS
            if item["requirement_id"] == "R4_DIFF_COVARIANCE"
        )
    )
    row["statement_class"] = "SUPPLIED_STANDARD_PHYSICS_ASSUMPTION"
    row["source_class_expected"] = "SUPPLIED_STANDARD_PHYSICS_ASSUMPTION"
    value = packet._fixture(
        [row],
        ["F_EH"],
        {"R4_DIFF_COVARIANCE": {"F_EH": eliminated}},
    )
    result = packet.evaluate_analysis(value)
    rejected = (
        result["status"] == "PRECHECK_FAILURE"
        and result["matrix_evaluated"] is False
    )
    return {
        "probe_id": "REVIEW_SOURCE_CLASS_DOUBLE_FIELD_RELABEL",
        "canonical_requirement_id": "R4_DIFF_COVARIANCE",
        "expected": "PRECHECK_FAILURE_BEFORE_MATRIX_EVALUATION",
        "observed_status": result["status"],
        "observed_diagnostic": result["diagnostic"],
        "observed_scientific_outcome": result["scientific_outcome"],
        "observed_supplied_exclusion_trace": result.get("summary", {}).get(
            "supplied_assumption_exclusion_trace", []
        ),
        "control_reference_affirmative_token": affirmative,
        "status": "PASS" if rejected else "FAIL",
        "diagnostic": "STATEMENT_CLASS_AUTHORITY_BINDING_NOT_ENFORCED",
    }


def _native_requirement(requirement_id: str = "R") -> dict[str, Any]:
    return packet._synthetic_requirement(requirement_id)


def _audit_cell_evidence() -> dict[str, Any]:
    affirmative = "AFFIRMATIVELY_SATISFIES_REQUIREMENT"
    equivalent = "EQUIVALENT_UNDER_LOCAL_BULK_RULE"
    requirement = _native_requirement()
    affirmative_result = packet.evaluate_analysis(packet._fixture(
        [requirement], ["F_EH"], {"R": {"F_EH": affirmative}}
    ))
    equivalence_result = packet.evaluate_analysis(packet._fixture(
        [requirement], ["F_EH"], {"R": {"F_EH": equivalent}}
    ))
    rejected = all(
        result["status"] == "PRECHECK_FAILURE"
        for result in (affirmative_result, equivalence_result)
    )
    return {
        "probe_id": "REVIEW_UNBOUND_COMPLETED_CELL_EVIDENCE",
        "expected": "BOTH_CELLS_REJECTED_WITHOUT_BOUND_EVIDENCE",
        "affirmative_observed_status": affirmative_result["status"],
        "affirmative_observed_outcome": affirmative_result["scientific_outcome"],
        "equivalence_observed_status": equivalence_result["status"],
        "equivalence_observed_outcome": equivalence_result["scientific_outcome"],
        "status": "PASS" if rejected else "FAIL",
        "diagnostic": "MATRIX_CELL_EVIDENCE_BINDING_NOT_ENFORCED",
    }


def _audit_equivalence_policy() -> dict[str, Any]:
    affirmative = "AFFIRMATIVELY_SATISFIES_REQUIREMENT"
    value = packet._fixture(
        [_native_requirement()],
        ["F_EH", "F_FR"],
        {"R": {"F_EH": affirmative, "F_FR": affirmative}},
        equivalence_map={"F_FR": "F_EH"},
    )
    value["equivalence_proofs"][0]["proof_class"] = (
        "FORBIDDEN_DIFFERENT_PROPAGATING_MODES"
    )
    result = packet.evaluate_analysis(value)
    rejected = (
        result["status"] == "PRECHECK_FAILURE"
        and result["matrix_evaluated"] is False
    )
    return {
        "probe_id": "REVIEW_FORBIDDEN_EQUIVALENCE_PROOF_CLASS",
        "member": "F_FR",
        "representative": "F_EH",
        "submitted_proof_class": "FORBIDDEN_DIFFERENT_PROPAGATING_MODES",
        "expected": "PRECHECK_FAILURE_BEFORE_EQUIVALENCE_REDUCTION",
        "observed_status": result["status"],
        "observed_diagnostic": result["diagnostic"],
        "observed_scientific_outcome": result["scientific_outcome"],
        "observed_affirmative_classes": result.get("summary", {}).get(
            "affirmative_equivalence_classes", []
        ),
        "status": "PASS" if rejected else "FAIL",
        "diagnostic": "EQUIVALENCE_PROOF_POLICY_NOT_ENFORCED",
    }


def _audit_undecidable_propagation() -> dict[str, Any]:
    affirmative = "AFFIRMATIVELY_SATISFIES_REQUIREMENT"
    undecidable = "NOT_DECIDABLE_FROM_REQUIREMENT"
    result = packet.evaluate_analysis(packet._fixture(
        [_native_requirement()],
        ["F_EH", "F_FR"],
        {"R": {"F_EH": affirmative, "F_FR": undecidable}},
        equivalence_map={"F_FR": "F_EH"},
    ))
    summary = result["summary"]
    conservative = (
        summary["unresolved_family_ids"] == ["F_FR"]
        and summary["unresolved_equivalence_classes"] == ["F_EH"]
        and result["scientific_outcome"] == "ACTION_FAMILY_UNDERDETERMINED"
    )
    return {
        "probe_id": "REVIEW_UNDECIDABLE_MEMBER_SHARED_REPRESENTATIVE",
        "expected_unresolved_family_ids": ["F_FR"],
        "expected_unresolved_equivalence_classes": ["F_EH"],
        "expected_scientific_outcome": "ACTION_FAMILY_UNDERDETERMINED",
        "observed_unresolved_family_ids": summary["unresolved_family_ids"],
        "observed_unresolved_equivalence_classes": summary[
            "unresolved_equivalence_classes"
        ],
        "observed_scientific_outcome": result["scientific_outcome"],
        "status": "PASS" if conservative else "FAIL",
        "diagnostic": "UNDECIDABLE_EQUIVALENCE_CLASS_ERASED",
    }


def _audit_viable_no_go() -> dict[str, Any]:
    affirmative = "AFFIRMATIVELY_SATISFIES_REQUIREMENT"
    result = packet.evaluate_analysis(packet._fixture(
        [_native_requirement()],
        ["F_FR"],
        {"R": {"F_FR": affirmative}},
        evidence={"distinctiveness_no_go_proved": True},
    ))
    expected = "NO_GO_UNDER_MINIMAL_METRIC_LOCAL_ASSUMPTIONS"
    return {
        "probe_id": "REVIEW_VIABLE_GRAVITY_DISTINCTIVENESS_NO_GO",
        "possible_equivalence_classes": sorted(set(
            result["summary"]["affirmative_equivalence_classes"]
            + result["summary"]["unresolved_equivalence_classes"]
        )),
        "submitted_distinctiveness_no_go_proved": True,
        "expected_scientific_outcome": expected,
        "observed_scientific_outcome": result["scientific_outcome"],
        "status": "PASS" if result["scientific_outcome"] == expected else "FAIL",
        "diagnostic": "VIABLE_DISTINCTIVENESS_NO_GO_BRANCH_UNREACHABLE",
    }


def _audit_shared_controls() -> dict[str, Any]:
    controls = packet.run_production_controls()
    passed = (
        controls["control_count"] == controls["control_pass_count"] == 8
        and controls["boundary_probe_count"]
        == controls["boundary_probe_pass_count"]
        == 2
        and controls["all_used_shared_entry_point"] is True
    )
    return {
        "production_entry_point_id": controls["production_entry_point_id"],
        "control_count": controls["control_count"],
        "control_pass_count": controls["control_pass_count"],
        "boundary_probe_count": controls["boundary_probe_count"],
        "boundary_probe_pass_count": controls["boundary_probe_pass_count"],
        "all_used_shared_entry_point": controls["all_used_shared_entry_point"],
        "status": "PASS" if passed else "FAIL",
        "rows": controls["controls"],
        "boundary_probes": controls["boundary_probes"],
    }


def build_review() -> dict[str, Any]:
    custody = _validate_custody()
    static_classes = _audit_static_statement_rows()
    source_class = _audit_source_class_enforcement()
    cell_evidence = _audit_cell_evidence()
    equivalence = _audit_equivalence_policy()
    undecidable = _audit_undecidable_propagation()
    no_go = _audit_viable_no_go()
    shared_controls = _audit_shared_controls()
    if static_classes["status"] != "PASS":
        raise ValueError("v1 static statement-class inventory changed")
    failed_audits = [source_class, cell_evidence, equivalence, undecidable, no_go]
    if not all(row["status"] == "FAIL" for row in failed_audits):
        raise ValueError("one or more v1 blocking witnesses did not reproduce")
    if shared_controls["status"] != "PASS":
        raise ValueError("retained v1 shared-path controls did not reproduce")
    if [row["order"] for row in FINDINGS] != [1, 2, 3, 4, 5]:
        raise ValueError("v1 review finding order mismatch")

    review_gates = [
        {"order": 1, "gate": "custody and deterministic reproduction", "status": "PASS"},
        {"order": 2, "gate": "static ten-row statement-class inventory", "status": "PASS"},
        {"order": 3, "gate": "production source/class authority enforcement", "status": "FAIL"},
        {"order": 4, "gate": "supplied-assumption native-pass isolation", "status": "PASS"},
        {"order": 5, "gate": "matrix epistemic-state vocabulary", "status": "PASS"},
        {"order": 6, "gate": "completed-cell evidence custody", "status": "FAIL"},
        {"order": 7, "gate": "local-bulk equivalence proof policy", "status": "FAIL"},
        {"order": 8, "gate": "conservative undecidable class reduction", "status": "FAIL"},
        {"order": 9, "gate": "complete six-outcome terminal partition", "status": "FAIL"},
        {"order": 10, "gate": "shared production-path controls", "status": "PASS"},
        {"order": 11, "gate": "direct standard-GR oracle isolation", "status": "PASS"},
    ]
    tool_path = Path(__file__).resolve()
    test_path = REPO_ROOT / TEST_RELATIVE_PATH
    if not test_path.exists():
        raise ValueError("native-principle v1 review focused test missing")

    return {
        "schema_id": (
            "NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_ACTION_SELECTION_"
            "PACKET_REVIEW_20260718_v1"
        ),
        "captured_at_utc": "2026-07-18T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "primary_diagnostic": PRIMARY_DIAGNOSTIC,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": (
            "PREPARATION_ONLY_REQUIREMENTS_ACTION_SELECTION_PACKET_V2_REPAIR"
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
            "V1's static inventory and shared-path baseline controls reproduce, but the "
            "real analysis is not authorized. Production permits caller-spoofed class "
            "authority, unbound affirmative and equivalence cells, unvalidated physical "
            "equivalence, erasure of unresolved class members, and no reachable viable-"
            "gravity distinctiveness no-go branch."
        ),
        "review_gates": {
            "gate_count": len(review_gates),
            "pass_count": sum(row["status"] == "PASS" for row in review_gates),
            "failure_count": sum(row["status"] == "FAIL" for row in review_gates),
            "rows": review_gates,
        },
        "static_statement_class_audit": static_classes,
        "production_statement_class_enforcement_audit": source_class,
        "matrix_cell_evidence_audit": cell_evidence,
        "equivalence_policy_audit": equivalence,
        "undecidable_propagation_audit": undecidable,
        "terminal_no_go_audit": no_go,
        "shared_path_control_audit": shared_controls,
        "standard_GR_isolation_audit": {
            "Einstein_Hilbert_role": "COMPARISON_ORACLE_ONLY",
            "direct_Einstein_properties_used_to_populate_native_cells": False,
            "supplied_assumption_changes_native_sets": False,
            "direct_isolation_status": "PASS",
            "post_reduction_comparator_safe": False,
            "blocking_dependencies": [
                "EQUIVALENCE_PROOF_POLICY_NOT_ENFORCED",
                "UNDECIDABLE_EQUIVALENCE_CLASS_ERASED",
            ],
        },
        "findings": {
            "finding_count": len(FINDINGS),
            "blocking_count": sum(row["severity"] == "BLOCKING" for row in FINDINGS),
            "rows": FINDINGS,
        },
        "required_v2_repairs": [
            "bind production rows to a closed frozen authority registry by canonical identity",
            "require typed bound evidence for every completed cell disposition",
            "validate equivalence edges and cells against allowed and forbidden local-bulk rules",
            "make unresolved status dominate class reduction absent an exact transfer proof",
            "implement and validate all six terminal domains including viable-gravity no-go",
            "add atomic adversarial controls while retaining one shared production entry point",
        ],
        "retained_results": {
            "requirement_source_bindings": "10_OF_10_STATIC_ROWS_RETAINED",
            "comparison_family_envelope": "7_OF_7_RETAINED",
            "matrix_cell_vocabulary": "7_STATES_RETAINED",
            "shared_production_controls": "8_OF_8_PASSED",
            "shared_boundary_probes": "2_OF_2_PASSED",
            "direct_standard_GR_isolation": "RETAINED",
            "minimal_gravitational_contract": "ACCEPTED",
            "native_candidate_readiness": "BLOCKED_NO_NATIVE_GRAVITATIONAL_PRINCIPLE",
            "real_matrix_cells": "0_OF_70",
        },
        "scope": {
            "independent_v1_review_executed": True,
            "v1_block_recorded": True,
            "v2_packet_prepared_now": False,
            "real_requirements_family_analysis_executed": False,
            "real_matrix_cells_computed": 0,
            "real_survivor_matrix_computed": False,
            "real_scientific_outcome_selected": False,
            "native_gravitational_principle_identified": False,
            "new_postulate_authorized": False,
            "gravitational_action_proposed_or_selected": False,
            "real_action_family_eliminated_or_adopted": False,
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
            "Independent v1 production-semantics review only. The ten static requirement "
            "rows, seven families, cell vocabulary, eight controls, two boundary probes, "
            "and direct standard-GR isolation are retained. Five blocking adversarial "
            "defect classes are reproduced. The real matrix remains 0/70; no family "
            "judgment, principle, postulate, action, matter sector, variation, GR result, "
            "general tooling lane, or automation is created."
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
            raise SystemExit("native-principle v1 review is stale or missing")
        report = json.loads(raw)
        print(json.dumps({
            "blocking_findings": report["findings"]["blocking_count"],
            "real_matrix_cells": report["scope"]["real_matrix_cells_computed"],
            "retained_controls": report["shared_path_control_audit"]["control_pass_count"],
            "status": "CHECKED",
            "verdict": report["verdict"],
        }, sort_keys=True))
        return 0
    report_path.write_bytes(raw)
    print(report_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

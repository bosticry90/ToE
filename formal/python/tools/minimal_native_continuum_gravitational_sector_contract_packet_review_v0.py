from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_SECTOR_CONTRACT_PACKET_REVIEW_"
    "20260717_v0.json"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_minimal_native_continuum_gravitational_sector_contract_packet_review_v0.py"
)
REVIEW_RELATIVE_PATH = (
    "formal/docs/lanes/"
    "MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_SECTOR_CONTRACT_PACKET_REVIEW_"
    "20260717_v0.md"
)
PACKET_REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_SECTOR_CONTRACT_PACKET_20260717_v0.json"
)
TARGET = (
    "review_minimal_native_continuum_gravitational_sector_contract_packet_v0_result"
)
VERDICT = "BLOCKED_NO_NATIVE_GRAVITATIONAL_PRINCIPLE"
PRIMARY_DIAGNOSTIC = "NO_BOUND_NATIVE_GRAVITATIONAL_PRINCIPLE_OR_POSTULATE"
SELECTED_NEXT_TARGET = (
    "select_response_to_no_native_gravitational_principle_from_full_toe_priority_map"
)

AUTHORITY_AND_SOURCE_HASHES = {
    "formal/docs/release/NATIVE_CONTINUUM_ACTION_ABSENCE_SCIENTIFIC_TARGET_SELECTION_20260717_v0.json":
        "86717db3c1a23c8d9562a398db847668d9422fef0261e682038d25e531d9abab",
    "formal/python/tools/native_continuum_action_absence_scientific_target_selection_v0.py":
        "1c91e2aae12390876810d698030d9ec61a3bfbd2eb1fc813e0b27ff52a05421a",
    "formal/python/tests/test_native_continuum_action_absence_scientific_target_selection_v0.py":
        "ecc8af33edc2d9e944eeb9c1af5fd43fffd4ffe7ae2795ca97869009f1dd2610",
    "formal/toe_formal/ToeFormal/Derivation/NativeContinuumActionAbsenceScientificTargetSelectionV0.lean":
        "95e66c9f1a33ad4c02673af2eaa9355d5afa83aacdb6a7f48847a9b3e967e8a9",
    "formal/docs/release/TOE_CANDIDATE_MASTER_ACTION_CK_FIREWALL_AUTHORITY_RECONCILIATION_PACKET_REVIEW_20260717_v0.json":
        "66ed74e9264c82eaa9715cc0369020f93b7956f9f3aa2f9b8b6abb5141fe2e64",
    "formal/docs/paper/TOE_CANDIDATE_MASTER_ACTION_v0.md":
        "23aa11c3784da178097eef8ed7c32f9decf4db038a611e4a16364b9bed2db867",
    "formal/docs/release/MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_AFTER_PHI_A_AND_PSI_A_RESULT_REVIEW_20260626_v0.json":
        "3d148464b39d50ae052866516d30bd3f167e1b80d276f56f593fc698f9e6734d",
    "formal/docs/release/SR_PILLAR_COORDINATE_CONVENTION_AND_CONSTANT_RESTORATION_PACKET_REVIEW_20260717_v3.json":
        "0dbe441d78de6eba0fe006f7b6b280b655a3feae3e1f9d66775eefae9e49a3b1",
    "formal/toe_formal/ToeFormal/Variational/ActionRep32Def.lean":
        "da375e85850deb5d32da8a60c24d2fd7021c95143f8da036973d9575bd398458",
    "formal/toe_formal/ToeFormal/Variational/FirstVariationRep32Def.lean":
        "8c7a6a3f3aa74f240945e3d2ac23a05c6e5fa6fa310977ba9c03db89f456d920",
    "formal/toe_formal/ToeFormal/QFT/DocumentMasterActionMapping.lean":
        "56ad40bfe0443a27b1c35142c52ae2430958dace2b8e62eef8e4e14e31e54ddf",
    "formal/toe_formal/ToeFormal/Variational/WeakFieldPoissonLimit.lean":
        "b2519245872eaed3d874c25836ce355cca9e3bc0f11914e806a74c691f8d14da",
    "formal/docs/release/GR_WEAK_ROTATING_SOURCE_GRAVITOMAGNETIC_RECOVERY_PACKET_REVIEW_20260717_v0.json":
        "de305a72dc522fe807c037bbe7980d96e3308d0547645ccb9939d1889720d987",
    "formal/docs/release/GR_NATIVE_CONTINUUM_METRIC_VARIATION_AND_TENSOR_SURFACE_PACKET_REVIEW_20260717_v0.json":
        "4b894a31d1eb9ea29b06f70934913f42a007db31bbf3ac75f2ab8411674d1939",
    "formal/docs/release/TOE_NATIVE_PSI_A_U1_STRESS_ENERGY_DEFINITION_POLICY_RESULT_REVIEW_20260624_v0.json":
        "fdadf7cb74401fd1d994841c9dbbbce5f6333e86d967d0aa349ed8987c183e8f",
    "formal/docs/release/QFT_GR_MATTER_FIELD_CONTENT_AND_LAGRANGIAN_CANDIDATE_PACKET_20260616_v0.json":
        "7232643ab971c1f647421c81bb52ef37f0a636262bc172d3fffc73ed1c6a4d54",
    "formal/docs/release/QFT_GR_CLASSICAL_EINSTEIN_SCALAR_COUPLING_ROUTE_PACKET_RESULT_REVIEW_20260618_v0.json":
        "0d9eb65ddb9fcf2e6dea8bd4feab58b51fb8db4dd002181bd4004df6d5395509",
    "formal/docs/lanes/MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_SECTOR_CONTRACT_PACKET_20260717_v0.md":
        "5fc170073b11907bb14c05984d577c9b68e0a8d6ebfcf8c7fedf081a4ef292d8",
    PACKET_REPORT_RELATIVE_PATH:
        "2031bc50487bdcd07c5a18dcf2fcdddb611337b5150fbbf416b0d6ab0b9d86d4",
    "formal/python/tools/minimal_native_continuum_gravitational_sector_contract_packet_v0.py":
        "6a3a835bf6bd2040ed906518174aef6dc7afa8d26c35b0dfc79f5644ef643cc1",
    "formal/python/tests/test_minimal_native_continuum_gravitational_sector_contract_packet_v0.py":
        "f415630d94c13d7c68db5bef92fec73e76457db4032ef3878c1d8201189e449a",
    "formal/toe_formal/ToeFormal/Derivation/MinimalNativeContinuumGravitationalSectorContractPacketV0.lean":
        "a2555ffb8a9e0bb231645b39cd8198bea13de4ff447054793608272d0201e30e",
    REVIEW_RELATIVE_PATH:
        "554e18d20bb3d6f2076cb4d6ea6c86480ee46d11f39f87c01673f37dfc8ec70c",
}

GATE_RESULTS = [
    {
        "order": 1,
        "gate": "custody and contract reproduction",
        "status": "PASS",
        "diagnostic": "CUSTODY_OR_CONTRACT_REPRODUCTION_FAILURE",
    },
    {
        "order": 2,
        "gate": "contract design completeness",
        "status": "PASS",
        "diagnostic": "CONTRACT_DESIGN_COMPLETENESS_FAILURE",
    },
    {
        "order": 3,
        "gate": "atomic control behavior",
        "status": "PASS",
        "diagnostic": "ATOMIC_CONTROL_CONTRACT_FAILURE",
    },
    {
        "order": 4,
        "gate": "authority firewalls",
        "status": "PASS",
        "diagnostic": "AUTHORITY_FIREWALL_FAILURE",
    },
    {
        "order": 5,
        "gate": "native gravitational principle or explicit postulate",
        "status": "FAIL",
        "diagnostic": PRIMARY_DIAGNOSTIC,
    },
    {
        "order": 6,
        "gate": "candidate matter coupling",
        "status": "NOT_EVALUATED_AFTER_PRIOR_FAILURE",
        "diagnostic": "BLOCKED_MATTER_COUPLING_UNDEFINED",
    },
    {
        "order": 7,
        "gate": "candidate dimensional and boundary satisfaction",
        "status": "NOT_EVALUATED_AFTER_PRIOR_FAILURE",
        "diagnostic": "BLOCKED_DIMENSIONAL_OR_BOUNDARY_CONTRACT",
    },
    {
        "order": 8,
        "gate": "candidate variation and recovery ladder",
        "status": "NOT_EVALUATED_AFTER_PRIOR_FAILURE",
        "diagnostic": "CANDIDATE_VARIATION_OR_RECOVERY_FAILURE",
    },
]

BASELINE_SYNTHETIC_CONTRACT = {
    "provenance_evidence_valid": True,
    "native_correction_defined": True,
    "C_k_embedded_or_penalized": False,
    "stress_source_derived_from_matter_action": True,
    "Rep32_continuum_authority_claimed": False,
    "all_SI_dimensions_present": True,
    "boundary_prescription_present": True,
    "unselected_tetrad_spinor_import": False,
}

CONTROL_MUTATIONS = [
    {
        "control_id": "CTRL_RELABELED_EINSTEIN_HILBERT_NATIVE",
        "field": "provenance_evidence_valid",
        "mutated_value": False,
        "expected_diagnostic": "PROVENANCE_CLASSIFICATION_FAILURE",
    },
    {
        "control_id": "CTRL_UNDEFINED_NATIVE_CORRECTION",
        "field": "native_correction_defined",
        "mutated_value": False,
        "expected_diagnostic": "CANDIDATE_COMPLETENESS_FAILURE",
    },
    {
        "control_id": "CTRL_CK_EMBEDDED_OR_PENALIZED",
        "field": "C_k_embedded_or_penalized",
        "mutated_value": True,
        "expected_diagnostic": "CK_FIREWALL_VIOLATION",
    },
    {
        "control_id": "CTRL_RETAINED_STRESS_INSERTED_NOT_DERIVED",
        "field": "stress_source_derived_from_matter_action",
        "mutated_value": False,
        "expected_diagnostic": "MATTER_SOURCE_DERIVATION_FAILURE",
    },
    {
        "control_id": "CTRL_REP32_NAME_IMPLIES_CONTINUUM_AUTHORITY",
        "field": "Rep32_continuum_authority_claimed",
        "mutated_value": True,
        "expected_diagnostic": "REP32_CONTINUUM_TRANSPORT_FAILURE",
    },
    {
        "control_id": "CTRL_ONE_SI_DIMENSION_OMITTED",
        "field": "all_SI_dimensions_present",
        "mutated_value": False,
        "expected_diagnostic": "DIMENSIONAL_CONTRACT_FAILURE",
    },
    {
        "control_id": "CTRL_BOUNDARY_PRESCRIPTION_OMITTED",
        "field": "boundary_prescription_present",
        "mutated_value": False,
        "expected_diagnostic": "BOUNDARY_VARIATION_CONTRACT_FAILURE",
    },
    {
        "control_id": "CTRL_UNSELECTED_TETRAD_SPINOR_IMPORT",
        "field": "unselected_tetrad_spinor_import",
        "mutated_value": True,
        "expected_diagnostic": "MINIMAL_FIELD_SCOPE_FAILURE",
    },
]

OUTCOME_ADJUDICATION = [
    {
        "outcome": "MINIMAL_NATIVE_GRAVITATIONAL_ACTION_CONTRACT_READY",
        "status": "NOT_SELECTED",
        "reason": "NO_DERIVED_OR_EXPLICITLY_POSTULATED_CANDIDATE_BOUND",
    },
    {
        "outcome": "SUPPLIED_EINSTEIN_HILBERT_SECTOR_ONLY",
        "status": "NOT_SELECTED_AS_PRIMARY",
        "reason": "COMPARATOR_EXISTS_BUT_REQUIRES_SEPARATE_ACTIVATION",
    },
    {
        "outcome": "BLOCKED_NO_NATIVE_GRAVITATIONAL_PRINCIPLE",
        "status": "SELECTED",
        "reason": PRIMARY_DIAGNOSTIC,
    },
    {
        "outcome": "BLOCKED_MATTER_COUPLING_UNDEFINED",
        "status": "NOT_SELECTED_AS_PRIMARY",
        "reason": "CONFIRMED_SECONDARY_BLOCK_DOWNSTREAM_OF_PROVENANCE_FAILURE",
    },
    {
        "outcome": "BLOCKED_DIMENSIONAL_OR_BOUNDARY_CONTRACT",
        "status": "NOT_SELECTED",
        "reason": "CONTRACT_DEFINITION_PASSES_CANDIDATE_SATISFACTION_UNEVALUATED",
    },
    {
        "outcome": "REQUIREMENTS_NO_GO_ROUTE_RECOMMENDED",
        "status": "NOT_SELECTED",
        "reason": "LATER_STRATEGIC_FORK_REQUIRES_FRESH_PRIORITY_DECISION",
    },
]


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _first_control_diagnostic(contract: dict[str, bool]) -> str:
    if not contract["provenance_evidence_valid"]:
        return "PROVENANCE_CLASSIFICATION_FAILURE"
    if not contract["native_correction_defined"]:
        return "CANDIDATE_COMPLETENESS_FAILURE"
    if contract["C_k_embedded_or_penalized"]:
        return "CK_FIREWALL_VIOLATION"
    if not contract["stress_source_derived_from_matter_action"]:
        return "MATTER_SOURCE_DERIVATION_FAILURE"
    if contract["Rep32_continuum_authority_claimed"]:
        return "REP32_CONTINUUM_TRANSPORT_FAILURE"
    if not contract["all_SI_dimensions_present"]:
        return "DIMENSIONAL_CONTRACT_FAILURE"
    if not contract["boundary_prescription_present"]:
        return "BOUNDARY_VARIATION_CONTRACT_FAILURE"
    if contract["unselected_tetrad_spinor_import"]:
        return "MINIMAL_FIELD_SCOPE_FAILURE"
    return "PASS"


def _execute_controls() -> dict[str, Any]:
    if _first_control_diagnostic(BASELINE_SYNTHETIC_CONTRACT) != "PASS":
        raise ValueError("synthetic positive contract did not pass")
    rows: list[dict[str, Any]] = []
    for mutation in CONTROL_MUTATIONS:
        mutated = copy.deepcopy(BASELINE_SYNTHETIC_CONTRACT)
        mutated[mutation["field"]] = mutation["mutated_value"]
        changed = [
            key for key in BASELINE_SYNTHETIC_CONTRACT
            if mutated[key] != BASELINE_SYNTHETIC_CONTRACT[key]
        ]
        observed = _first_control_diagnostic(mutated)
        passed = changed == [mutation["field"]] and observed == mutation["expected_diagnostic"]
        rows.append({
            **mutation,
            "mutation_count": len(changed),
            "observed_diagnostic": observed,
            "passed": passed,
        })
    return {
        "positive_baseline_passed": True,
        "control_count": len(rows),
        "passed_count": sum(1 for row in rows if row["passed"]),
        "all_atomic_and_exact": all(row["passed"] for row in rows),
        "rows": rows,
    }


def _validate_authority_and_sources() -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for relative_path, expected_hash in AUTHORITY_AND_SOURCE_HASHES.items():
        observed = _sha256((REPO_ROOT / relative_path).read_bytes())
        if observed != expected_hash:
            raise ValueError(f"minimal native GR review hash mismatch: {relative_path}")
        rows.append({"relative_path": relative_path, "sha256": observed})

    packet = json.loads(
        (REPO_ROOT / PACKET_REPORT_RELATIVE_PATH).read_text(encoding="utf-8")
    )
    if packet.get("selected_next_target") != TARGET:
        raise ValueError("review did not consume prepared contract target")
    if packet.get("verdict") != "PREPARED_PENDING_INDEPENDENT_REVIEW":
        raise ValueError("prepared contract verdict mismatch")
    expected_counts = {
        "provenance": packet["provenance_contract"].get("class_count"),
        "completeness": packet["candidate_completeness_contract"].get("gate_count"),
        "recovery": packet["recovery_contract"].get("stage_count"),
        "outcomes": packet["outcome_contract"].get("outcome_count"),
        "controls": packet["control_contract"].get("control_count"),
    }
    if expected_counts != {
        "provenance": 3,
        "completeness": 12,
        "recovery": 10,
        "outcomes": 6,
        "controls": 8,
    }:
        raise ValueError("prepared contract count mismatch")
    if packet["matter_source_contract"].get("S_m_g_chi_is_existing_action") is not False:
        raise ValueError("generic matter notation unexpectedly treated as action")
    if packet["C_k_firewall"].get("action_embedding_allowed") is not False:
        raise ValueError("prepared contract unexpectedly permits C_k embedding")

    selection = json.loads(
        (
            REPO_ROOT
            / "formal/docs/release/NATIVE_CONTINUUM_ACTION_ABSENCE_"
            "SCIENTIFIC_TARGET_SELECTION_20260717_v0.json"
        ).read_text(encoding="utf-8")
    )
    if selection["scope"].get("native_gravitational_action_defined") is not False:
        raise ValueError("selection unexpectedly defined a native action")

    matter = json.loads(
        (
            REPO_ROOT
            / "formal/docs/release/QFT_GR_MATTER_FIELD_CONTENT_AND_LAGRANGIAN_"
            "CANDIDATE_PACKET_20260616_v0.json"
        ).read_text(encoding="utf-8")
    )
    if matter.get("matter_field_content_selected") is not False:
        raise ValueError("matter field content unexpectedly selected")
    if matter.get("lagrangian_density_selected") is not False:
        raise ValueError("matter Lagrangian unexpectedly selected")

    comparator = json.loads(
        (
            REPO_ROOT
            / "formal/docs/release/QFT_GR_CLASSICAL_EINSTEIN_SCALAR_COUPLING_"
            "ROUTE_PACKET_RESULT_REVIEW_20260618_v0.json"
        ).read_text(encoding="utf-8")
    )
    if comparator.get("provisional_classical_sandbox_route_only") is not True:
        raise ValueError("supplied comparator boundary mismatch")

    review = (REPO_ROOT / REVIEW_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        "BLOCKED_NO_NATIVE_GRAVITATIONAL_PRINCIPLE",
        "NO_BOUND_NATIVE_GRAVITATIONAL_PRINCIPLE_OR_POSTULATE",
        "THE CONTRACT IS COMPLETE",
        "8 / 8 EXACT",
        "coupling remains independently undefined",
        "later candidate-first versus requirements/no-go choice",
    ):
        if token not in review:
            raise ValueError(f"human minimal native GR review token missing: {token}")
    return rows


def build_review() -> dict[str, Any]:
    authority = _validate_authority_and_sources()
    controls = _execute_controls()
    if not controls["all_atomic_and_exact"]:
        raise ValueError("independent control execution did not pass 8/8")
    selected = [row for row in OUTCOME_ADJUDICATION if row["status"] == "SELECTED"]
    if len(selected) != 1 or selected[0]["outcome"] != VERDICT:
        raise ValueError("terminal outcome selection mismatch")
    failed = [row for row in GATE_RESULTS if row["status"] == "FAIL"]
    if len(failed) != 1 or failed[0]["order"] != 5:
        raise ValueError("fail-fast gate structure mismatch")
    tool_path = Path(__file__).resolve()
    test_path = REPO_ROOT / TEST_RELATIVE_PATH
    if not test_path.exists():
        raise ValueError("minimal native GR review focused test missing")

    return {
        "schema_id": (
            "MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_SECTOR_CONTRACT_PACKET_"
            "REVIEW_20260717_v0"
        ),
        "captured_at_utc": "2026-07-17T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "primary_diagnostic": PRIMARY_DIAGNOSTIC,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": "FRESH_FULL_PRIORITY_RESPONSE_SELECTION_ONLY",
        "authority": {
            "reviewed_packet_id": (
                "MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_SECTOR_CONTRACT_PACKET_"
                "20260717_v0"
            ),
            "reviewed_packet_verdict": "PREPARED_PENDING_INDEPENDENT_REVIEW",
            "frozen_inputs": authority,
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
            "CONTRACT_COMPLETE_CURRENT_RECORD_BLOCKED_BEFORE_CANDIDATE_PREPARATION"
        ),
        "contract_design_review": {
            "status": "PASS_COMPLETE_BOUNDED_REVIEW_CONTRACT",
            "provenance_class_count": 3,
            "metric_field_count": 1,
            "completeness_gate_count": 12,
            "recovery_stage_count": 10,
            "outcome_count": 6,
            "atomic_control_count": 8,
            "SI_and_compact_support_contract_complete": True,
            "generic_matter_notation_is_not_existing_action": True,
            "authority_firewalls_complete": True,
        },
        "control_execution": controls,
        "fail_fast_review": {
            "gate_count": len(GATE_RESULTS),
            "pass_count": sum(1 for row in GATE_RESULTS if row["status"] == "PASS"),
            "failure_count": len(failed),
            "not_evaluated_count": sum(
                1 for row in GATE_RESULTS
                if row["status"] == "NOT_EVALUATED_AFTER_PRIOR_FAILURE"
            ),
            "first_failed_gate_order": 5,
            "rows": GATE_RESULTS,
        },
        "native_principle_review": {
            "status": "FAIL",
            "project_principle_bound_that_selects_action": False,
            "derived_action_family_bound": False,
            "explicit_postulated_native_candidate_selected": False,
            "schematic_master_action_selects_candidate": False,
            "C_k_firewall_selects_candidate": False,
            "Rep32_selects_continuum_candidate": False,
            "GR01_selects_continuum_candidate": False,
            "standard_GR_comparator_exists": True,
            "standard_GR_comparator_is_native": False,
        },
        "matter_coupling_posture": {
            "current_matter_field_content": "NOT_SELECTED",
            "current_matter_lagrangian": "NOT_SELECTED",
            "variation_derived_stress_energy": "NOT_AVAILABLE",
            "secondary_block_confirmed": True,
            "selected_as_primary_outcome": False,
            "reason_not_primary": "NATIVE_PRINCIPLE_GATE_FAILS_FIRST",
        },
        "candidate_satisfaction_posture": {
            "candidate_formula": "NOT_PROPOSED_OR_SELECTED",
            "candidate_dimensions": "NOT_EVALUATED",
            "candidate_boundary_variation": "NOT_EVALUATED",
            "candidate_symmetry_identity": "NOT_EVALUATED",
            "candidate_matter_source": "NOT_EVALUATED",
            "metric_variation": "NOT_EXECUTED",
            "recovery_stages_executed": 0,
        },
        "outcome_adjudication": {
            "outcome_count": len(OUTCOME_ADJUDICATION),
            "selected_outcome_count": len(selected),
            "rows": OUTCOME_ADJUDICATION,
        },
        "fresh_response_options": [
            {
                "route_id": "EXPLICIT_POSTULATED_NATIVE_GRAVITATIONAL_CANDIDATE",
                "authorized_now": False,
            },
            {
                "route_id": "NATIVE_DYNAMICAL_CORE_REQUIREMENTS_AND_NO_GO",
                "authorized_now": False,
            },
            {
                "route_id": "SUPPLIED_STANDARD_GR_COMPARATOR",
                "authorized_now": False,
            },
            {
                "route_id": "PIVOT_TO_OTHER_HIGH_LEVERAGE_PHYSICS_OBLIGATION",
                "authorized_now": False,
            },
        ],
        "retained_scientific_posture": {
            "contract_design": "ACCEPTED_COMPLETE_BOUNDED_REVIEW_CONTRACT",
            "native_gravitational_principle": "NOT_FOUND",
            "native_gravitational_candidate": "NOT_PROPOSED_OR_SELECTED",
            "matter_action": "NOT_DEFINED",
            "historical_master_action": "SCHEMATIC_ONLY",
            "C_k": "EXTERNAL_ADMISSIBILITY_AUDIT_ONLY",
            "Rep32": "NO_CONTINUUM_ACTION_AUTHORITY",
            "standard_GR": "SUPPLIED_COMPARATOR_ONLY",
            "tensor_field_equation": "NOT_DERIVED",
            "gravitomagnetic_recovery": "BLOCKED_UPSTREAM",
        },
        "scope": {
            "independent_review_executed": True,
            "contract_design_accepted": True,
            "gravitational_action_proposed_selected_or_derived": False,
            "native_postulate_selected": False,
            "successor_master_action_prepared_or_created": False,
            "metric_tetrad_spin_or_matter_variation_executed": False,
            "stress_energy_derived": False,
            "Einstein_equation_imported_or_derived": False,
            "standard_GR_comparator_activated": False,
            "Newton_Poisson_or_tensor_calculation_executed": False,
            "gravitomagnetic_calculation_executed": False,
            "C_k_embedded_or_varied": False,
            "Rep32_continuum_transport_claimed": False,
            "requirements_no_go_route_selected": False,
            "master_action_promoted": False,
            "GR_pillar_completed": False,
            "simulation_executed": False,
            "empirical_analysis_executed": False,
            "repository_migration_executed": False,
            "general_symbolic_tooling_created": False,
            "automation_created": False,
        },
        "claim_ceiling": (
            "Independent contract review only. The bounded contract design passes, but "
            "the current record contains no native gravitational principle and no "
            "explicitly selected postulated candidate. Candidate-first work is blocked "
            "as BLOCKED_NO_NATIVE_GRAVITATIONAL_PRINCIPLE. Matter coupling remains "
            "independently undefined. No action, postulate, successor theory, variation, "
            "stress-energy, tensor equation, comparator activation, GR recovery, route "
            "selection, promotion, empirical result, general tooling, or automation is "
            "created."
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
            raise SystemExit("minimal native GR contract review is stale or missing")
        review = json.loads(raw)
        print(json.dumps({
            "contract_design": review["contract_design_review"]["status"],
            "controls": review["control_execution"]["passed_count"],
            "first_failed_gate": review["fail_fast_review"]["first_failed_gate_order"],
            "status": "CHECKED",
            "verdict": review["verdict"],
        }, sort_keys=True))
        return 0
    report_path.write_bytes(raw)
    print(report_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
import unicodedata
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.prompt_dependency_identity import (
    identity_sha256_path,
    prompt_dependency_is_nonblocking,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-PACKET-v0.json"
MANIFEST_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-MANIFEST-v0.json"
PREPARATION_REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_PACKET_20260713_v0.json"
PREPARATION_GENERATOR_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness.py"
REVIEW_REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_PACKET_RESULT_REVIEW_20260713_v0.json"
PACKET_PATH = REPO_ROOT / PACKET_RELATIVE_PATH
REVIEW_REPORT_PATH = REPO_ROOT / REVIEW_REPORT_RELATIVE_PATH

CAPTURED_AT_UTC = "2026-07-13T00:00:00Z"
REVIEW_TARGET = "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_packet_v0_result"
ACCEPTED_TARGET = "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_guardrail_packet_v0"
BLOCKED_TARGET = "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_packet_v1"
REVIEW_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_PACKET_RESULT_REVIEW_20260713_v0"
PREPARATION_COMMIT = "743b3bbe2a8392cfdce63f06f93022fa249e1d73"
PREPARATION_PARENT = "8053308324682e2e3bef19e467d2abc94837907d"
EXPECTED_HASHES = {
    PREPARATION_GENERATOR_RELATIVE_PATH: "d88998839f35aa1bfd269a9488f38df806338f8724c77fc7860f56bab7512df1",
    PACKET_RELATIVE_PATH: "98a635b92d3a2b5479cc41aca80760a965a249fb3ae16c476b3a50aab6e10100",
    MANIFEST_RELATIVE_PATH: "d5383d4ba773e18fbe6bb350da859a4cd22ec17f4e0f947b30c41417257bf291",
    PREPARATION_REPORT_RELATIVE_PATH: "326867a78b07f215271738d2fc3712c34b43b16c9002adbc77ea55fda01aa0bc",
}
PROMPT_RELATIVE_PATH = "Prompt.txt"
PROMPT_DEPENDENCY_ROLE = "DEMOTE_TO_NONBLOCKING_PROVENANCE"
PROMPT_SHA256 = "2bc6996ea28e96c50e688ed3d30ee24808af411a244eb594aad89ff80fda8433"

ROUTE_REVIEW_RELATIVE_PATH = "formal/docs/release/POST_DIRAC_MAXWELL_FULL_ZERO_MODE_CANONICAL_RESULT_ROUTE_DECISION_PACKET_RESULT_REVIEW_20260713_v0.json"
CANONICAL_REVIEW_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_CANONICAL_SIMULATION_RESULT_REVIEW_20260713_v0.json"
BLOCKER_REVIEW_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_3P1_TO_1P1_REDUCTION_CONSISTENCY_PACKET_RESULT_REVIEW_20260713_v0.json"
ANALYTIC_REVIEW_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_REDUCTION_WITH_TRANSVERSE_FIELDS_PACKET_RESULT_REVIEW_20260713_v0.json"
GUARDRAIL_REVIEW_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DISCRETE_NUMERICAL_GUARDRAIL_PACKET_RESULT_REVIEW_20260713_v0.json"
FREEZE_REVIEW_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_CANONICAL_PARAMETER_FREEZE_PACKET_RESULT_REVIEW_20260713_v0.json"
SOURCE_HASHES = {
    ROUTE_REVIEW_RELATIVE_PATH: "6e6426de69dfbb831a7ed3c1c76f0acb32321a47eb663e3ce0fd2f96f7af637d",
    CANONICAL_REVIEW_RELATIVE_PATH: "9b518024fa8a13b73d19e01576375484d5acc24e4f5896adaa612b46f500e040",
    BLOCKER_REVIEW_RELATIVE_PATH: "3f2879163b5e8e90fba286eacdbdebdfdf3ce5b043169ade5f5b8db41b95eec6",
    ANALYTIC_REVIEW_RELATIVE_PATH: "e4a830678d863319d5509bf43e332a778708b7b82bd6db5903be5a389fef34de",
    GUARDRAIL_REVIEW_RELATIVE_PATH: "b881d23e9bd201b09bb023a1e897306afff681bd57ccb224a9c6baf562be57b6",
    FREEZE_REVIEW_RELATIVE_PATH: "2fb867bcc8cf8271d2511db2de8d9d605db5888d0ec407db9eab9085149d81f3",
}
EXPECTED_PROPOSITIONS = {
    "P_ROBUSTNESS_ROUTE_SELECTED": (ROUTE_REVIEW_RELATIVE_PATH, "/selected_candidate_id", "DESCENDANT_NECESSITY_ROBUSTNESS"),
    "P_ROBUSTNESS_PREPARATION_AUTHORIZED": (ROUTE_REVIEW_RELATIVE_PATH, "/authority_rotation/descendant_necessity_robustness_preparation_authorized", True),
    "P_CANONICAL_E_REPRO_ACCEPTED": (CANONICAL_REVIEW_RELATIVE_PATH, "/accepted_claim_label", "E-REPRO"),
    "P_CANONICAL_TRANSVERSE_SIGNAL": (CANONICAL_REVIEW_RELATIVE_PATH, "/result_metrics/transverse_signal", 6.826809919994493e-08),
    "P_CANONICAL_EXCHANGE_RATIO": (CANONICAL_REVIEW_RELATIVE_PATH, "/result_metrics/exchange_ratio", 352.6967159703898),
    "P_ORIGINAL_TRANSVERSE_BLOCKER": (BLOCKER_REVIEW_RELATIVE_PATH, "/blocker_code", "B-BLOCKED_TRANSVERSE_SECTOR_NOT_INVARIANT"),
    "P_BLOCKER_CONFIRMED": (BLOCKER_REVIEW_RELATIVE_PATH, "/blocker_confirmed", True),
    "P_FULL_DESCENDANT_REDUCTION_ACCEPTED": (ANALYTIC_REVIEW_RELATIVE_PATH, "/authority_rotation/full_zero_mode_analytic_repair_accepted", True),
    "P_PURE_TRUNCATION_NOT_REHABILITATED": (ANALYTIC_REVIEW_RELATIVE_PATH, "/authority_rotation/pure_1p1_truncation_rehabilitated", False),
    "P_NUMERICAL_GUARDRAIL_ACCEPTED": (GUARDRAIL_REVIEW_RELATIVE_PATH, "/authority_rotation/numerical_guardrail_accepted", True),
    "P_CANONICAL_EXCHANGE_GATE_REFERENCE": (FREEZE_REVIEW_RELATIVE_PATH, "/accepted_canonical_freeze/minimum_exchange_ratio", 100.0),
    "P_CANONICAL_TRANSVERSE_GATE_REFERENCE": (FREEZE_REVIEW_RELATIVE_PATH, "/accepted_canonical_freeze/minimum_transverse_signal", 3e-08),
    "P_CANONICAL_ENERGY_CLASS_REFERENCE": (FREEZE_REVIEW_RELATIVE_PATH, "/accepted_canonical_freeze/energy_classification", "BOUNDED_CONVERGENT_ENERGY_ERROR"),
}
EXPECTED_AXES = {
    "ETA_Q": ("q_1p1 / m", ["WEAKER", "CANONICAL", "STRONGER"]),
    "F_PERP_INITIAL": ("(E_phi2(0)+E_phi3(0))/E_total(0)", ["ZERO", "MODEST", "LARGER_ADMITTED"]),
    "THETA_W": ("Arg(W)", ["TRIVIAL", "NONTRIVIAL", "SYMMETRY_PARTNER_IF_DISTINCT"]),
    "DELTA_THETA_PSI": ("frozen relative phase between selected charge/species or reduced-sector amplitudes", ["CANONICAL", "POSITIVE_OFFSET", "NEGATIVE_OFFSET"]),
    "MU_MASS_DOMAIN": ("m * L_x", ["CANONICAL", "ONE_BOUNDED_VARIATION"]),
}
EXPECTED_EXISTING_OBSERVABLES = ["GAUSS_RESIDUAL", "CONTINUITY_RESIDUAL", "DIRAC_ADJOINT_RESIDUALS", "MAXWELL_RESIDUALS", "LINK_NORM_ERROR", "ENERGY_DRIFT", "SPATIAL_CONVERGENCE", "TEMPORAL_CONVERGENCE", "WILSON_CONTINUUM_BEHAVIOR", "EXCHANGE_TO_DRIFT_RATIO"]
EXPECTED_DESCENDANT_OBSERVABLES = ["DELTA_E_PHI2", "DELTA_E_PHI3", "X2_SPINOR_PHI2_EXCHANGE", "X3_SPINOR_PHI3_EXCHANGE", "F_EXCHANGE_PERP", "R_PERP_OBSERVABLE", "C_PERP_SOURCE_NORM", "R_TRUNC_EQUATION_RESIDUAL", "T_DIVERGENCE"]
EXPECTED_DESCENDANT_DEFINITIONS = {
    "DELTA_E_PHI2": "E_phi2(t)-E_phi2(0)",
    "DELTA_E_PHI3": "E_phi3(t)-E_phi3(0)",
    "X2_SPINOR_PHI2_EXCHANGE": "registered spinor-to-phi2 exchange integral with the accepted sign convention",
    "X3_SPINOR_PHI3_EXCHANGE": "registered spinor-to-phi3 exchange integral with the accepted sign convention",
    "F_EXCHANGE_PERP": "(|X2|+|X3|)/(|X_longitudinal|+|X2|+|X3|+epsilon_exchange_floor)",
    "R_PERP_OBSERVABLE": "|O_full-O_forced_truncation|/(|O_full|+epsilon_observable_floor)",
    "C_PERP_SOURCE_NORM": "sqrt(|J2|^2+|J3|^2) under the forced truncation",
    "R_TRUNC_EQUATION_RESIDUAL": "sqrt(|Box(phi2)-J2|^2+|Box(phi3)-J3|^2) evaluated for the forced truncation",
    "T_DIVERGENCE": "inf{t: R_perp,O(t) >= delta_O}",
}
EXPECTED_POSITIVE_CONTROLS = ["P_CANONICAL_ACCEPTED_RESULT_UNCHANGED", "P_CHARGE_CONJUGATE_PARAMETER_CASE", "P_ANALYTIC_INVARIANT_DESCENDANT_FREE", "P_INITIAL_ZERO_DESCENDANTS_DYNAMICALLY_SOURCED", "P_INDEPENDENT_PHI2_EXCITATION", "P_INDEPENDENT_PHI3_EXCITATION", "P_PHI2_PHI3_INTERCHANGE", "P_WEAK_COUPLING_APPROACH"]
EXPECTED_NEGATIVE_CONTROLS = ["N_FORCE_BOTH_DESCENDANTS_ZERO_WITH_SOURCE", "N_DROP_ONLY_PHI2", "N_DROP_ONLY_PHI3", "N_OMIT_DESCENDANT_ENERGY", "N_OMIT_TRANSVERSE_EXCHANGE_CHANNEL", "N_REVERSE_TRANSVERSE_EXCHANGE_SIGN", "N_WRONG_GAMMA2_BLOCK", "N_WRONG_GAMMA3_BLOCK", "N_SUPPRESS_SECTOR_MULTIPLICITY", "N_DESCENDANTS_RELABELED_INVENTED_MATTER", "N_CANONICAL_THRESHOLDS_REUSED_UNSCALED", "N_POST_EXECUTION_FAVORABLE_POINT_SELECTION", "N_FAILED_POINTS_EXCLUDED_FROM_DOMAIN"]
EXPECTED_ROBUSTNESS_OUTCOMES = ["BROADLY_ROBUST", "CONDITIONALLY_ROBUST", "THRESHOLD_SENSITIVE", "NUMERICALLY_BLOCKED", "MODEL_DOMAIN_LIMITED"]
EXPECTED_DESCENDANT_OUTCOMES = ["DESCENDANTS_DYNAMICALLY_NECESSARY_QUANTITATIVELY_SMALL", "DESCENDANT_DOMINATED_REGIME", "INTERMEDIATE_DESCENDANT_CONTRIBUTION"]


def _normalize(value: Any) -> Any:
    if isinstance(value, str):
        return unicodedata.normalize("NFC", value)
    if isinstance(value, list):
        return [_normalize(item) for item in value]
    if isinstance(value, dict):
        return {_normalize(str(key)): _normalize(item) for key, item in value.items()}
    return value


def canonical_json_bytes(payload: Any) -> bytes:
    return (json.dumps(_normalize(payload), allow_nan=False, ensure_ascii=False, indent=2, sort_keys=True) + "\n").encode("utf-8")


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha256_path(path: Path) -> str:
    return identity_sha256_path(path, repo_root=REPO_ROOT)


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected object: {path}")
    return value


def _json_pointer(document: Any, pointer: str) -> Any:
    current = document
    for raw_part in pointer[1:].split("/"):
        part = raw_part.replace("~1", "/").replace("~0", "~")
        current = current[int(part)] if isinstance(current, list) else current[part]
    return current


def custody() -> dict[str, Any]:
    commit = subprocess.run(["git", "rev-parse", PREPARATION_COMMIT], cwd=REPO_ROOT, capture_output=True, text=True, check=False).stdout.strip()
    parent = subprocess.run(["git", "rev-parse", f"{PREPARATION_COMMIT}^"], cwd=REPO_ROOT, capture_output=True, text=True, check=False).stdout.strip()
    working = {path: sha256_path(REPO_ROOT / path) for path in EXPECTED_HASHES}
    committed: dict[str, str] = {}
    for path in EXPECTED_HASHES:
        result = subprocess.run(["git", "show", f"{PREPARATION_COMMIT}:{path}"], cwd=REPO_ROOT, capture_output=True, check=False)
        committed[path] = sha256_bytes(result.stdout) if result.returncode == 0 else "MISSING"
    passed = commit == PREPARATION_COMMIT and parent == PREPARATION_PARENT and working == EXPECTED_HASHES and committed == EXPECTED_HASHES
    return {"commit": commit, "parent": parent, "working_hashes": working, "commit_hashes": committed, "expected_hashes": EXPECTED_HASHES, "passed": passed}


def independent_evidence_audit(packet: dict[str, Any]) -> dict[str, Any]:
    sources = {path: load_json(REPO_ROOT / path) for path in SOURCE_HASHES}
    records = {item["proposition_id"]: item for item in packet["evidence_records"]}
    checks = []
    for proposition_id, (source_path, pointer, expected) in EXPECTED_PROPOSITIONS.items():
        record = records.get(proposition_id, {})
        observed = _json_pointer(sources[source_path], pointer)
        passed = (
            sha256_path(REPO_ROOT / source_path) == SOURCE_HASHES[source_path]
            and record.get("source_path") == source_path
            and record.get("source_hash") == SOURCE_HASHES[source_path]
            and record.get("source_locator", {}).get("pointer") == pointer
            and record.get("evidence_role") == "REPOSITORY_STATE_EVIDENCE"
            and record.get("route_support_eligible") is True
            and observed == expected
            and record.get("expected_source_value") == expected
        )
        checks.append({"proposition_id": proposition_id, "observed_value": observed, "passed": passed})
    return {"source_count": len(SOURCE_HASHES), "proposition_count": len(checks), "checks": checks, "all_sources_and_propositions_match": len(records) == 13 and all(item["passed"] for item in checks)}


def independent_design_audit(packet: dict[str, Any]) -> dict[str, Any]:
    tracks = {item["track_id"]: item for item in packet["comparison_tracks"]}
    axes = {item["axis_id"]: item for item in packet["parameter_axes"]}
    axis_checks = {
        axis_id: axes.get(axis_id, {}).get("definition") == definition
        and axes.get(axis_id, {}).get("required_level_roles") == levels
        and axes.get(axis_id, {}).get("dimensionless") is True
        and axes.get(axis_id, {}).get("exact_values_frozen") is False
        for axis_id, (definition, levels) in EXPECTED_AXES.items()
    }
    registry = packet["observable_registry"]
    matrix = packet["bounded_matrix_policy"]
    policy = packet["threshold_and_pilot_policy"]
    outcomes = packet["outcome_taxonomy"]
    descendant_definitions = {item["observable_id"]: item["definition"] for item in registry["descendant_observables"]}
    return {
        "question_tracks_separate": packet["question_tracks_separate"] is True and {item["claim_track"] for item in packet["scientific_questions"]} == {"MODEL_ROBUSTNESS", "DESCENDANT_NECESSITY"},
        "full_only_positive_robustness": tracks["MODEL_ROBUSTNESS"]["eligible_model_ids"] == ["FULL_ACCEPTED_DESCENDANT_AWARE_SYSTEM"] and tracks["MODEL_ROBUSTNESS"]["forced_truncation_eligible_for_positive_claim"] is False,
        "forced_truncation_negative_only": tracks["DESCENDANT_NECESSITY"]["invalid_comparator_is_negative_control_only"] is True and "INTENTIONALLY_NONINVARIANT_COMPARATOR" in tracks["DESCENDANT_NECESSITY"]["model_ids"],
        "special_subdomain_proof_gated": tracks["INVARIANT_SPECIAL_SUBDOMAIN"]["status"] == "CONDITIONAL_ON_SEPARATE_ACCEPTED_ANALYTIC_PROOF" and len(tracks["INVARIANT_SPECIAL_SUBDOMAIN"]["proof_requirements"]) == 5,
        "axis_checks": axis_checks,
        "all_axes_match": list(axes) == list(EXPECTED_AXES) and all(axis_checks.values()),
        "matrix_bounded": matrix["full_cartesian_sweep_forbidden"] is True and matrix["future_exact_unique_scientific_row_count_minimum"] == 12 and matrix["future_exact_unique_scientific_row_count_maximum"] == 14 and matrix["exact_matrix_must_be_frozen_before_any_new_calibration_run"] is True and matrix["difficult_points_may_not_be_removed_after_pilot_observation"] is True,
        "existing_observables_match": [item["observable_id"] for item in registry["existing_observables"]] == EXPECTED_EXISTING_OBSERVABLES,
        "descendant_observables_match": [item["observable_id"] for item in registry["descendant_observables"]] == EXPECTED_DESCENDANT_OBSERVABLES,
        "descendant_definitions_match": descendant_definitions == EXPECTED_DESCENDANT_DEFINITIONS,
        "future_observable_freezes_required": all(registry["future_freeze_requirements"].values()),
        "positive_controls_match": [item["control_id"] for item in packet["positive_controls"]] == EXPECTED_POSITIVE_CONTROLS,
        "negative_controls_match": [item["control_id"] for item in packet["negative_controls"]] == EXPECTED_NEGATIVE_CONTROLS,
        "blocker_is_permanent_regression": packet["original_reduction_blocker_is_permanent_regression"] is True and packet["negative_controls"][0]["permanent_regression"] is True,
        "canonical_thresholds_reference_only": policy["canonical_thresholds_are_reference_evidence_only"] is True and policy["canonical_thresholds_automatically_reused"] is False,
        "pilot_unauthorized": policy["pilot_authorized"] is False and policy["new_thresholds_frozen"] is False and policy["new_solver_or_grid_values_frozen"] is False,
        "scientific_design_immutable_during_future_pilot": set(policy["pilot_may_not_change"]) == {"scientific_questions", "parameter_axes", "comparators", "observable_ids", "control_ids", "outcome_classes", "claim_ceiling"},
        "robustness_outcomes_match": [item["outcome_id"] for item in outcomes["robustness_status_classes"]] == EXPECTED_ROBUSTNESS_OUTCOMES,
        "descendant_outcomes_match": [item["outcome_id"] for item in outcomes["descendant_significance_classes"]] == EXPECTED_DESCENDANT_OUTCOMES,
        "multi_axis_nonpass_preservation": outcomes["simple_pass_fail_forbidden"] is True and outcomes["multi_axis_classification_required"] is True and outcomes["negative_inconclusive_and_blocked_outcomes_preserved"] is True,
    }


DECISION_IDS = [
    "immutable_descendant_necessity_robustness_preparation_is_bound",
    "accepted_route_review_is_the_exact_live_authority",
    "all_six_sources_and_thirteen_propositions_are_independently_bound",
    "necessity_and_robustness_questions_remain_separate",
    "full_descendant_aware_model_is_the_only_positive_robustness_candidate",
    "forced_truncation_is_an_intentionally_noninvariant_negative_comparator_only",
    "descendant_free_special_subdomain_requires_separate_accepted_invariance_proof",
    "all_five_normalized_axis_definitions_and_level_roles_are_reconstructed",
    "exact_axis_values_solver_settings_and_thresholds_remain_unfrozen",
    "anchor_OAT_corner_matrix_is_bounded_to_twelve_through_fourteen_unique_rows",
    "ten_existing_numerical_observables_are_preserved",
    "nine_descendant_observables_and_formulas_are_reconstructed",
    "observable_floors_norms_aggregation_and_divergence_gates_require_future_freeze",
    "eight_positive_control_definitions_are_reconstructed",
    "thirteen_negative_control_definitions_are_reconstructed",
    "original_transverse_blocker_remains_a_permanent_regression",
    "canonical_thresholds_are_reference_only_not_automatically_transferred",
    "future_pilot_cannot_change_scientific_questions_axes_comparators_observables_controls_outcomes_or_claim",
    "five_robustness_and_three_descendant_significance_outcomes_are_reconstructed",
    "multi_axis_taxonomy_preserves_negative_inconclusive_blocked_and_domain_limited_results",
    "fifteen_design_mutations_are_exactly_diagnosed",
    "completed_canonical_result_is_not_reopened",
    "only_robustness_guardrail_preparation_is_authorized",
    "claim_ceiling_and_all_nonpromotion_boundaries_hold",
    "Prompt_is_preserved",
]


def build_review_report() -> dict[str, Any]:
    packet = load_json(PACKET_PATH)
    custody_result = custody()
    evidence = independent_evidence_audit(packet)
    design = independent_design_audit(packet)
    policy = packet["threshold_and_pilot_policy"]
    boundary = packet["boundary"]
    controls = packet["mutation_controls"]
    decisions = {
        "immutable_descendant_necessity_robustness_preparation_is_bound": custody_result["passed"],
        "accepted_route_review_is_the_exact_live_authority": packet["target"] == "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_packet_v0" and packet["input_artifacts"][0] == {"path": ROUTE_REVIEW_RELATIVE_PATH, "sha256": SOURCE_HASHES[ROUTE_REVIEW_RELATIVE_PATH]},
        "all_six_sources_and_thirteen_propositions_are_independently_bound": evidence["source_count"] == 6 and evidence["proposition_count"] == 13 and evidence["all_sources_and_propositions_match"],
        "necessity_and_robustness_questions_remain_separate": design["question_tracks_separate"],
        "full_descendant_aware_model_is_the_only_positive_robustness_candidate": design["full_only_positive_robustness"],
        "forced_truncation_is_an_intentionally_noninvariant_negative_comparator_only": design["forced_truncation_negative_only"],
        "descendant_free_special_subdomain_requires_separate_accepted_invariance_proof": design["special_subdomain_proof_gated"],
        "all_five_normalized_axis_definitions_and_level_roles_are_reconstructed": design["all_axes_match"],
        "exact_axis_values_solver_settings_and_thresholds_remain_unfrozen": packet["exact_parameter_values_frozen"] is False and policy["new_thresholds_frozen"] is False and policy["new_solver_or_grid_values_frozen"] is False,
        "anchor_OAT_corner_matrix_is_bounded_to_twelve_through_fourteen_unique_rows": design["matrix_bounded"],
        "ten_existing_numerical_observables_are_preserved": design["existing_observables_match"],
        "nine_descendant_observables_and_formulas_are_reconstructed": design["descendant_observables_match"] and design["descendant_definitions_match"],
        "observable_floors_norms_aggregation_and_divergence_gates_require_future_freeze": design["future_observable_freezes_required"],
        "eight_positive_control_definitions_are_reconstructed": design["positive_controls_match"],
        "thirteen_negative_control_definitions_are_reconstructed": design["negative_controls_match"],
        "original_transverse_blocker_remains_a_permanent_regression": design["blocker_is_permanent_regression"],
        "canonical_thresholds_are_reference_only_not_automatically_transferred": design["canonical_thresholds_reference_only"],
        "future_pilot_cannot_change_scientific_questions_axes_comparators_observables_controls_outcomes_or_claim": design["pilot_unauthorized"] and design["scientific_design_immutable_during_future_pilot"],
        "five_robustness_and_three_descendant_significance_outcomes_are_reconstructed": design["robustness_outcomes_match"] and design["descendant_outcomes_match"],
        "multi_axis_taxonomy_preserves_negative_inconclusive_blocked_and_domain_limited_results": design["multi_axis_nonpass_preservation"],
        "fifteen_design_mutations_are_exactly_diagnosed": len(controls) == 15 and all(item["passed"] for item in controls) and all(item["changed_premise_count"] == 1 and item["observed_diagnostics"] == [item["expected_diagnostic"]] for item in controls),
        "completed_canonical_result_is_not_reopened": packet["completed_canonical_result_reopened"] is False,
        "only_robustness_guardrail_preparation_is_authorized": packet["post_acceptance_target"] == ACCEPTED_TARGET and boundary["scientific_design_prepared"] is True and boundary["scientific_design_accepted"] is False and boundary["robustness_guardrail_preparation_authorized"] is False and boundary["pilot_authorized"] is False and boundary["canonical_robustness_execution_authorized"] is False,
        "claim_ceiling_and_all_nonpromotion_boundaries_hold": packet["claim_ceiling_not_yet_earned"] is True and boundary["universal_Maxwell_Dirac_robustness_claimed"] is False and boundary["physical_necessity_in_nature_claimed"] is False and boundary["fermionic_QFT_claimed"] is False and boundary["quantized_electromagnetism_claimed"] is False and boundary["pillar_completion_claimed"] is False and boundary["seam_closure_claimed"] is False and boundary["new_fundamental_physics_claimed"] is False and boundary["C_k_dynamics_claimed"] is False and boundary["master_action_validated"] is False and boundary["repository_wide_green_claimed"] is False,
        "Prompt_is_preserved": prompt_dependency_is_nonblocking(PROMPT_DEPENDENCY_ROLE),
    }
    ordered = [{"decision_id": item, "passed": decisions[item]} for item in DECISION_IDS]
    failed = [item["decision_id"] for item in ordered if not item["passed"]]
    accepted = not failed
    return {
        "schema_id": REVIEW_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "review_target": REVIEW_TARGET,
        "accepted": accepted,
        "verdict": "ACCEPT_SCIENTIFIC_DESIGN" if accepted else "B-BLOCKED",
        "selected_next_target": ACCEPTED_TARGET if accepted else BLOCKED_TARGET,
        "selected_next_target_kind": ACCEPTED_TARGET if accepted else BLOCKED_TARGET,
        "decision_count": len(DECISION_IDS),
        "passed_decision_count": len(DECISION_IDS) - len(failed),
        "failed_decision_ids": failed,
        "decisions": ordered,
        "preparation_custody": custody_result,
        "independent_evidence_audit": evidence,
        "independent_design_audit": design,
        "accepted_design": {
            "scientific_question_tracks": ["MODEL_ROBUSTNESS", "DESCENDANT_NECESSITY"],
            "parameter_axis_ids": list(EXPECTED_AXES),
            "future_exact_unique_scientific_row_count_range": [12, 14],
            "positive_control_count": len(EXPECTED_POSITIVE_CONTROLS),
            "negative_control_count": len(EXPECTED_NEGATIVE_CONTROLS),
            "existing_observable_count": len(EXPECTED_EXISTING_OBSERVABLES),
            "descendant_observable_count": len(EXPECTED_DESCENDANT_OBSERVABLES),
            "robustness_outcomes": EXPECTED_ROBUSTNESS_OUTCOMES,
            "descendant_significance_outcomes": EXPECTED_DESCENDANT_OUTCOMES,
        },
        "authority_rotation": {
            "scientific_design_accepted": accepted,
            "robustness_guardrail_preparation_authorized": accepted,
            "robustness_guardrail_accepted": False,
            "pilot_authorized": False,
            "exact_parameter_matrix_frozen": False,
            "thresholds_frozen": False,
            "canonical_robustness_execution_authorized": False,
            "canonical_result_reopened": False,
            "universal_robustness_authorized": False,
            "physical_necessity_in_nature_authorized": False,
            "pillar_completion_authorized": False,
            "seam_closure_authorized": False,
            "C_k_dynamics_authorized": False,
            "master_action_validation_authorized": False,
        },
        "claim": "The descendant-necessity and robustness scientific design is accepted; only robustness-guardrail preparation is authorized, with exact values, thresholds, pilot, and execution still blocked." if accepted else "The descendant-necessity and robustness design is blocked.",
        "nonclaims": [
            "no exact robustness parameter matrix or thresholds frozen",
            "no pilot or robustness execution authorized",
            "no universal robustness or physical necessity in nature",
            "no fermionic QFT or quantized electromagnetism",
            "no pillar completion, seam closure, new physics, C_k dynamics, or master-action validation",
            "no repository-wide green claim",
        ],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Independently review the descendant necessity and robustness scientific design.")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    try:
        report = build_review_report()
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    expected = canonical_json_bytes(report)
    if args.write:
        REVIEW_REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
        REVIEW_REPORT_PATH.write_bytes(expected)
        print(f"wrote robustness design review: {report['verdict']}; guardrail preparation only")
        return 0 if report["accepted"] else 2
    if args.check:
        if not REVIEW_REPORT_PATH.is_file() or REVIEW_REPORT_PATH.read_bytes() != expected:
            print("stale or missing robustness design review", file=sys.stderr)
            return 1
        print(f"robustness design review verified: {report['verdict']}; guardrail preparation selected")
        return 0 if report["accepted"] else 2
    sys.stdout.buffer.write(expected)
    return 0 if report["accepted"] else 2


if __name__ == "__main__":
    raise SystemExit(main())

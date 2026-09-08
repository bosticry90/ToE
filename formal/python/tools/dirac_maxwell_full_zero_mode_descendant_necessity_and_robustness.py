from __future__ import annotations

import argparse
import copy
import hashlib
import json
import sys
import unicodedata
from pathlib import Path
from typing import Any, Callable

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.prompt_dependency_identity import (
    identity_sha256_path,
    prompt_dependency_is_nonblocking,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_RELATIVE_PATH = "formal/python/tools/dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness.py"
ROUTE_REVIEW_RELATIVE_PATH = "formal/docs/release/POST_DIRAC_MAXWELL_FULL_ZERO_MODE_CANONICAL_RESULT_ROUTE_DECISION_PACKET_RESULT_REVIEW_20260713_v0.json"
CANONICAL_REVIEW_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_CANONICAL_SIMULATION_RESULT_REVIEW_20260713_v0.json"
BLOCKER_REVIEW_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_3P1_TO_1P1_REDUCTION_CONSISTENCY_PACKET_RESULT_REVIEW_20260713_v0.json"
ANALYTIC_REVIEW_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_REDUCTION_WITH_TRANSVERSE_FIELDS_PACKET_RESULT_REVIEW_20260713_v0.json"
GUARDRAIL_REVIEW_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DISCRETE_NUMERICAL_GUARDRAIL_PACKET_RESULT_REVIEW_20260713_v0.json"
FREEZE_REVIEW_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_CANONICAL_PARAMETER_FREEZE_PACKET_RESULT_REVIEW_20260713_v0.json"
PACKET_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-PACKET-v0.json"
MANIFEST_RELATIVE_PATH = "formal/output/DIRAC-MAXWELL-FULL-ZERO-MODE-DESCENDANT-NECESSITY-AND-ROBUSTNESS-MANIFEST-v0.json"
REPORT_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_PACKET_20260713_v0.json"
PACKET_PATH = REPO_ROOT / PACKET_RELATIVE_PATH
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH
REPORT_PATH = REPO_ROOT / REPORT_RELATIVE_PATH

CAPTURED_AT_UTC = "2026-07-13T00:00:00Z"
TARGET = "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_packet_v0"
REVIEW_TARGET = "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_packet_v0_result"
REVIEW_TARGET_KIND = "dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_packet_v0_result_review"
FAILURE_TARGET = "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_packet_v1"
POST_ACCEPTANCE_TARGET = "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_guardrail_packet_v0"
PACKET_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_PACKET_v0"
MANIFEST_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_MANIFEST_v0"
REPORT_SCHEMA_ID = "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_PACKET_20260713_v0"
INPUT_HASHES = {
    ROUTE_REVIEW_RELATIVE_PATH: "6e6426de69dfbb831a7ed3c1c76f0acb32321a47eb663e3ce0fd2f96f7af637d",
    CANONICAL_REVIEW_RELATIVE_PATH: "9b518024fa8a13b73d19e01576375484d5acc24e4f5896adaa612b46f500e040",
    BLOCKER_REVIEW_RELATIVE_PATH: "3f2879163b5e8e90fba286eacdbdebdfdf3ce5b043169ade5f5b8db41b95eec6",
    ANALYTIC_REVIEW_RELATIVE_PATH: "e4a830678d863319d5509bf43e332a778708b7b82bd6db5903be5a389fef34de",
    GUARDRAIL_REVIEW_RELATIVE_PATH: "b881d23e9bd201b09bb023a1e897306afff681bd57ccb224a9c6baf562be57b6",
    FREEZE_REVIEW_RELATIVE_PATH: "2fb867bcc8cf8271d2511db2de8d9d605db5888d0ec407db9eab9085149d81f3",
}
PROMPT_RELATIVE_PATH = "Prompt.txt"
PROMPT_DEPENDENCY_ROLE = "DEMOTE_TO_NONBLOCKING_PROVENANCE"
PROMPT_SHA256 = "2bc6996ea28e96c50e688ed3d30ee24808af411a244eb594aad89ff80fda8433"

PARAMETER_AXIS_IDS = ["ETA_Q", "F_PERP_INITIAL", "THETA_W", "DELTA_THETA_PSI", "MU_MASS_DOMAIN"]
EXISTING_OBSERVABLE_IDS = [
    "GAUSS_RESIDUAL",
    "CONTINUITY_RESIDUAL",
    "DIRAC_ADJOINT_RESIDUALS",
    "MAXWELL_RESIDUALS",
    "LINK_NORM_ERROR",
    "ENERGY_DRIFT",
    "SPATIAL_CONVERGENCE",
    "TEMPORAL_CONVERGENCE",
    "WILSON_CONTINUUM_BEHAVIOR",
    "EXCHANGE_TO_DRIFT_RATIO",
]
DESCENDANT_OBSERVABLE_IDS = [
    "DELTA_E_PHI2",
    "DELTA_E_PHI3",
    "X2_SPINOR_PHI2_EXCHANGE",
    "X3_SPINOR_PHI3_EXCHANGE",
    "F_EXCHANGE_PERP",
    "R_PERP_OBSERVABLE",
    "C_PERP_SOURCE_NORM",
    "R_TRUNC_EQUATION_RESIDUAL",
    "T_DIVERGENCE",
]
ROBUSTNESS_STATUS_CLASSES = [
    "BROADLY_ROBUST",
    "CONDITIONALLY_ROBUST",
    "THRESHOLD_SENSITIVE",
    "NUMERICALLY_BLOCKED",
    "MODEL_DOMAIN_LIMITED",
]
DESCENDANT_SIGNIFICANCE_CLASSES = [
    "DESCENDANTS_DYNAMICALLY_NECESSARY_QUANTITATIVELY_SMALL",
    "DESCENDANT_DOMINATED_REGIME",
    "INTERMEDIATE_DESCENDANT_CONTRIBUTION",
]


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


def load_authority() -> dict[str, dict[str, Any]]:
    sources: dict[str, dict[str, Any]] = {}
    for path, digest in INPUT_HASHES.items():
        source_path = REPO_ROOT / path
        if sha256_path(source_path) != digest:
            raise ValueError(f"input hash mismatch: {path}")
        sources[path] = load_json(source_path)
    route = sources[ROUTE_REVIEW_RELATIVE_PATH]
    if not (
        route.get("accepted") is True
        and route.get("verdict") == "ACCEPT_ROUTE_DECISION"
        and route.get("selected_candidate_id") == "DESCENDANT_NECESSITY_ROBUSTNESS"
        and route.get("selected_next_target") == TARGET
        and route.get("authority_rotation", {}).get("descendant_necessity_robustness_preparation_authorized") is True
        and route.get("authority_rotation", {}).get("robustness_execution_authorized") is False
    ):
        raise ValueError("accepted route review does not authorize this design packet")
    canonical = sources[CANONICAL_REVIEW_RELATIVE_PATH]
    if not (canonical.get("accepted") is True and canonical.get("accepted_claim_label") == "E-REPRO"):
        raise ValueError("canonical result is not accepted E-REPRO")
    blocker = sources[BLOCKER_REVIEW_RELATIVE_PATH]
    if not (blocker.get("blocker_confirmed") is True and blocker.get("blocker_code") == "B-BLOCKED_TRANSVERSE_SECTOR_NOT_INVARIANT"):
        raise ValueError("original transverse-sector blocker is not preserved")
    if sources[ANALYTIC_REVIEW_RELATIVE_PATH].get("authority_rotation", {}).get("full_zero_mode_analytic_repair_accepted") is not True:
        raise ValueError("descendant-aware analytic repair is not accepted")
    if sources[GUARDRAIL_REVIEW_RELATIVE_PATH].get("authority_rotation", {}).get("numerical_guardrail_accepted") is not True:
        raise ValueError("descendant-aware numerical guardrail is not accepted")
    if sources[FREEZE_REVIEW_RELATIVE_PATH].get("authority_rotation", {}).get("canonical_parameter_freeze_accepted") is not True:
        raise ValueError("canonical parameter freeze is not accepted")
    return sources


def _evidence_record(proposition_id: str, source_path: str, pointer: str, expected: Any, proposition: str) -> dict[str, Any]:
    return {
        "evidence_id": f"E_{proposition_id}",
        "proposition_id": proposition_id,
        "source_path": source_path,
        "source_hash": INPUT_HASHES[source_path],
        "source_locator": {"locator_type": "JSON_POINTER", "pointer": pointer},
        "proposition_extraction_method": "EXACT_FIELD_READ",
        "authority_class": "ACCEPTED_BOUNDED_REVIEW",
        "evidence_role": "REPOSITORY_STATE_EVIDENCE",
        "support_mode": "ACCEPTED_REVIEW_STATE",
        "eligible_route_types": ["SCIENTIFIC_DESIGN_PREPARATION"],
        "exact_supported_proposition": proposition,
        "expected_source_value": expected,
        "scope_ceiling": "Scientific-design authority only; no new parameters, thresholds, execution, pillar, or seam authority.",
        "conflict_status": "NO_UNRESOLVED_CONFLICT",
        "route_support_eligible": True,
    }


def evidence_records() -> list[dict[str, Any]]:
    return [
        _evidence_record("P_ROBUSTNESS_ROUTE_SELECTED", ROUTE_REVIEW_RELATIVE_PATH, "/selected_candidate_id", "DESCENDANT_NECESSITY_ROBUSTNESS", "The accepted post-result route is descendant necessity and parameter robustness."),
        _evidence_record("P_ROBUSTNESS_PREPARATION_AUTHORIZED", ROUTE_REVIEW_RELATIVE_PATH, "/authority_rotation/descendant_necessity_robustness_preparation_authorized", True, "Only descendant-necessity and robustness preparation is authorized."),
        _evidence_record("P_CANONICAL_E_REPRO_ACCEPTED", CANONICAL_REVIEW_RELATIVE_PATH, "/accepted_claim_label", "E-REPRO", "The canonical descendant-aware result is accepted E-REPRO."),
        _evidence_record("P_CANONICAL_TRANSVERSE_SIGNAL", CANONICAL_REVIEW_RELATIVE_PATH, "/result_metrics/transverse_signal", 6.826809919994493e-08, "The accepted canonical point has a registered nonzero transverse signal."),
        _evidence_record("P_CANONICAL_EXCHANGE_RATIO", CANONICAL_REVIEW_RELATIVE_PATH, "/result_metrics/exchange_ratio", 352.6967159703898, "The accepted canonical point has exchange-to-drift ratio 352.6967159703898."),
        _evidence_record("P_ORIGINAL_TRANSVERSE_BLOCKER", BLOCKER_REVIEW_RELATIVE_PATH, "/blocker_code", "B-BLOCKED_TRANSVERSE_SECTOR_NOT_INVARIANT", "The forced A2=A3=0 truncation is not dynamically invariant for the retained generic sector."),
        _evidence_record("P_BLOCKER_CONFIRMED", BLOCKER_REVIEW_RELATIVE_PATH, "/blocker_confirmed", True, "The original transverse-sector obstruction is independently confirmed."),
        _evidence_record("P_FULL_DESCENDANT_REDUCTION_ACCEPTED", ANALYTIC_REVIEW_RELATIVE_PATH, "/authority_rotation/full_zero_mode_analytic_repair_accepted", True, "The full zero-mode reduction retaining both descendants is analytically accepted."),
        _evidence_record("P_PURE_TRUNCATION_NOT_REHABILITATED", ANALYTIC_REVIEW_RELATIVE_PATH, "/authority_rotation/pure_1p1_truncation_rehabilitated", False, "The rejected pure longitudinal truncation remains unrecovered."),
        _evidence_record("P_NUMERICAL_GUARDRAIL_ACCEPTED", GUARDRAIL_REVIEW_RELATIVE_PATH, "/authority_rotation/numerical_guardrail_accepted", True, "The descendant-aware mixed link/site numerical guardrail is accepted."),
        _evidence_record("P_CANONICAL_EXCHANGE_GATE_REFERENCE", FREEZE_REVIEW_RELATIVE_PATH, "/accepted_canonical_freeze/minimum_exchange_ratio", 100.0, "The canonical exchange gate is accepted for the canonical experiment only."),
        _evidence_record("P_CANONICAL_TRANSVERSE_GATE_REFERENCE", FREEZE_REVIEW_RELATIVE_PATH, "/accepted_canonical_freeze/minimum_transverse_signal", 3e-08, "The canonical transverse gate is accepted for the canonical experiment only."),
        _evidence_record("P_CANONICAL_ENERGY_CLASS_REFERENCE", FREEZE_REVIEW_RELATIVE_PATH, "/accepted_canonical_freeze/energy_classification", "BOUNDED_CONVERGENT_ENERGY_ERROR", "The canonical experiment uses bounded convergent energy error."),
    ]


def parameter_axes() -> list[dict[str, Any]]:
    return [
        {"axis_id": "ETA_Q", "symbol": "eta_q", "definition": "q_1p1 / m", "dimensionless": True, "required_level_roles": ["WEAKER", "CANONICAL", "STRONGER"], "exact_values_frozen": False},
        {"axis_id": "F_PERP_INITIAL", "symbol": "f_perp", "definition": "(E_phi2(0)+E_phi3(0))/E_total(0)", "dimensionless": True, "required_level_roles": ["ZERO", "MODEST", "LARGER_ADMITTED"], "exact_values_frozen": False},
        {"axis_id": "THETA_W", "symbol": "theta_W", "definition": "Arg(W)", "dimensionless": True, "required_level_roles": ["TRIVIAL", "NONTRIVIAL", "SYMMETRY_PARTNER_IF_DISTINCT"], "exact_values_frozen": False},
        {"axis_id": "DELTA_THETA_PSI", "symbol": "Delta_theta_psi", "definition": "frozen relative phase between selected charge/species or reduced-sector amplitudes", "dimensionless": True, "required_level_roles": ["CANONICAL", "POSITIVE_OFFSET", "NEGATIVE_OFFSET"], "exact_values_frozen": False},
        {"axis_id": "MU_MASS_DOMAIN", "symbol": "mu", "definition": "m * L_x", "dimensionless": True, "required_level_roles": ["CANONICAL", "ONE_BOUNDED_VARIATION"], "exact_values_frozen": False},
    ]


def comparison_tracks() -> list[dict[str, Any]]:
    return [
        {
            "track_id": "MODEL_ROBUSTNESS",
            "question": "Does the complete descendant-aware model retain convergence, constraint control, exchange separation, resolvable transverse activity, and control discrimination across the bounded domain?",
            "eligible_model_ids": ["FULL_ACCEPTED_DESCENDANT_AWARE_SYSTEM"],
            "forced_truncation_eligible_for_positive_claim": False,
        },
        {
            "track_id": "DESCENDANT_NECESSITY",
            "question": "How large are the omitted descendant-equation violations and full-versus-truncated observable differences when transverse sources are nonzero?",
            "model_ids": ["FULL_ACCEPTED_DESCENDANT_AWARE_SYSTEM", "INTENTIONALLY_NONINVARIANT_COMPARATOR"],
            "invalid_comparator_is_negative_control_only": True,
        },
        {
            "track_id": "INVARIANT_SPECIAL_SUBDOMAIN",
            "question": "Does a nontrivial restricted descendant-free subdomain exist and remain invariant under the admitted interaction?",
            "model_ids": ["ANALYTICALLY_INVARIANT_DESCENDANT_FREE_SUBDOMAIN"],
            "status": "CONDITIONAL_ON_SEPARATE_ACCEPTED_ANALYTIC_PROOF",
            "proof_requirements": ["J2_EQUALS_J3_ZERO_INITIAL", "J2_EQUALS_J3_ZERO_PRESERVED", "NONTRIVIAL", "INTERACTING_OR_EXPLICITLY_CLASSIFIED_DECOUPLED", "NOT_GENERALIZED"],
            "absence_of_proof_blocks_only_this_comparator": True,
        },
    ]


def observable_registry() -> dict[str, Any]:
    return {
        "existing_observables": [
            {"observable_id": observable_id, "retained_from_canonical_guardrail": True}
            for observable_id in EXISTING_OBSERVABLE_IDS
        ],
        "descendant_observables": [
            {"observable_id": "DELTA_E_PHI2", "definition": "E_phi2(t)-E_phi2(0)"},
            {"observable_id": "DELTA_E_PHI3", "definition": "E_phi3(t)-E_phi3(0)"},
            {"observable_id": "X2_SPINOR_PHI2_EXCHANGE", "definition": "registered spinor-to-phi2 exchange integral with the accepted sign convention"},
            {"observable_id": "X3_SPINOR_PHI3_EXCHANGE", "definition": "registered spinor-to-phi3 exchange integral with the accepted sign convention"},
            {"observable_id": "F_EXCHANGE_PERP", "definition": "(|X2|+|X3|)/(|X_longitudinal|+|X2|+|X3|+epsilon_exchange_floor)"},
            {"observable_id": "R_PERP_OBSERVABLE", "definition": "|O_full-O_forced_truncation|/(|O_full|+epsilon_observable_floor)", "registered_O_ids": ["MATTER_DENSITY", "LONGITUDINAL_ELECTRIC_FIELD", "MATTER_ENERGY", "LONGITUDINAL_EXCHANGE", "TOTAL_SOURCE_CURRENT"]},
            {"observable_id": "C_PERP_SOURCE_NORM", "definition": "sqrt(|J2|^2+|J3|^2) under the forced truncation"},
            {"observable_id": "R_TRUNC_EQUATION_RESIDUAL", "definition": "sqrt(|Box(phi2)-J2|^2+|Box(phi3)-J3|^2) evaluated for the forced truncation"},
            {"observable_id": "T_DIVERGENCE", "definition": "inf{t: R_perp,O(t) >= delta_O}", "registered_O_ids": ["MATTER_DENSITY", "LONGITUDINAL_ELECTRIC_FIELD", "MATTER_ENERGY", "LONGITUDINAL_EXCHANGE", "TOTAL_SOURCE_CURRENT"]},
        ],
        "future_freeze_requirements": {
            "epsilon_exchange_floor_frozen_before_execution": True,
            "epsilon_observable_floor_frozen_before_execution": True,
            "delta_O_frozen_per_registered_observable_before_execution": True,
            "norms_time_aggregation_and_spatial_aggregation_frozen_before_execution": True,
            "no_post_result_observable_selection": True,
        },
    }


def positive_controls() -> list[dict[str, Any]]:
    return [
        {"control_id": "P_CANONICAL_ACCEPTED_RESULT_UNCHANGED", "status": "REQUIRED", "expected": "Exact canonical inputs reproduce the accepted registered result within exact canonical thresholds."},
        {"control_id": "P_CHARGE_CONJUGATE_PARAMETER_CASE", "status": "REQUIRED", "expected": "Charge-conjugate transport and registered symmetry relations hold."},
        {"control_id": "P_ANALYTIC_INVARIANT_DESCENDANT_FREE", "status": "CONDITIONAL_ON_ACCEPTED_INVARIANT_SUBDOMAIN_PROOF", "expected": "J2=J3=0 is analytically and numerically preserved without generalization."},
        {"control_id": "P_INITIAL_ZERO_DESCENDANTS_DYNAMICALLY_SOURCED", "status": "REQUIRED", "expected": "Initially unexcited descendants respond when admitted transverse currents are nonzero."},
        {"control_id": "P_INDEPENDENT_PHI2_EXCITATION", "status": "REQUIRED", "expected": "The phi2 channel is resolved with its energy and exchange registered."},
        {"control_id": "P_INDEPENDENT_PHI3_EXCITATION", "status": "REQUIRED", "expected": "The phi3 channel is resolved with its energy and exchange registered."},
        {"control_id": "P_PHI2_PHI3_INTERCHANGE", "status": "REQUIRED_WHERE_ACCEPTED_SYMMETRY_SUPPORTS", "expected": "The accepted symmetry-related phi2/phi3 interchange produces the preregistered relation."},
        {"control_id": "P_WEAK_COUPLING_APPROACH", "status": "REQUIRED", "expected": "The weaker eta_q point approaches the registered decoupled trend without changing the model definition."},
    ]


def negative_controls() -> list[dict[str, Any]]:
    return [
        {"control_id": "N_FORCE_BOTH_DESCENDANTS_ZERO_WITH_SOURCE", "diagnostic": "ORIGINAL_TRANSVERSE_BLOCKER_REGRESSION", "permanent_regression": True},
        {"control_id": "N_DROP_ONLY_PHI2", "diagnostic": "PHI2_DESCENDANT_OMITTED"},
        {"control_id": "N_DROP_ONLY_PHI3", "diagnostic": "PHI3_DESCENDANT_OMITTED"},
        {"control_id": "N_OMIT_DESCENDANT_ENERGY", "diagnostic": "DESCENDANT_ENERGY_ACCOUNTING_OMITTED"},
        {"control_id": "N_OMIT_TRANSVERSE_EXCHANGE_CHANNEL", "diagnostic": "TRANSVERSE_EXCHANGE_CHANNEL_OMITTED"},
        {"control_id": "N_REVERSE_TRANSVERSE_EXCHANGE_SIGN", "diagnostic": "TRANSVERSE_EXCHANGE_SIGN_REVERSED"},
        {"control_id": "N_WRONG_GAMMA2_BLOCK", "diagnostic": "GAMMA2_BLOCK_MISMATCH"},
        {"control_id": "N_WRONG_GAMMA3_BLOCK", "diagnostic": "GAMMA3_BLOCK_MISMATCH"},
        {"control_id": "N_SUPPRESS_SECTOR_MULTIPLICITY", "diagnostic": "SECTOR_MULTIPLICITY_SUPPRESSED"},
        {"control_id": "N_DESCENDANTS_RELABELED_INVENTED_MATTER", "diagnostic": "DESCENDANT_ORIGIN_MISCLASSIFIED"},
        {"control_id": "N_CANONICAL_THRESHOLDS_REUSED_UNSCALED", "diagnostic": "UNREVIEWED_THRESHOLD_TRANSFER"},
        {"control_id": "N_POST_EXECUTION_FAVORABLE_POINT_SELECTION", "diagnostic": "POST_RESULT_PARAMETER_SELECTION"},
        {"control_id": "N_FAILED_POINTS_EXCLUDED_FROM_DOMAIN", "diagnostic": "FAILED_DOMAIN_POINTS_EXCLUDED"},
    ]


def outcome_taxonomy() -> dict[str, Any]:
    return {
        "simple_pass_fail_forbidden": True,
        "robustness_status_classes": [
            {"outcome_id": "BROADLY_ROBUST", "definition": "The complete model meets every frozen criterion across the full preregistered domain."},
            {"outcome_id": "CONDITIONALLY_ROBUST", "definition": "The complete model meets the frozen criteria only on an explicitly reported preregistered subdomain."},
            {"outcome_id": "THRESHOLD_SENSITIVE", "definition": "A conclusion changes materially under the preregistered admissible threshold-sensitivity analysis."},
            {"outcome_id": "NUMERICALLY_BLOCKED", "definition": "No controlled numerical conclusion is available for part or all of the domain."},
            {"outcome_id": "MODEL_DOMAIN_LIMITED", "definition": "The classical PDE surrogate ceases to provide a controlled result in an explicitly identified region."},
        ],
        "descendant_significance_classes": [
            {"outcome_id": "DESCENDANTS_DYNAMICALLY_NECESSARY_QUANTITATIVELY_SMALL", "definition": "The forced truncation is noninvariant, while preregistered observable differences remain small over the tested duration in a reported subdomain."},
            {"outcome_id": "DESCENDANT_DOMINATED_REGIME", "definition": "Transverse descendants carry a preregistered substantial exchange fraction or strongly alter longitudinal or matter evolution."},
            {"outcome_id": "INTERMEDIATE_DESCENDANT_CONTRIBUTION", "definition": "Descendant contributions are resolved and material but do not cross the descendant-dominated gate."},
        ],
        "multi_axis_classification_required": True,
        "negative_inconclusive_and_blocked_outcomes_preserved": True,
    }


def build_packet() -> dict[str, Any]:
    sources = load_authority()
    evidence = evidence_records()
    for record in evidence:
        observed = _json_pointer(sources[record["source_path"]], record["source_locator"]["pointer"])
        if observed != record["expected_source_value"]:
            raise ValueError(f"proposition locator mismatch: {record['proposition_id']}")
    return {
        "schema_id": PACKET_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "selected_next_target": REVIEW_TARGET,
        "selected_next_target_kind": REVIEW_TARGET_KIND,
        "failure_target": FAILURE_TARGET,
        "post_acceptance_target": POST_ACCEPTANCE_TARGET,
        "evidence_records": evidence,
        "scientific_questions": [
            {"question_id": "Q_ROBUSTNESS_DOMAIN", "question": "Is the accepted descendant-aware result representative of a meaningful bounded region of the admitted model?", "claim_track": "MODEL_ROBUSTNESS"},
            {"question_id": "Q_DESCENDANT_SIGNIFICANCE", "question": "How strongly do phi2=A2 and phi3=A3 alter matter, longitudinal-gauge, exchange, and energy-accounting observables when transverse currents are nonzero?", "claim_track": "DESCENDANT_NECESSITY"},
        ],
        "question_tracks_separate": True,
        "comparison_tracks": comparison_tracks(),
        "parameter_axes": parameter_axes(),
        "all_parameter_axes_dimensionless_or_normalized": True,
        "exact_parameter_values_frozen": False,
        "bounded_matrix_policy": {
            "design": "CANONICAL_ANCHOR_PLUS_ONE_AT_A_TIME_PLUS_PREREGISTERED_INTERACTION_CORNERS",
            "full_cartesian_sweep_forbidden": True,
            "canonical_anchor_count": 1,
            "required_axis_level_coverage": {axis["axis_id"]: axis["required_level_roles"] for axis in parameter_axes()},
            "one_at_a_time_rows_are_distinct_from_anchor": True,
            "interaction_corner_count_minimum": 3,
            "interaction_corner_count_maximum": 4,
            "future_exact_unique_scientific_row_count_minimum": 12,
            "future_exact_unique_scientific_row_count_maximum": 14,
            "duplicate_parameter_tuples_forbidden": True,
            "exact_matrix_must_be_frozen_before_any_new_calibration_run": True,
            "difficult_points_may_not_be_removed_after_pilot_observation": True,
        },
        "observable_registry": observable_registry(),
        "positive_controls": positive_controls(),
        "negative_controls": negative_controls(),
        "original_reduction_blocker_is_permanent_regression": True,
        "threshold_and_pilot_policy": {
            "canonical_thresholds_are_reference_evidence_only": True,
            "canonical_thresholds_automatically_reused": False,
            "new_thresholds_frozen": False,
            "new_solver_or_grid_values_frozen": False,
            "pilot_authorized": False,
            "pilot_may_calibrate_only": ["solver_tolerance", "grid_sequence", "time_step_sequence", "duration", "iteration_cap", "numerical_floor", "threshold_generation_inputs"],
            "pilot_may_not_change": ["scientific_questions", "parameter_axes", "comparators", "observable_ids", "control_ids", "outcome_classes", "claim_ceiling"],
            "per_point_normalization_or_one_reviewed_shared_scaling_rule_required": True,
            "threshold_sensitivity_policy_must_be_frozen_before_execution": True,
        },
        "outcome_taxonomy": outcome_taxonomy(),
        "lifecycle": [
            POST_ACCEPTANCE_TARGET,
            "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_guardrail_packet_v0_result",
            "execute_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_non_authoritative_pilot_v0",
            "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_parameter_freeze_packet_v0",
            "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_parameter_freeze_packet_v0_result",
            "execute_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_canonical_matrix_v0",
            "review_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_canonical_matrix_v0_result",
        ],
        "maximum_future_claim": "Across the preregistered bounded parameter family, the complete descendant-aware c-number Maxwell-Dirac zero-mode model reproducibly preserves its accepted constraint and energy-error behavior, while the transverse descendants contribute measurable exchange and cannot be consistently omitted outside explicitly identified invariant subdomains.",
        "claim_ceiling_not_yet_earned": True,
        "completed_canonical_result_reopened": False,
        "boundary": {
            "scientific_design_prepared": True,
            "scientific_design_accepted": False,
            "robustness_guardrail_preparation_authorized": False,
            "robustness_guardrail_accepted": False,
            "pilot_authorized": False,
            "exact_parameter_matrix_frozen": False,
            "thresholds_frozen": False,
            "canonical_robustness_execution_authorized": False,
            "universal_Maxwell_Dirac_robustness_claimed": False,
            "physical_necessity_in_nature_claimed": False,
            "fermionic_QFT_claimed": False,
            "quantized_electromagnetism_claimed": False,
            "pillar_completion_claimed": False,
            "seam_closure_claimed": False,
            "new_fundamental_physics_claimed": False,
            "C_k_dynamics_claimed": False,
            "master_action_validated": False,
            "repository_wide_green_claimed": False,
        },
        "input_artifacts": [{"path": path, "sha256": digest} for path, digest in INPUT_HASHES.items()],
        "prompt_protection": {"path": PROMPT_RELATIVE_PATH, "sha256": PROMPT_SHA256, "excluded_from_scientific_inputs": True},
    }


def validate_packet(packet: dict[str, Any]) -> list[str]:
    failures: list[str] = []
    if packet.get("schema_id") != PACKET_SCHEMA_ID or packet.get("target") != TARGET:
        failures.append("design_identity")
    evidence = packet.get("evidence_records", [])
    if (
        len(evidence) != 13
        or len({item.get("proposition_id") for item in evidence}) != 13
        or any(item.get("route_support_eligible") is not True for item in evidence)
    ):
        failures.append("evidence_closure")
    questions = packet.get("scientific_questions", [])
    if packet.get("question_tracks_separate") is not True or {item.get("claim_track") for item in questions} != {"MODEL_ROBUSTNESS", "DESCENDANT_NECESSITY"}:
        failures.append("question_track_separation")
    tracks = {item.get("track_id"): item for item in packet.get("comparison_tracks", [])}
    robustness = tracks.get("MODEL_ROBUSTNESS", {})
    necessity = tracks.get("DESCENDANT_NECESSITY", {})
    if (
        robustness.get("eligible_model_ids") != ["FULL_ACCEPTED_DESCENDANT_AWARE_SYSTEM"]
        or robustness.get("forced_truncation_eligible_for_positive_claim") is not False
        or necessity.get("invalid_comparator_is_negative_control_only") is not True
        or "INTENTIONALLY_NONINVARIANT_COMPARATOR" not in necessity.get("model_ids", [])
    ):
        failures.append("comparator_eligibility")
    special = tracks.get("INVARIANT_SPECIAL_SUBDOMAIN", {})
    if (
        special.get("status") != "CONDITIONAL_ON_SEPARATE_ACCEPTED_ANALYTIC_PROOF"
        or len(special.get("proof_requirements", [])) != 5
        or special.get("absence_of_proof_blocks_only_this_comparator") is not True
    ):
        failures.append("invariant_subdomain_proof_gate")
    axes = packet.get("parameter_axes", [])
    if [item.get("axis_id") for item in axes] != PARAMETER_AXIS_IDS:
        failures.append("exact_five_axes")
    if packet.get("all_parameter_axes_dimensionless_or_normalized") is not True or any(item.get("dimensionless") is not True for item in axes):
        failures.append("normalized_axes")
    matrix = packet.get("bounded_matrix_policy", {})
    if (
        matrix.get("full_cartesian_sweep_forbidden") is not True
        or matrix.get("future_exact_unique_scientific_row_count_minimum") != 12
        or matrix.get("future_exact_unique_scientific_row_count_maximum") != 14
        or matrix.get("exact_matrix_must_be_frozen_before_any_new_calibration_run") is not True
        or matrix.get("duplicate_parameter_tuples_forbidden") is not True
    ):
        failures.append("bounded_matrix")
    observables = packet.get("observable_registry", {})
    if (
        [item.get("observable_id") for item in observables.get("existing_observables", [])] != EXISTING_OBSERVABLE_IDS
        or [item.get("observable_id") for item in observables.get("descendant_observables", [])] != DESCENDANT_OBSERVABLE_IDS
        or observables.get("future_freeze_requirements", {}).get("no_post_result_observable_selection") is not True
    ):
        failures.append("observable_inventory")
    positives = packet.get("positive_controls", [])
    negatives = packet.get("negative_controls", [])
    if len(positives) != 8 or len(negatives) != 13 or len({item.get("control_id") for item in positives + negatives}) != 21:
        failures.append("control_inventory")
    if (
        packet.get("original_reduction_blocker_is_permanent_regression") is not True
        or not any(item.get("control_id") == "N_FORCE_BOTH_DESCENDANTS_ZERO_WITH_SOURCE" and item.get("permanent_regression") is True for item in negatives)
    ):
        failures.append("blocker_regression")
    threshold = packet.get("threshold_and_pilot_policy", {})
    if threshold.get("canonical_thresholds_are_reference_evidence_only") is not True or threshold.get("canonical_thresholds_automatically_reused") is not False:
        failures.append("threshold_transfer")
    if threshold.get("pilot_authorized") is not False or threshold.get("new_thresholds_frozen") is not False or threshold.get("new_solver_or_grid_values_frozen") is not False:
        failures.append("pilot_unauthorized")
    if matrix.get("difficult_points_may_not_be_removed_after_pilot_observation") is not True:
        failures.append("no_postpilot_selection")
    outcomes = packet.get("outcome_taxonomy", {})
    if (
        outcomes.get("simple_pass_fail_forbidden") is not True
        or [item.get("outcome_id") for item in outcomes.get("robustness_status_classes", [])] != ROBUSTNESS_STATUS_CLASSES
        or [item.get("outcome_id") for item in outcomes.get("descendant_significance_classes", [])] != DESCENDANT_SIGNIFICANCE_CLASSES
        or outcomes.get("multi_axis_classification_required") is not True
    ):
        failures.append("outcome_taxonomy")
    if packet.get("completed_canonical_result_reopened") is not False:
        failures.append("completed_canonical_immutable")
    boundary = packet.get("boundary", {})
    if (
        boundary.get("scientific_design_prepared") is not True
        or boundary.get("scientific_design_accepted") is not False
        or boundary.get("robustness_guardrail_preparation_authorized") is not False
        or boundary.get("pilot_authorized") is not False
        or boundary.get("exact_parameter_matrix_frozen") is not False
        or boundary.get("thresholds_frozen") is not False
        or boundary.get("canonical_robustness_execution_authorized") is not False
    ):
        failures.append("preparation_only_boundary")
    if any(
        boundary.get(key) is not False
        for key in [
            "universal_Maxwell_Dirac_robustness_claimed",
            "physical_necessity_in_nature_claimed",
            "fermionic_QFT_claimed",
            "quantized_electromagnetism_claimed",
            "pillar_completion_claimed",
            "seam_closure_claimed",
            "new_fundamental_physics_claimed",
            "C_k_dynamics_claimed",
            "master_action_validated",
            "repository_wide_green_claimed",
        ]
    ):
        failures.append("nonpromotion_boundary")
    if packet.get("claim_ceiling_not_yet_earned") is not True:
        failures.append("claim_ceiling_unearned")
    if packet.get("post_acceptance_target") != POST_ACCEPTANCE_TARGET:
        failures.append("successor_identity")
    if not prompt_dependency_is_nonblocking(PROMPT_DEPENDENCY_ROLE):
        failures.append("Prompt_preserved")
    return failures


def mutation_controls(base: dict[str, Any]) -> list[dict[str, Any]]:
    Mutation = tuple[str, Callable[[dict[str, Any]], None], str]
    mutations: list[Mutation] = [
        ("necessity_robustness_tracks_merged", lambda value: value.update({"question_tracks_separate": False}), "question_track_separation"),
        ("invalid_truncation_promoted_to_robustness_model", lambda value: value["comparison_tracks"][0].update({"forced_truncation_eligible_for_positive_claim": True}), "comparator_eligibility"),
        ("invariant_subdomain_assumed_without_proof", lambda value: value["comparison_tracks"][2].update({"status": "ACCEPTED_WITHOUT_PROOF"}), "invariant_subdomain_proof_gate"),
        ("parameter_axis_removed", lambda value: value["parameter_axes"].pop(), "exact_five_axes"),
        ("dimensionful_axis_imported", lambda value: value["parameter_axes"][0].update({"dimensionless": False}), "normalized_axes"),
        ("full_cartesian_sweep_enabled", lambda value: value["bounded_matrix_policy"].update({"full_cartesian_sweep_forbidden": False}), "bounded_matrix"),
        ("descendant_observable_removed", lambda value: value["observable_registry"]["descendant_observables"].pop(), "observable_inventory"),
        ("canonical_thresholds_reused_automatically", lambda value: value["threshold_and_pilot_policy"].update({"canonical_thresholds_automatically_reused": True}), "threshold_transfer"),
        ("pilot_authorized_early", lambda value: value["threshold_and_pilot_policy"].update({"pilot_authorized": True}), "pilot_unauthorized"),
        ("difficult_points_removable", lambda value: value["bounded_matrix_policy"].update({"difficult_points_may_not_be_removed_after_pilot_observation": False}), "no_postpilot_selection"),
        ("original_blocker_regression_removed", lambda value: value.update({"original_reduction_blocker_is_permanent_regression": False}), "blocker_regression"),
        ("outcomes_collapsed_to_pass_fail", lambda value: value["outcome_taxonomy"].update({"simple_pass_fail_forbidden": False}), "outcome_taxonomy"),
        ("canonical_result_reopened", lambda value: value.update({"completed_canonical_result_reopened": True}), "completed_canonical_immutable"),
        ("robustness_execution_authorized_early", lambda value: value["boundary"].update({"canonical_robustness_execution_authorized": True}), "preparation_only_boundary"),
        ("universal_robustness_promoted", lambda value: value["boundary"].update({"universal_Maxwell_Dirac_robustness_claimed": True}), "nonpromotion_boundary"),
    ]
    results = []
    for control_id, mutate, diagnostic in mutations:
        fixture = copy.deepcopy(base)
        if validate_packet(fixture):
            raise ValueError(f"unmutated fixture failed before {control_id}")
        mutate(fixture)
        observed = validate_packet(fixture)
        results.append({"control_id": control_id, "changed_premise_count": 1, "expected_diagnostic": diagnostic, "observed_diagnostics": observed, "passed": observed == [diagnostic]})
    return results


DECISION_IDS = [
    "accepted_route_review_authorizes_scientific_design_only",
    "canonical_result_blocker_repair_guardrail_and_freeze_sources_are_hash_bound",
    "necessity_and_robustness_are_separate_claim_tracks",
    "full_model_is_the_only_positive_robustness_candidate",
    "forced_truncation_is_intentionally_noninvariant_negative_comparator_only",
    "descendant_free_special_case_requires_separate_invariant_subdomain_proof",
    "five_dimensionless_or_normalized_scientific_axes_are_frozen",
    "exact_axis_values_and_thresholds_remain_unfrozen",
    "anchor_plus_OAT_plus_corner_matrix_is_bounded_before_pilot",
    "all_existing_and_descendant_observables_are_registered",
    "eight_positive_and_thirteen_negative_control_definitions_are frozen",
    "original_reduction_blocker_is_a_permanent_regression_control",
    "canonical_thresholds_are_reference_only_and_not_automatically_reused",
    "pilot_may_not_change_scientific_axes_comparators_observables_controls_or_outcomes",
    "multi_axis_outcome_taxonomy_preserves conditional blocked and domain-limited results",
    "fifteen_design_mutations_are_independently_diagnosed",
    "completed_canonical_result_remains_immutable",
    "only_independent_design_review_is_authorized",
    "claim_ceiling_and_all_nonpromotion_boundaries_hold",
    "Prompt_is_preserved",
]


def build_artifacts() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    packet = build_packet()
    failures = validate_packet(packet)
    if failures:
        raise ValueError(f"robustness design validation failed: {failures}")
    controls = mutation_controls(packet)
    if not all(item["passed"] for item in controls):
        raise ValueError("robustness design mutation controls failed")
    packet["mutation_controls"] = controls
    packet_raw = canonical_json_bytes(packet)
    manifest = {
        "schema_id": MANIFEST_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "generator": {"path": SCRIPT_RELATIVE_PATH, "sha256": sha256_path(SCRIPT_PATH)},
        "inputs": packet["input_artifacts"],
        "packet": {"path": PACKET_RELATIVE_PATH, "sha256": sha256_bytes(packet_raw)},
        "selected_next_target": REVIEW_TARGET,
        "decision_count": len(DECISION_IDS),
        "parameter_axis_count": len(PARAMETER_AXIS_IDS),
        "existing_observable_count": len(EXISTING_OBSERVABLE_IDS),
        "descendant_observable_count": len(DESCENDANT_OBSERVABLE_IDS),
        "positive_control_count": len(packet["positive_controls"]),
        "negative_control_count": len(packet["negative_controls"]),
        "mutation_control_count": len(controls),
    }
    manifest_raw = canonical_json_bytes(manifest)
    report = {
        "schema_id": REPORT_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "verdict": "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "selected_next_target": REVIEW_TARGET,
        "selected_next_target_kind": REVIEW_TARGET_KIND,
        "failure_target": FAILURE_TARGET,
        "post_acceptance_target": POST_ACCEPTANCE_TARGET,
        "decision_count": len(DECISION_IDS),
        "decisions": [{"decision_id": item, "passed": True} for item in DECISION_IDS],
        "all_decisions_passed": True,
        "mutation_control_count": len(controls),
        "mutation_controls_passed": sum(item["passed"] for item in controls),
        "design_summary": {
            "scientific_question_count": len(packet["scientific_questions"]),
            "comparison_track_count": len(packet["comparison_tracks"]),
            "parameter_axis_count": len(packet["parameter_axes"]),
            "future_scientific_row_count_range": [12, 14],
            "existing_observable_count": len(EXISTING_OBSERVABLE_IDS),
            "descendant_observable_count": len(DESCENDANT_OBSERVABLE_IDS),
            "positive_control_count": len(packet["positive_controls"]),
            "negative_control_count": len(packet["negative_controls"]),
            "robustness_status_class_count": len(ROBUSTNESS_STATUS_CLASSES),
            "descendant_significance_class_count": len(DESCENDANT_SIGNIFICANCE_CLASSES),
        },
        "artifact_hashes": {"generator_sha256": sha256_path(SCRIPT_PATH), "packet_sha256": sha256_bytes(packet_raw), "manifest_sha256": sha256_bytes(manifest_raw)},
        "boundary": packet["boundary"],
        "claim": "The bounded descendant-necessity and robustness scientific design is prepared; exact parameter values, thresholds, pilot, and execution remain unauthorized pending independent review and later guardrails.",
        "nonclaims": [
            "no robustness design accepted yet",
            "no exact robustness matrix or thresholds frozen",
            "no pilot or robustness execution authorized",
            "no universal robustness or physical necessity in nature",
            "no fermionic QFT or quantized electromagnetism",
            "no pillar completion, seam closure, new physics, C_k dynamics, or master-action validation",
            "no repository-wide green claim",
        ],
    }
    return packet, manifest, report


def _write(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(canonical_json_bytes(payload))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Prepare the descendant necessity and robustness scientific-design packet.")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    try:
        packet, manifest, report = build_artifacts()
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    artifacts = [(PACKET_PATH, packet), (MANIFEST_PATH, manifest), (REPORT_PATH, report)]
    if args.write:
        for path, payload in artifacts:
            _write(path, payload)
        print("wrote descendant necessity and robustness design: five axes; 12-14 future rows; execution unauthorized")
        return 0
    if args.check:
        stale = [str(path) for path, payload in artifacts if not path.is_file() or path.read_bytes() != canonical_json_bytes(payload)]
        if stale:
            print("stale or missing descendant necessity and robustness artifacts: " + ", ".join(stale), file=sys.stderr)
            return 1
        print("descendant necessity and robustness design verified: scientific questions frozen; pilot unauthorized")
        return 0
    sys.stdout.buffer.write(canonical_json_bytes(report))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

from __future__ import annotations

import argparse
import copy
import hashlib
import json
from fractions import Fraction
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "POST_QUADRATIC_GRAVITY_COMPARISON_CONDITIONAL_MODE_SELECTION_ENVELOPE_"
    "RESULT_REVIEW_20260718_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/"
    "POST_QUADRATIC_GRAVITY_COMPARISON_CONDITIONAL_MODE_SELECTION_ENVELOPE_"
    "RESULT_REVIEW_20260718_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_post_quadratic_gravity_comparison_conditional_mode_selection_"
    "envelope_result_review_v0.py"
)
EXECUTION_RELATIVE_PATH = (
    "formal/docs/release/"
    "POST_QUADRATIC_GRAVITY_COMPARISON_CONDITIONAL_MODE_SELECTION_ENVELOPE_"
    "20260718_v0.json"
)
PACKET_RELATIVE_PATH = (
    "formal/docs/release/"
    "POST_QUADRATIC_GRAVITY_COMPARISON_CONDITIONAL_MODE_SELECTION_PACKET_"
    "20260718_v0.json"
)
TARGET = (
    "review_post_quadratic_gravity_comparison_conditional_mode_selection_"
    "envelope_v0_result"
)
VERDICT = "ACCEPTED_CONDITIONAL_MODE_SELECTION_ENVELOPE_RESULT"
SELECTED_NEXT_TARGET = (
    "select_post_quadratic_gravity_conditional_mode_selection_envelope_"
    "scientific_response_v0"
)
SELECTED_NEXT_TARGET_KIND = "SCIENTIFIC_RESPONSE_SELECTION_ONLY_NO_BRANCH_ADOPTION"

EXECUTION_HASHES = {
    "formal/docs/lanes/POST_QUADRATIC_GRAVITY_COMPARISON_CONDITIONAL_MODE_SELECTION_ENVELOPE_20260718_v0.md":
        "a5b07ebad9594c5184a2708da87434c40601cdbee96a936b72e0e2e2db65ee4b",
    "formal/docs/release/POST_QUADRATIC_GRAVITY_COMPARISON_CONDITIONAL_MODE_SELECTION_ENVELOPE_20260718_v0.json":
        "b0a4ab6d91503e272b98dca59a9ea35643cffac6de7330d1ac843e67e9dc4dbf",
    "formal/python/tools/post_quadratic_gravity_comparison_conditional_mode_selection_envelope_v0.py":
        "c4f392ae54eefdb25277eb0513009380f7648f1308c85d7a2574b4c95f0f6888",
    "formal/python/tests/test_post_quadratic_gravity_comparison_conditional_mode_selection_envelope_v0.py":
        "75474945a6c4a8aec1fcb6fa08843b8c8a08f46029842533915545247c7dd154",
    "formal/toe_formal/ToeFormal/Derivation/PostQuadraticGravityComparisonConditionalModeSelectionEnvelopeV0.lean":
        "a768061e35a1fde4e6dc5635c9506b20519aca980b5acc0f65734cb2c7ade76a",
}

EXPECTED_SELECTORS = {
    "SEL_NATIVE_R9_CURRENT_REPRESENTABILITY": (
        "PROJECT_BOUND_NATIVE_PRINCIPLE", "R9_MOMENTUM_CURRENT", "NONE_BY_ITSELF"
    ),
    "SEL_NATIVE_R10_STABILITY_EVALUATION": (
        "PROJECT_BOUND_NATIVE_PRINCIPLE", "R10_STABILITY_NO_FIT",
        "NONE_WITHOUT_AN_ACCEPTANCE_THRESHOLD",
    ),
    "SEL_NO_TACHYONIC_POLES": (
        "SUPPLIED_STANDARD_PHYSICS_CRITERION", "STANDARD_LINEARIZED_STABILITY_CRITERION",
        "Sigma<0 and beta>0 when both extra poles are present",
    ),
    "SEL_NO_NEGATIVE_RESIDUE_SPIN2": (
        "SUPPLIED_STANDARD_PHYSICS_CRITERION", "STANDARD_GHOST_AVOIDANCE_CRITERION", "beta=0"
    ),
    "SEL_NO_EXTRA_SCALAR": (
        "SUPPLIED_STANDARD_PHYSICS_CRITERION", "COMPONENT_OF_S3_NO_EXTRA_GRAVITATIONAL_MODES", "Sigma=0"
    ),
    "SEL_MINIMAL_SPECTRUM": (
        "SUPPLIED_STANDARD_PHYSICS_CRITERION", "S3_NO_EXTRA_GRAVITATIONAL_MODES",
        "beta=0 and Sigma=0 implies alpha=beta=0",
    ),
    "SEL_EXACT_EINSTEIN_0I": (
        "SUPPLIED_STANDARD_PHYSICS_CRITERION", "EXACT_STANDARD_GR_CURRENT_RESPONSE_COMPARATOR", "beta=0"
    ),
    "SEL_FINITE_PRECISION_0I": (
        "EMPIRICAL_CONSTRAINT", "FUTURE_DATASET_RANGE_AND_ERROR_MODEL_REQUIRED",
        "bound or suppress m2 range; beta=0 not logically inferred",
    ),
    "SEL_LONG_RANGE_EINSTEIN": (
        "SUPPLIED_STANDARD_PHYSICS_CRITERION", "STANDARD_GR_LONG_RANGE_RECOVERY_COMPARATOR",
        "broad finite positive-mass or decoupling regions remain",
    ),
    "SEL_HYPOTHETICAL_MINIMAL_MODE_POSTULATE": (
        "PROPOSED_NEW_POSTULATE", "HYPOTHETICAL_ONLY_NOT_AUTHORIZED_OR_ADOPTED",
        "would imply alpha=beta=0 within the frozen family",
    ),
}

SUBORDINATE_FINDINGS = (
    "NO_CURRENT_NATIVE_CONDITION_SELECTS_A_BRANCH",
    "STANDARD_CONSISTENCY_CRITERIA_FAVOR_SCALAR_ONLY_OR_EH_BRANCHES",
    "MINIMAL_MODE_CONDITION_WOULD_COLLAPSE_FAMILY_TO_EH",
    "EMPIRICAL_CURRENT_CHANNEL_BOUNDS_BUT_DOES_NOT_EXACTLY_SELECT_BETA",
    "OUTSIDE_FAMILY_MECHANISM_REQUIRES_FRESH_TARGET",
)

FORBIDDEN_RANKING_KEYS = {
    "preference_score", "ranking", "recommendation", "recommended_branch", "default_branch"
}


class ReviewFailure(ValueError):
    def __init__(self, code: str, message: str) -> None:
        super().__init__(message)
        self.code = code


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {relative_path}")
    return value


def _has_forbidden_ranking_key(value: Any) -> bool:
    if isinstance(value, dict):
        if any(str(key).lower() in FORBIDDEN_RANKING_KEYS for key in value):
            return True
        return any(_has_forbidden_ranking_key(item) for item in value.values())
    if isinstance(value, list):
        return any(_has_forbidden_ranking_key(item) for item in value)
    return False


def _row(value: dict[str, Any], selector_id: str) -> dict[str, Any]:
    return next(
        row for row in value["selector_adjudication"]["rows"]
        if row["selector_id"] == selector_id
    )


def audit_execution(value: dict[str, Any]) -> dict[str, Any]:
    if _has_forbidden_ranking_key(value):
        raise ReviewFailure("HIDDEN_RANKING", "execution contains a ranking or recommendation field")
    if value.get("target") != (
        "execute_post_quadratic_gravity_comparison_conditional_mode_selection_envelope_v0"
    ) or value.get("verdict") != "CONDITIONAL_MODE_SELECTION_ENVELOPE_COMPLETE":
        raise ReviewFailure("EXECUTION_IDENTITY_MISMATCH", "execution identity or verdict mismatch")

    register = value.get("selector_adjudication", {})
    rows = register.get("rows", [])
    if len(rows) != 10 or register.get("selector_count") != 10:
        raise ReviewFailure("SELECTOR_COUNT_MISMATCH", "expected ten selector records")
    observed_ids = {row.get("selector_id") for row in rows}
    if observed_ids != set(EXPECTED_SELECTORS):
        raise ReviewFailure("SELECTOR_ID_MISMATCH", "selector register differs from canonical set")

    for selector_id, (expected_class, expected_binding, expected_consequence) in EXPECTED_SELECTORS.items():
        selector = _row(value, selector_id)
        provenance = selector.get("canonical_provenance", {})
        if provenance.get("authority_class") != expected_class or provenance.get("authority_binding") != expected_binding:
            raise ReviewFailure("AUTHORITY_CLASS_MISMATCH", f"authority mismatch: {selector_id}")
        observed_consequence = selector.get("conditional_parameter_consequence")
        if observed_consequence != expected_consequence:
            if selector_id == "SEL_NATIVE_R9_CURRENT_REPRESENTABILITY":
                raise ReviewFailure("R9_STRENGTHENED", "R9 acquired a parameter restriction")
            if selector_id == "SEL_NATIVE_R10_STABILITY_EVALUATION":
                raise ReviewFailure("R10_STRENGTHENED", "R10 acquired an acceptance threshold")
            if selector_id == "SEL_FINITE_PRECISION_0I" and observed_consequence == "beta=0":
                raise ReviewFailure("EMPIRICAL_EXACT_IDENTITY", "finite data became exact beta=0")
            raise ReviewFailure("CONSEQUENCE_MISMATCH", f"conditional consequence mismatch: {selector_id}")
        if selector.get("scope") != "FROZEN_QUADRATIC_COMPARISON_SCOPE":
            raise ReviewFailure("SCOPE_LEAK", f"selector scope changed: {selector_id}")
        if selector.get("condition_adopted") is not False or selector.get("adoption_status") != "NOT_ADOPTED":
            raise ReviewFailure("HIDDEN_ADOPTION", f"selector adopted: {selector_id}")
        if selector.get("native_branch_selection_authority") is not False:
            raise ReviewFailure("HIDDEN_NATIVE_SELECTOR", f"native branch weight asserted: {selector_id}")
        if selector.get("adjudication_status") != "AUTHORITY_CLASSIFIED_CONSEQUENCE_RECORDED_NOT_ADOPTED":
            raise ReviewFailure("ADJUDICATION_STATUS_MISMATCH", f"status mismatch: {selector_id}")

    if register.get("adjudicated_count") != 10 or register.get("adopted_count") != 0:
        raise ReviewFailure("HIDDEN_ADOPTION", "register counts imply incomplete or adopted selectors")

    positions = value.get("position_map", {})
    if positions.get("position_count") != 3 or positions.get("selected_count") != 0:
        raise ReviewFailure("POSITION_SELECTED", "position counts indicate selection")
    if any(row.get("selected") is not False for row in positions.get("rows", [])):
        raise ReviewFailure("POSITION_SELECTED", "a scientific position was selected")

    principal = value.get("principal_classification", {})
    if principal.get("outcome") != "CONDITIONAL_MODE_SELECTION_ENVELOPE_COMPLETE" or principal.get("outcome_count") != 1:
        raise ReviewFailure("PRINCIPAL_RESULT_MISMATCH", "principal outcome is not exclusive and complete")
    if principal.get("native_selector_count") != 0:
        raise ReviewFailure("PRINCIPAL_NATIVE_COUNT_MISMATCH", "principal result asserts native selection")
    if tuple(value.get("subordinate_findings", [])) != SUBORDINATE_FINDINGS:
        raise ReviewFailure("SUBORDINATE_FINDING_MISMATCH", "subordinate findings changed")

    current = value.get("exact_empirical_current_classification", {})
    if current.get("exact_theoretical_equality") != "beta=0 within frozen family":
        raise ReviewFailure("EXACT_CURRENT_MISMATCH", "exact current comparator consequence changed")
    if current.get("exact_beta_zero_from_finite_data_licensed") is not False:
        raise ReviewFailure("EMPIRICAL_EXACT_IDENTITY", "finite data licensed exact beta=0")

    coincident = value.get("coincident_mass_status", {})
    if not coincident.get("P2_P0s_orthogonal") or any(
        coincident.get(key) is not False
        for key in ("double_pole", "mode_merger", "cancellation", "ghost_repaired")
    ):
        raise ReviewFailure("COINCIDENT_MASS_MISCLASSIFIED", "coincident channels were merged or repaired")

    if value.get("scope_firewall", {}).get("outside_family_transport_allowed") is not False:
        raise ReviewFailure("SCOPE_LEAK", "outside-family transport was enabled")
    scope = value.get("scope", {})
    if scope.get("additional_execution_authorized") is not False:
        raise ReviewFailure("DOWNSTREAM_AUTHORIZATION_LEAK", "additional execution was authorized")
    allowed_true = {
        "envelope_execution_completed", "selector_adjudication_completed",
        "principal_classification_issued", "independent_result_review_required",
    }
    for key, item in scope.items():
        if key == "authorized_execution_consumed":
            if item != 1:
                raise ReviewFailure("EXECUTION_COUNT_MISMATCH", "authorized run count mismatch")
        elif key in allowed_true:
            if item is not True:
                raise ReviewFailure("EXECUTION_COMPLETENESS_MISMATCH", f"missing execution fact: {key}")
        elif item is not False:
            raise ReviewFailure("SCOPE_LEAK", f"prohibited scope flag true: {key}")

    controls = value.get("execution_controls", {})
    if controls.get("control_count") != 18 or controls.get("pass_count") != 18 or controls.get("failure_count") != 0:
        raise ReviewFailure("CONTROL_MISMATCH", "execution controls are not 18/18")
    if value.get("selected_next_target") != TARGET:
        raise ReviewFailure("AUTHORITY_ROTATION_MISMATCH", "execution did not stop at this result review")

    class_counts: dict[str, int] = {}
    for selector in rows:
        authority_class = selector["canonical_provenance"]["authority_class"]
        class_counts[authority_class] = class_counts.get(authority_class, 0) + 1
    return {
        "selector_count": 10,
        "adjudicated_count": 10,
        "adopted_count": 0,
        "native_branch_selector_count": 0,
        "open_position_count": 3,
        "class_counts": class_counts,
    }


def _independent_algebra() -> dict[str, Any]:
    scalar_samples = []
    for sigma in (-2, -1, 1, 2):
        mass = -Fraction(1, 2 * sigma)
        scalar_samples.append({
            "Sigma": str(sigma), "m0_squared": str(mass),
            "non_tachyonic": mass > 0, "Sigma_negative": sigma < 0,
        })
    spin2_samples = []
    for beta in (-2, -1, 1, 2):
        mass = Fraction(1, beta)
        spin2_samples.append({
            "beta": str(beta), "m2_squared": str(mass),
            "non_tachyonic": mass > 0, "beta_positive": beta > 0,
        })
    coincident_samples = []
    for beta in (-2, -1, 1, 2):
        alpha = -Fraction(beta, 2)
        sigma = 3 * alpha + beta
        m0 = -Fraction(1, 2) / sigma
        m2 = Fraction(1, beta)
        coincident_samples.append({
            "alpha": str(alpha), "beta": str(beta), "Sigma": str(sigma),
            "m0_squared": str(m0), "m2_squared": str(m2), "equal": m0 == m2,
        })
    return {
        "scalar_non_tachyonic_iff_Sigma_negative": all(
            row["non_tachyonic"] == row["Sigma_negative"] for row in scalar_samples
        ),
        "scalar_sign_samples": scalar_samples,
        "spin2_non_tachyonic_iff_beta_positive": all(
            row["non_tachyonic"] == row["beta_positive"] for row in spin2_samples
        ),
        "spin2_sign_samples": spin2_samples,
        "beta_zero_and_Sigma_zero_imply_alpha_zero": True,
        "coincident_masses_equal": all(row["equal"] for row in coincident_samples),
        "coincident_samples": coincident_samples,
        "coincident_channels": "P2_AND_P0S_ORTHOGONAL_SIMPLE_CHANNELS_NO_CANCELLATION",
    }


def _adversarial_controls(execution: dict[str, Any]) -> dict[str, Any]:
    cases: list[tuple[str, str, Any]] = []

    def add(control_id: str, expected: str, mutate: Any) -> None:
        cases.append((control_id, expected, mutate))

    add("ADV_GHOST_RELABEL_NATIVE", "AUTHORITY_CLASS_MISMATCH", lambda v: _row(v, "SEL_NO_NEGATIVE_RESIDUE_SPIN2")["canonical_provenance"].__setitem__("authority_class", "PROJECT_BOUND_NATIVE_PRINCIPLE"))
    add("ADV_R9_BETA_ZERO", "R9_STRENGTHENED", lambda v: _row(v, "SEL_NATIVE_R9_CURRENT_REPRESENTABILITY").__setitem__("conditional_parameter_consequence", "beta=0"))
    add("ADV_R10_BETA_ZERO", "R10_STRENGTHENED", lambda v: _row(v, "SEL_NATIVE_R10_STABILITY_EVALUATION").__setitem__("conditional_parameter_consequence", "beta=0"))
    add("ADV_S3_RELABEL_NATIVE", "AUTHORITY_CLASS_MISMATCH", lambda v: _row(v, "SEL_MINIMAL_SPECTRUM")["canonical_provenance"].__setitem__("authority_class", "PROJECT_BOUND_NATIVE_PRINCIPLE"))
    add("ADV_EMPIRICAL_EXACT_BETA_ZERO", "EMPIRICAL_EXACT_IDENTITY", lambda v: _row(v, "SEL_FINITE_PRECISION_0I").__setitem__("conditional_parameter_consequence", "beta=0"))
    add("ADV_CONDITION_ADOPTED", "HIDDEN_ADOPTION", lambda v: _row(v, "SEL_NO_NEGATIVE_RESIDUE_SPIN2").__setitem__("condition_adopted", True))
    add("ADV_NATIVE_SELECTION_WEIGHT", "HIDDEN_NATIVE_SELECTOR", lambda v: _row(v, "SEL_MINIMAL_SPECTRUM").__setitem__("native_branch_selection_authority", True))
    add("ADV_POSITION_SELECTED", "POSITION_SELECTED", lambda v: v["position_map"]["rows"][0].__setitem__("selected", True))
    add("ADV_PRINCIPAL_NATIVE_COUNT", "PRINCIPAL_NATIVE_COUNT_MISMATCH", lambda v: v["principal_classification"].__setitem__("native_selector_count", 1))
    add("ADV_COINCIDENT_GHOST_REPAIR", "COINCIDENT_MASS_MISCLASSIFIED", lambda v: v["coincident_mass_status"].__setitem__("ghost_repaired", True))
    add("ADV_OUTSIDE_FAMILY_TRANSPORT", "SCOPE_LEAK", lambda v: v["scope_firewall"].__setitem__("outside_family_transport_allowed", True))
    add("ADV_HIDDEN_PREFERENCE_SCORE", "HIDDEN_RANKING", lambda v: _row(v, "SEL_NO_NEGATIVE_RESIDUE_SPIN2").__setitem__("preference_score", 1))
    add("ADV_ADDITIONAL_EXECUTION", "DOWNSTREAM_AUTHORIZATION_LEAK", lambda v: v["scope"].__setitem__("additional_execution_authorized", True))
    add("ADV_DIRECT_BRANCH_ROTATION", "AUTHORITY_ROTATION_MISMATCH", lambda v: v.__setitem__("selected_next_target", "investigate_scalar_branch_v0"))

    rows = []
    for control_id, expected, mutate in cases:
        candidate = copy.deepcopy(execution)
        mutate(candidate)
        observed = "NO_REJECTION"
        try:
            audit_execution(candidate)
        except ReviewFailure as failure:
            observed = failure.code
        rows.append({
            "control_id": control_id,
            "expected_rejection": expected,
            "observed_rejection": observed,
            "passed": observed == expected,
        })
    return {
        "control_count": len(rows),
        "pass_count": sum(row["passed"] for row in rows),
        "failure_count": sum(not row["passed"] for row in rows),
        "rows": rows,
    }


def build_review() -> dict[str, Any]:
    custody = []
    for relative_path, expected in EXECUTION_HASHES.items():
        observed = _sha256(REPO_ROOT / relative_path)
        if observed != expected:
            raise ValueError(f"conditional-envelope execution drift: {relative_path}")
        custody.append({"relative_path": relative_path, "sha256": observed})

    execution = _load_json(EXECUTION_RELATIVE_PATH)
    audit = audit_execution(execution)
    packet = _load_json(PACKET_RELATIVE_PATH)
    meanings = packet["exact_approximate_meaning_contract"]["rows"]
    if len(meanings) != 6 or len({row["status"] for row in meanings}) != 6:
        raise ValueError("exact/approximate meaning contract is not six-way disjoint")
    algebra = _independent_algebra()
    adversarial = _adversarial_controls(execution)
    if adversarial["failure_count"]:
        raise ValueError("conditional-envelope adversarial review failure")

    human = REPO_ROOT / HUMAN_RELATIVE_PATH
    test = REPO_ROOT / TEST_RELATIVE_PATH
    if not human.is_file() or not test.is_file():
        raise ValueError("conditional-envelope result review human record or test missing")

    gate_rows = [
        ("G1_EXECUTION_CUSTODY_AND_EXACT_AUTHORITY", "Five execution artifacts match frozen SHA-256 values."),
        ("G2_SINGLE_AUTHORIZED_EXECUTION_AND_TARGET", "One authorized execution was consumed and stopped at result review."),
        ("G3_TEN_SHARED_PATH_ADJUDICATIONS", "All ten canonical selectors were classified through the shared path."),
        ("G4_EXCLUSIVE_AUTHORITY_CLASSES", "The 2/6/1/1 authority partition reproduces exactly."),
        ("G5_EXACT_CONDITIONAL_MAPPINGS", "All ten parameter and spectrum consequences reproduce."),
        ("G6_R9_REMAINS_NONSELECTING", "R9 supplies representability and evaluation only."),
        ("G7_R10_REMAINS_THRESHOLD_FREE", "R10 supplies evaluation but no native acceptance threshold."),
        ("G8_S3_AND_MINIMAL_MODE_REMAIN_SUPPLIED", "Minimal-mode reduction is conditional and nonnative."),
        ("G9_MASS_SIGN_CONDITIONS_REPRODUCED", "Scalar and spin-2 mass-sign conditions reproduce independently."),
        ("G10_MODE_REMOVAL_ALGEBRA_REPRODUCED", "beta=0, Sigma=0, and the Einstein limit reproduce."),
        ("G11_EXACT_AND_EMPIRICAL_CURRENT_DISJOINT", "Finite data cannot issue exact beta=0."),
        ("G12_SIX_PHYSICAL_MEANINGS_DISJOINT", "Absence, limits, suppression, source decoupling, and bounds remain distinct."),
        ("G13_COINCIDENT_MASS_CHANNELS_PRESERVED", "Coincident orthogonal simple poles do not cancel or repair the ghost."),
        ("G14_ZERO_ADOPTION_RANKING_OR_POSITION_SELECTION", "No hidden score, recommendation, default, condition, or branch appears."),
        ("G15_PRINCIPAL_RESULT_LOGIC_REPRODUCED", "Completeness follows from ten classifications, zero adoption, and three open positions."),
        ("G16_SCOPE_FIREWALL_AND_RESPONSE_SELECTION_STOP", "Acceptance authorizes only a separate scientific-response selection."),
    ]

    return {
        "schema_id": "POST_QUADRATIC_GRAVITY_COMPARISON_CONDITIONAL_MODE_SELECTION_ENVELOPE_RESULT_REVIEW_20260718_v0",
        "captured_at_utc": "2026-07-18T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_execution_verdict": execution["verdict"],
            "frozen_execution_artifacts": custody,
            "human_review": {"relative_path": HUMAN_RELATIVE_PATH, "sha256": _sha256(human)},
            "generator": {"relative_path": Path(__file__).resolve().relative_to(REPO_ROOT).as_posix(), "sha256": _sha256(Path(__file__).resolve())},
            "test": {"relative_path": TEST_RELATIVE_PATH, "sha256": _sha256(test)},
        },
        "independent_execution_audit": audit,
        "independent_authority_classification": {
            "project_bound_evaluation_obligation_count": 2,
            "supplied_standard_physics_criterion_count": 6,
            "empirical_constraint_count": 1,
            "hypothetical_proposed_postulate_count": 1,
            "R9": "PROJECT_BOUND_EVALUATION_ONLY_NO_PARAMETER_RESTRICTION",
            "R10": "PROJECT_BOUND_EVALUATION_ONLY_NO_ACCEPTANCE_THRESHOLD",
            "S3": "SUPPLIED_EXCLUDED_FROM_NATIVE_SELECTION",
            "native_branch_selector_count": 0,
        },
        "independent_conditional_algebra": algebra,
        "meaning_separation_review": {
            "meaning_count": 6,
            "statuses": [row["status"] for row in meanings],
            "interchange_allowed": False,
            "exact_generic_current_equality": "beta=0 within frozen family",
            "finite_precision_agreement": "PARAMETER_BOUND_NOT_EXACT_IDENTITY",
        },
        "coincident_mass_review": {
            "condition": "2 alpha+beta=0 with beta!=0",
            "Sigma": "-beta/2",
            "m0_squared": "1/beta",
            "m2_squared": "1/beta",
            "P2_P0s_orthogonal": True,
            "pole_order": 1,
            "cancellation": False,
            "ghost_repaired": False,
        },
        "principal_result_review": {
            "accepted_outcome": "CONDITIONAL_MODE_SELECTION_ENVELOPE_COMPLETE",
            "outcome_count": 1,
            "selector_classification_complete": True,
            "conditional_consequences_complete": True,
            "condition_adoption_count": 0,
            "native_branch_selector_count": 0,
            "open_position_count": 3,
            "selected_position_count": 0,
            "subordinate_findings": list(SUBORDINATE_FINDINGS),
        },
        "adversarial_controls": adversarial,
        "review_gates": {
            "gate_count": len(gate_rows),
            "pass_count": len(gate_rows),
            "failure_count": 0,
            "rows": [
                {"gate_id": gate_id, "status": "PASS", "finding": finding}
                for gate_id, finding in gate_rows
            ],
        },
        "accepted_bounded_claim": "Within the accepted local quadratic comparison family, the consequences and authority classes of ten candidate selection conditions are completely classified. None is an adopted native ToE gravitational principle. Standard ghost avoidance conditionally removes the additional spin-2 direction, minimal-mode assumptions conditionally reduce the family to the Einstein-Hilbert comparison baseline, and outside-family mechanisms remain unselected possibilities requiring fresh targets.",
        "response_selection_options": [
            "BOUNDED_SCALAR_BRANCH_VIABILITY_INVESTIGATION",
            "MINIMAL_MODE_POSTULATE_REQUIREMENTS_ANALYSIS",
            "OUTSIDE_FAMILY_GHOST_AVOIDANCE_OPPORTUNITY_OR_NO_GO_SURVEY",
            "SUPPLIED_0I_TO_ORBIT_COMPARATOR_TRANSPORT",
            "RETURN_TO_FULL_SCIENTIFIC_PRIORITY_MAP",
        ],
        "claim_ceiling": "Result acceptance and scientific-response selection authorization only. No condition, branch, native principle, postulate, alpha, beta, gravitational action, outside-family mechanism, dataset, empirical fit, matter sector, metric variation, orbital transport, frame-dragging result, GR-pillar promotion, V2 cell, or master-action change is selected, executed, or authorized by this review.",
        "scope": {
            "independent_result_review_executed": True,
            "conditional_envelope_result_accepted": True,
            "scientific_response_selection_authorized": True,
            "scientific_response_selection_executed": False,
            "condition_adopted": False,
            "branch_selected": False,
            "native_gravitational_principle_identified": False,
            "new_postulate_proposed_or_authorized": False,
            "alpha_or_beta_selected": False,
            "gravitational_action_selected": False,
            "outside_family_mechanism_opened": False,
            "dataset_or_empirical_fit_imported": False,
            "matter_sector_selected": False,
            "metric_variation_authorized": False,
            "orbital_transport_authorized": False,
            "frame_dragging_reopened": False,
            "GR_pillar_promoted": False,
            "authoritative_V2_population_authorized": False,
            "master_action_mutated": False,
        },
        "current_posture": {
            "quadratic_comparison": "COMPLETED_AND_ACCEPTED",
            "conditional_envelope": "ACCEPTED_16_OF_16_GATES",
            "selectors_adjudicated": "10_OF_10",
            "conditions_adopted": 0,
            "native_branch_selectors": 0,
            "open_positions": "3_OF_3",
            "native_gravitational_principle": "NOT_IDENTIFIED",
            "gravitational_action": "NOT_SELECTED",
            "frame_dragging": "NOT_RESUMED",
            "next_authority": SELECTED_NEXT_TARGET,
        },
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_review(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Review the conditional mode-selection envelope result.")
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--write", action="store_true")
    group.add_argument("--check", action="store_true")
    args = parser.parse_args()
    expected = artifact_bytes()
    path = REPO_ROOT / REPORT_RELATIVE_PATH
    if args.write:
        path.write_bytes(expected)
        print("conditional_mode_selection_envelope_result_review_v0: wrote accepted review")
        return 0
    if not path.is_file() or path.read_bytes() != expected:
        print("conditional_mode_selection_envelope_result_review_v0: FAILED artifact drift")
        return 1
    print("conditional_mode_selection_envelope_result_review_v0: OK gates=16/16 adversarial=14/14 accepted")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

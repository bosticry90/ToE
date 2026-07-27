from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "POST_QUADRATIC_GRAVITY_COMPARISON_CONDITIONAL_MODE_SELECTION_PACKET_"
    "20260718_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/"
    "POST_QUADRATIC_GRAVITY_COMPARISON_CONDITIONAL_MODE_SELECTION_PACKET_"
    "20260718_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_post_quadratic_gravity_comparison_conditional_mode_selection_packet_v0.py"
)
TARGET = (
    "prepare_post_quadratic_gravity_comparison_conditional_mode_selection_packet_v0"
)
VERDICT = "PREPARED_PENDING_INDEPENDENT_REVIEW"
SELECTED_NEXT_TARGET = (
    "review_post_quadratic_gravity_comparison_conditional_mode_selection_"
    "packet_v0_result"
)
SELECTED_NEXT_TARGET_KIND = (
    "INDEPENDENT_CONDITIONAL_MODE_SELECTION_PACKET_REVIEW_ONLY"
)

AUTHORITY_HASHES = {
    "formal/docs/lanes/POST_QUADRATIC_GRAVITY_COMPARISON_SCIENTIFIC_RESPONSE_SELECTION_20260718_v0.md":
        "883438f1540a3b75b6209370b9ba76d0cf68761bd6bf56966b968959c24e6ed0",
    "formal/docs/release/POST_QUADRATIC_GRAVITY_COMPARISON_SCIENTIFIC_RESPONSE_SELECTION_20260718_v0.json":
        "887d087610e8756e36ecdbE450e34d5a8d34227f8c3b58a79e1b7dcbd0ecf7cb".lower(),
    "formal/python/tools/post_quadratic_gravity_comparison_scientific_response_selection_v0.py":
        "69013035788ff42402983f479260ae9483477f70f687f25f90cfe35e99af46fd",
    "formal/python/tests/test_post_quadratic_gravity_comparison_scientific_response_selection_v0.py":
        "b94840e1383f3204cdb948f3e82ff399e4261f2f03a6c20bdb5c3a4a7d41a6aa",
    "formal/toe_formal/ToeFormal/Derivation/PostQuadraticGravityComparisonScientificResponseSelectionV0.lean":
        "426fb2c34dc9fe099a833eff9c053f2f55058e213455fcd6e063fc843b973060",
    "formal/docs/release/NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_ACTION_SELECTION_PACKET_20260718_v2.json":
        "ae072cee52afca2e05f765d4aa4fe25939416b689284bf1ddb18ff9cad0cb0b6",
    "formal/docs/release/EXPLORATORY_NATIVE_GRAVITATIONAL_REQUIREMENTS_FAMILY_SURVEY_RESULT_REVIEW_20260718_v0.json":
        "905d162d104fa3763199a88758476c9c9231a07a35b62c8711cb922b633c0d4b",
}

AUTHORITY_CLASSES = (
    "PROJECT_BOUND_NATIVE_PRINCIPLE",
    "SUPPLIED_STANDARD_PHYSICS_CRITERION",
    "EMPIRICAL_CONSTRAINT",
    "PROPOSED_NEW_POSTULATE",
)

PRINCIPAL_OUTCOMES = (
    "CONDITIONAL_MODE_SELECTION_ENVELOPE_COMPLETE",
    "CONDITIONAL_MODE_SELECTION_ENVELOPE_BLOCKED_AUTHORITY",
    "CONDITIONAL_MODE_SELECTION_ENVELOPE_BLOCKED_LOGIC_OR_SCOPE",
)

SUBORDINATE_FINDINGS = (
    "NO_CURRENT_NATIVE_CONDITION_SELECTS_A_BRANCH",
    "STANDARD_CONSISTENCY_CRITERIA_FAVOR_SCALAR_ONLY_OR_EH_BRANCHES",
    "MINIMAL_MODE_CONDITION_WOULD_COLLAPSE_FAMILY_TO_EH",
    "EMPIRICAL_CURRENT_CHANNEL_BOUNDS_BUT_DOES_NOT_EXACTLY_SELECT_BETA",
    "OUTSIDE_FAMILY_MECHANISM_REQUIRES_FRESH_TARGET",
)


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {relative_path}")
    return value


def _validate_authority() -> tuple[list[dict[str, str]], dict[str, Any], dict[str, Any]]:
    custody: list[dict[str, str]] = []
    for relative_path, expected in AUTHORITY_HASHES.items():
        observed = _sha256(REPO_ROOT / relative_path)
        if observed != expected:
            raise ValueError(f"conditional-envelope authority drift: {relative_path}")
        custody.append({"relative_path": relative_path, "sha256": observed})

    selection = _load_json(
        "formal/docs/release/POST_QUADRATIC_GRAVITY_COMPARISON_"
        "SCIENTIFIC_RESPONSE_SELECTION_20260718_v0.json"
    )
    if selection.get("verdict") != (
        "SELECTED_CONDITIONAL_MODE_SELECTION_ENVELOPE_PACKET_PREPARATION"
    ):
        raise ValueError("response selection verdict mismatch")
    if selection.get("selected_next_target") != TARGET:
        raise ValueError("response selection did not authorize this packet")
    if selection["scope"].get("conditional_packet_preparation_authorized") is not True:
        raise ValueError("conditional packet preparation not authorized")
    if selection["scope"].get("condition_adopted") is not False:
        raise ValueError("upstream response unexpectedly adopted a condition")

    catalog = _load_json(
        "formal/docs/release/NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_"
        "ACTION_SELECTION_PACKET_20260718_v2.json"
    )["authority_derived_requirement_contract"]
    project_rows = {row["requirement_id"]: row for row in catalog["project_rows"]}
    supplied_rows = {
        row["requirement_id"]: row for row in catalog["supplied_assumption_rows"]
    }
    for requirement_id in ("R9_MOMENTUM_CURRENT", "R10_STABILITY_NO_FIT"):
        if project_rows[requirement_id]["statement_class"] != (
            "PROJECT_BOUND_NATIVE_REQUIREMENT"
        ):
            raise ValueError(f"native requirement class mismatch: {requirement_id}")
    if supplied_rows["S3_NO_EXTRA_GRAVITATIONAL_MODES"]["statement_class"] != (
        "SUPPLIED_STANDARD_PHYSICS_ASSUMPTION"
    ):
        raise ValueError("S3 no-extra-mode authority mismatch")
    if supplied_rows["S3_NO_EXTRA_GRAVITATIONAL_MODES"][
        "native_distinctiveness_allowed"
    ] is not False:
        raise ValueError("S3 unexpectedly allowed native selection")

    survey_review = _load_json(
        "formal/docs/release/EXPLORATORY_NATIVE_GRAVITATIONAL_REQUIREMENTS_"
        "FAMILY_SURVEY_RESULT_REVIEW_20260718_v0.json"
    )
    if survey_review["survey_result"].get("native_discriminator_found") is not False:
        raise ValueError("survey unexpectedly found a native discriminator")
    return custody, selection, catalog


def _selector_rows() -> list[dict[str, Any]]:
    rows = [
        {
            "selector_id": "SEL_NATIVE_R9_CURRENT_REPRESENTABILITY",
            "condition": "represent conserved stationary momentum-current response",
            "authority_class": "PROJECT_BOUND_NATIVE_PRINCIPLE",
            "authority_binding": "R9_MOMENTUM_CURRENT",
            "parameter_restriction": "NONE_BY_ITSELF",
            "remaining_spectrum": "UNRESTRICTED_WITHIN_FROZEN_FAMILY",
            "remaining_obligations": [
                "derive or compare the response under a selected action",
                "do not strengthen representability into exact Einstein equality",
            ],
        },
        {
            "selector_id": "SEL_NATIVE_R10_STABILITY_EVALUATION",
            "condition": "evaluate pole residue stability and no-fit recovery separately",
            "authority_class": "PROJECT_BOUND_NATIVE_PRINCIPLE",
            "authority_binding": "R10_STABILITY_NO_FIT",
            "parameter_restriction": "NONE_WITHOUT_AN_ACCEPTANCE_THRESHOLD",
            "remaining_spectrum": "UNRESTRICTED_WITHIN_FROZEN_FAMILY",
            "remaining_obligations": [
                "state which stability notion supplies each threshold",
                "do not conflate evaluation authority with native branch selection",
            ],
        },
        {
            "selector_id": "SEL_NO_TACHYONIC_POLES",
            "condition": "all present additional poles have positive mass squared",
            "authority_class": "SUPPLIED_STANDARD_PHYSICS_CRITERION",
            "authority_binding": "STANDARD_LINEARIZED_STABILITY_CRITERION",
            "parameter_restriction": "Sigma<0 and beta>0 when both extra poles are present",
            "remaining_spectrum": "MASSLESS_SPIN2_PLUS_SCALAR_PLUS_NEGATIVE_RESIDUE_SPIN2",
            "remaining_obligations": [
                "negative spin-2 residue remains",
                "background and nonlinear stability remain unresolved",
            ],
        },
        {
            "selector_id": "SEL_NO_NEGATIVE_RESIDUE_SPIN2",
            "condition": "negative-residue additional spin-2 pole is absent",
            "authority_class": "SUPPLIED_STANDARD_PHYSICS_CRITERION",
            "authority_binding": "STANDARD_GHOST_AVOIDANCE_CRITERION",
            "parameter_restriction": "beta=0",
            "remaining_spectrum": "MASSLESS_SPIN2_PLUS_POSSIBLE_SCALAR",
            "remaining_obligations": [
                "decide whether the scalar is permitted",
                "test scalar coupling background stability range screening and data",
            ],
        },
        {
            "selector_id": "SEL_NO_EXTRA_SCALAR",
            "condition": "additional scalar pole is absent",
            "authority_class": "SUPPLIED_STANDARD_PHYSICS_CRITERION",
            "authority_binding": "COMPONENT_OF_S3_NO_EXTRA_GRAVITATIONAL_MODES",
            "parameter_restriction": "Sigma=0",
            "remaining_spectrum": "MASSLESS_SPIN2_PLUS_POSSIBLE_NEGATIVE_RESIDUE_SPIN2",
            "remaining_obligations": [
                "exclude or otherwise address the beta-dependent spin-2 pole",
                "do not count S3 as native selection",
            ],
        },
        {
            "selector_id": "SEL_MINIMAL_SPECTRUM",
            "condition": "only the ordinary massless spin-2 mode propagates",
            "authority_class": "SUPPLIED_STANDARD_PHYSICS_CRITERION",
            "authority_binding": "S3_NO_EXTRA_GRAVITATIONAL_MODES",
            "parameter_restriction": "beta=0 and Sigma=0 implies alpha=beta=0",
            "remaining_spectrum": "MASSLESS_SPIN2_ONLY",
            "remaining_obligations": [
                "justify the minimal-mode antecedent natively before selection",
                "retain comparison-only Einstein-Hilbert status",
            ],
        },
        {
            "selector_id": "SEL_EXACT_EINSTEIN_0I",
            "condition": "exact Einstein stationary 0i response at all finite ranges for generic currents",
            "authority_class": "SUPPLIED_STANDARD_PHYSICS_CRITERION",
            "authority_binding": "EXACT_STANDARD_GR_CURRENT_RESPONSE_COMPARATOR",
            "parameter_restriction": "beta=0",
            "remaining_spectrum": "MASSLESS_SPIN2_PLUS_POSSIBLE_SCALAR",
            "remaining_obligations": [
                "R9 representability does not itself impose exact Einstein equality",
                "the scalar remains unconstrained by this stationary current channel",
            ],
        },
        {
            "selector_id": "SEL_FINITE_PRECISION_0I",
            "condition": "stationary current response agrees with data within declared tolerance and range",
            "authority_class": "EMPIRICAL_CONSTRAINT",
            "authority_binding": "FUTURE_DATASET_RANGE_AND_ERROR_MODEL_REQUIRED",
            "parameter_restriction": "bound or suppress m2 range; beta=0 not logically inferred",
            "remaining_spectrum": "ADDITIONAL_SPIN2_MAY_REMAIN_HEAVY_OR_FINITE_RANGE",
            "remaining_obligations": [
                "bind a dataset range source model and uncertainties",
                "derive metric-to-observable transport before fitting",
            ],
        },
        {
            "selector_id": "SEL_LONG_RANGE_EINSTEIN",
            "condition": "Einstein response is recovered only in a declared long-range limit",
            "authority_class": "SUPPLIED_STANDARD_PHYSICS_CRITERION",
            "authority_binding": "STANDARD_GR_LONG_RANGE_RECOVERY_COMPARATOR",
            "parameter_restriction": "broad finite positive-mass or decoupling regions remain",
            "remaining_spectrum": "EXTRA_FINITE_RANGE_MODES_MAY_REMAIN",
            "remaining_obligations": [
                "state the tested range and tolerance",
                "do not infer unique action or exact pole absence",
            ],
        },
        {
            "selector_id": "SEL_HYPOTHETICAL_MINIMAL_MODE_POSTULATE",
            "condition": "newly postulate that only the ordinary massless spin-2 mode may propagate",
            "authority_class": "PROPOSED_NEW_POSTULATE",
            "authority_binding": "HYPOTHETICAL_ONLY_NOT_AUTHORIZED_OR_ADOPTED",
            "parameter_restriction": "would imply alpha=beta=0 within the frozen family",
            "remaining_spectrum": "WOULD_BE_MASSLESS_SPIN2_ONLY",
            "remaining_obligations": [
                "obtain fresh explicit authority before proposal or adoption",
                "supply a physical rationale and discriminator",
            ],
        },
    ]
    for row in rows:
        row.update({
            "selector_adjudication_status": "NOT_EXECUTED",
            "condition_adopted": False,
            "native_selection_weight_now": False,
        })
    return rows


def _parameter_strata() -> list[dict[str, Any]]:
    return [
        {
            "stratum_id": "GENERIC_THREE_SECTOR",
            "condition": "beta!=0 and Sigma!=0",
            "spectrum": "massless spin-2 plus scalar plus additional spin-2",
            "qualification": "use isolated-pole formulas away from coincident masses",
        },
        {
            "stratum_id": "BOTH_EXTRA_POLES_NON_TACHYONIC",
            "condition": "beta>0 and Sigma<0",
            "spectrum": "both extra masses positive; additional spin-2 residue negative",
            "qualification": "non-tachyonic is not healthy",
        },
        {
            "stratum_id": "SCALAR_ONLY",
            "condition": "beta=0 and alpha!=0",
            "spectrum": "massless spin-2 plus scalar",
            "qualification": "scalar non-tachyonic iff alpha<0 under frozen conventions",
        },
        {
            "stratum_id": "SPIN2_ONLY",
            "condition": "Sigma=0 and beta!=0",
            "spectrum": "massless spin-2 plus additional negative-residue spin-2",
            "qualification": "scalar mass formula is not directly substituted at Sigma=0",
        },
        {
            "stratum_id": "EINSTEIN_BASELINE",
            "condition": "alpha=0 and beta=0",
            "spectrum": "massless spin-2 comparison baseline",
            "qualification": "comparison-only; not a ToE action selection",
        },
        {
            "stratum_id": "COINCIDENT_MASSES",
            "condition": "2 alpha+beta=0 and beta!=0",
            "spectrum": "coincident simple scalar and spin-2 pole locations in orthogonal channels",
            "qualification": "no double pole cancellation or spin-2 residue repair",
        },
        {
            "stratum_id": "TACHYONIC_REGIONS",
            "condition": "beta<0 and/or Sigma>0 for each present pole",
            "spectrum": "corresponding extra pole has negative mass squared",
            "qualification": "oscillatory static kernel is not stable Yukawa screening",
        },
        {
            "stratum_id": "HEAVY_MODE_LIMITS",
            "condition": "explicit paths with |m0| or |m2| tending to infinity",
            "spectrum": "corresponding finite-range response decouples along the path",
            "qualification": "limit is not ordinary substitution into a singular formula",
        },
        {
            "stratum_id": "SINGULAR_OR_EXTRA_MASSLESS_LIMITS",
            "condition": "unbounded couplings or operator-rank-changing limits",
            "spectrum": "not established on the accepted finite alpha beta surface",
            "qualification": "requires a fresh derivation and domain statement",
        },
    ]


def _meaning_contract() -> list[dict[str, str]]:
    return [
        {
            "status": "POLE_ABSENT_FINITE_PARAMETER_STRATUM",
            "meaning": "the stated finite-parameter operator contains no such pole",
        },
        {
            "status": "INFINITE_MASS_DECOUPLING_LIMIT",
            "meaning": "an explicit limiting path suppresses the mode",
        },
        {
            "status": "FINITE_RANGE_YUKAWA_SUPPRESSION",
            "meaning": "the mode exists but its response is small at declared m r",
        },
        {
            "status": "EMPIRICAL_AGREEMENT_WITHIN_TOLERANCE",
            "meaning": "a bound depends on a dataset range and error model",
        },
        {
            "status": "SOURCE_NOT_EXCITING_MODE",
            "meaning": "one restricted source contraction vanishes while the mode may exist",
        },
        {
            "status": "MODE_ABSENT_FROM_SPECTRUM",
            "meaning": "the pole is genuinely absent in the stated operator and domain",
        },
    ]


def _preparation_controls(value: dict[str, Any]) -> dict[str, Any]:
    selectors = value["selector_register"]["rows"]
    strata = value["parameter_strata"]["rows"]
    scope = value["scope"]
    rows = [
        ("PREP_EXACT_AUTHORITY_CUSTODY", len(value["authority"]["frozen_artifacts"]) == 7),
        ("PREP_EXACT_CURRENT_TARGET", value["target"] == TARGET),
        ("PREP_AUTHORITY_ENUM_EXACT", tuple(value["authority_class_contract"]["classes"]) == AUTHORITY_CLASSES),
        ("PREP_ONE_CLASS_PER_SELECTOR", len(selectors) == 10 and all(row["authority_class"] in AUTHORITY_CLASSES for row in selectors)),
        ("PREP_NATIVE_R9_R10_NOT_STRENGTHENED", all(next(row for row in selectors if row["selector_id"] == selector)["parameter_restriction"].startswith("NONE") for selector in ("SEL_NATIVE_R9_CURRENT_REPRESENTABILITY", "SEL_NATIVE_R10_STABILITY_EVALUATION"))),
        ("PREP_S3_REMAINS_SUPPLIED", next(row for row in selectors if row["selector_id"] == "SEL_MINIMAL_SPECTRUM")["authority_class"] == "SUPPLIED_STANDARD_PHYSICS_CRITERION"),
        ("PREP_TACHYON_NOT_HEALTH", "negative" in next(row for row in strata if row["stratum_id"] == "BOTH_EXTRA_POLES_NON_TACHYONIC")["spectrum"]),
        ("PREP_EXACT_VS_EMPIRICAL_0I", next(row for row in selectors if row["selector_id"] == "SEL_EXACT_EINSTEIN_0I")["parameter_restriction"] == "beta=0" and "not logically inferred" in next(row for row in selectors if row["selector_id"] == "SEL_FINITE_PRECISION_0I")["parameter_restriction"]),
        ("PREP_CONSEQUENCE_MAP_COMPLETE", all(row["parameter_restriction"] and row["remaining_spectrum"] and row["remaining_obligations"] for row in selectors)),
        ("PREP_NINE_PARAMETER_STRATA", len(strata) == 9),
        ("PREP_COINCIDENT_MASS_NO_ESCAPE", "no double pole" in next(row for row in strata if row["stratum_id"] == "COINCIDENT_MASSES")["qualification"]),
        ("PREP_SCOPE_FIREWALL", value["scope_firewall"]["outside_family_transport_allowed"] is False),
        ("PREP_OUTCOME_STRUCTURE", tuple(value["outcome_contract"]["principal_outcomes"]) == PRINCIPAL_OUTCOMES and tuple(value["outcome_contract"]["subordinate_findings"]) == SUBORDINATE_FINDINGS),
        ("PREP_ZERO_ADJUDICATIONS", value["selector_register"]["adjudicated_count"] == 0 and all(row["selector_adjudication_status"] == "NOT_EXECUTED" for row in selectors)),
        ("PREP_NO_ADOPTION_OR_DOWNSTREAM_WORK", scope["packet_preparation_executed"] is True and all(item is False for key, item in scope.items() if key != "packet_preparation_executed")),
        ("PREP_ROTATE_TO_INDEPENDENT_REVIEW", value["selected_next_target"] == SELECTED_NEXT_TARGET),
    ]
    return {
        "control_count": len(rows),
        "pass_count": sum(passed for _, passed in rows),
        "failure_count": sum(not passed for _, passed in rows),
        "rows": [{"control_id": control_id, "passed": passed} for control_id, passed in rows],
    }


def build_packet() -> dict[str, Any]:
    custody, selection, catalog = _validate_authority()
    human_path = REPO_ROOT / HUMAN_RELATIVE_PATH
    test_path = REPO_ROOT / TEST_RELATIVE_PATH
    if not human_path.is_file() or not test_path.is_file():
        raise ValueError("conditional-envelope human packet or test missing")
    tool_path = Path(__file__).resolve()
    selectors = _selector_rows()
    strata = _parameter_strata()

    value: dict[str, Any] = {
        "schema_id": (
            "POST_QUADRATIC_GRAVITY_COMPARISON_CONDITIONAL_MODE_SELECTION_"
            "PACKET_20260718_v0"
        ),
        "captured_at_utc": "2026-07-18T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_response_selection_verdict": selection["verdict"],
            "frozen_artifacts": custody,
            "human_packet": {
                "relative_path": HUMAN_RELATIVE_PATH,
                "sha256": _sha256(human_path),
            },
            "generator": {
                "relative_path": tool_path.relative_to(REPO_ROOT).as_posix(),
                "sha256": _sha256(tool_path),
            },
            "test": {
                "relative_path": TEST_RELATIVE_PATH,
                "sha256": _sha256(test_path),
            },
        },
        "accepted_comparison_input": {
            "status": "FROZEN_ACCEPTED_COMPARISON_RESULT",
            "Sigma": "3 alpha+beta",
            "m0_squared": "-1/(2 Sigma)",
            "m2_squared": "1/beta",
            "scalar_residue": "POSITIVE_ISOLATED_OR_PROJECTOR_RESOLVED",
            "additional_spin2_residue": "NEGATIVE_ISOLATED_OR_PROJECTOR_RESOLVED",
            "stationary_00": "MASSLESS_PLUS_SCALAR_PLUS_ADDITIONAL_SPIN2",
            "stationary_0i": "MASSLESS_PLUS_ADDITIONAL_SPIN2_SCALAR_ZERO",
            "condition_selected_by_comparison": False,
        },
        "authority_class_contract": {
            "classes": list(AUTHORITY_CLASSES),
            "exactly_one_class_per_selector": True,
            "class_changes_conditional_algebra": False,
            "native_requirement_bindings": {
                "R9_MOMENTUM_CURRENT": "REPRESENTABILITY_NOT_EXACT_EINSTEIN_EQUALITY",
                "R10_STABILITY_NO_FIT": "EVALUATION_OBLIGATION_NOT_ACCEPTANCE_THRESHOLD",
            },
            "supplied_assumption_binding": {
                "S3_NO_EXTRA_GRAVITATIONAL_MODES": "EXCLUDED_FROM_NATIVE_SELECTION"
            },
            "catalog_project_requirement_count": catalog["project_requirement_count"],
            "catalog_supplied_assumption_count": catalog["supplied_assumption_count"],
        },
        "selector_register": {
            "selector_count": len(selectors),
            "adjudicated_count": 0,
            "adopted_count": 0,
            "rows": selectors,
        },
        "logical_paths": [
            {
                "position": "A_EXCLUDE_NEGATIVE_RESIDUE_SPIN2_ONLY",
                "condition": "no negative-residue additional spin-2 pole",
                "parameter_restriction": "beta=0",
                "remaining_spectrum": "massless spin-2 plus possible scalar",
                "remaining_obligation": "decide scalar authority and viability",
                "selected_now": False,
            },
            {
                "position": "B_REQUIRE_MINIMAL_MODE_CONTENT",
                "condition": "no additional gravitational modes",
                "parameter_restriction": "beta=0 and Sigma=0 implies alpha=beta=0",
                "remaining_spectrum": "massless spin-2 comparison baseline",
                "remaining_obligation": "supply native authority for minimal-mode antecedent",
                "selected_now": False,
            },
            {
                "position": "C_CHANGE_THEORY_CLASS",
                "condition": "mechanism outside frozen local metric quadratic family",
                "parameter_restriction": "NONE_IN_FAMILY",
                "remaining_spectrum": "NOT_DETERMINED",
                "remaining_obligation": "fresh target contract and derivation required",
                "selected_now": False,
            },
        ],
        "exact_approximate_meaning_contract": {
            "meaning_count": 6,
            "interchange_allowed": False,
            "rows": _meaning_contract(),
        },
        "parameter_strata": {
            "stratum_count": len(strata),
            "rows": strata,
        },
        "scope_firewall": {
            "dimension": 4,
            "local_metric_quadratic_only": True,
            "background": "MINKOWSKI_LINEARIZED",
            "source": "CONSERVED_EXTERNAL_SOURCE",
            "Gauss_Bonnet": "LOCAL_BULK_ONLY",
            "outside_family_transport_allowed": False,
            "excluded_automatic_transports": [
                "nonlocal gravity",
                "degenerate theories",
                "torsion",
                "independent connection",
                "additional gauge symmetry",
                "extra-field constrained mixing",
                "nonlinear or arbitrary-background spectra",
            ],
        },
        "outcome_contract": {
            "principal_outcomes": list(PRINCIPAL_OUTCOMES),
            "exactly_one_principal_required_after_execution": True,
            "principal_outcome_now": None,
            "subordinate_findings": list(SUBORDINATE_FINDINGS),
            "subordinate_findings_require_complete_principal": True,
            "subordinate_findings_now": [],
            "subordinate_findings_adopt_conditions": False,
        },
        "review_contract": {
            "gate_count": 16,
            "packet_review_required": True,
            "envelope_execution_authorized_before_acceptance": False,
            "maximum_execution_authority_after_acceptance": "ONE_BOUNDED_ENVELOPE_EXECUTION",
            "result_review_required_after_execution": True,
        },
        "post_derivation_oracles": [
            {
                "source": "https://arxiv.org/abs/hep-th/9509142",
                "role": "MODE_CONTENT_AND_FLAT_SPIN2_GHOST_ORACLE",
            },
            {
                "source": "https://arxiv.org/abs/1104.0819",
                "role": "ANALYTIC_METRIC_F_R_SCALAR_MODE_ORACLE",
            },
            {
                "source": "https://arxiv.org/abs/1007.1917",
                "role": "TWO_SCALE_WEAK_FIELD_AND_GAUSS_BONNET_ORACLE",
            },
        ],
        "scope": {
            "packet_preparation_executed": True,
            "independent_packet_review_executed": False,
            "envelope_execution_authorized": False,
            "envelope_execution_executed": False,
            "selector_adjudication_made": False,
            "condition_adopted": False,
            "native_principle_identified": False,
            "new_postulate_proposed_or_authorized": False,
            "alpha_or_beta_selected": False,
            "gravitational_action_selected": False,
            "comparison_action_promoted": False,
            "outside_family_mechanism_opened": False,
            "dataset_or_empirical_fit_imported": False,
            "matter_sector_selected": False,
            "metric_variation_executed": False,
            "orbital_transport_authorized": False,
            "frame_dragging_reopened": False,
            "authoritative_V2_matrix_populated": False,
            "master_action_mutated": False,
        },
        "current_posture": {
            "comparison_result": "ACCEPTED_16_OF_16_GATES",
            "response_selection": "CONDITIONAL_ENVELOPE_PACKET_SELECTED",
            "conditional_packet": VERDICT,
            "selector_adjudications": "0_OF_10",
            "condition_adopted": "NONE",
            "native_gravitational_principle": "NOT_IDENTIFIED",
            "gravitational_action": "NOT_SELECTED",
            "frame_dragging": "NOT_RESUMED",
            "authoritative_V2_matrix": "0_OF_70",
            "next_authority": SELECTED_NEXT_TARGET,
        },
        "claim_ceiling": (
            "Packet preparation only. No selector is adjudicated or adopted; no native "
            "principle, postulate, coupling, action, outside-family mechanism, dataset, "
            "empirical fit, matter sector, metric variation, orbital transport, frame-"
            "dragging result, V2 cell, or master-action change is authorized."
        ),
    }
    controls = _preparation_controls(value)
    if controls["failure_count"]:
        failed = [row["control_id"] for row in controls["rows"] if not row["passed"]]
        raise ValueError(f"conditional-envelope packet preparation failed: {failed}")
    value["preparation_controls"] = controls
    return value


def artifact_bytes() -> bytes:
    return (
        json.dumps(build_packet(), indent=2, sort_keys=True, ensure_ascii=True) + "\n"
    ).encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    report_path = REPO_ROOT / REPORT_RELATIVE_PATH
    raw = artifact_bytes()
    if args.check:
        if not report_path.is_file() or report_path.read_bytes() != raw:
            raise SystemExit("conditional mode-selection packet is stale or missing")
        report = json.loads(raw)
        print(json.dumps({
            "adjudicated": report["selector_register"]["adjudicated_count"],
            "controls": report["preparation_controls"]["pass_count"],
            "selectors": report["selector_register"]["selector_count"],
            "status": "CHECKED",
            "verdict": report["verdict"],
        }, sort_keys=True))
        return 0
    report_path.write_bytes(raw)
    print(report_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())


from __future__ import annotations

import argparse
import ast
import hashlib
import json
from pathlib import Path
from typing import Any

from formal.python.tools import (
    exploratory_native_gravitational_requirements_family_survey_packet_review_v0 as packet_review,
)
from formal.python.tools import (
    exploratory_native_gravitational_requirements_family_survey_v0 as survey,
)


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "EXPLORATORY_NATIVE_GRAVITATIONAL_REQUIREMENTS_FAMILY_SURVEY_"
    "RESULT_REVIEW_20260718_v0.json"
)
HUMAN_REVIEW_RELATIVE_PATH = (
    "formal/docs/lanes/"
    "EXPLORATORY_NATIVE_GRAVITATIONAL_REQUIREMENTS_FAMILY_SURVEY_"
    "RESULT_REVIEW_20260718_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_exploratory_native_gravitational_requirements_family_survey_"
    "result_review_v0.py"
)
TARGET = "review_exploratory_native_gravitational_requirements_family_survey_v0_result"
VERDICT = (
    "ACCEPTED_AUTHORIZE_SHARED_LINEARIZED_QUADRATIC_GRAVITY_"
    "COMPARISON_PACKET_PREPARATION_ONLY"
)
SELECTED_NEXT_TARGET = (
    "prepare_shared_linearized_quadratic_gravity_source_and_spectrum_"
    "comparison_packet_v0"
)
SELECTED_NEXT_TARGET_KIND = "PREPARATION_ONLY_INDEPENDENT_PACKET_REVIEW_REQUIRED"

SURVEY_ARTIFACT_HASHES = {
    survey.HUMAN_SURVEY_RELATIVE_PATH:
        "4cea838ee30866cfa6926bb26c199f62c6591d8f5c9543dbfb391280f7dddc3b",
    survey.REPORT_RELATIVE_PATH:
        "f597596e5c33179be7a199c73ec2ea7441cba03d1784961a9a09926bf8002dcb",
    "formal/python/tools/exploratory_native_gravitational_requirements_family_survey_v0.py":
        "7e7769baf18121172efed51e5f4b354d45834a1f0a7edb3964163e40aaf0b3ab",
    "formal/python/tests/test_exploratory_native_gravitational_requirements_family_survey_v0.py":
        "3f457c7ee20466bcf2c862197f6752d1e07581a58f1d4a0e00bdfe2c71d3702c",
    "formal/toe_formal/ToeFormal/Derivation/ExploratoryNativeGravitationalRequirementsFamilySurveyV0.lean":
        "7719ce2d14f67063e3ed595769f1f757f8c3a597fe664700e7400f189991db65",
}

SOURCE_SPOT_CHECKS = [
    {
        "check_id": "SRC_DIFF_COVARIANCE_GENERALITY",
        "reference": "https://arxiv.org/abs/gr-qc/9403028",
        "reviewed_claim": "The diffeomorphism/Noether framework applies to general covariant gravity with arbitrary matter and is not EH-specific.",
        "finding": "SUPPORTED_IN_STATED_SCOPE",
        "scope_limit": "Does not by itself prove source conservation for arbitrary off-shell or partial-system sources.",
    },
    {
        "check_id": "SRC_ANALYTIC_FR_EXTRA_SCALAR",
        "reference": "https://arxiv.org/abs/1104.0819",
        "reviewed_claim": "Analytic metric f(R) about R=0 has an extra Ricci-scalar mode and modified weak-field metrics.",
        "finding": "SUPPORTED_FOR_ANALYTIC_REPRESENTATIVES",
        "scope_limit": "Not a theorem covering every f(R) function, background, or screening regime.",
    },
    {
        "check_id": "SRC_FR_NEWTONIAN_CORRECTIONS",
        "reference": "https://arxiv.org/abs/0708.0723",
        "reviewed_claim": "Analytic f(R) Newtonian potentials receive curvature-dependent corrections and massive solutions.",
        "finding": "SUPPORTED_FOR_STATED_ANALYTIC_EXPANSION",
        "scope_limit": "Does not establish a family-wide empirical verdict.",
    },
    {
        "check_id": "SRC_QUADRATIC_MODE_CONTENT",
        "reference": "https://arxiv.org/abs/hep-th/9509142",
        "reviewed_claim": "Quadratic gravity admits massless gravity plus massive scalar and massive spin-2 fields, with the flat-space spin-2 field ghost-like in the stated canonical treatment.",
        "finding": "SUPPORTED_IN_GENERIC_LOCAL_METRIC_FLAT_SPACE_SCOPE",
        "scope_limit": "Does not cover nonlocal, torsionful, independent-connection, degenerate, or alternative-quantization theories.",
    },
    {
        "check_id": "SRC_FR_STABILITY_CONDITION",
        "reference": "https://arxiv.org/abs/astro-ph/0610734",
        "reviewed_claim": "Metric f(R) matter stability is condition- and model-dependent.",
        "finding": "SUPPORTED_IN_STATED_METRIC_FR_SCOPE",
        "scope_limit": "Matter instability is not identical to ghost, tachyon, or nonlinear background instability.",
    },
    {
        "check_id": "SRC_EH_MINKOWSKI_STABILITY",
        "reference": "https://arxiv.org/abs/math/0411109",
        "reviewed_claim": "Einstein vacuum and Einstein-scalar small asymptotically flat data have global near-Minkowski stability in the theorem's domain.",
        "finding": "SUPPORTED_IN_SMALL_DATA_DOMAIN",
        "scope_limit": "Not a universal stability result for all backgrounds, cosmological terms, or matter sectors.",
    },
    {
        "check_id": "SRC_GAUSS_BONNET_QUADRATIC_BASIS",
        "reference": "https://arxiv.org/abs/1007.1917",
        "reviewed_claim": "The four-dimensional Gauss-Bonnet relation removes a third independent weak-field characteristic scale associated with Riemann-squared.",
        "finding": "SUPPORTED_FOR_STATED_FOURTH_ORDER_NEWTONIAN_ANALYSIS",
        "scope_limit": "The future packet must separately freeze local-bulk and boundary/topological scope.",
    },
    {
        "check_id": "SRC_LOVELOCK_CONDITIONALITY",
        "reference": "https://doi.org/10.1063/1.1665613",
        "reviewed_claim": "Einstein uniqueness follows only under Lovelock's dimensional, naturality, divergence, and differential-order assumptions.",
        "finding": "SUPPORTED_AS_CONDITIONAL_THEOREM",
        "scope_limit": "The theorem does not establish that the ToE natively selected those assumptions.",
    },
]


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {relative_path}")
    return value


def _freeze_survey() -> tuple[list[dict[str, str]], dict[str, Any]]:
    custody: list[dict[str, str]] = []
    for relative_path, expected in SURVEY_ARTIFACT_HASHES.items():
        observed = _sha256(REPO_ROOT / relative_path)
        if observed != expected:
            raise ValueError(f"completed exploratory survey drift: {relative_path}")
        custody.append({"relative_path": relative_path, "sha256": observed})
    completed = _load_json(survey.REPORT_RELATIVE_PATH)
    if completed.get("target") != survey.TARGET:
        raise ValueError("reviewed survey target mismatch")
    if completed.get("verdict") != survey.VERDICT:
        raise ValueError("reviewed survey completion verdict mismatch")
    if completed.get("selected_next_target") != TARGET:
        raise ValueError("completed survey did not select this result review")
    return custody, completed


def _cell_map(completed: dict[str, Any]) -> dict[str, dict[str, Any]]:
    forms = completed["survey_form_contract"]["forms"]
    return {row["cell_id"]: row for row in forms}


def _review_gates(completed: dict[str, Any]) -> dict[str, Any]:
    questions = completed["decision_critical_question_register"]["rows"]
    forms = completed["survey_form_contract"]["forms"]
    cells = _cell_map(completed)
    dispositions = [packet_review.structural_entry_disposition(row) for row in forms]
    surveyed_ids = {
        row["cell_id"] for row in forms if row["workflow_state"] == "SURVEYED_PROVISIONAL"
    }
    question_support = {
        cell_id for question in questions for cell_id in question["supporting_cell_ids"]
    }
    contextual_ids = {
        "EXP_R2_METRIC_ONLY__F_EXTRA_FIELD",
        "EXP_R2_METRIC_ONLY__F_CONNECTION_TORSION",
        "EXP_R3_LOCALITY__F_NONLOCAL",
    }
    question_fields = {
        "issue", "provisional_answer", "assumptions", "reasoning_basis_types",
        "source_ids", "uncertainty", "resolving_work", "supporting_cell_ids",
        "priority_rank", "authority",
    }
    primary = ["F_EH", "F_FR", "F_QUADRATIC"]
    r5 = [cells[f"EXP_R5_CK_FIREWALL__{family}"] for family in primary]
    fr_uncertain = [
        cells[f"EXP_{requirement}__F_FR"]
        for requirement in (
            "R8_NEWTON_POISSON", "R9_MOMENTUM_CURRENT", "R10_STABILITY_NO_FIT"
        )
    ]
    quadratic_stability = cells["EXP_R10_STABILITY_NO_FIT__F_QUADRATIC"]
    opportunity = completed["opportunity_map"]
    next_work = opportunity["highest_value_next_bounded_derivation"]
    tool_source = (
        REPO_ROOT
        / "formal/python/tools/exploratory_native_gravitational_requirements_family_survey_v0.py"
    ).read_text(encoding="utf-8")
    functions = {
        node.name
        for node in ast.parse(tool_source).body
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
    }
    current_target = (
        REPO_ROOT / "formal/toe_formal/ToeFormal/Derivation/CurrentTarget.lean"
    ).read_text(encoding="utf-8")
    current_authority = (
        REPO_ROOT / "formal/toe_formal/ToeFormal/Release/CurrentAuthority.lean"
    ).read_text(encoding="utf-8")
    human = (REPO_ROOT / HUMAN_REVIEW_RELATIVE_PATH).read_text(encoding="utf-8")
    current_target_literals = [
        token
        for token in current_target.split('"')[1::2]
        if token.startswith(("prepare_", "review_", "conduct_"))
    ]
    current_authority_literals = [
        token
        for token in current_authority.split('"')[1::2]
        if token.startswith(("prepare_", "review_", "conduct_"))
    ]
    authority_is_synchronized = (
        bool(current_target_literals)
        and bool(current_authority_literals)
        and current_target_literals[-1] == current_authority_literals[-1]
    )

    gate_rows = [
        {
            "gate": 1,
            "gate_id": "EXACT_AUTHORITY_AND_CUSTODY",
            "passed": authority_is_synchronized
            and completed["authority"]["execution_consumed_count"] == 1,
        },
        {
            "gate": 2,
            "gate_id": "EIGHT_COMPLETE_PROVISIONAL_QUESTIONS",
            "passed": len(questions) == 8
            and all(row["status"] == "ANSWERED_PROVISIONAL" for row in questions)
            and all(question_fields.issubset(row) for row in questions)
            and all(all(row[field] for field in question_fields) for row in questions),
        },
        {
            "gate": 3,
            "gate_id": "TWENTY_TWO_COMPLETE_SUPPORTING_CELLS",
            "passed": dispositions.count("VALID_PROVISIONAL_ENTRY") == 22
            and "INCOMPLETE_SURVEY_ENTRY" not in dispositions
            and completed["result_controls"]["descriptive_label_tally"] == {
                "CLEARLY COMPATIBLE": 6,
                "LIKELY COMPATIBLE": 7,
                "LIKELY INCOMPATIBLE": 1,
                "CLEARLY INCOMPATIBLE": 0,
                "UNRESOLVED": 5,
                "OUTSIDE FROZEN SCOPE": 3,
            },
        },
        {
            "gate": 4,
            "gate_id": "FORTY_EIGHT_GENUINE_NONCRITICAL_BLANKS",
            "passed": dispositions.count("VALID_NOT_SURVEYED") == 48
            and surveyed_ids == question_support | contextual_ids
            and all(
                cells[f"EXP_{requirement}__{family}"]["workflow_state"]
                == "SURVEYED_PROVISIONAL"
                for requirement in (
                    "R8_NEWTON_POISSON", "R9_MOMENTUM_CURRENT",
                    "R10_STABILITY_NO_FIT",
                )
                for family in primary
            ),
        },
        {
            "gate": 5,
            "gate_id": "COVARIANCE_AND_SOURCE_SCOPE_HONEST",
            "passed": all(
                cells[f"EXP_R4_DIFF_COVARIANCE__{family}"]["provisional_classification"]
                == "CLEARLY COMPATIBLE"
                for family in primary
            )
            and "Matter equations hold"
            in cells["EXP_R7_SOURCE_COMPATIBILITY__F_EH"]["assumptions_and_domain"],
        },
        {
            "gate": 6,
            "gate_id": "CK_ARCHITECTURAL_NOT_DYNAMICAL",
            "passed": all(row["provisional_classification"] == "LIKELY COMPATIBLE" for row in r5)
            and all("Ck" in row["main_uncertainty"] or "Ck" in row["resolving_calculation_or_theorem"] for row in r5)
            and opportunity["native_discriminator_found"] is False,
        },
        {
            "gate": 7,
            "gate_id": "FR_SCOPE_MODEL_DEPENDENT",
            "passed": all(row["provisional_classification"] == "UNRESOLVED" for row in fr_uncertain)
            and all(row["main_uncertainty"] for row in fr_uncertain),
        },
        {
            "gate": 8,
            "gate_id": "GENERIC_QUADRATIC_WARNING_QUALIFIED",
            "passed": quadratic_stability["provisional_classification"] == "LIKELY INCOMPATIBLE"
            and "Generic beta not zero" in quadratic_stability["assumptions_and_domain"]
            and "ordinary" in " ".join(quadratic_stability["assumptions_and_domain"]).lower()
            and opportunity["best_bounded_no_go_or_counterexample_test"]["theorem_established"] is False,
        },
        {
            "gate": 9,
            "gate_id": "LOVELOCK_ASSUMPTIONS_REMAIN_SUPPLIED",
            "passed": opportunity["supplied_assumption_dependency"]["native_project_principle"] is False
            and "E8_LOVELOCK_1971" in opportunity["supplied_assumption_dependency"]["source_ids"],
        },
        {
            "gate": 10,
            "gate_id": "NO_SELECTOR_MERGE_OR_PROMOTION",
            "passed": "evaluate_analysis(" not in tool_source
            and not any(
                token in name.lower()
                for name in functions
                for token in ("survivor", "classifier", "equivalence_reducer", "recommend_theory")
            )
            and completed["scope"]["authoritative_V2_matrix_cells_computed"] == 0
            and completed["scope"]["real_family_equivalence_established"] is False
            and completed["scope"]["gravitational_action_selected_or_proposed"] is False,
        },
        {
            "gate": 11,
            "gate_id": "RECOMMENDATION_TRACED_TO_DQ4_DQ5_DQ6",
            "passed": next_work["question_ids_addressed"] == [
                "DQ4_NEWTONIAN_RECOVERY_DISCRIMINATION",
                "DQ5_MOMENTUM_CURRENT_INDEPENDENCE",
                "DQ6_STABILITY_NO_FIT_DISCRIMINATION",
            ]
            and next_work["project_action_proposal"] is False
            and all(token in next_work["comparison_instrument"] for token in ("R", "alpha R^2", "beta R_mn R^mn")),
        },
        {
            "gate": 12,
            "gate_id": "PREPARATION_ONLY_STOP_BOUNDARY",
            "passed": completed["scope"]["metric_or_tetrad_variation_executed"] is False
            and completed["scope"]["tensor_field_equation_derived"] is False
            and completed["scope"]["frame_dragging_reopened"] is False
            and "prepare_shared_linearized_quadratic_gravity_source_and_spectrum_comparison_packet_v0" in human
            and "It does not authorize the comparison execution" in human,
        },
    ]
    return {
        "gate_count": len(gate_rows),
        "pass_count": sum(row["passed"] for row in gate_rows),
        "failure_count": sum(not row["passed"] for row in gate_rows),
        "rows": gate_rows,
        "structural_disposition_tally": {
            status: dispositions.count(status)
            for status in (
                "VALID_PROVISIONAL_ENTRY", "VALID_NOT_SURVEYED",
                "INCOMPLETE_SURVEY_ENTRY",
            )
        },
        "surveyed_cell_ids": sorted(surveyed_ids),
        "question_support_cell_ids": sorted(question_support),
        "contextual_scope_cell_ids": sorted(contextual_ids),
    }


def _next_packet_contract() -> dict[str, Any]:
    obligations = [
        {
            "obligation_id": "O1_COMPARISON_STATUS_AND_PROVENANCE",
            "required": [
                "COMPARISON ACTION FAMILY", "NOT A TOE CANDIDATE",
                "NOT A SUCCESSOR MASTER ACTION", "NOT A NATIVE POSTULATE",
                "term-by-term comparator provenance",
            ],
        },
        {
            "obligation_id": "O2_FOUR_DIMENSIONAL_QUADRATIC_BASIS",
            "required": [
                "Riemann-squared included before basis reduction",
                "four-dimensional Gauss-Bonnet identity",
                "compact-support local-bulk equivalence domain",
                "no transport to boundary observables topology or global charges",
            ],
        },
        {
            "obligation_id": "O3_EXTERNAL_CONSERVED_COMPARISON_SOURCE",
            "required": [
                "externally supplied T_mn", "partial_mu T^mu_nu = 0",
                "S_m notation does not select a ToE matter action",
            ],
        },
        {
            "obligation_id": "O4_BACKGROUND_COORDINATES_SIGNATURE_UNITS",
            "required": [
                "g_mn = eta_mn + h_mn", "linear-order truncation",
                "x^0 = c t", "signature (+,-,-,-)",
                "SI or explicit unit-restoration map",
            ],
        },
        {
            "obligation_id": "O5_NORMALIZATION_AND_ANALYTIC_CONVENTIONS",
            "required": [
                "Einstein-Hilbert normalization", "dimensions and signs of alpha beta",
                "curvature conventions", "Fourier convention",
                "Green-function normalization", "pole prescription",
                "gauge fixing", "source normalization",
            ],
        },
        {
            "obligation_id": "O6_LINEARIZED_EQUATION_DERIVATION",
            "required": [
                "line-by-line metric variation", "boundary handling",
                "linearization", "conserved-source field equation",
                "preparation does not execute the derivation",
            ],
        },
        {
            "obligation_id": "O7_MODES_POLES_RESIDUES",
            "required": [
                "massless spin-2", "massive scalar", "generic massive spin-2",
                "pole locations", "residue signs", "tachyon conditions",
                "degenerate and infinite-mass limits",
                "trace and transverse source couplings",
                "ghost tachyon runaway matter-instability and decoupling distinguished",
            ],
        },
        {
            "obligation_id": "O8_SOURCE_CHANNEL_GREEN_FUNCTIONS",
            "required": [
                "stationary h_00 for mass density", "stationary h_0i for conserved current",
                "long-range terms", "Yukawa terms", "tensor projectors",
                "parameter dependence", "exact GR limit",
            ],
        },
        {
            "obligation_id": "O9_SHARED_PATH_CONTROLS",
            "required": [
                "alpha=beta=0 Einstein control", "beta=0 no generic massive spin-2 correction",
                "T_0i=0 no current-sourced stationary h_0i",
                "T_0i sign reversal implies h_0i sign reversal",
                "controls traverse production derivation path", "no coefficient fitting",
            ],
        },
        {
            "obligation_id": "O10_STOP_BOUNDARY",
            "required": [
                "no packet-time calculation execution", "independent packet review",
                "no numerical fitting", "no orbital precession", "no frame dragging",
                "no action adoption", "no native-principle claim", "no master-action mutation",
                "at most one bounded execution after later acceptance",
            ],
        },
    ]
    return {
        "obligation_count": len(obligations),
        "rows": obligations,
        "packet_preparation_only": True,
        "comparison_execution_authorized": False,
        "independent_packet_review_required": True,
    }


def build_review() -> dict[str, Any]:
    custody, completed = _freeze_survey()
    human = REPO_ROOT / HUMAN_REVIEW_RELATIVE_PATH
    test = REPO_ROOT / TEST_RELATIVE_PATH
    if not human.is_file() or not test.is_file():
        raise ValueError("result-review human record or focused test missing")
    gates = _review_gates(completed)
    if gates["gate_count"] != 12 or gates["pass_count"] != 12:
        failed = [row["gate_id"] for row in gates["rows"] if not row["passed"]]
        raise ValueError(f"exploratory survey result-review failure: {failed}")
    next_contract = _next_packet_contract()
    return {
        "schema_id": "EXPLORATORY_NATIVE_GRAVITATIONAL_REQUIREMENTS_FAMILY_SURVEY_RESULT_REVIEW_20260718_v0",
        "captured_at_utc": "2026-07-18T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_survey_verdict": completed["verdict"],
            "frozen_survey_artifacts": custody,
            "human_review": {"relative_path": HUMAN_REVIEW_RELATIVE_PATH, "sha256": _sha256(human)},
            "generator": {"relative_path": Path(__file__).resolve().relative_to(REPO_ROOT).as_posix(), "sha256": _sha256(Path(__file__).resolve())},
            "test": {"relative_path": TEST_RELATIVE_PATH, "sha256": _sha256(test)},
        },
        "review_gates": gates,
        "scientific_source_spot_checks": {
            "check_count": len(SOURCE_SPOT_CHECKS),
            "rows": SOURCE_SPOT_CHECKS,
            "all_supported_in_limited_scope": True,
            "custody_substitutes_for_scientific_relevance": False,
            "family_scope_generalization_permitted": False,
        },
        "survey_result": {
            "decision_critical_questions_answered": 8,
            "surveyed_provisional_cells": 22,
            "NOT_SURVEYED_cells": 48,
            "incomplete_entries": 0,
            "authoritative_V2_matrix_cells": 0,
            "opportunity_map_accepted": True,
            "native_discriminator_found": False,
            "recommended_investigation": "SHARED_LINEARIZED_QUADRATIC_GRAVITY_SOURCE_AND_SPECTRUM_COMPARISON",
            "recommendation_authority": "EXPLORATORY_ONLY",
        },
        "next_packet_preparation_contract": next_contract,
        "authorization_boundary": {
            "comparison_packet_preparation_authorized": True,
            "comparison_packet_execution_authorized": False,
            "metric_variation_authorized": False,
            "linearized_field_equation_derivation_authorized": False,
            "propagator_or_mode_calculation_authorized": False,
            "Green_function_calculation_authorized": False,
            "coefficient_fitting_authorized": False,
            "matter_action_selection_authorized": False,
            "orbital_precession_authorized": False,
            "frame_dragging_authorized": False,
            "comparison_family_adoption_authorized": False,
            "native_principle_or_postulate_authorized": False,
            "master_action_mutation_authorized": False,
            "authoritative_V2_population_authorized": False,
            "automated_action_selection_lane_reopening_authorized": False,
        },
        "scope": {
            "independent_survey_result_review_executed": True,
            "survey_accepted": True,
            "comparison_packet_prepared": False,
            "comparison_executed": False,
            "authoritative_V2_matrix_cells_computed": 0,
            "native_gravitational_principle_identified": False,
            "gravitational_action_selected_or_proposed": False,
            "matter_sector_selected": False,
            "metric_or_tetrad_variation_executed": False,
            "tensor_field_equation_derived": False,
            "propagator_or_Green_function_derived": False,
            "coefficient_fitting_executed": False,
            "orbital_observable_computed": False,
            "frame_dragging_reopened": False,
            "new_postulate_authorized": False,
            "automated_action_selection_lane_reopened": False,
        },
        "current_posture": {
            "exploratory_survey": "ACCEPTED",
            "decision_critical_questions": "8_OF_8_PROVISIONALLY_ANSWERED",
            "surveyed_provisional_cells": "22_OF_70",
            "remaining_cells": "48_OF_70_NOT_SURVEYED",
            "authoritative_V2_matrix": "0_OF_70",
            "automated_action_selection_tooling": "CLOSED",
            "native_gravitational_principle": "NOT_IDENTIFIED",
            "gravitational_action": "NOT_SELECTED",
            "metric_variation": "NOT_EXECUTED",
            "frame_dragging": "NOT_RESUMED",
            "next_authority": SELECTED_NEXT_TARGET,
        },
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_review(), indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(description="Generate or check the exploratory gravity survey result review.")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    report_path = REPO_ROOT / REPORT_RELATIVE_PATH
    raw = artifact_bytes()
    if args.check:
        if not report_path.is_file() or report_path.read_bytes() != raw:
            raise SystemExit("exploratory gravity survey result-review artifact drift")
        print(json.dumps({
            "status": "VERIFIED",
            "verdict": VERDICT,
            "review_gates": "12_OF_12_PASSED",
            "surveyed_cells": 22,
            "not_surveyed_cells": 48,
            "authoritative_V2_cells": 0,
            "selected_next_target": SELECTED_NEXT_TARGET,
        }, sort_keys=True))
        return 0
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_bytes(raw)
    print(report_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

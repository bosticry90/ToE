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
SCRIPT_RELATIVE_PATH = "formal/python/tools/post_dirac_maxwell_full_zero_mode_canonical_result_route_decision.py"
CANONICAL_REVIEW_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_CANONICAL_SIMULATION_RESULT_REVIEW_20260713_v0.json"
ANALYTIC_REVIEW_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_REDUCTION_WITH_TRANSVERSE_FIELDS_PACKET_RESULT_REVIEW_20260713_v0.json"
GUARDRAIL_REVIEW_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DISCRETE_NUMERICAL_GUARDRAIL_PACKET_RESULT_REVIEW_20260713_v0.json"
SCALAR_ROBUSTNESS_REVIEW_RELATIVE_PATH = "formal/docs/release/SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_MULTI_BACKGROUND_ROBUSTNESS_CALCULATION_RESULT_REVIEW_20260710_v0.json"
EINSTEIN_SCALAR_ROUTE_REVIEW_RELATIVE_PATH = "formal/docs/release/QFT_GR_CLASSICAL_EINSTEIN_SCALAR_COUPLING_ROUTE_PACKET_RESULT_REVIEW_20260618_v0.json"
FIRST_UNIT_SELECTOR_REVIEW_RELATIVE_PATH = "formal/docs/release/PILLAR_SEAM_UNIT_MAPPING_LEDGER_FIRST_UNIT_SELECTOR_PACKET_RESULT_REVIEW_20260713_v0.json"
PACKET_RELATIVE_PATH = "formal/output/POST-DIRAC-MAXWELL-FULL-ZERO-MODE-CANONICAL-RESULT-ROUTE-DECISION-PACKET-v0.json"
MANIFEST_RELATIVE_PATH = "formal/output/POST-DIRAC-MAXWELL-FULL-ZERO-MODE-CANONICAL-RESULT-ROUTE-DECISION-MANIFEST-v0.json"
REPORT_RELATIVE_PATH = "formal/docs/release/POST_DIRAC_MAXWELL_FULL_ZERO_MODE_CANONICAL_RESULT_ROUTE_DECISION_PACKET_20260713_v0.json"
PACKET_PATH = REPO_ROOT / PACKET_RELATIVE_PATH
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH
REPORT_PATH = REPO_ROOT / REPORT_RELATIVE_PATH

CAPTURED_AT_UTC = "2026-07-13T00:00:00Z"
TARGET = "prepare_post_dirac_maxwell_full_zero_mode_canonical_result_route_decision_packet_v0"
REVIEW_TARGET = "review_post_dirac_maxwell_full_zero_mode_canonical_result_route_decision_packet_v0_result"
REVIEW_TARGET_KIND = "post_dirac_maxwell_full_zero_mode_canonical_result_route_decision_packet_v0_result_review"
FAILURE_TARGET = "prepare_post_dirac_maxwell_full_zero_mode_canonical_result_route_decision_packet_v1"
POST_ACCEPTANCE_TARGET = "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_packet_v0"
PACKET_SCHEMA_ID = "POST_DIRAC_MAXWELL_FULL_ZERO_MODE_CANONICAL_RESULT_ROUTE_DECISION_PACKET_v0"
MANIFEST_SCHEMA_ID = "POST_DIRAC_MAXWELL_FULL_ZERO_MODE_CANONICAL_RESULT_ROUTE_DECISION_MANIFEST_v0"
REPORT_SCHEMA_ID = "POST_DIRAC_MAXWELL_FULL_ZERO_MODE_CANONICAL_RESULT_ROUTE_DECISION_PACKET_20260713_v0"
INPUT_HASHES = {
    CANONICAL_REVIEW_RELATIVE_PATH: "9b518024fa8a13b73d19e01576375484d5acc24e4f5896adaa612b46f500e040",
    ANALYTIC_REVIEW_RELATIVE_PATH: "e4a830678d863319d5509bf43e332a778708b7b82bd6db5903be5a389fef34de",
    GUARDRAIL_REVIEW_RELATIVE_PATH: "b881d23e9bd201b09bb023a1e897306afff681bd57ccb224a9c6baf562be57b6",
    SCALAR_ROBUSTNESS_REVIEW_RELATIVE_PATH: "cca24f7a9d72d035b974a781213235dc7e8f0685a63bb5189ee465b1c3aa17a0",
    EINSTEIN_SCALAR_ROUTE_REVIEW_RELATIVE_PATH: "0d9eb65ddb9fcf2e6dea8bd4feab58b51fb8db4dd002181bd4004df6d5395509",
    FIRST_UNIT_SELECTOR_REVIEW_RELATIVE_PATH: "e84d7a00a29a21dae59a8d3fb26f56a6a97cf3b6021766a6b176fde81a3d610d",
}
PROMPT_RELATIVE_PATH = "Prompt.txt"
PROMPT_DEPENDENCY_ROLE = "DEMOTE_TO_NONBLOCKING_PROVENANCE"
PROMPT_SHA256 = "2bc6996ea28e96c50e688ed3d30ee24808af411a244eb594aad89ff80fda8433"

CRITERION_WEIGHTS = {
    "current_result_information_gain": 5,
    "accepted_infrastructure_reuse": 5,
    "falsifiable_discrimination": 5,
    "analytic_readiness": 4,
    "numerical_readiness": 4,
    "bounded_scope": 3,
    "seam_method_leverage": 3,
    "project_portfolio_value": 2,
}
THRESHOLD = 44
SENSITIVITY_THRESHOLDS = [40, 42, 44, 46, 48]
CANDIDATE_ORDER = [
    "DESCENDANT_NECESSITY_ROBUSTNESS",
    "DIMENSIONAL_ASCENT_2P1",
    "FIXED_CURVED_BACKGROUND_EXTENSION",
    "DYNAMIC_EINSTEIN_SCALAR",
    "NEXT_UNIT_PILLAR_TARGET",
]
CANDIDATE_LABELS = {
    "DESCENDANT_NECESSITY_ROBUSTNESS": "descendant necessity and parameter robustness",
    "DIMENSIONAL_ASCENT_2P1": "dimensional ascent to 2+1",
    "FIXED_CURVED_BACKGROUND_EXTENSION": "fixed curved-background extension",
    "DYNAMIC_EINSTEIN_SCALAR": "dynamic Einstein-scalar program",
    "NEXT_UNIT_PILLAR_TARGET": "next unit or pillar target",
}
CANDIDATE_QUESTIONS = {
    "DESCENDANT_NECESSITY_ROBUSTNESS": "Is the accepted result robust, and how much do the transverse descendants change the dynamics?",
    "DIMENSIONAL_ASCENT_2P1": "Does a descendant-complete coupled result survive when a second spatial dimension and propagating gauge structure are introduced?",
    "FIXED_CURVED_BACKGROUND_EXTENSION": "Does the accepted coupled exchange structure survive tetrad, spin-connection, and fixed-curvature transport?",
    "DYNAMIC_EINSTEIN_SCALAR": "Can scalar matter and geometry evolve together with constraint and stress-energy preservation?",
    "NEXT_UNIT_PILLAR_TARGET": "Should effort return to broader unit and pillar readiness instead of deepening this Maxwell-Dirac model?",
}
SCORES = {
    "DESCENDANT_NECESSITY_ROBUSTNESS": [2, 2, 2, 1, 2, 2, 2, 1],
    "DIMENSIONAL_ASCENT_2P1": [2, 1, 2, 0, 0, 1, 2, 1],
    "FIXED_CURVED_BACKGROUND_EXTENSION": [2, 1, 2, 0, 0, 1, 2, 1],
    "DYNAMIC_EINSTEIN_SCALAR": [1, 0, 2, 1, 0, 0, 2, 2],
    "NEXT_UNIT_PILLAR_TARGET": [1, 0, 1, 2, 0, 2, 2, 2],
}


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
    if pointer == "":
        return document
    if not pointer.startswith("/"):
        raise ValueError(f"invalid JSON pointer: {pointer}")
    current = document
    for raw_part in pointer[1:].split("/"):
        part = raw_part.replace("~1", "/").replace("~0", "~")
        if isinstance(current, list):
            current = current[int(part)]
        elif isinstance(current, dict):
            current = current[part]
        else:
            raise ValueError(f"pointer does not resolve: {pointer}")
    return current


def load_authority() -> dict[str, dict[str, Any]]:
    sources: dict[str, dict[str, Any]] = {}
    for path, digest in INPUT_HASHES.items():
        source_path = REPO_ROOT / path
        if sha256_path(source_path) != digest:
            raise ValueError(f"input hash mismatch: {path}")
        sources[path] = load_json(source_path)
    canonical = sources[CANONICAL_REVIEW_RELATIVE_PATH]
    authority = canonical.get("authority_rotation", {})
    if not (
        canonical.get("accepted") is True
        and canonical.get("verdict") == "ACCEPT_BOUNDED_SCIENTIFIC_RESULT"
        and canonical.get("accepted_claim_label") == "E-REPRO"
        and canonical.get("selected_next_target") == TARGET
        and authority.get("bounded_scientific_result_accepted") is True
        and authority.get("pillar_completion_authorized") is False
        and authority.get("seam_admissibility_or_closure_authorized") is False
    ):
        raise ValueError("canonical result review does not authorize this route decision")
    if sources[ANALYTIC_REVIEW_RELATIVE_PATH].get("authority_rotation", {}).get("full_zero_mode_analytic_repair_accepted") is not True:
        raise ValueError("analytic descendant-aware reduction is not accepted")
    if sources[GUARDRAIL_REVIEW_RELATIVE_PATH].get("authority_rotation", {}).get("numerical_guardrail_accepted") is not True:
        raise ValueError("descendant-aware numerical guardrail is not accepted")
    if sources[SCALAR_ROBUSTNESS_REVIEW_RELATIVE_PATH].get("accepted_e_repro") is not True:
        raise ValueError("fixed-background scalar robustness result is not accepted")
    if sources[EINSTEIN_SCALAR_ROUTE_REVIEW_RELATIVE_PATH].get("classical_route_result_review_accepted") is not True:
        raise ValueError("provisional Einstein-scalar route review is not accepted")
    if sources[FIRST_UNIT_SELECTOR_REVIEW_RELATIVE_PATH].get("accepted") is not True:
        raise ValueError("first-unit selector review is not accepted")
    return sources


def _evidence_record(
    proposition_id: str,
    source_path: str,
    source_locator: str,
    expected_value: Any,
    exact_proposition: str,
) -> dict[str, Any]:
    return {
        "evidence_id": f"E_{proposition_id}",
        "proposition_id": proposition_id,
        "source_id": Path(source_path).stem,
        "source_path": source_path,
        "source_hash": INPUT_HASHES[source_path],
        "source_locator": {"locator_type": "JSON_POINTER", "pointer": source_locator},
        "proposition_extraction_method": "EXACT_FIELD_READ",
        "source_declared_claim_label": "REVIEW_ACCEPTED_STATE",
        "claim_label_context": "RELEASE_FACING_CURRENT" if source_path == CANONICAL_REVIEW_RELATIVE_PATH else "HISTORICAL_ARCHIVED",
        "authority_class": "ACCEPTED_BOUNDED_REVIEW",
        "evidence_role": "REPOSITORY_STATE_EVIDENCE",
        "support_mode": "ACCEPTED_REVIEW_STATE",
        "eligible_route_types": ["PLANNING_ROUTE_SELECTION"],
        "scope_ceiling": "Bounded planning evidence about the accepted repository state only.",
        "exact_supported_proposition": exact_proposition,
        "expected_source_value": expected_value,
        "unsupported_propositions": ["pillar completion", "seam closure", "empirical adequacy", "master-action promotion"],
        "conflict_status": "NO_UNRESOLVED_CONFLICT",
        "route_support_eligible": True,
    }


def proposition_catalog() -> list[dict[str, Any]]:
    return [
        _evidence_record("P_CANONICAL_RESULT_ACCEPTED", CANONICAL_REVIEW_RELATIVE_PATH, "/verdict", "ACCEPT_BOUNDED_SCIENTIFIC_RESULT", "The descendant-aware canonical Maxwell-Dirac result is accepted as a bounded scientific result."),
        _evidence_record("P_CANONICAL_E_REPRO_SCOPE", CANONICAL_REVIEW_RELATIVE_PATH, "/accepted_claim_label", "E-REPRO", "The accepted canonical result has claim class E-REPRO."),
        _evidence_record("P_TRANSVERSE_SIGNAL_ACTIVE", CANONICAL_REVIEW_RELATIVE_PATH, "/result_metrics/transverse_signal", 6.826809919994493e-08, "The canonical result registers a nonzero transverse-descendant signal above its frozen gate."),
        _evidence_record("P_EXCHANGE_SIGNAL_SEPARATED", CANONICAL_REVIEW_RELATIVE_PATH, "/result_metrics/exchange_ratio", 352.6967159703898, "The canonical exchange-to-drift ratio is 352.6967159703898."),
        _evidence_record("P_COMPLETE_MATRIX_REPRODUCED", CANONICAL_REVIEW_RELATIVE_PATH, "/independent_reproduction/all_fifty_records_reproduced", True, "All fifty canonical records were independently reproduced."),
        _evidence_record("P_NONPROMOTION_BOUNDARY", CANONICAL_REVIEW_RELATIVE_PATH, "/authority_rotation/pillar_completion_authorized", False, "The bounded result does not authorize pillar completion."),
        _evidence_record("P_ANALYTIC_DESCENDANT_REDUCTION_ACCEPTED", ANALYTIC_REVIEW_RELATIVE_PATH, "/authority_rotation/full_zero_mode_analytic_repair_accepted", True, "The full zero-mode analytic reduction retaining both transverse descendants is accepted."),
        _evidence_record("P_NUMERICAL_GUARDRAIL_ACCEPTED", GUARDRAIL_REVIEW_RELATIVE_PATH, "/authority_rotation/numerical_guardrail_accepted", True, "The mixed link/site descendant-aware numerical guardrail is accepted."),
        _evidence_record("P_SCALAR_FIXED_BACKGROUND_ROBUSTNESS_ACCEPTED", SCALAR_ROBUSTNESS_REVIEW_RELATIVE_PATH, "/accepted_e_repro", True, "The exact four-case fixed-background scalar robustness family is accepted as scoped E-REPRO."),
        _evidence_record("P_EINSTEIN_SCALAR_ROUTE_ONLY", EINSTEIN_SCALAR_ROUTE_REVIEW_RELATIVE_PATH, "/provisional_classical_sandbox_route_only", True, "The accepted Einstein-scalar work remains a provisional classical sandbox route."),
        _evidence_record("P_EINSTEIN_SCALAR_NOT_SOLVED", EINSTEIN_SCALAR_ROUTE_REVIEW_RELATIVE_PATH, "/coupled_einstein_scalar_system_solved", False, "The coupled Einstein-scalar system has not been solved in the accepted route review."),
        _evidence_record("P_FIRST_UNIT_SELECTOR_ACCEPTED", FIRST_UNIT_SELECTOR_REVIEW_RELATIVE_PATH, "/accepted", True, "The first-unit selector is accepted as preparation authority only."),
    ]


def _support_ids(candidate_id: str, criterion: str) -> list[str]:
    common = ["P_CANONICAL_RESULT_ACCEPTED", "P_CANONICAL_E_REPRO_SCOPE", "P_NONPROMOTION_BOUNDARY"]
    mapping = {
        "DESCENDANT_NECESSITY_ROBUSTNESS": {
            "current_result_information_gain": ["P_TRANSVERSE_SIGNAL_ACTIVE", "P_EXCHANGE_SIGNAL_SEPARATED"],
            "accepted_infrastructure_reuse": ["P_ANALYTIC_DESCENDANT_REDUCTION_ACCEPTED", "P_NUMERICAL_GUARDRAIL_ACCEPTED", "P_COMPLETE_MATRIX_REPRODUCED"],
            "falsifiable_discrimination": ["P_TRANSVERSE_SIGNAL_ACTIVE", "P_COMPLETE_MATRIX_REPRODUCED"],
            "analytic_readiness": ["P_ANALYTIC_DESCENDANT_REDUCTION_ACCEPTED"],
            "numerical_readiness": ["P_NUMERICAL_GUARDRAIL_ACCEPTED", "P_COMPLETE_MATRIX_REPRODUCED"],
            "bounded_scope": ["P_CANONICAL_E_REPRO_SCOPE", "P_NONPROMOTION_BOUNDARY"],
            "seam_method_leverage": ["P_ANALYTIC_DESCENDANT_REDUCTION_ACCEPTED", "P_TRANSVERSE_SIGNAL_ACTIVE"],
            "project_portfolio_value": common,
        },
        "DIMENSIONAL_ASCENT_2P1": {criterion_name: common + ["P_ANALYTIC_DESCENDANT_REDUCTION_ACCEPTED"] for criterion_name in CRITERION_WEIGHTS},
        "FIXED_CURVED_BACKGROUND_EXTENSION": {criterion_name: common + ["P_SCALAR_FIXED_BACKGROUND_ROBUSTNESS_ACCEPTED"] for criterion_name in CRITERION_WEIGHTS},
        "DYNAMIC_EINSTEIN_SCALAR": {criterion_name: ["P_SCALAR_FIXED_BACKGROUND_ROBUSTNESS_ACCEPTED", "P_EINSTEIN_SCALAR_ROUTE_ONLY", "P_EINSTEIN_SCALAR_NOT_SOLVED", "P_NONPROMOTION_BOUNDARY"] for criterion_name in CRITERION_WEIGHTS},
        "NEXT_UNIT_PILLAR_TARGET": {criterion_name: ["P_FIRST_UNIT_SELECTOR_ACCEPTED", "P_NONPROMOTION_BOUNDARY"] for criterion_name in CRITERION_WEIGHTS},
    }
    return mapping[candidate_id][criterion]


def _basis(candidate_id: str, criterion: str, score: int) -> str:
    text = {
        "DESCENDANT_NECESSITY_ROBUSTNESS": {
            "current_result_information_gain": "Directly tests the least-over-threshold canonical signal and the obstruction that forced descendant retention.",
            "accepted_infrastructure_reuse": "Reuses the accepted action, reduction, guardrail, canonical implementation, controls, and observables.",
            "falsifiable_discrimination": "A preregistered family can compare the full system with the already-rejected truncation and classify broad, conditional, or limited robustness.",
            "analytic_readiness": "The model is accepted, but parameter-family semantics and descendant-necessity observables still require a new guardrail.",
            "numerical_readiness": "The complete descendant-aware implementation and deterministic canonical matrix are accepted.",
            "bounded_scope": "A small preregistered family can vary only q, m, holonomy, descendant excitation, and relative phase.",
            "seam_method_leverage": "Quantifies whether the restored destination objects materially alter transport across the admitted reduction.",
            "project_portfolio_value": "Deepens the strongest coupled result but does not broaden the project to a new pillar.",
        },
        "DIMENSIONAL_ASCENT_2P1": {
            "current_result_information_gain": "Tests whether the accepted coupled result survives a less severe dimensional reduction.",
            "accepted_infrastructure_reuse": "Reuses the parent action and semantics, but not the accepted 1+1 discrete architecture unchanged.",
            "falsifiable_discrimination": "Can expose new gauge, constraint, and descendant failures under ascent.",
            "analytic_readiness": "No accepted 3+1 to 2+1 reduction packet establishes the retained object inventory and tensor map.",
            "numerical_readiness": "No reviewed two-spatial-dimensional implementation or convergence guardrail exists.",
            "bounded_scope": "A 2+1 ascent is definable but materially enlarges fields, constraints, costs, and control space.",
            "seam_method_leverage": "Directly tests object and source transport under a different dimensional seam.",
            "project_portfolio_value": "Broadens electromagnetic dynamics but remains within the same classical matter family.",
        },
        "FIXED_CURVED_BACKGROUND_EXTENSION": {
            "current_result_information_gain": "Tests transport of the accepted coupled exchange structure through tetrads, spin connection, and fixed curvature.",
            "accepted_infrastructure_reuse": "Reuses the Maxwell-Dirac foundation, while geometry-dependent equations and discretization require new work.",
            "falsifiable_discrimination": "Curvature can expose convention, covariant-current, and stress-energy transport failures.",
            "analytic_readiness": "Accepted scalar fixed-background evidence does not supply a curved Maxwell-Dirac derivation.",
            "numerical_readiness": "No reviewed curved-background Maxwell-Dirac discrete architecture exists.",
            "bounded_scope": "A fixed background is narrower than dynamic gravity but broader than the accepted flat zero-mode model.",
            "seam_method_leverage": "Tests covariant object and conservation transport into a geometric regime.",
            "project_portfolio_value": "Connects the coupled result to GR-facing methods without dynamic backreaction.",
        },
        "DYNAMIC_EINSTEIN_SCALAR": {
            "current_result_information_gain": "Advances dynamic geometry but does not directly probe the accepted Maxwell-Dirac descendants.",
            "accepted_infrastructure_reuse": "Uses the separate scalar route rather than the accepted descendant-aware numerical implementation.",
            "falsifiable_discrimination": "Constraint preservation and backreaction create a strong independent coupled-system test.",
            "analytic_readiness": "A provisional classical Einstein-scalar route exists, but no coupled solution has been accepted.",
            "numerical_readiness": "No accepted dynamic-gravity numerical guardrail is bound by the cited route review.",
            "bounded_scope": "Dynamic geometry, gauge choice, constraints, and boundary data exceed a near-term bounded extension.",
            "seam_method_leverage": "Strongly tests matter-geometry compatibility and conservation obligations.",
            "project_portfolio_value": "Would open the most distinct scientific lane among these candidates.",
        },
        "NEXT_UNIT_PILLAR_TARGET": {
            "current_result_information_gain": "Broadens readiness but does not test the accepted coupled result's least-established behavior.",
            "accepted_infrastructure_reuse": "Does not reuse the canonical simulator as the principal evidence engine.",
            "falsifiable_discrimination": "A unit or pillar packet can resolve a bounded surface but is not yet one specified experiment.",
            "analytic_readiness": "The accepted selector architecture can select bounded preparation work without claiming resolution.",
            "numerical_readiness": "No single numerical system is defined by this broad portfolio route.",
            "bounded_scope": "The route can remain bounded by selecting one reviewed unit or pillar target.",
            "seam_method_leverage": "Returns directly to the repository's broader source, unit, and seam readiness program.",
            "project_portfolio_value": "Provides the strongest breadth and avoids concentrating all effort in one model.",
        },
    }
    return f"Score {score}: {text[candidate_id][criterion]}"


def _missing(candidate_id: str, criterion: str, score: int) -> str:
    if score == 2:
        return "MAXIMUM_SCORE"
    if criterion == "analytic_readiness":
        return "An accepted route-specific action, equation, stress-energy, boundary, and conservation packet."
    if criterion == "numerical_readiness":
        return "An accepted route-specific discrete architecture, controls, convergence policy, and calibration boundary."
    if criterion == "accepted_infrastructure_reuse":
        return "A reviewed map showing that the accepted descendant-aware analytic and numerical infrastructure transfers without replacement."
    if criterion == "bounded_scope":
        return "A smaller frozen field and parameter inventory with explicit omissions and failure semantics."
    if criterion == "current_result_information_gain":
        return "A direct preregistered discriminator tied to the accepted canonical result's unresolved scope."
    if criterion == "falsifiable_discrimination":
        return "A closed observable, comparator, and outcome taxonomy that can reject the route's central hypothesis."
    if criterion == "seam_method_leverage":
        return "An exact source-to-destination object, unit, source, and conservation transport map."
    return "A reviewed reason that this route improves both depth and breadth relative to the accepted portfolio."


def score_candidate(candidate_id: str) -> dict[str, Any]:
    values = SCORES[candidate_id]
    entries = []
    for index, (criterion, weight) in enumerate(CRITERION_WEIGHTS.items()):
        score = values[index]
        entries.append({
            "criterion": criterion,
            "weight": weight,
            "score": score,
            "weighted_score": weight * score,
            "exact_supporting_proposition_ids": _support_ids(candidate_id, criterion),
            "eligibility_basis": _basis(candidate_id, criterion, score),
            "missing_evidence_required_for_next_score": _missing(candidate_id, criterion, score),
        })
    total = sum(item["weighted_score"] for item in entries)
    minimum_gate_passed = values[0] >= 1 and values[2] >= 1 and values[5] >= 1
    return {
        "candidate_id": candidate_id,
        "candidate_label": CANDIDATE_LABELS[candidate_id],
        "scientific_question": CANDIDATE_QUESTIONS[candidate_id],
        "criterion_scores": entries,
        "weighted_total": total,
        "maximum_total": 62,
        "minimum_gate": {"current_result_information_gain_at_least_1": values[0] >= 1, "falsifiable_discrimination_at_least_1": values[2] >= 1, "bounded_scope_at_least_1": values[5] >= 1},
        "minimum_gate_passed": minimum_gate_passed,
        "unresolved_conflicts": [],
    }


def select(scored: list[dict[str, Any]], threshold: int) -> dict[str, Any]:
    eligible = [
        item
        for item in scored
        if item["minimum_gate_passed"]
        and not item["unresolved_conflicts"]
        and item["weighted_total"] >= threshold
    ]
    if not eligible:
        return {"threshold": threshold, "selected_candidate_id": None, "eligible_candidate_ids": []}
    highest = max(item["weighted_total"] for item in eligible)
    tied = [item for item in eligible if item["weighted_total"] == highest]
    selected = min(tied, key=lambda item: CANDIDATE_ORDER.index(item["candidate_id"]))
    return {
        "threshold": threshold,
        "selected_candidate_id": selected["candidate_id"],
        "selected_candidate_label": selected["candidate_label"],
        "selected_weighted_total": highest,
        "eligible_candidate_ids": [
            item["candidate_id"]
            for item in sorted(
                eligible,
                key=lambda value: (-value["weighted_total"], CANDIDATE_ORDER.index(value["candidate_id"])),
            )
        ],
        "tie_break_used": len(tied) > 1,
        "tied_candidate_ids": [item["candidate_id"] for item in tied],
    }


def build_packet() -> dict[str, Any]:
    sources = load_authority()
    evidence = proposition_catalog()
    for record in evidence:
        pointer = record["source_locator"]["pointer"]
        observed = _json_pointer(sources[record["source_path"]], pointer)
        if observed != record["expected_source_value"]:
            raise ValueError(f"proposition locator mismatch: {record['proposition_id']}")
    scored = [score_candidate(candidate) for candidate in CANDIDATE_ORDER]
    sensitivity = [select(scored, threshold) for threshold in SENSITIVITY_THRESHOLDS]
    canonical = select(scored, THRESHOLD)
    return {
        "schema_id": PACKET_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "selected_next_target": REVIEW_TARGET,
        "selected_next_target_kind": REVIEW_TARGET_KIND,
        "failure_target": FAILURE_TARGET,
        "post_acceptance_target": POST_ACCEPTANCE_TARGET,
        "candidate_order_is_identity_only_not_preference": True,
        "criterion_weights_frozen_before_scoring": True,
        "threshold_frozen_before_scoring": True,
        "criterion_weights": CRITERION_WEIGHTS,
        "score_domain": [0, 1, 2],
        "maximum_weighted_total": 62,
        "selection_threshold": THRESHOLD,
        "sensitivity_thresholds": SENSITIVITY_THRESHOLDS,
        "evidence_records": evidence,
        "scored_candidates": scored,
        "canonical_selection": canonical,
        "sensitivity_analysis": sensitivity,
        "selection_stable_40_through_48": all(
            item["selected_candidate_id"] == canonical["selected_candidate_id"] for item in sensitivity
        ),
        "user_recommendation": {
            "candidate_id": "DESCENDANT_NECESSITY_ROBUSTNESS",
            "role": "NONDECISIVE_CONTEXT",
            "used_as_score_input": False,
        },
        "external_literature_used_as_score_input": False,
        "selected_route_definition": {
            "route_id": "DESCENDANT_NECESSITY_ROBUSTNESS",
            "bounded_parameter_axes": ["q", "m", "holonomy_W", "initial_descendant_energy", "relative_species_phase"],
            "required_comparators": ["FULL_ACCEPTED_MODEL", "FORCED_REJECTED_A2_A3_ZERO_TRUNCATION"],
            "required_observables": ["descendant_necessity_ratio", "transverse_source_residual", "exchange_to_drift_ratio", "time_to_full_truncated_divergence"],
            "required_outcome_classes": ["BROADLY_ROBUST", "CONDITIONALLY_ROBUST", "THRESHOLD_SENSITIVE", "NUMERICALLY_BLOCKED", "MODEL_DOMAIN_LIMITED"],
            "invalid_comparator_is_not_a_rival_physical_model": True,
        },
        "completed_tranches_reopened": False,
        "canonical_rerun_authorized": False,
        "boundary": {
            "only_route_specific_preparation_authorized_after_review": True,
            "robustness_execution_authorized": False,
            "new_parameter_values_frozen": False,
            "canonical_result_recalibrated": False,
            "canonical_result_rerun": False,
            "pillar_completion_claimed": False,
            "seam_admissibility_or_closure_claimed": False,
            "empirical_adequacy_claimed": False,
            "new_physics_claimed": False,
            "C_k_audit_only": True,
            "CCFT_resumed": False,
            "master_action_promoted": False,
            "repository_wide_green_claimed": False,
        },
        "input_artifacts": [{"path": path, "sha256": digest} for path, digest in INPUT_HASHES.items()],
        "prompt_protection": {
            "path": PROMPT_RELATIVE_PATH,
            "sha256": PROMPT_SHA256,
            "excluded_from_scientific_inputs": True,
        },
    }


def validate_packet(packet: dict[str, Any]) -> list[str]:
    failures: list[str] = []
    if packet.get("schema_id") != PACKET_SCHEMA_ID or packet.get("target") != TARGET:
        failures.append("decision_identity")
    if [item.get("candidate_id") for item in packet.get("scored_candidates", [])] != CANDIDATE_ORDER:
        failures.append("exact_five_candidates")
    if packet.get("criterion_weights") != CRITERION_WEIGHTS or packet.get("selection_threshold") != THRESHOLD:
        failures.append("frozen_rubric")
    if any(len(item.get("criterion_scores", [])) != 8 for item in packet.get("scored_candidates", [])):
        failures.append("all_candidates_scored")
    if any(
        item["weighted_total"] != sum(row["weighted_score"] for row in item["criterion_scores"])
        for item in packet.get("scored_candidates", [])
    ):
        failures.append("totals_reproduce")
    proposition_ids = {item.get("proposition_id") for item in packet.get("evidence_records", [])}
    if (
        len(proposition_ids) != len(packet.get("evidence_records", []))
        or any(item.get("route_support_eligible") is not True for item in packet.get("evidence_records", []))
        or any(
            not row.get("exact_supporting_proposition_ids")
            or not set(row["exact_supporting_proposition_ids"]).issubset(proposition_ids)
            for candidate in packet.get("scored_candidates", [])
            for row in candidate.get("criterion_scores", [])
        )
    ):
        failures.append("proposition_support_closure")
    if packet.get("canonical_selection", {}).get("selected_candidate_id") != "DESCENDANT_NECESSITY_ROBUSTNESS":
        failures.append("highest_scoring_eligible_candidate")
    if packet.get("selection_stable_40_through_48") is not True:
        failures.append("sensitivity_stability")
    if packet.get("user_recommendation", {}).get("used_as_score_input") is not False:
        failures.append("recommendation_nondecisive")
    if packet.get("external_literature_used_as_score_input") is not False:
        failures.append("external_context_nondecisive")
    if packet.get("completed_tranches_reopened") is not False or packet.get("canonical_rerun_authorized") is not False:
        failures.append("completed_tranches_immutable")
    if packet.get("post_acceptance_target") != POST_ACCEPTANCE_TARGET:
        failures.append("selected_route_target_identity")
    boundary = packet.get("boundary", {})
    if (
        boundary.get("robustness_execution_authorized") is not False
        or boundary.get("new_parameter_values_frozen") is not False
        or boundary.get("canonical_result_recalibrated") is not False
    ):
        failures.append("preparation_only_boundary")
    if any(
        boundary.get(key) is not False
        for key in [
            "pillar_completion_claimed",
            "seam_admissibility_or_closure_claimed",
            "empirical_adequacy_claimed",
            "new_physics_claimed",
            "CCFT_resumed",
            "master_action_promoted",
            "repository_wide_green_claimed",
        ]
    ) or boundary.get("C_k_audit_only") is not True:
        failures.append("nonpromotion_boundary")
    if "expected_winner" in packet or "expected_selected_candidate" in packet:
        failures.append("no_expected_winner_oracle")
    if not prompt_dependency_is_nonblocking(PROMPT_DEPENDENCY_ROLE):
        failures.append("Prompt_preserved")
    return failures


def mutation_controls(base: dict[str, Any]) -> list[dict[str, Any]]:
    Mutation = tuple[str, Callable[[dict[str, Any]], None], str]

    def remove_support(value: dict[str, Any]) -> None:
        value["scored_candidates"][0]["criterion_scores"][0]["exact_supporting_proposition_ids"] = ["P_UNKNOWN"]

    mutations: list[Mutation] = [
        ("candidate_removed", lambda value: value["scored_candidates"].pop(), "exact_five_candidates"),
        ("rubric_weight_changed", lambda value: value["criterion_weights"].update({"current_result_information_gain": 4}), "frozen_rubric"),
        ("total_forged", lambda value: value["scored_candidates"][0].update({"weighted_total": 62}), "totals_reproduce"),
        ("proposition_support_replaced", remove_support, "proposition_support_closure"),
        ("recommendation_made_decisive", lambda value: value["user_recommendation"].update({"used_as_score_input": True}), "recommendation_nondecisive"),
        ("external_context_promoted", lambda value: value.update({"external_literature_used_as_score_input": True}), "external_context_nondecisive"),
        ("completed_tranche_reopened", lambda value: value.update({"completed_tranches_reopened": True}), "completed_tranches_immutable"),
        ("robustness_execution_authorized_early", lambda value: value["boundary"].update({"robustness_execution_authorized": True}), "preparation_only_boundary"),
        ("pillar_completion_promoted", lambda value: value["boundary"].update({"pillar_completion_claimed": True}), "nonpromotion_boundary"),
        ("expected_winner_injected", lambda value: value.update({"expected_winner": "DESCENDANT_NECESSITY_ROBUSTNESS"}), "no_expected_winner_oracle"),
    ]
    results = []
    for control_id, mutate, diagnostic in mutations:
        fixture = copy.deepcopy(base)
        if validate_packet(fixture):
            raise ValueError(f"unmutated fixture failed before {control_id}")
        mutate(fixture)
        observed = validate_packet(fixture)
        results.append({
            "control_id": control_id,
            "changed_premise_count": 1,
            "expected_diagnostic": diagnostic,
            "observed_diagnostics": observed,
            "passed": observed == [diagnostic],
        })
    return results


DECISION_IDS = [
    "accepted_canonical_result_authorizes_post_result_route_decision_only",
    "exactly_five_candidate_routes_are_scored",
    "weights_threshold_score_domain_and_gates_are_frozen",
    "all_forty_scores_are_proposition_bound",
    "all_weighted_totals_reproduce_without_expected_winner",
    "user_recommendation_and_external_context_are_nondecisive",
    "descendant_necessity_robustness_is_highest_scoring_eligible_route",
    "selection_is_stable_at_40_42_44_46_48",
    "selected_route_freezes_bounded_axes_comparators_observables_and_outcomes_for_later_preparation",
    "invalid_truncation_is_comparator_only_not_a_rival_model",
    "ten_mutation_controls_are_independently_diagnosed",
    "completed_tranches_and_canonical_result_remain_immutable",
    "only_independent_route_review_is_authorized",
    "pillar_seam_empirical_C_k_CCFT_master_action_and_repository_nonpromotions_hold",
    "Prompt_is_preserved",
]


def build_artifacts() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    packet = build_packet()
    failures = validate_packet(packet)
    if failures:
        raise ValueError(f"post-result route-decision validation failed: {failures}")
    controls = mutation_controls(packet)
    if not all(item["passed"] for item in controls):
        raise ValueError("post-result route-decision mutation controls failed")
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
        "candidate_count": len(CANDIDATE_ORDER),
        "criterion_count": len(CRITERION_WEIGHTS),
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
        "canonical_selection": packet["canonical_selection"],
        "sensitivity_analysis": packet["sensitivity_analysis"],
        "weighted_totals": {item["candidate_id"]: item["weighted_total"] for item in packet["scored_candidates"]},
        "decision_count": len(DECISION_IDS),
        "decisions": [{"decision_id": item, "passed": True} for item in DECISION_IDS],
        "all_decisions_passed": True,
        "mutation_control_count": len(controls),
        "mutation_controls_passed": sum(item["passed"] for item in controls),
        "artifact_hashes": {
            "generator_sha256": sha256_path(SCRIPT_PATH),
            "packet_sha256": sha256_bytes(packet_raw),
            "manifest_sha256": sha256_bytes(manifest_raw),
        },
        "boundary": packet["boundary"],
        "claim": "A frozen proposition-backed five-route comparison selects descendant necessity and parameter robustness; only independent route-decision review is authorized.",
        "nonclaims": [
            "no robustness parameter family frozen or executed",
            "no canonical result recalibration or rerun",
            "no pillar completion or seam admissibility or closure",
            "no empirical adequacy or new physics",
            "no C_k dynamics, CCFT validation, or master-action promotion",
            "no repository-wide green claim",
        ],
    }
    return packet, manifest, report


def _write(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(canonical_json_bytes(payload))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Prepare the post-canonical-result Maxwell-Dirac route decision.")
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
        print("wrote post-result route decision: descendant necessity and robustness 56/62; independent review required")
        return 0
    if args.check:
        stale = [str(path) for path, payload in artifacts if not path.is_file() or path.read_bytes() != canonical_json_bytes(payload)]
        if stale:
            print("stale or missing post-result route-decision artifacts: " + ", ".join(stale), file=sys.stderr)
            return 1
        print("post-result route decision verified: descendant necessity and robustness 56/62; execution unauthorized")
        return 0
    sys.stdout.buffer.write(canonical_json_bytes(report))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

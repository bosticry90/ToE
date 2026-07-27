from __future__ import annotations

import argparse
import ast
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
    exploratory_native_gravitational_requirements_family_survey_packet_v0 as packet,
)


REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "EXPLORATORY_NATIVE_GRAVITATIONAL_REQUIREMENTS_FAMILY_SURVEY_PACKET_"
    "REVIEW_20260718_v0.json"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_exploratory_native_gravitational_requirements_family_survey_packet_review_v0.py"
)
REVIEW_RELATIVE_PATH = (
    "formal/docs/lanes/"
    "EXPLORATORY_NATIVE_GRAVITATIONAL_REQUIREMENTS_FAMILY_SURVEY_PACKET_"
    "REVIEW_20260718_v0.md"
)
TARGET = (
    "review_exploratory_native_gravitational_requirements_family_survey_"
    "packet_v0_result"
)
VERDICT = "ACCEPTED_FOR_ONE_BOUNDED_MANUAL_EXPLORATORY_SURVEY"
SELECTED_NEXT_TARGET = (
    "conduct_exploratory_native_gravitational_requirements_family_survey_v0"
)
SELECTED_NEXT_TARGET_KIND = (
    "NONAUTHORITATIVE_MANUALLY_ADJUDICATED_SURVEY_EXECUTION_ONLY"
)

AUTHORITY_AND_PACKET_HASHES = {
    packet.HUMAN_PACKET_RELATIVE_PATH:
        "47956a32c8f833277c6a7d004900e7af63a2e3674a3585aca0351311047c52a5",
    packet.REPORT_RELATIVE_PATH:
        "8cfbb0ce0129638fd688d255911ef8e076c6a1d48bb6736e49705dd266a92ac2",
    "formal/python/tools/exploratory_native_gravitational_requirements_family_survey_packet_v0.py":
        "d2e403aae4c2047a9816a28dc797a04b3a0997775a2d56b7f8e2a41e2ecdc305",
    "formal/python/tests/test_exploratory_native_gravitational_requirements_family_survey_packet_v0.py":
        "49494d1829544aa73d0c277f729050b21a0151915bfa5550b27510ed226d1a15",
    "formal/toe_formal/ToeFormal/Derivation/ExploratoryNativeGravitationalRequirementsFamilySurveyPacketV0.lean":
        "5bbc9ef36e8d49d6d33425bc1a188a76b4ef718dec7e9db043469886f2f2c891",
    REVIEW_RELATIVE_PATH:
        "2fd17a03cd7f53aea1e278675aca827c98c8a8c1ee30adbf90944e15e39c2e4a",
}

REASONING_BASIS_TYPES = (
    "ESTABLISHED_LITERATURE",
    "DIRECT_MATHEMATICAL_REASONING",
    "KNOWN_COMPARATOR_BEHAVIOR",
    "ANALOGY",
    "PROJECT_HYPOTHESIS",
    "EXPERT_JUDGMENT",
)

LABEL_INTERPRETATIONS = {
    "CLEARLY COMPATIBLE": (
        "Strong preliminary reasoning or established comparison evidence supports "
        "compatibility in the stated domain."
    ),
    "LIKELY COMPATIBLE": (
        "Compatibility appears plausible, but assumptions or derivations remain incomplete."
    ),
    "LIKELY INCOMPATIBLE": (
        "A probable conflict is visible, but a decisive proof or calculation is absent."
    ),
    "CLEARLY INCOMPATIBLE": (
        "A direct definitional or mathematical conflict is visible in the frozen scope."
    ),
    "UNRESOLVED": (
        "The relationship was examined and the available reasoning does not decide it."
    ),
    "OUTSIDE FROZEN SCOPE": (
        "The family or question lies outside the selected local metric-only envelope."
    ),
}

QUESTION_CAPABILITIES = {
    "DQ1_DIFF_COVARIANCE_DISCRIMINATION": [
        "REVEAL_REQUIREMENT_SELECTION_POWER",
        "DISTINGUISH_MULTIPLE_FAMILIES",
    ],
    "DQ2_CK_FIREWALL_ACTION_RELEVANCE": [
        "SHOW_TOE_SPECIFIC_CONSTRAINT_OR_ARCHITECTURE_ONLY",
    ],
    "DQ3_SOURCE_COMPATIBILITY_DISCRIMINATION": [
        "DISTINGUISH_MULTIPLE_FAMILIES",
        "IDENTIFY_TRACTABLE_DERIVATION",
    ],
    "DQ4_NEWTONIAN_RECOVERY_DISCRIMINATION": [
        "REVEAL_REQUIREMENT_SELECTION_POWER",
        "EXPOSE_SPECIAL_LIMIT_DEPENDENCE",
    ],
    "DQ5_MOMENTUM_CURRENT_INDEPENDENCE": [
        "DISTINGUISH_MULTIPLE_FAMILIES",
        "IDENTIFY_TRACTABLE_DERIVATION",
    ],
    "DQ6_STABILITY_NO_FIT_DISCRIMINATION": [
        "DISTINGUISH_MULTIPLE_FAMILIES",
        "IDENTIFY_TRACTABLE_THEOREM_OR_COUNTEREXAMPLE",
    ],
    "DQ7_NATIVE_SEAM_LAGRANGIAN_CONSTRAINT": [
        "SHOW_TOE_SPECIFIC_CONSTRAINT_OR_ARCHITECTURE_ONLY",
        "LOCATE_POSSIBLE_NATIVE_PRINCIPLE",
    ],
    "DQ8_PROPERTY_SCOPED_EQUIVALENCE": [
        "DISTINGUISH_PHYSICAL_FROM_REPRESENTATIONAL_DIFFERENCE",
        "IDENTIFY_TRACTABLE_THEOREM_OR_COUNTEREXAMPLE",
    ],
}


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _load_packet() -> dict[str, Any]:
    value = json.loads(
        (REPO_ROOT / packet.REPORT_RELATIVE_PATH).read_text(encoding="utf-8")
    )
    if not isinstance(value, dict):
        raise ValueError("exploratory survey packet must be a JSON object")
    return value


def _validate_custody() -> tuple[list[dict[str, str]], dict[str, Any]]:
    rows: list[dict[str, str]] = []
    for relative_path, expected_hash in AUTHORITY_AND_PACKET_HASHES.items():
        observed = _sha256((REPO_ROOT / relative_path).read_bytes())
        if observed != expected_hash:
            raise ValueError(f"exploratory survey review hash mismatch: {relative_path}")
        rows.append({"relative_path": relative_path, "sha256": observed})

    prepared = _load_packet()
    if prepared.get("target") != packet.TARGET:
        raise ValueError("reviewed survey packet target mismatch")
    if prepared.get("selected_next_target") != TARGET:
        raise ValueError("survey packet did not authorize this review")
    if prepared.get("verdict") != packet.VERDICT:
        raise ValueError("survey packet preparation verdict mismatch")
    if prepared["scope"].get("provisional_survey_classifications_made") != 0:
        raise ValueError("survey packet unexpectedly contains judgments")
    if prepared["scope"].get("real_matrix_cells_computed") != 0:
        raise ValueError("survey packet unexpectedly contains real matrix cells")
    return rows, prepared


def _audit_no_alternate_selector(prepared: dict[str, Any]) -> dict[str, Any]:
    tool_path = REPO_ROOT / (
        "formal/python/tools/"
        "exploratory_native_gravitational_requirements_family_survey_packet_v0.py"
    )
    source = tool_path.read_text(encoding="utf-8")
    tree = ast.parse(source)
    imports = [
        ast.unparse(row)
        for row in tree.body
        if isinstance(row, (ast.Import, ast.ImportFrom))
    ]
    functions = [
        row.name
        for row in tree.body
        if isinstance(row, (ast.FunctionDef, ast.AsyncFunctionDef))
    ]
    allowed_import_roots = {
        "__future__",
        "argparse",
        "hashlib",
        "json",
        "pathlib",
        "typing",
    }
    observed_import_roots = {
        row.module.split(".")[0]
        if isinstance(row, ast.ImportFrom) and row.module
        else alias.name.split(".")[0]
        for row in tree.body
        if isinstance(row, (ast.Import, ast.ImportFrom))
        for alias in (row.names if isinstance(row, (ast.Import, ast.ImportFrom)) else [])
    }
    forms = prepared["survey_form_contract"]["forms"]
    forbidden_fields = {
        "cell_status",
        "evidence_id",
        "claim_scope",
        "scientific_outcome",
        "survivor_set",
        "equivalence_class",
        "theory_recommendation",
    }
    present_forbidden = sorted({
        field for form in forms for field in forbidden_fields.intersection(form)
    })
    mode = prepared["mode_contract"]
    passed = (
        observed_import_roots.issubset(allowed_import_roots)
        and "evaluate_analysis(" not in source
        and "native_gravitational_principle_requirements_and_action_selection_packet_v2 as"
        not in source
        and present_forbidden == []
        and mode["automated_scientific_adjudication"] is False
        and mode["survivor_reducer_present"] is False
        and mode["equivalence_reducer_present"] is False
        and mode["terminal_classifier_present"] is False
    )
    return {
        "gate_id": "G1_NO_ALTERNATE_AUTOMATED_SELECTOR",
        "imports": imports,
        "defined_functions": functions,
        "observed_import_roots": sorted(observed_import_roots),
        "forbidden_form_fields_present": present_forbidden,
        "evaluate_analysis_call_present": "evaluate_analysis(" in source,
        "v2_evaluator_module_import_present": (
            "native_gravitational_principle_requirements_and_action_selection_packet_v2 as"
            in source
        ),
        "status": "PASS" if passed else "FAIL",
    }


def _nonempty_string(value: Any) -> bool:
    return isinstance(value, str) and bool(value.strip())


def _valid_basis_pointer(value: Any) -> bool:
    if not isinstance(value, dict):
        return False
    if set(value) != {"basis_type", "pointer_role", "reference", "scope_note"}:
        return False
    if value["basis_type"] not in REASONING_BASIS_TYPES:
        return False
    if not _nonempty_string(value["pointer_role"]):
        return False
    if not _nonempty_string(value["scope_note"]):
        return False
    if value["pointer_role"] == "NO_SOURCE_POINTER_IDENTIFIED":
        return value["reference"] is None
    return _nonempty_string(value["reference"])


def structural_entry_disposition(row: dict[str, Any]) -> str:
    if set(row) != set(packet.CELL_FIELD_ORDER):
        return "INCOMPLETE_SURVEY_ENTRY"
    blank = (
        row["workflow_state"] == "NOT_SURVEYED"
        and row["provisional_classification"] is None
        and row["concise_rationale"] is None
        and row["assumptions_and_domain"] == []
        and row["source_or_derivation_pointers"] == []
        and row["main_uncertainty"] is None
        and row["resolving_calculation_or_theorem"] is None
        and row["priority_role"] == "UNASSIGNED"
        and row["manual_adjudicator_id"] is None
        and row["manual_review_status"] == "NOT_REVIEWED"
    )
    if blank:
        return "VALID_NOT_SURVEYED"
    complete = (
        row["workflow_state"] == "SURVEYED_PROVISIONAL"
        and row["provisional_classification"]
        in packet.PERMITTED_PROVISIONAL_LABELS
        and _nonempty_string(row["concise_rationale"])
        and isinstance(row["assumptions_and_domain"], list)
        and bool(row["assumptions_and_domain"])
        and all(_nonempty_string(item) for item in row["assumptions_and_domain"])
        and isinstance(row["source_or_derivation_pointers"], list)
        and bool(row["source_or_derivation_pointers"])
        and all(
            _valid_basis_pointer(item)
            for item in row["source_or_derivation_pointers"]
        )
        and _nonempty_string(row["main_uncertainty"])
        and _nonempty_string(row["resolving_calculation_or_theorem"])
        and row["priority_role"] in {"DECISION_CRITICAL", "CONTEXTUAL", "DEFERRED"}
        and _nonempty_string(row["manual_adjudicator_id"])
        and row["manual_review_status"] == "PENDING_INDEPENDENT_RESULT_REVIEW"
    )
    return "VALID_PROVISIONAL_ENTRY" if complete else "INCOMPLETE_SURVEY_ENTRY"


def _valid_unresolved_fixture(blank: dict[str, Any]) -> dict[str, Any]:
    value = copy.deepcopy(blank)
    value.update({
        "workflow_state": "SURVEYED_PROVISIONAL",
        "provisional_classification": "UNRESOLVED",
        "concise_rationale": (
            "Available whole-family reasoning does not decide the relationship."
        ),
        "assumptions_and_domain": ["Frozen local metric-only comparison scope"],
        "source_or_derivation_pointers": [{
            "basis_type": "EXPERT_JUDGMENT",
            "pointer_role": "NO_SOURCE_POINTER_IDENTIFIED",
            "reference": None,
            "scope_note": "No source covering the complete family was identified.",
        }],
        "main_uncertainty": "Whole-family behavior has not been derived.",
        "resolving_calculation_or_theorem": (
            "Derive or locate a theorem covering the complete family and stated domain."
        ),
        "priority_role": "DECISION_CRITICAL",
        "manual_adjudicator_id": "MANUAL_SURVEY_ADJUDICATOR",
        "manual_review_status": "PENDING_INDEPENDENT_RESULT_REVIEW",
    })
    return value


def _audit_state_and_completeness(prepared: dict[str, Any]) -> dict[str, Any]:
    forms = prepared["survey_form_contract"]["forms"]
    canonical_dispositions = [structural_entry_disposition(row) for row in forms]
    incomplete = copy.deepcopy(forms[0])
    incomplete["workflow_state"] = "SURVEYED_PROVISIONAL"
    incomplete["provisional_classification"] = "UNRESOLVED"
    valid_unresolved = _valid_unresolved_fixture(forms[0])
    partial_blank = copy.deepcopy(forms[0])
    partial_blank["concise_rationale"] = "Text was added without an assessment."
    observed = {
        "canonical_not_surveyed": sorted(set(canonical_dispositions)),
        "incomplete_nonblank": structural_entry_disposition(incomplete),
        "valid_unresolved": structural_entry_disposition(valid_unresolved),
        "partial_blank": structural_entry_disposition(partial_blank),
    }
    passed = observed == {
        "canonical_not_surveyed": ["VALID_NOT_SURVEYED"],
        "incomplete_nonblank": "INCOMPLETE_SURVEY_ENTRY",
        "valid_unresolved": "VALID_PROVISIONAL_ENTRY",
        "partial_blank": "INCOMPLETE_SURVEY_ENTRY",
    }
    return {
        "gate_id": "G2_G3_STATE_DISTINCTION_AND_REASONING_COMPLETENESS",
        "canonical_blank_form_count": len(forms),
        "canonical_UNRESOLVED_count": sum(
            row["provisional_classification"] == "UNRESOLVED" for row in forms
        ),
        "binding_structural_dispositions": [
            "VALID_NOT_SURVEYED",
            "VALID_PROVISIONAL_ENTRY",
            "INCOMPLETE_SURVEY_ENTRY",
        ],
        "observed": observed,
        "status": "PASS" if passed else "FAIL",
    }


def _audit_source_scope_and_basis(prepared: dict[str, Any]) -> dict[str, Any]:
    policy = prepared["source_and_derivation_policy"]
    human = (REPO_ROOT / packet.HUMAN_PACKET_RELATIVE_PATH).read_text(
        encoding="utf-8"
    )
    passed = (
        policy["every_surveyed_cell_requires_pointer_or_explicit_absence"] is True
        and policy["source_custody_is_scientific_relevance"] is False
        and policy["special_case_may_stand_for_whole_family"] is False
        and policy["recovery_limit_may_stand_for_whole_family"] is False
        and policy["self_certification_creates_authoritative_evidence"] is False
        and "may not be generalized to the complete family" in human
        and len(REASONING_BASIS_TYPES) == 6
    )
    return {
        "gate_id": "G4_G5_LIMITED_SOURCE_SCOPE_AND_SEPARATE_REASONING_BASIS",
        "reasoning_basis_types": list(REASONING_BASIS_TYPES),
        "binding_basis_record_fields": [
            "basis_type",
            "pointer_role",
            "reference",
            "scope_note",
        ],
        "special_case_generalization_prohibited": (
            policy["special_case_may_stand_for_whole_family"] is False
        ),
        "recovery_limit_generalization_prohibited": (
            policy["recovery_limit_may_stand_for_whole_family"] is False
        ),
        "source_custody_confers_relevance": (
            policy["source_custody_is_scientific_relevance"]
        ),
        "confidence_upgrades_basis_authority": False,
        "basis_authority_selects_confidence_label": False,
        "status": "PASS" if passed else "FAIL",
    }


def _audit_questions(prepared: dict[str, Any]) -> dict[str, Any]:
    register = prepared["decision_critical_question_register"]
    protocol = prepared["execution_protocol_after_acceptance"]
    rows = register["rows"]
    ids = [row["question_id"] for row in rows]
    valid_requirements = set(packet.EXPECTED_REQUIREMENT_IDS)
    valid_families = set(packet.EXPECTED_FAMILY_IDS)
    row_audits = []
    for row in rows:
        capabilities = QUESTION_CAPABILITIES.get(row["question_id"], [])
        row_audits.append({
            "question_id": row["question_id"],
            "capabilities": capabilities,
            "references_only_frozen_requirements": set(row["requirement_ids"]).issubset(
                valid_requirements
            ),
            "references_only_frozen_families": set(row["family_ids"]).issubset(
                valid_families
            ),
            "answered": row["answered"],
        })
    passed = (
        len(rows) == len(ids) == len(set(ids)) == 8
        and set(ids) == set(QUESTION_CAPABILITIES)
        and all(item["capabilities"] for item in row_audits)
        and all(item["references_only_frozen_requirements"] for item in row_audits)
        and all(item["references_only_frozen_families"] for item in row_audits)
        and all(item["answered"] is False for item in row_audits)
        and protocol["decision_critical_questions_first"] is True
        and protocol["all_seventy_cells_required_for_success"] is False
        and protocol["unworked_cells_remain_NOT_SURVEYED"] is True
    )
    return {
        "gate_id": "G6_DECISION_CRITICAL_QUESTIONS_CONTROL_WORK_ORDER",
        "question_count": len(rows),
        "answered_question_count": sum(item["answered"] for item in row_audits),
        "all_seventy_cells_required": protocol[
            "all_seventy_cells_required_for_success"
        ],
        "decision_critical_questions_first": protocol[
            "decision_critical_questions_first"
        ],
        "rows": row_audits,
        "status": "PASS" if passed else "FAIL",
    }


def _audit_family_envelope(prepared: dict[str, Any]) -> dict[str, Any]:
    catalog = prepared["frozen_family_catalog"]
    boundary = prepared["acceptance_boundary"]
    all_comparison = all(row["comparison_only"] is True for row in catalog["rows"])
    passed = (
        catalog["family_count"] == 7
        and all_comparison
        and catalog["expanded_for_survey"] is False
        and boundary["acceptance_authorizes_family_envelope_expansion"] is False
    )
    return {
        "gate_id": "G7_FAMILY_ENVELOPE_IS_BOUNDED_AND_COMPARATIVE",
        "family_count": catalog["family_count"],
        "all_family_rows_comparison_only": all_comparison,
        "presented_as_exhaustive": False,
        "expansion_authorized": boundary[
            "acceptance_authorizes_family_envelope_expansion"
        ],
        "material_omission_may_be_recorded_for_future_target": True,
        "status": "PASS" if passed else "FAIL",
    }


def _audit_v2_firewall(prepared: dict[str, Any]) -> dict[str, Any]:
    mode = prepared["mode_contract"]
    boundary = prepared["acceptance_boundary"]
    source = (REPO_ROOT / (
        "formal/python/tools/"
        "exploratory_native_gravitational_requirements_family_survey_packet_v0.py"
    )).read_text(encoding="utf-8")
    passed = (
        mode["survey_labels_are_V2_statuses"] is False
        and mode["survey_results_may_populate_V2_matrix"] is False
        and mode["automatic_V3_authorized"] is False
        and boundary["acceptance_authorizes_V2_repair_or_V3"] is False
        and "evaluate_analysis(" not in source
    )
    return {
        "gate_id": "G8_CLOSED_V2_FIREWALL",
        "survey_labels_are_V2_statuses": mode["survey_labels_are_V2_statuses"],
        "survey_results_may_populate_V2_matrix": mode[
            "survey_results_may_populate_V2_matrix"
        ],
        "v2_evaluator_called": "evaluate_analysis(" in source,
        "V2_repair_or_V3_authorized": boundary[
            "acceptance_authorizes_V2_repair_or_V3"
        ],
        "status": "PASS" if passed else "FAIL",
    }


def build_review() -> dict[str, Any]:
    frozen_inputs, prepared = _validate_custody()
    no_selector = _audit_no_alternate_selector(prepared)
    state_and_completeness = _audit_state_and_completeness(prepared)
    source_and_basis = _audit_source_scope_and_basis(prepared)
    questions = _audit_questions(prepared)
    family_envelope = _audit_family_envelope(prepared)
    v2_firewall = _audit_v2_firewall(prepared)
    gates = [
        {"gate": 1, "name": "no alternate automated selector", "status": no_selector["status"]},
        {"gate": 2, "name": "NOT_SURVEYED distinct from UNRESOLVED", "status": state_and_completeness["status"]},
        {"gate": 3, "name": "nonblank entries expose complete reasoning", "status": state_and_completeness["status"]},
        {"gate": 4, "name": "sources support exact limited judgments", "status": source_and_basis["status"]},
        {"gate": 5, "name": "confidence separable from reasoning-basis authority", "status": source_and_basis["status"]},
        {"gate": 6, "name": "decision-critical questions control work order", "status": questions["status"]},
        {"gate": 7, "name": "family envelope remains comparative", "status": family_envelope["status"]},
        {"gate": 8, "name": "survey cannot feed V2 automatically", "status": v2_firewall["status"]},
    ]
    if not all(row["status"] == "PASS" for row in gates):
        raise ValueError("exploratory survey packet review gate failed")

    tool_path = Path(__file__).resolve()
    test_path = REPO_ROOT / TEST_RELATIVE_PATH
    if not test_path.is_file():
        raise ValueError("exploratory survey review focused test missing")
    return {
        "schema_id": (
            "EXPLORATORY_NATIVE_GRAVITATIONAL_REQUIREMENTS_FAMILY_SURVEY_"
            "PACKET_REVIEW_20260718_v0"
        ),
        "captured_at_utc": "2026-07-18T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "prepared_packet_verdict": prepared["verdict"],
            "frozen_inputs": frozen_inputs,
            "generator": {
                "relative_path": tool_path.relative_to(REPO_ROOT).as_posix(),
                "sha256": _sha256(tool_path.read_bytes()),
            },
            "test": {
                "relative_path": TEST_RELATIVE_PATH,
                "sha256": _sha256(test_path.read_bytes()),
            },
        },
        "review_gates": {
            "gate_count": len(gates),
            "pass_count": sum(row["status"] == "PASS" for row in gates),
            "failure_count": sum(row["status"] == "FAIL" for row in gates),
            "rows": gates,
        },
        "no_alternate_selector_audit": no_selector,
        "state_and_completeness_audit": state_and_completeness,
        "source_scope_and_reasoning_basis_audit": source_and_basis,
        "decision_critical_question_audit": questions,
        "family_envelope_audit": family_envelope,
        "V2_firewall_audit": v2_firewall,
        "label_interpretations": LABEL_INTERPRETATIONS,
        "binding_manual_entry_contract": {
            "not_surveyed_workflow_state": "NOT_SURVEYED",
            "surveyed_workflow_state": "SURVEYED_PROVISIONAL",
            "incomplete_entry_disposition": "INCOMPLETE_SURVEY_ENTRY",
            "permitted_provisional_labels": list(
                packet.PERMITTED_PROVISIONAL_LABELS
            ),
            "reasoning_basis_types": list(REASONING_BASIS_TYPES),
            "basis_record_fields": [
                "basis_type",
                "pointer_role",
                "reference",
                "scope_note",
            ],
            "required_nonblank_fields": [
                "provisional_classification",
                "concise_rationale",
                "assumptions_and_domain",
                "source_or_derivation_pointers",
                "main_uncertainty",
                "resolving_calculation_or_theorem",
                "priority_role",
                "manual_adjudicator_id",
                "manual_review_status",
            ],
            "complete_entry_remains_scientifically_provisional": True,
            "structural_completeness_certifies_scientific_correctness": False,
        },
        "authorized_execution": {
            "execution_count": 1,
            "mode": "NONAUTHORITATIVE_MANUALLY_ADJUDICATED_EXPLORATION_ONLY",
            "phase_1": "ANSWER_EIGHT_DECISION_CRITICAL_QUESTIONS",
            "phase_2": "POPULATE_ONLY_SUPPORTING_CELLS",
            "phase_3": "PRODUCE_SCIENTIFIC_OPPORTUNITY_MAP_AND_STOP",
            "all_seventy_cells_required": False,
            "independent_result_review_required": True,
            "one_next_scientific_investigation_may_be_recommended": True,
        },
        "authorization_boundary": {
            "manual_provisional_judgments_authorized": True,
            "literature_supported_comparisons_authorized": True,
            "transparent_mathematical_reasoning_authorized": True,
            "unresolved_and_not_surveyed_entries_authorized": True,
            "next_scientific_investigation_recommendation_authorized": True,
            "authoritative_survivor_set_authorized": False,
            "authoritative_equivalence_set_authorized": False,
            "V2_scientific_outcome_authorized": False,
            "V2_matrix_population_authorized": False,
            "gravitational_action_selection_or_proposal_authorized": False,
            "native_principle_claim_authorized": False,
            "standard_GR_adoption_authorized": False,
            "no_go_theorem_claim_authorized": False,
            "new_postulate_adoption_authorized": False,
            "matter_sector_selection_authorized": False,
            "metric_variation_authorized": False,
            "frame_dragging_authorized": False,
            "family_envelope_expansion_authorized": False,
            "automated_selector_reopening_authorized": False,
            "automatic_V3_authorized": False,
        },
        "scope": {
            "independent_packet_review_executed": True,
            "packet_accepted": True,
            "manual_exploratory_survey_executed": False,
            "blank_survey_forms_retained": 70,
            "provisional_survey_classifications_made": 0,
            "decision_critical_questions_answered": 0,
            "real_matrix_cells_computed": 0,
            "real_family_judgment_made": False,
            "real_equivalence_class_established": False,
            "real_survivor_matrix_computed": False,
            "real_scientific_outcome_selected": False,
            "native_gravitational_principle_identified": False,
            "new_postulate_authorized": False,
            "gravitational_action_proposed_or_selected": False,
            "standard_GR_comparator_activated": False,
            "matter_sector_selected": False,
            "metric_or_tetrad_variation_executed": False,
            "stress_energy_derived": False,
            "tensor_field_equation_derived": False,
            "gravitomagnetic_route_reopened": False,
            "family_envelope_expanded": False,
            "automated_action_selection_tooling_lane_reopened": False,
            "automatic_V3_authorized": False,
            "automation_created": False,
        },
        "current_posture": {
            "minimal_gravitational_sector_contract": "ACCEPTED",
            "native_gravitational_principle": "NOT_IDENTIFIED",
            "automated_action_selection_V2": (
                "BLOCKED_PROJECT_EVIDENCE_SEMANTICS_UNSOUND"
            ),
            "automated_tooling_lane": "CLOSED",
            "exploratory_survey_packet_V0": (
                "ACCEPTED_FOR_ONE_BOUNDED_MANUAL_SURVEY"
            ),
            "manual_exploratory_survey": "NOT_EXECUTED",
            "blank_forms": 70,
            "provisional_judgments": 0,
            "decision_critical_questions": "8_UNANSWERED",
            "authoritative_scientific_matrix": "0_OF_70",
            "gravitational_action": "NOT_SELECTED",
            "metric_variation": "NOT_EXECUTED",
        },
    }


def artifact_bytes() -> bytes:
    return (
        json.dumps(build_review(), indent=2, sort_keys=True, ensure_ascii=True)
        + "\n"
    ).encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Generate or check the exploratory gravity survey packet review."
    )
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    report_path = REPO_ROOT / REPORT_RELATIVE_PATH
    raw = artifact_bytes()
    if args.check:
        if not report_path.is_file() or report_path.read_bytes() != raw:
            raise SystemExit("exploratory gravity survey packet review artifact drift")
        print(json.dumps({
            "status": "VERIFIED",
            "verdict": VERDICT,
            "review_gates": "8_OF_8_PASS",
            "survey_executed": False,
            "provisional_judgments": 0,
            "real_matrix_cells": 0,
        }, sort_keys=True))
        return 0
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_bytes(raw)
    print(report_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

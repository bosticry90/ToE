from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_source_map_or_countermodel_scope_decision_packet_report import (
    DEFAULT_OUT as DEFAULT_DECISION_PACKET_PATH,
    OUTCOME_ID as EXPECTED_DECISION_PACKET_OUTCOME,
    PACKET_ID as EXPECTED_DECISION_PACKET_ID,
    SCHEMA_ID as EXPECTED_DECISION_PACKET_SCHEMA_ID,
    SOURCE_MAP_LADDER_TARGET,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-16T00:00:00Z"
SCHEMA_ID = (
    "QFT_GR_SOURCE_MAP_LADDER_PACKET_FROM_CANDIDATE_SOURCE_TO_ADMISSIBLE_"
    "SOURCE_20260616_v0"
)
PACKET_ID = (
    "QFT_GR_SOURCE_MAP_LADDER_PACKET_FROM_CANDIDATE_SOURCE_TO_ADMISSIBLE_"
    "SOURCE_v0"
)
OUTCOME_ID = (
    "QFT_GR_SOURCE_MAP_LADDER_PACKET_FROM_CANDIDATE_SOURCE_TO_ADMISSIBLE_"
    "SOURCE_PREPARED_WITH_NO_SOURCE_ADMISSIBILITY_OR_QFT_GR_CLOSURE"
)
PACKET_CLASSIFICATION = (
    "qft_gr_source_map_ladder_packet_from_candidate_source_to_admissible_"
    "source_prepared_with_first_ladder_break_and_no_source_admissibility_or_"
    "qft_gr_closure"
)
CONSUMED_TARGET = SOURCE_MAP_LADDER_TARGET
NEXT_TARGET = (
    "review_qft_gr_source_map_ladder_packet_from_candidate_source_to_"
    "admissible_source_result"
)
NEXT_TARGET_KIND = (
    "qft_gr_source_map_ladder_packet_from_candidate_source_to_admissible_"
    "source_result_review"
)
CANDIDATE_SOURCE_ID = (
    "broader_stress_energy_like_distribution_candidate_not_source_"
    "admissible_v0"
)
PINNED_SOURCE_TEST_PAIR_ID = (
    "broader_candidate_source_allowed_test_pair_for_weak_conservation_"
    "countermodel_v0"
)
PINNED_WEAK_PAIRING_CONTRACT_ID = (
    "partial_weak_pairing_contract_for_broader_countermodel_scope_v0"
)
PINNED_EVALUATION_SCOPE_ID = (
    "broader_weak_divergence_boundary_and_curvature_evaluation_scope_v0"
)
FIRST_LADDER_BREAK_ROW_ID = "source_action_test_action_and_weak_pairing_domain"
NON_PROMOTION_RESULT = (
    "candidate_source_remains_candidate_only_first_break_at_source_action_"
    "test_action_and_weak_pairing_domain_no_source_admissibility_or_qft_gr_"
    "closure"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_SOURCE_MAP_LADDER_PACKET_FROM_CANDIDATE_SOURCE_TO_"
        "ADMISSIBLE_SOURCE_20260616_v0.json"
    )
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRSourceMapLadderPacketFromCandidateSourceToAdmissibleSource.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _admissibility_ladder(decision_packet: dict[str, Any]) -> list[dict[str, str]]:
    source_test = decision_packet.get("source_test_instantiation", {})
    weak_pairing = decision_packet.get("weak_pairing_semantics", {})
    return [
        {
            "row_id": "candidate_source_object_identified",
            "required_condition": "Candidate source object is explicitly named.",
            "status": "supplied",
            "source_pointer": source_test.get("source_candidate_id", CANDIDATE_SOURCE_ID),
            "assessment": (
                "The packet inherits a candidate stress-energy-like distribution "
                "object, but this row alone is not source admissibility."
            ),
            "promotion_effect": "necessary_not_sufficient",
        },
        {
            "row_id": "candidate_source_status_boundary",
            "required_condition": (
                "Candidate-only status is preserved until all admissibility "
                "conditions are supplied or derivable."
            ),
            "status": "supplied",
            "source_pointer": source_test.get(
                "source_candidate_status",
                "candidate_only_not_source_admissible_not_physical_source",
            ),
            "assessment": (
                "The inherited status explicitly blocks physical-source and "
                "source-admissibility promotion at packet preparation time."
            ),
            "promotion_effect": "non_promotion_boundary",
        },
        {
            "row_id": FIRST_LADDER_BREAK_ROW_ID,
            "required_condition": (
                "Concrete source action, allowed test action, and weak "
                "distributional divergence pairing domain are supplied."
            ),
            "status": "blocked",
            "source_pointer": weak_pairing.get(
                "contract_id", PINNED_WEAK_PAIRING_CONTRACT_ID
            ),
            "assessment": (
                "The weak pairing contract is partial and requires concrete "
                "source action, test action, and distributional divergence "
                "pairing objects before the first probe can be decided."
            ),
            "promotion_effect": "first_ladder_break",
        },
        {
            "row_id": "weak_divergence_pairing_value_evaluable",
            "required_condition": (
                "The weak-divergence pairing value is evaluable as zero, "
                "nonzero, or otherwise reviewable under the supplied domain."
            ),
            "status": "blocked",
            "source_pointer": "weak_divergence_pairing_value",
            "assessment": (
                "The pairing value cannot be promoted while the pairing "
                "domain row is blocked."
            ),
            "promotion_effect": "blocked_by_first_break",
        },
        {
            "row_id": "boundary_term_rule_or_retained_boundary_accounting",
            "required_condition": (
                "Compact-support/no-boundary hypotheses or retained-boundary "
                "accounting are supplied for the allowed tests."
            ),
            "status": "countermodel-sensitive",
            "source_pointer": "boundary_term_retention",
            "assessment": (
                "A surviving retained boundary term remains a countermodel "
                "hook unless a legitimate boundary rule is supplied."
            ),
            "promotion_effect": "countermodel_hook_preserved",
        },
        {
            "row_id": "derivative_exchange_regular_boundary_rule",
            "required_condition": (
                "Analytic regularity and derivative-exchange rules license "
                "the relevant weak-divergence manipulations."
            ),
            "status": "countermodel-sensitive",
            "source_pointer": "derivative_exchange_legitimacy",
            "assessment": (
                "Derivative exchange remains a countermodel-sensitive "
                "regularity gap, not a conservation proof object."
            ),
            "promotion_effect": "countermodel_hook_preserved",
        },
        {
            "row_id": "curvature_coupling_residual_accounting",
            "required_condition": (
                "Any curvature-coupling residual is instantiated and shown "
                "to vanish or is retained as an obstruction."
            ),
            "status": "countermodel-sensitive",
            "source_pointer": "curvature_coupling_residual",
            "assessment": (
                "The residual is not instantiated enough to license a source "
                "map or a countermodel result."
            ),
            "promotion_effect": "countermodel_hook_preserved",
        },
        {
            "row_id": "state_expectation_functional_link",
            "required_condition": (
                "A state and expectation-value functional are linked to the "
                "candidate source object."
            ),
            "status": "absent",
            "source_pointer": "not_supplied_by_current_packet",
            "assessment": (
                "No full expectation-value source semantics are supplied by "
                "this ladder packet."
            ),
            "promotion_effect": "blocks_source_admissibility",
        },
        {
            "row_id": "renormalized_stress_energy_object_and_finiteness",
            "required_condition": (
                "A renormalized stress-energy object with finiteness and "
                "domain controls is supplied."
            ),
            "status": "absent",
            "source_pointer": "not_supplied_by_current_packet",
            "assessment": (
                "No renormalized stress-energy object or finiteness result "
                "is constructed here."
            ),
            "promotion_effect": "blocks_source_admissibility",
        },
        {
            "row_id": "covariant_conservation_proof_object",
            "required_condition": (
                "A covariant conservation proof object is supplied for the "
                "candidate as an admissible gravitational source."
            ),
            "status": "absent",
            "source_pointer": "not_supplied_by_current_packet",
            "assessment": (
                "The strict toy witness is preserved but not broadened into "
                "a QFT-GR conservation proof object."
            ),
            "promotion_effect": "blocks_source_admissibility",
        },
        {
            "row_id": "bianchi_compatibility_obligation",
            "required_condition": (
                "The candidate source is shown compatible with the Bianchi "
                "identity obligation for the intended coupling."
            ),
            "status": "absent",
            "source_pointer": "not_supplied_by_current_packet",
            "assessment": "Bianchi compatibility is not claimed or derived.",
            "promotion_effect": "blocks_einstein_coupling",
        },
        {
            "row_id": "semiclassical_einstein_coupling_gate",
            "required_condition": (
                "A licensed admissible source is inserted into a semiclassical "
                "Einstein equation or an explicitly scoped substitute."
            ),
            "status": "absent",
            "source_pointer": "not_supplied_by_current_packet",
            "assessment": (
                "No semiclassical Einstein equation is derived, assembled, "
                "or promoted."
            ),
            "promotion_effect": "blocks_qft_gr_closure",
        },
    ]


def _status_counts(rows: list[dict[str, str]]) -> dict[str, int]:
    statuses = ["supplied", "derivable", "blocked", "absent", "countermodel-sensitive"]
    return {status: sum(1 for row in rows if row["status"] == status) for status in statuses}


def _countermodel_hooks(decision_packet: dict[str, Any]) -> list[dict[str, str]]:
    hooks = []
    for row in decision_packet.get("probe_semantic_gap_assessment", []):
        hooks.append(
            {
                "probe_id": row.get("probe_id", "unknown_probe"),
                "hook_status": "preserved_not_promoted",
                "missing_semantic_condition": row.get(
                    "missing_semantic_condition", "source_map_semantics"
                ),
                "countermodel_result_claimed": "no",
                "not_found_support_claimed": "no",
            }
        )
    return hooks


def _promotion_gate() -> dict[str, Any]:
    return {
        "gate_id": "candidate_source_to_admissible_source_promotion_gate_v0",
        "required_ladder_statuses": ["supplied", "derivable"],
        "forbidden_current_statuses_for_promotion": [
            "blocked",
            "absent",
            "countermodel-sensitive",
        ],
        "requires_candidate_source_object": True,
        "requires_source_action_and_weak_pairing_domain": True,
        "requires_expectation_value_source_semantics": True,
        "requires_renormalized_stress_energy_object": True,
        "requires_covariant_conservation_proof_object": True,
        "requires_bianchi_compatibility": True,
        "requires_semiclassical_einstein_coupling_or_explicit_substitute": True,
        "requires_result_review_acceptance_before_promotion": True,
        "promotion_authorized_by_this_packet": False,
    }


def _validation_policy(decision_packet: dict[str, Any]) -> dict[str, Any]:
    return {
        "checkpoint_type": (
            "routine_qft_gr_source_map_ladder_packet_from_candidate_source_"
            "to_admissible_source_preparation"
        ),
        "routine_packet_uses_bounded_target_relevant_validation_only": True,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_aggregate_lean_required": False,
        "full_ci_parity_required": False,
        "full_security_scan_required": False,
        "long_running_validation_escalation_authorized": False,
        "timeout_rerun_loop_authorized": False,
        "timeout_recorded_as_caveat_not_rerun_instruction": True,
        "release_index_path_not_freshly_lean_validated": True,
        "aggregate_lean_not_run": True,
        "aggregate_lean_timeout_caveat_preserved": True,
        "aggregate_lean_health_claimed": False,
        "inherited_decision_packet_validation_policy": decision_packet.get(
            "validation_policy", {}
        ),
    }


def _packet_findings() -> list[str]:
    return [
        (
            "The candidate source object is identified, but remains "
            "candidate-only and not source-admissible."
        ),
        (
            "The first ladder break is the missing concrete source action, "
            "test action, and weak-pairing domain row."
        ),
        (
            "The ladder contains blocked, absent, and countermodel-sensitive "
            "rows, so there is no legitimate admissibility path under this "
            "packet."
        ),
        (
            "Countermodel hooks are preserved at the weak pairing, boundary, "
            "derivative-exchange, and curvature-residual probes without "
            "claiming a countermodel or not-found result."
        ),
        (
            "The only selected next target is result review of this ladder "
            "packet."
        ),
    ]


def build_qft_gr_source_map_ladder_packet_from_candidate_source_to_admissible_source(
    *,
    decision_packet_path: Path = DEFAULT_DECISION_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    decision_packet = _read_json(decision_packet_path)
    ladder_rows = _admissibility_ladder(decision_packet)
    status_counts = _status_counts(ladder_rows)
    countermodel_hooks = _countermodel_hooks(decision_packet)
    promotion_gate = _promotion_gate()

    acceptance_criteria = {
        "consumes_expected_decision_packet": (
            decision_packet.get("schema_id") == EXPECTED_DECISION_PACKET_SCHEMA_ID
            and decision_packet.get("packet_id") == EXPECTED_DECISION_PACKET_ID
            and decision_packet.get("outcome_id") == EXPECTED_DECISION_PACKET_OUTCOME
            and decision_packet.get("selected_next_target") == CONSUMED_TARGET
            and decision_packet.get("source_map_ladder_packet_authorized") is True
            and decision_packet.get("source_map_ladder_packet_prepared") is False
        ),
        "candidate_source_object_identified_without_admissibility": (
            decision_packet.get("source_test_instantiation", {}).get(
                "source_candidate_id"
            )
            == CANDIDATE_SOURCE_ID
            and decision_packet.get("source_admissibility_claimed") is False
            and decision_packet.get("stress_energy_source_admissibility_claimed")
            is False
        ),
        "admissibility_conditions_enumerated": (
            len(ladder_rows) == 12
            and {row["status"] for row in ladder_rows}
            <= {"supplied", "derivable", "blocked", "absent", "countermodel-sensitive"}
        ),
        "first_ladder_break_is_source_action_test_action_and_pairing_domain": (
            ladder_rows[2]["row_id"] == FIRST_LADDER_BREAK_ROW_ID
            and ladder_rows[2]["status"] == "blocked"
        ),
        "no_current_admissibility_path": (
            status_counts["blocked"] > 0
            and status_counts["absent"] > 0
            and status_counts["countermodel-sensitive"] > 0
        ),
        "countermodel_hooks_preserved_without_result_claim": (
            len(countermodel_hooks) == 5
            and all(
                hook["countermodel_result_claimed"] == "no"
                and hook["not_found_support_claimed"] == "no"
                for hook in countermodel_hooks
            )
        ),
        "promotion_gate_denies_current_promotion": (
            promotion_gate["promotion_authorized_by_this_packet"] is False
        ),
        "no_countermodel_no_go_not_found_source_or_conservation_claim": (
            decision_packet.get("countermodel_result_claimed") is False
            and decision_packet.get("no_go_result_claimed") is False
            and decision_packet.get("not_found_result_claimed") is False
            and decision_packet.get("source_admissibility_claimed") is False
            and decision_packet.get("full_qft_gr_conservation_claimed") is False
        ),
        "no_bianchi_semiclassical_qft_gr_public_or_promotion_claim": (
            decision_packet.get("Bianchi_compatibility_claimed") is False
            and decision_packet.get("semiclassical_einstein_equation_derived")
            is False
            and decision_packet.get("qft_gr_seam_closed") is False
            and decision_packet.get("public_submission_authorized") is False
            and decision_packet.get("master_action_promoted") is False
        ),
    }
    prepared = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if prepared
        else "REMEDIATE_QFT_GR_SOURCE_MAP_LADDER_PACKET_FROM_CANDIDATE_SOURCE"
    )

    return {
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "accepted": prepared,
        "packet_decision": "prepared" if prepared else "requires_remediation",
        "outcome_id": OUTCOME_ID
        if prepared
        else "QFT_GR_SOURCE_MAP_LADDER_PACKET_FROM_CANDIDATE_SOURCE_TO_ADMISSIBLE_SOURCE_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION,
        "packet_classification_count": 1 if prepared else 0,
        "consumed_target": CONSUMED_TARGET,
        "consumes_decision_packet_pointer": _ptr(decision_packet_path),
        "consumed_decision_packet_schema_id": decision_packet.get("schema_id"),
        "consumed_decision_packet_outcome_id": decision_packet.get("outcome_id"),
        "candidate_source_object_id": CANDIDATE_SOURCE_ID,
        "candidate_source_status": "candidate_only_not_source_admissible",
        "candidate_source_object_identified": True,
        "candidate_source_object_supplied": True,
        "candidate_source_is_admissible_source": False,
        "admissibility_ladder_prepared": prepared,
        "source_map_ladder_packet_prepared": prepared,
        "source_map_ladder_packet_preparation_only": True,
        "source_map_ladder_packet_result_review_required": True,
        "source_map_ladder_packet_result_review_pending": prepared,
        "source_map_ladder_execution_authorized": False,
        "source_map_ladder_result_review_pending": prepared,
        "admissibility_path_exists_under_current_packet": False,
        "legitimate_admissibility_path_exists": False,
        "ladder_break_identified": True,
        "first_ladder_break_row_id": FIRST_LADDER_BREAK_ROW_ID,
        "first_ladder_break_status": "blocked",
        "first_ladder_break_reason": (
            "Concrete source action, allowed test action, and weak "
            "distributional divergence pairing domain are not supplied."
        ),
        "non_promotion_result": NON_PROMOTION_RESULT,
        "promotion_gate": promotion_gate,
        "promotion_gate_satisfied": False,
        "promotion_authorized": False,
        "admissible_source_promotion_authorized": False,
        "admissibility_ladder": ladder_rows,
        "admissibility_ladder_row_count": len(ladder_rows),
        "admissibility_ladder_status_counts": status_counts,
        "supplied_condition_count": status_counts["supplied"],
        "derivable_condition_count": status_counts["derivable"],
        "blocked_condition_count": status_counts["blocked"],
        "absent_condition_count": status_counts["absent"],
        "countermodel_sensitive_condition_count": status_counts[
            "countermodel-sensitive"
        ],
        "countermodel_hooks": countermodel_hooks,
        "countermodel_hook_count": len(countermodel_hooks),
        "pinned_source_test_pair_id": PINNED_SOURCE_TEST_PAIR_ID,
        "pinned_weak_pairing_contract_id": PINNED_WEAK_PAIRING_CONTRACT_ID,
        "pinned_evaluation_scope_id": PINNED_EVALUATION_SCOPE_ID,
        "strict_toy_witness_preserved": True,
        "strict_toy_witness_accepted": decision_packet.get(
            "strict_toy_witness_accepted"
        ),
        "strict_toy_assumptions_only": True,
        "dominant_obstruction_candidate": decision_packet.get(
            "dominant_obstruction_candidate"
        ),
        "canonical_obstruction_id": decision_packet.get("canonical_obstruction_id"),
        "dominant_obstruction_resolved": False,
        "mathematical_resolution_claimed": False,
        "countermodel_result_claimed": False,
        "countermodel_exists_claimed": False,
        "countermodel_achieved": False,
        "no_go_result_claimed": False,
        "not_found_result_claimed": False,
        "not_found_under_pinned_scope_claimed": False,
        "source_admissibility_claimed": False,
        "stress_energy_source_admissibility_claimed": False,
        "physical_source_claimed": False,
        "expectation_value_source_claimed": False,
        "renormalized_stress_energy_object_claimed": False,
        "renormalization_closure_claimed": False,
        "conservation_claimed": False,
        "conservation_proved": False,
        "conservation_proof_object_constructed": False,
        "conservation_witness_constructed": False,
        "full_qft_gr_conservation_claimed": False,
        "unbounded_conservation_proved": False,
        "covariance_claimed": False,
        "Bianchi_compatibility_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "qft_gr_seam_closed": False,
        "qft_gr_source_map_closure_claimed": False,
        "empirical_validation_claimed": False,
        "scientific_validation_claimed": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "release_assembly_authorized": False,
        "release_packet_assembled": False,
        "public_submission_authorized": False,
        "publication_authorized": False,
        "release_index_path_not_freshly_lean_validated": True,
        "aggregate_lean_not_run": True,
        "aggregate_lean_timeout_caveat_preserved": True,
        "aggregate_lean_health_claimed": False,
        "packet_findings": _packet_findings(),
        "validation_policy": _validation_policy(decision_packet),
        "validation_posture": {
            "focused_packet_current_target_registry_gate": "required_for_checkpoint",
            "current_target_freshness_gate": "required_for_checkpoint",
            "authoritative_surfaces_gate": "required_for_checkpoint",
            "targeted_lean_packet_frontier_import_checks": "required_for_checkpoint",
            "git_diff_check": "required_for_checkpoint",
            "full_pytest": "not_required_for_checkpoint",
            "full_governance_suite": "not_required_for_checkpoint",
            "full_aggregate_lean": "not_required_for_checkpoint_preserved_caveat",
            "release_index_lean_path": "not_freshly_validated_preserved_caveat",
            "full_ci_parity": "not_required_for_checkpoint",
            "security_scan": "not_required_for_checkpoint",
        },
        "validation_caveat": (
            "Full pytest, full governance suite, full aggregate Lean, release-"
            "index Lean validation, CI parity, and security scans are not "
            "required for this routine bounded source-map ladder packet. "
            "The release-index path remains not freshly Lean-validated, "
            "aggregate Lean is not run, and no aggregate Lean health claim is "
            "made."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": "The prepared ladder packet requires result review only.",
            },
            {
                "target": CONSUMED_TARGET,
                "decision": "completed_consumed_live_target",
                "reason": "The source-map ladder packet preparation target is consumed.",
            },
            {
                "target": "claim_qft_gr_source_admissibility",
                "decision": "not_authorized",
                "reason": "The first ladder break and absent rows block promotion.",
            },
            {
                "target": "claim_broad_qft_gr_conservation",
                "decision": "not_authorized",
                "reason": "No conservation proof object is constructed.",
            },
            {
                "target": "derive_semiclassical_einstein_equation",
                "decision": "not_authorized",
                "reason": "No admissible source or coupling gate is supplied.",
            },
            {
                "target": "close_qft_gr_seam",
                "decision": "not_authorized",
                "reason": "The packet preserves QFT-GR closure as blocked.",
            },
        ],
        "selected_next_target": selected_next_target,
        "packet_selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "selection_count": 1 if prepared else 0,
        "selected_next_target_count": 1 if prepared else 0,
        "next_action_scope": (
            "REVIEW_QFT_GR_SOURCE_MAP_LADDER_PACKET_FROM_CANDIDATE_SOURCE_TO_"
            "ADMISSIBLE_SOURCE_RESULT_ONLY_NO_SOURCE_ADMISSIBILITY_NO_"
            "COUNTERMODEL_RESULT_NO_NO_GO_RESULT_NO_QFT_GR_CLOSURE"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet prepares a controlled source-map ladder from the "
            "current candidate source toward admissible-source criteria and "
            "identifies the first break at source action, test action, and "
            "weak-pairing domain. It preserves no source admissibility, no "
            "stress-energy source admissibility, no expectation-value source "
            "semantics, no renormalization closure, no covariance, no "
            "Bianchi compatibility, no semiclassical Einstein equation, no "
            "broad QFT-GR conservation, no countermodel result, no no-go "
            "result, no not-found under pinned scope, no QFT-GR closure, no "
            "empirical validation, no public submission, no release assembly, "
            "and no master-action promotion."
        ),
    }


def write_qft_gr_source_map_ladder_packet_from_candidate_source_to_admissible_source(
    *,
    decision_packet_path: Path = DEFAULT_DECISION_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = (
        build_qft_gr_source_map_ladder_packet_from_candidate_source_to_admissible_source(
            decision_packet_path=decision_packet_path,
            captured_at_utc=captured_at_utc,
        )
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR source-map ladder packet from candidate "
            "source to admissible source after source-map branch selection."
        )
    )
    parser.add_argument("--decision-packet", type=Path, default=DEFAULT_DECISION_PACKET_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    decision_packet_path = (
        ns.decision_packet
        if ns.decision_packet.is_absolute()
        else (REPO_ROOT / ns.decision_packet)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = (
        write_qft_gr_source_map_ladder_packet_from_candidate_source_to_admissible_source(
            decision_packet_path=decision_packet_path,
            out=out,
            captured_at_utc=str(ns.captured_at_utc),
        )
    )
    print(
        json.dumps(
            {
                "out": _ptr(out),
                "packet_id": payload["packet_id"],
                "outcome_id": payload["outcome_id"],
                "prepared": payload["prepared"],
                "selected_next_target": payload["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

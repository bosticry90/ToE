from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "TOE_CANDIDATE_MASTER_ACTION_CK_FIREWALL_AUTHORITY_RECONCILIATION_PACKET_20260717_v0.json"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_toe_candidate_master_action_ck_firewall_authority_reconciliation_packet_v0.py"
)
CONTRACT_RELATIVE_PATH = (
    "formal/docs/lanes/"
    "TOE_CANDIDATE_MASTER_ACTION_CK_FIREWALL_AUTHORITY_RECONCILIATION_PACKET_20260717_v0.md"
)
TARGET = "prepare_toe_candidate_master_action_ck_firewall_authority_reconciliation_packet_v0"
SELECTED_NEXT_TARGET = (
    "review_toe_candidate_master_action_ck_firewall_authority_reconciliation_packet_v0_result"
)

AUTHORITY_AND_SOURCE_HASHES = {
    "formal/docs/release/TOE_CANDIDATE_MASTER_ACTION_CK_FIREWALL_RESPONSE_SELECTION_20260717_v0.json":
        "916daaa79809a0f7d9ca993e78504b41c995a8c2a0204b94c22d863ff302dac7",
    "formal/docs/paper/TOE_CANDIDATE_MASTER_ACTION_v0.md":
        "23aa11c3784da178097eef8ed7c32f9decf4db038a611e4a16364b9bed2db867",
    "formal/docs/release/MASTER_ACTION_CK_CONSTRAINT_FUNCTIONAL_DEFINITION_PACKET_RESULT_REVIEW_20260618_v0.json":
        "78aea408a5cf0838a63cd13d73e2c07ed716f2d2863daefe11eccfd7c0582860",
    "formal/docs/release/PHI_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_RESULT_REVIEW_20260618_v0.json":
        "b114e5b8764182a6b166eae9aac1a3b9dee3604cc0fe15f24321657b2e9bd48e",
    "formal/docs/release/PHI_BRIDGE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_RESULT_REVIEW_20260618_v0.json":
        "6dfacff078b2ace3b4652aff027f38bd28b2a75916bdb45389dddb1272073c86",
    "formal/docs/release/PHI_TRANSPORT_CONSISTENCY_CK_FUNCTIONAL_EMBEDDING_PACKET_RESULT_REVIEW_20260619_v0.json":
        "a5c8b0542f6e06193886e3c9d9e64d261a560d0e3fbbf545a9d3498fb51435ee",
    "formal/docs/release/TOE_NATIVE_A_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_RESULT_REVIEW_20260622_v0.json":
        "6fa377fb1da03ba4c9f4dc5928a63f3d8eb9f8c07470e00a478520b4e759fedf",
    "formal/docs/release/TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_RESULT_REVIEW_20260622_v0.json":
        "2e8043663f6781564c2c6f31fade5161142ffa22a86bbcd06d85b7f640c0cd11",
    "formal/docs/release/TOE_NATIVE_A_TRANSPORT_CONSISTENCY_CK_FUNCTIONAL_EMBEDDING_PACKET_RESULT_REVIEW_20260623_v0.json":
        "20f82fd70a0139ec709d57b6bc02119246229491a1207b15883339353fedfca3",
    "formal/docs/release/TOE_NATIVE_PSI_A_U1_CEXCHANGE_FUNCTIONAL_EMBEDDING_PACKET_RESULT_REVIEW_20260625_v0.json":
        "122943f1fbf55720ee78b1d9df662f499cefe91c625f0b6ffe1a595b2a581c16",
    "formal/docs/release/MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_AFTER_PHI_A_AND_PSI_A_RESULT_REVIEW_20260626_v0.json":
        "3d148464b39d50ae052866516d30bd3f167e1b80d276f56f593fc698f9e6734d",
    "formal/docs/release/MASTER_ACTION_SURFACE_SELECTION_AFTER_CK_FAMILY_STATUS_SYNTHESIS_20260626_v0.json":
        "54eae29c2e3567a10b0c1b9163b40c1b5db0d5dcc32ec7ba4f1e5e0f95d099a1",
    "formal/docs/release/MASTER_ACTION_CK_FAMILY_GAP_REVIEW_AFTER_PHI_A_AND_PSI_A_RESULT_REVIEW_20260626_v0.json":
        "836adb2246561d9873ebefa7281ed7d76a3f9973dcf87b0a7cd2b70fcbc819a7",
    "formal/docs/release/TOE_CANONICAL_ACTION_PROMOTION_STANDARD_v0.md":
        "664abff716240aa93443578864f83e39c7d62ee483bf3698d924992419a0e9f8",
    "formal/docs/release/PROMOTION_GOVERNANCE_LANE_POLICY_20260418_v0.md":
        "b491ab9f0b93f56cdcb705b568a24dd65ed5d52980c37741f09bbc1dab511a5d",
    "formal/docs/release/DEPRECATED_GATE_RETIREMENT_POLICY_v0.md":
        "5d33980b6668e17bbabb86ca162680d517030a98541583956f382e2a82ce37b7",
    "formal/docs/release/RESEARCH_MODE_AUTHORITY_OWNERSHIP_MATRIX_20260419_v0.md":
        "f08adcd5dd4b91f05fcc1469152170d26074b903adf928f92438ea898453aa85",
    CONTRACT_RELATIVE_PATH:
        "59d325ce8412c799508b13dfebfc5a93ad6a86f62102cdf1ce43b59734519523",
}

FIREWALL_SOURCES = [
    {
        "source_id": "MASTER_ACTION_CK_CONSTRAINT_FUNCTIONAL_DEFINITION_PACKET_RESULT_REVIEW",
        "relative_path": "formal/docs/release/MASTER_ACTION_CK_CONSTRAINT_FUNCTIONAL_DEFINITION_PACKET_RESULT_REVIEW_20260618_v0.json",
        "captured_at_utc": "2026-06-18T00:00:00Z",
        "scope": "CROSS_FAMILY_OPTION_INDEX",
        "effect": "NO_CONCRETE_CK_SELECTED_CK_INACTIVE_UNDEFINED_NO_VARIATION",
    },
    {
        "source_id": "PHI_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_RESULT_REVIEW",
        "relative_path": "formal/docs/release/PHI_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_RESULT_REVIEW_20260618_v0.json",
        "captured_at_utc": "2026-06-18T00:00:00Z",
        "scope": "PHI_SOURCE_LANE",
        "effect": "ADMISSIBILITY_ONLY_NO_ACTION_VARIATION_OR_PROMOTION",
    },
    {
        "source_id": "PHI_BRIDGE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_RESULT_REVIEW",
        "relative_path": "formal/docs/release/PHI_BRIDGE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_RESULT_REVIEW_20260618_v0.json",
        "captured_at_utc": "2026-06-18T00:00:00Z",
        "scope": "PHI_BRIDGE_LANE",
        "effect": "ADMISSIBILITY_ONLY_NO_ACTION_VARIATION_OR_PROMOTION",
    },
    {
        "source_id": "PHI_TRANSPORT_CONSISTENCY_CK_FUNCTIONAL_EMBEDDING_PACKET_RESULT_REVIEW",
        "relative_path": "formal/docs/release/PHI_TRANSPORT_CONSISTENCY_CK_FUNCTIONAL_EMBEDDING_PACKET_RESULT_REVIEW_20260619_v0.json",
        "captured_at_utc": "2026-06-19T00:00:00Z",
        "scope": "PHI_TRANSPORT_LANE",
        "effect": "ADMISSIBILITY_ONLY_NO_ACTION_VARIATION_OR_PROMOTION",
    },
    {
        "source_id": "TOE_NATIVE_A_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_RESULT_REVIEW",
        "relative_path": "formal/docs/release/TOE_NATIVE_A_SOURCE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_RESULT_REVIEW_20260622_v0.json",
        "captured_at_utc": "2026-06-22T00:00:00Z",
        "scope": "A_SOURCE_LANE",
        "effect": "ADMISSIBILITY_ONLY_ACTION_EMBEDDING_NOT_SELECTED",
    },
    {
        "source_id": "TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_RESULT_REVIEW",
        "relative_path": "formal/docs/release/TOE_NATIVE_A_BRIDGE_ADMISSIBILITY_CK_FUNCTIONAL_EMBEDDING_PACKET_RESULT_REVIEW_20260622_v0.json",
        "captured_at_utc": "2026-06-22T00:00:00Z",
        "scope": "A_BRIDGE_LANE",
        "effect": "ADMISSIBILITY_ONLY_ACTION_EMBEDDING_NOT_SELECTED_PENALTY_UNLICENSED",
    },
    {
        "source_id": "TOE_NATIVE_A_TRANSPORT_CONSISTENCY_CK_FUNCTIONAL_EMBEDDING_PACKET_RESULT_REVIEW",
        "relative_path": "formal/docs/release/TOE_NATIVE_A_TRANSPORT_CONSISTENCY_CK_FUNCTIONAL_EMBEDDING_PACKET_RESULT_REVIEW_20260623_v0.json",
        "captured_at_utc": "2026-06-23T00:00:00Z",
        "scope": "A_TRANSPORT_LANE",
        "effect": "ADMISSIBILITY_ONLY_ACTION_EMBEDDING_NOT_SELECTED_PENALTY_UNLICENSED",
    },
    {
        "source_id": "TOE_NATIVE_PSI_A_U1_CEXCHANGE_FUNCTIONAL_EMBEDDING_PACKET_RESULT_REVIEW",
        "relative_path": "formal/docs/release/TOE_NATIVE_PSI_A_U1_CEXCHANGE_FUNCTIONAL_EMBEDDING_PACKET_RESULT_REVIEW_20260625_v0.json",
        "captured_at_utc": "2026-06-25T00:00:00Z",
        "scope": "PSI_A_EXCHANGE_LANE",
        "effect": "ADMISSIBILITY_ONLY_MULTIPLIER_BLOCKED_PENALTY_UNLICENSED_NO_VARIATION",
    },
    {
        "source_id": "MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW",
        "relative_path": "formal/docs/release/MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_AFTER_PHI_A_AND_PSI_A_RESULT_REVIEW_20260626_v0.json",
        "captured_at_utc": "2026-06-26T00:00:00Z",
        "scope": "AGGREGATE_CK_FAMILY_STATUS",
        "effect": "ALL_CK_FAMILIES_ADMISSIBILITY_ONLY_NO_EMBEDDING_OR_VARIATION",
    },
    {
        "source_id": "MASTER_ACTION_SURFACE_SELECTION_AFTER_CK_FAMILY_STATUS_SYNTHESIS",
        "relative_path": "formal/docs/release/MASTER_ACTION_SURFACE_SELECTION_AFTER_CK_FAMILY_STATUS_SYNTHESIS_20260626_v0.json",
        "captured_at_utc": "2026-06-26T00:00:00Z",
        "scope": "AGGREGATE_MASTER_ACTION_SELECTOR",
        "effect": "FIREWALL_RETAINED_WORKING_FORM_NONPROMOTION_GAP_REVIEW_SELECTED",
    },
    {
        "source_id": "MASTER_ACTION_CK_FAMILY_GAP_REVIEW_RESULT_REVIEW",
        "relative_path": "formal/docs/release/MASTER_ACTION_CK_FAMILY_GAP_REVIEW_AFTER_PHI_A_AND_PSI_A_RESULT_REVIEW_20260626_v0.json",
        "captured_at_utc": "2026-06-26T00:00:00Z",
        "scope": "AGGREGATE_CK_GAP_REVIEW",
        "effect": "ALL_CK_FAMILIES_ADMISSIBILITY_ONLY_NO_EMBEDDING_OR_VARIATION",
    },
]

SUPERSESSION_PATTERNS = [
    "toe_candidate_master_action_v0",
    "supersed",
    "amend",
    "withdraw",
    "replaces the",
    "replaced by",
    "prior multiplier",
    "earlier action",
    "historical action",
    "no future candidate action",
    "all action surfaces",
]

ALLOWED_OUTCOMES = [
    "CK_FIREWALL_EXPLICITLY_SUPERSEDES_ACTION_TERM",
    "MASTER_ACTION_REMAINS_SCHEMATIC_ONLY",
    "CK_DYNAMICAL_EMBEDDING_REQUIRES_NEW_THEORY_SELECTION",
    "BLOCKED_AUTHORITY_PRECEDENCE_UNRESOLVED",
]

AUTHORITY_RULES = [
    {
        "rule_id": "TOE_CANONICAL_ACTION_PROMOTION_STANDARD_v0",
        "relative_path": "formal/docs/release/TOE_CANONICAL_ACTION_PROMOTION_STANDARD_v0.md",
        "applicability": "CANONICAL_PROMOTION_ONLY_NOT_NONCANONICAL_V0_AMENDMENT",
    },
    {
        "rule_id": "PROMOTION_GOVERNANCE_LANE_POLICY_20260418_v0",
        "relative_path": "formal/docs/release/PROMOTION_GOVERNANCE_LANE_POLICY_20260418_v0.md",
        "applicability": "CANONICAL_MUTATION_AND_FAIL_CLOSED_CONTRADICTION_REVIEW",
    },
    {
        "rule_id": "DEPRECATED_GATE_RETIREMENT_POLICY_v0",
        "relative_path": "formal/docs/release/DEPRECATED_GATE_RETIREMENT_POLICY_v0.md",
        "applicability": "EXPLICIT_SUPERSEDING_PATH_RULE_SCOPED_TO_GOVERNANCE_AND_GATES",
    },
    {
        "rule_id": "RESEARCH_MODE_AUTHORITY_OWNERSHIP_MATRIX_20260419_v0",
        "relative_path": "formal/docs/release/RESEARCH_MODE_AUTHORITY_OWNERSHIP_MATRIX_20260419_v0.md",
        "applicability": "RESEARCH_MODE_CANNOT_MUTATE_CANONICAL_AUTHORITY",
    },
]


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _token_scan() -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    total = 0
    for source in FIREWALL_SOURCES:
        raw = (REPO_ROOT / source["relative_path"]).read_text(encoding="utf-8").lower()
        hits = {pattern: raw.count(pattern) for pattern in SUPERSESSION_PATTERNS if raw.count(pattern)}
        count = sum(hits.values())
        total += count
        rows.append({
            "source_id": source["source_id"],
            "match_count": count,
            "matches": hits,
        })
    return {
        "classification": "PREPARATION_SCAN_NOT_PRECEDENCE_RULING",
        "patterns": SUPERSESSION_PATTERNS,
        "source_count": len(rows),
        "total_match_count": total,
        "rows": rows,
        "preparation_finding": "NO_EXPLICIT_SUPERSESSION_TOKEN_FOUND_IN_PREPARATION_SCAN",
    }


def _validate_authority_and_sources() -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for relative_path, expected_hash in AUTHORITY_AND_SOURCE_HASHES.items():
        observed = _sha256((REPO_ROOT / relative_path).read_bytes())
        if observed != expected_hash:
            raise ValueError(f"C_k reconciliation packet authority mismatch: {relative_path}")
        rows.append({"relative_path": relative_path, "sha256": observed})

    selection = json.loads(
        (REPO_ROOT / "formal/docs/release/TOE_CANDIDATE_MASTER_ACTION_CK_FIREWALL_RESPONSE_SELECTION_20260717_v0.json").read_text(encoding="utf-8")
    )
    if selection.get("selected_next_target") != TARGET:
        raise ValueError("C_k reconciliation packet did not consume selected target")
    if selection.get("verdict") != (
        "SELECTED_CK_FIREWALL_AUTHORITY_RECONCILIATION_PREPARATION"
    ):
        raise ValueError("C_k reconciliation response-selection verdict mismatch")

    action = (
        REPO_ROOT / "formal/docs/paper/TOE_CANDIDATE_MASTER_ACTION_v0.md"
    ).read_text(encoding="utf-8")
    for token in (
        "Classification:\n- `P-POLICY`",
        "working-form artifact only",
        "explicitly non-canonical",
        "sum_k lambda_k * C_k(g, psi, A, phi, rho)",
    ):
        if token not in action:
            raise ValueError(f"original action authority token missing: {token}")

    for source in FIREWALL_SOURCES:
        data = json.loads((REPO_ROOT / source["relative_path"]).read_text(encoding="utf-8"))
        if data.get("captured_at_utc") != source["captured_at_utc"]:
            raise ValueError(f"firewall source date mismatch: {source['source_id']}")
        if data.get("master_action_promoted") is not False:
            raise ValueError(f"firewall source unexpectedly promotes action: {source['source_id']}")

    specific_sources = FIREWALL_SOURCES[1:8]
    for source in specific_sources:
        data = json.loads((REPO_ROOT / source["relative_path"]).read_text(encoding="utf-8"))
        if data.get("admissibility_only_route_selected") is not True:
            raise ValueError(f"specific firewall route mismatch: {source['source_id']}")

    for source in FIREWALL_SOURCES[8:]:
        data = json.loads((REPO_ROOT / source["relative_path"]).read_text(encoding="utf-8"))
        if data.get("all_C_k_families_admissibility_only") is not True:
            raise ValueError(f"aggregate firewall scope mismatch: {source['source_id']}")
        if data.get("C_k_action_embedding_selected") is not False:
            raise ValueError(f"aggregate firewall embedding mismatch: {source['source_id']}")
        if data.get("C_k_action_variation_authorized") is not False:
            raise ValueError(f"aggregate firewall variation mismatch: {source['source_id']}")

    scan = _token_scan()
    if scan["total_match_count"] != 0:
        raise ValueError("preparation supersession scan unexpectedly found a match")

    contract = (REPO_ROOT / CONTRACT_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        "NO_EXPLICIT_SUPERSESSION_TOKEN_FOUND_IN_PREPARATION_SCAN",
        "CK_FIREWALL_EXPLICITLY_SUPERSEDES_ACTION_TERM",
        "BLOCKED_AUTHORITY_PRECEDENCE_UNRESOLVED",
        "Commit or filesystem chronology grants no\nprecedence by itself",
        "This packet authorizes independent reconciliation review only",
    ):
        if token not in contract:
            raise ValueError(f"reconciliation contract token missing: {token}")
    return rows


def build_packet() -> dict[str, Any]:
    authority = _validate_authority_and_sources()
    scan = _token_scan()
    tool_path = Path(__file__).resolve()
    test_path = REPO_ROOT / TEST_RELATIVE_PATH
    if not test_path.exists():
        raise ValueError("C_k reconciliation packet focused test missing")

    return {
        "schema_id": "TOE_CANDIDATE_MASTER_ACTION_CK_FIREWALL_AUTHORITY_RECONCILIATION_PACKET_20260717_v0",
        "captured_at_utc": "2026-07-17T00:00:00Z",
        "target": TARGET,
        "verdict": "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": "INDEPENDENT_AUTHORITY_RECONCILIATION_REVIEW_ONLY",
        "authority": {
            "consumed_selection_verdict": (
                "SELECTED_CK_FIREWALL_AUTHORITY_RECONCILIATION_PREPARATION"
            ),
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
        "scientific_question": (
            "Does explicit project authority establish that the later admissibility-only "
            "C_k firewall removed the displayed multiplier term from the intended "
            "dynamical theory, or does the displayed master action remain unresolved "
            "and therefore nonvariational?"
        ),
        "original_action": {
            "source_id": "TOE_CANDIDATE_MASTER_ACTION_v0",
            "relative_path": "formal/docs/paper/TOE_CANDIDATE_MASTER_ACTION_v0.md",
            "sha256": AUTHORITY_AND_SOURCE_HASHES["formal/docs/paper/TOE_CANDIDATE_MASTER_ACTION_v0.md"],
            "authority_class": "P_POLICY_WORKING_FORM_NONCANONICAL_UNPROMOTED",
            "internal_captured_date": "NOT_DECLARED",
            "displayed_term": "sum_k lambda_k C_k(g,psi,A,phi,rho)",
            "term_presented_as": "SEAM_COMPATIBILITY_BRIDGE_ADMISSIBILITY_TRANSPORT_CONSISTENCY_MULTIPLIER_TERM",
            "complete_C_k_and_lambda_dynamical_contract_supplied": False,
            "repository_history_is_precedence_authority": False,
        },
        "firewall_corpus": {
            "controlling_source_count": len(FIREWALL_SOURCES),
            "source_type": "ACCEPTED_RESULT_REVIEWS_AND_AGGREGATE_STATUS_SELECTION_SURFACES",
            "unreviewed_preparation_packets_are_independent_controlling_authority": False,
            "rows": FIREWALL_SOURCES,
        },
        "explicit_token_scan": scan,
        "existing_authority_rules": {
            "rule_count": len(AUTHORITY_RULES),
            "rows": AUTHORITY_RULES,
            "general_later_timestamp_wins_rule_bound": False,
            "new_precedence_rule_may_be_invented_by_review": False,
        },
        "precedence_evidence_hierarchy": [
            "explicit source-specific supersession, amendment, withdrawal, replacement, or deprecation",
            "existing authority rule with declared scope demonstrably covering the candidate action",
            "current-authority or promotion record explicitly registering and linking a successor",
            "aggregate firewall scope explicitly governing all candidate action surfaces and the earlier multiplier formulation",
        ],
        "insufficient_evidence_alone": [
            "later date",
            "filename order",
            "local-lane admissibility decision",
            "repeated nonpromotion language",
            "scientific convenience",
            "lambda_k=0 workaround",
            "inferred preference for external admissibility",
        ],
        "resolution_contract": {
            "exactly_one_terminal_outcome_required": True,
            "allowed_outcomes": ALLOWED_OUTCOMES,
            "rows": [
                {
                    "outcome": "CK_FIREWALL_EXPLICITLY_SUPERSEDES_ACTION_TERM",
                    "required_evidence": "explicit supersession/amendment path or already-established applicable authority rule",
                    "maximum_next_authority": "prepare_TOE_CANDIDATE_MASTER_ACTION_v1_without_Ck_dynamics",
                },
                {
                    "outcome": "MASTER_ACTION_REMAINS_SCHEMATIC_ONLY",
                    "required_evidence": "authority establishes blueprint or sector-inventory status rather than one executable functional",
                    "maximum_next_authority": "select_next_scientific_target_with_native_continuum_action_not_defined",
                },
                {
                    "outcome": "CK_DYNAMICAL_EMBEDDING_REQUIRES_NEW_THEORY_SELECTION",
                    "required_evidence": "displayed term remains intended and no authority removes it",
                    "maximum_next_authority": "select_whether_to_open_new_ck_dynamical_theory_route",
                },
                {
                    "outcome": "BLOCKED_AUTHORITY_PRECEDENCE_UNRESOLVED",
                    "required_evidence": "conflict persists with no explicit supersession or applicable precedence rule",
                    "maximum_next_authority": "select_fresh_scientific_theory_decision_after_unresolved_precedence",
                },
            ],
        },
        "historical_and_successor_boundaries": {
            "historical_v0_byte_preserved": True,
            "v0_may_be_silently_modified": False,
            "lambda_k_zero_is_resolution": False,
            "C_k_may_be_declared_inactive_inside_v0": False,
            "successor_created_by_packet": False,
            "possible_successor_initial_classification": (
                "WORKING_FORM_NONCANONICAL_UNPROMOTED_UNVARIED"
            ),
            "successor_inherits_v0_variation_or_recovery_claims": False,
        },
        "downstream_gates": {
            "tetrad_and_spin_connection": "CLOSED_NOT_EVALUATED",
            "Dirac_variation": "CLOSED_NOT_EVALUATED",
            "statistical_sector": "CLOSED_NOT_EVALUATED",
            "dimensions_and_constants": "CLOSED_NOT_EVALUATED",
            "boundary_sufficiency": "CLOSED_NOT_EVALUATED",
            "stress_energy_generation": "CLOSED_NOT_EVALUATED",
            "Rep32_relationship": "CLOSED_NOT_EVALUATED",
            "tensor_field_equation": "CLOSED_NOT_DERIVED",
            "gravitomagnetic_recovery": "BLOCKED_FIELD_EQUATION_SURFACE_FAILURE",
        },
        "independent_review_acceptance_criteria": [
            "original action source, class, displayed term, hash, and missing internal date reproduce",
            "all eleven controlling firewall sources and hashes reproduce",
            "local versus aggregate scope is checked for every firewall source",
            "explicit token scan corpus and patterns reproduce",
            "all four authority-rule surfaces and applicability limits reproduce",
            "chronology remains provenance context only",
            "exactly one outcome follows from existing authority rather than new policy",
            "historical v0 remains unchanged",
            "no successor action or downstream calculation is created",
        ],
        "hard_stop": {
            "stopping_rule": (
                "Freeze one original action, eleven firewall authorities, four existing "
                "authority rules, one evidence hierarchy, four outcomes, and stop for "
                "independent reconciliation review."
            ),
            "only_independent_review_next": True,
            "precedence_ruling_authorized_now": False,
            "action_mutation_authorized_now": False,
        },
        "scope": {
            "packet_preparation_only": True,
            "precedence_ruling_executed": False,
            "action_deleted_or_amended": False,
            "action_projected_or_deprecated": False,
            "successor_action_prepared": False,
            "successor_action_created": False,
            "C_k_dynamical_route_selected": False,
            "C_k_embedded_or_varied": False,
            "lambda_k_set_to_zero": False,
            "metric_or_tetrad_variation_executed": False,
            "Einstein_equation_imported": False,
            "standard_GR_comparator_activated": False,
            "gravitomagnetic_route_reopened": False,
            "master_action_promoted": False,
            "GR_pillar_completed": False,
            "seam_closed": False,
            "simulation_executed": False,
            "empirical_analysis_executed": False,
            "repository_migration_executed": False,
            "automation_created": False,
        },
        "claim_ceiling": (
            "Prepared authority-reconciliation contract only. One original action, "
            "eleven accepted firewall authorities, four existing authority-rule "
            "surfaces, an evidence hierarchy, and four outcomes are frozen for "
            "independent review. No precedence decision, action mutation, successor "
            "action, C_k dynamics, variation, GR recovery, promotion, empirical result, "
            "or automation is created."
        ),
    }


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
        if not report_path.exists() or report_path.read_bytes() != raw:
            raise SystemExit("C_k firewall authority reconciliation packet is stale or missing")
        packet = json.loads(raw)
        print(json.dumps({
            "firewall_sources": packet["firewall_corpus"]["controlling_source_count"],
            "outcomes": len(packet["resolution_contract"]["allowed_outcomes"]),
            "scan_matches": packet["explicit_token_scan"]["total_match_count"],
            "status": "CHECKED",
            "verdict": packet["verdict"],
        }, sort_keys=True))
        return 0
    report_path.write_bytes(raw)
    print(report_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

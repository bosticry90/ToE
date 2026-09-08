from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "TOE_CANDIDATE_MASTER_ACTION_CK_FIREWALL_AUTHORITY_RECONCILIATION_"
    "PACKET_REVIEW_20260717_v0.json"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_toe_candidate_master_action_ck_firewall_authority_reconciliation_"
    "packet_review_v0.py"
)
REVIEW_RELATIVE_PATH = (
    "formal/docs/lanes/"
    "TOE_CANDIDATE_MASTER_ACTION_CK_FIREWALL_AUTHORITY_RECONCILIATION_"
    "PACKET_REVIEW_20260717_v0.md"
)
PACKET_REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "TOE_CANDIDATE_MASTER_ACTION_CK_FIREWALL_AUTHORITY_RECONCILIATION_"
    "PACKET_20260717_v0.json"
)
TARGET = (
    "review_toe_candidate_master_action_ck_firewall_authority_"
    "reconciliation_packet_v0_result"
)
VERDICT = "MASTER_ACTION_REMAINS_SCHEMATIC_ONLY"
SELECTED_NEXT_TARGET = (
    "select_next_scientific_target_with_native_continuum_action_not_defined"
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
    "formal/docs/lanes/TOE_CANDIDATE_MASTER_ACTION_CK_FIREWALL_AUTHORITY_RECONCILIATION_PACKET_20260717_v0.md":
        "59d325ce8412c799508b13dfebfc5a93ad6a86f62102cdf1ce43b59734519523",
    PACKET_REPORT_RELATIVE_PATH:
        "9e7e30a3967f3d77c1b348c18e30a97418e851a2d791f5abf061b4bf6c7db9ec",
    "formal/python/tools/toe_candidate_master_action_ck_firewall_authority_reconciliation_packet_v0.py":
        "d87eae3170390dea1642bd3c21799ed68803043d72505dcdaa0c1b89d6103458",
    "formal/python/tests/test_toe_candidate_master_action_ck_firewall_authority_reconciliation_packet_v0.py":
        "10219a01f4e1dbb42956983d3c6c863bca893a711bac17225fe9118e6dd95193",
    "formal/toe_formal/ToeFormal/Derivation/ToeCandidateMasterActionCKFirewallAuthorityReconciliationPacketV0.lean":
        "b7bc6bee1beb14fb0f02a0709777ea6a3280c85796adbe8f979397185eaf071d",
    REVIEW_RELATIVE_PATH:
        "bc7bae0bf6b1d4e5167968e7d2d3687d02d754a4d309921fb44c4032e9d1ccd1",
}

AGGREGATE_SOURCES = [
    {
        "source_id": "MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_RESULT_REVIEW",
        "relative_path": (
            "formal/docs/release/MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_"
            "AFTER_PHI_A_AND_PSI_A_RESULT_REVIEW_20260626_v0.json"
        ),
        "finding": (
            "ALL_CK_FAMILIES_ADMISSIBILITY_ONLY_AND_MASTER_ACTION_REMAINS_"
            "WORKING_FORM_NONCANONICAL_NONPROMOTED_ORGANIZING_SURFACE"
        ),
    },
    {
        "source_id": "MASTER_ACTION_SURFACE_SELECTION_AFTER_CK_FAMILY_STATUS_SYNTHESIS",
        "relative_path": (
            "formal/docs/release/MASTER_ACTION_SURFACE_SELECTION_AFTER_CK_"
            "FAMILY_STATUS_SYNTHESIS_20260626_v0.json"
        ),
        "finding": (
            "ORGANIZING_SURFACE_BOUNDARY_PRESERVED_AND_GAP_REVIEW_SELECTED_"
            "INSTEAD_OF_ACTION_VARIATION"
        ),
    },
    {
        "source_id": "MASTER_ACTION_CK_FAMILY_GAP_REVIEW_RESULT_REVIEW",
        "relative_path": (
            "formal/docs/release/MASTER_ACTION_CK_FAMILY_GAP_REVIEW_AFTER_"
            "PHI_A_AND_PSI_A_RESULT_REVIEW_20260626_v0.json"
        ),
        "finding": (
            "NO_SAFE_CK_ACTION_EMBEDDING_AND_MASTER_ACTION_REMAINS_WORKING_"
            "FORM_NONCANONICAL_NONPROMOTED_ORGANIZING_SURFACE"
        ),
    },
]

AUTHORITY_RULE_APPLICATIONS = [
    {
        "rule_id": "TOE_CANONICAL_ACTION_PROMOTION_STANDARD_v0",
        "result": "BLOCKS_PROMOTION_BUT_DOES_NOT_AMEND_V0",
    },
    {
        "rule_id": "PROMOTION_GOVERNANCE_LANE_POLICY_20260418_v0",
        "result": "FAILS_CLOSED_ON_CONTRADICTION_BUT_DOES_NOT_DELETE_TERM",
    },
    {
        "rule_id": "DEPRECATED_GATE_RETIREMENT_POLICY_v0",
        "result": "EXPLICIT_PATH_REQUIRED_BUT_DIRECT_SCOPE_DOES_NOT_COVER_ACTION",
    },
    {
        "rule_id": "RESEARCH_MODE_AUTHORITY_OWNERSHIP_MATRIX_20260419_v0",
        "result": "RESEARCH_MODE_CANNOT_MUTATE_AUTHORITY_AND_RULE_DOES_NOT_ADJUDICATE_TERM",
    },
]

OUTCOME_ADJUDICATION = [
    {
        "outcome": "CK_FIREWALL_EXPLICITLY_SUPERSEDES_ACTION_TERM",
        "status": "REJECTED",
        "reason": "NO_EXPLICIT_OR_RULE_BASED_SUPERSESSION_PATH",
    },
    {
        "outcome": "MASTER_ACTION_REMAINS_SCHEMATIC_ONLY",
        "status": "SELECTED",
        "reason": "SELF_LIMITED_WORKING_FORM_PLUS_ACCEPTED_AGGREGATE_ORGANIZING_SURFACE_STATUS",
    },
    {
        "outcome": "CK_DYNAMICAL_EMBEDDING_REQUIRES_NEW_THEORY_SELECTION",
        "status": "NOT_SELECTED",
        "reason": "CURRENT_RECORD_DOES_NOT_LICENSE_DISPLAYED_TERM_AS_EXECUTABLE_DYNAMICS",
    },
    {
        "outcome": "BLOCKED_AUTHORITY_PRECEDENCE_UNRESOLVED",
        "status": "NOT_SELECTED",
        "reason": "PRECEDENCE_UNRESOLVED_BUT_MAXIMUM_PRESENT_STATUS_IS_ALREADY_SCHEMATIC_ONLY",
    },
]


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _validate_authority_and_sources() -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for relative_path, expected_hash in AUTHORITY_AND_SOURCE_HASHES.items():
        observed = _sha256((REPO_ROOT / relative_path).read_bytes())
        if observed != expected_hash:
            raise ValueError(f"C_k authority review hash mismatch: {relative_path}")
        rows.append({"relative_path": relative_path, "sha256": observed})

    packet = json.loads(
        (REPO_ROOT / PACKET_REPORT_RELATIVE_PATH).read_text(encoding="utf-8")
    )
    if packet.get("selected_next_target") != TARGET:
        raise ValueError("review did not consume the prepared reconciliation target")
    if packet.get("verdict") != "PREPARED_PENDING_INDEPENDENT_REVIEW":
        raise ValueError("prepared reconciliation verdict mismatch")
    if packet["explicit_token_scan"].get("total_match_count") != 0:
        raise ValueError("explicit supersession scan no longer reproduces")
    if len(packet["firewall_corpus"].get("rows", [])) != 11:
        raise ValueError("eleven-source firewall corpus no longer reproduces")
    if len(packet["existing_authority_rules"].get("rows", [])) != 4:
        raise ValueError("four-rule authority corpus no longer reproduces")
    if packet["resolution_contract"].get("allowed_outcomes") != [
        row["outcome"] for row in OUTCOME_ADJUDICATION
    ]:
        raise ValueError("four-outcome resolution contract mismatch")

    action = (
        REPO_ROOT / "formal/docs/paper/TOE_CANDIDATE_MASTER_ACTION_v0.md"
    ).read_text(encoding="utf-8")
    for token in (
        "working-form artifact only",
        "explicitly non-canonical",
        "sum_k lambda_k * C_k(g, psi, A, phi, rho)",
        "delta S_ToE = 0",
    ):
        if token not in action:
            raise ValueError(f"historical action token missing: {token}")

    organizing_token = (
        "The master action remains a working-form, noncanonical, non-promoted "
        "organizing surface."
    )
    for row in AGGREGATE_SOURCES:
        value = json.loads(
            (REPO_ROOT / row["relative_path"]).read_text(encoding="utf-8")
        )
        if value.get("all_C_k_families_admissibility_only") is not True:
            raise ValueError(f"aggregate firewall status mismatch: {row['source_id']}")
        if value.get("C_k_action_embedding_selected") is not False:
            raise ValueError(f"aggregate embedding status mismatch: {row['source_id']}")
        if organizing_token not in value.get("non_claim_boundary", ""):
            raise ValueError(f"aggregate organizing status missing: {row['source_id']}")

    review = (REPO_ROOT / REVIEW_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        "MASTER_ACTION_REMAINS_SCHEMATIC_ONLY",
        "native continuum action = NOT YET DEFINED",
        "No explicit supersession path",
        "precedence decision is needed merely to keep v0 schematic",
        "all variational and GR-recovery gates remain closed",
    ):
        if token not in review:
            raise ValueError(f"human C_k authority review token missing: {token}")
    return rows


def build_review() -> dict[str, Any]:
    authority = _validate_authority_and_sources()
    tool_path = Path(__file__).resolve()
    test_path = REPO_ROOT / TEST_RELATIVE_PATH
    if not test_path.exists():
        raise ValueError("C_k authority review focused test missing")

    selected = [row for row in OUTCOME_ADJUDICATION if row["status"] == "SELECTED"]
    if len(selected) != 1 or selected[0]["outcome"] != VERDICT:
        raise ValueError("authority review must select exactly the schematic-only outcome")

    return {
        "schema_id": (
            "TOE_CANDIDATE_MASTER_ACTION_CK_FIREWALL_AUTHORITY_"
            "RECONCILIATION_PACKET_REVIEW_20260717_v0"
        ),
        "captured_at_utc": "2026-07-17T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "primary_diagnostic": "NO_EXECUTABLE_NATIVE_CONTINUUM_ACTION_AUTHORITY",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": "FRESH_SCIENTIFIC_TARGET_SELECTION_ONLY",
        "authority": {
            "reviewed_packet_id": (
                "TOE_CANDIDATE_MASTER_ACTION_CK_FIREWALL_AUTHORITY_"
                "RECONCILIATION_PACKET_20260717_v0"
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
        "review_question": (
            "Do existing authority records resolve the C_k action/firewall conflict, "
            "or is a fresh theory decision required before defining a successor action?"
        ),
        "answer": (
            "NO_TERM_DELETION_AUTHORIZED_BUT_V0_IS_LIMITED_TO_SCHEMATIC_"
            "ORGANIZING_SURFACE_STATUS"
        ),
        "source_scope_review": {
            "status": "PASS",
            "historical_action_source_count": 1,
            "firewall_source_count": 11,
            "local_or_option_index_source_count": 8,
            "aggregate_source_count": 3,
            "authority_rule_count": 4,
            "chronology_used_as_precedence": False,
            "downstream_scientific_convenience_used": False,
        },
        "explicit_supersession_review": {
            "status": "NOT_ESTABLISHED",
            "reproduced_scan_match_count": 0,
            "manual_scope_review_found_explicit_supersession": False,
            "historical_action_named_as_superseded": False,
            "displayed_term_withdrawn_or_removed": False,
            "successor_registered_and_linked": False,
            "applicable_existing_rule_amends_v0": False,
        },
        "historical_action_review": {
            "source_id": "TOE_CANDIDATE_MASTER_ACTION_v0",
            "classification": "P_POLICY_WORKING_FORM_NONCANONICAL_UNPROMOTED",
            "working_form_only_self_classification": True,
            "contains_displayed_C_k_multiplier_term": True,
            "contains_stationarity_condition": True,
            "complete_C_k_multiplier_variation_contract": False,
            "historical_bytes_preserved": True,
            "term_deleted_declared_inactive_or_projected": False,
        },
        "aggregate_organizing_surface_review": {
            "status": "PASS",
            "source_count": len(AGGREGATE_SOURCES),
            "rows": AGGREGATE_SOURCES,
            "all_C_k_families_admissibility_only": True,
            "action_embedding_or_variation_authorized": False,
            "master_action_status": (
                "WORKING_FORM_NONCANONICAL_NONPROMOTED_ORGANIZING_SURFACE"
            ),
        },
        "authority_rule_application": {
            "rule_count": len(AUTHORITY_RULE_APPLICATIONS),
            "rows": AUTHORITY_RULE_APPLICATIONS,
            "rule_authorizes_historical_mutation": False,
            "rule_authorizes_successor_creation": False,
            "rule_authorizes_executable_action_claim": False,
        },
        "outcome_adjudication": {
            "allowed_outcome_count": len(OUTCOME_ADJUDICATION),
            "selected_outcome_count": len(selected),
            "rows": OUTCOME_ADJUDICATION,
        },
        "terminal_reasoning": {
            "selected": VERDICT,
            "why_not_explicit_supersession": (
                "No accepted source or applicable existing rule removes the term, "
                "amends v0, or registers a successor."
            ),
            "why_schematic_only": (
                "V0 is self-limited to a noncanonical working form, and three accepted "
                "aggregate records retain it as an organizing surface while refusing "
                "C_k embedding and variation."
            ),
            "why_not_dynamical_embedding": (
                "The accepted record does not license the displayed term as current "
                "executable dynamics; opening that route would be a new theory choice."
            ),
            "why_not_unresolved_precedence": (
                "The record does not resolve deletion precedence, but it does resolve "
                "the maximum present status as schematic and non-executable."
            ),
        },
        "retained_status": {
            "historical_v0": "SCHEMATIC_WORKING_FORM_ORGANIZING_SURFACE",
            "native_executable_continuum_action": "NOT_YET_DEFINED",
            "C_k": "ADMISSIBILITY_AUDIT_ONLY_UNDER_CURRENT_ACCEPTED_POLICY",
            "successor_action": "NOT_CREATED_NOT_PREPARED",
            "bounded_discrete_Newton_Poisson_GR": "RETAINED",
            "gravitomagnetic_route": "BLOCKED_FIELD_EQUATION_SURFACE_FAILURE",
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
        "scope": {
            "independent_review_executed": True,
            "historical_action_mutated": False,
            "precedence_supersession_declared": False,
            "successor_action_prepared": False,
            "successor_action_created": False,
            "C_k_dynamical_route_selected": False,
            "C_k_embedded_or_varied": False,
            "lambda_k_set_to_zero": False,
            "metric_tetrad_or_spin_variation_executed": False,
            "stress_energy_calculated": False,
            "Einstein_equation_imported_or_derived": False,
            "standard_GR_comparator_activated": False,
            "gravitomagnetic_calculation_executed": False,
            "master_action_promoted": False,
            "GR_pillar_completed": False,
            "seam_closed": False,
            "simulation_executed": False,
            "empirical_analysis_executed": False,
            "repository_migration_executed": False,
            "automation_created": False,
        },
        "claim_ceiling": (
            "Independent authority review only. No existing authority removes the C_k "
            "term or creates a successor. V0 remains a schematic working-form organizing "
            "surface, and no executable native continuum action is currently defined. "
            "No action mutation, C_k dynamics, variation, tensor field equation, GR "
            "recovery, promotion, empirical result, or automation is created."
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
            raise SystemExit("C_k authority reconciliation review is stale or missing")
        review = json.loads(raw)
        print(json.dumps({
            "firewall_sources": review["source_scope_review"]["firewall_source_count"],
            "outcome": review["verdict"],
            "status": "CHECKED",
            "successor_created": review["scope"]["successor_action_created"],
        }, sort_keys=True))
        return 0
    report_path.write_bytes(raw)
    print(report_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

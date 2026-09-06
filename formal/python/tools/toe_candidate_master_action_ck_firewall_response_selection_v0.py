from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "TOE_CANDIDATE_MASTER_ACTION_CK_FIREWALL_RESPONSE_SELECTION_20260717_v0.json"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_toe_candidate_master_action_ck_firewall_response_selection_v0.py"
)
TARGET = (
    "select_response_to_gr_native_continuum_action_contract_block_from_full_toe_priority_map"
)
SELECTED_NEXT_TARGET = (
    "prepare_toe_candidate_master_action_ck_firewall_authority_reconciliation_packet_v0"
)

AUTHORITY_HASHES = {
    "formal/docs/lanes/GR_NATIVE_CONTINUUM_METRIC_VARIATION_AND_TENSOR_SURFACE_PACKET_REVIEW_20260717_v0.md":
        "70b33f70e3389d68b0feea9a8d0f41c9f833b58db6f0a86e8ff81384a74dad92",
    "formal/docs/release/GR_NATIVE_CONTINUUM_METRIC_VARIATION_AND_TENSOR_SURFACE_PACKET_REVIEW_20260717_v0.json":
        "4b894a31d1eb9ea29b06f70934913f42a007db31bbf3ac75f2ab8411674d1939",
    "formal/python/tools/gr_native_continuum_metric_variation_and_tensor_surface_packet_review_v0.py":
        "87a53a683d9adb53db898f68c9e6eee1fa7d4a1d2366711d4e5d489364845ed5",
    "formal/python/tests/test_gr_native_continuum_metric_variation_and_tensor_surface_packet_review_v0.py":
        "2197d37c1aa8b4dd7f85e118e5c085a1f860fde4b4616800ec7c0d328a3a7712",
    "formal/toe_formal/ToeFormal/Derivation/GRNativeContinuumMetricVariationAndTensorSurfacePacketReviewV0.lean":
        "039fb416af71f77c6893448e60e47366ddedcf751c9fdf1c701b5738dc6aa760",
    "formal/docs/paper/TOE_CANDIDATE_MASTER_ACTION_v0.md":
        "23aa11c3784da178097eef8ed7c32f9decf4db038a611e4a16364b9bed2db867",
    "formal/docs/release/MASTER_ACTION_CK_CONSTRAINT_FUNCTIONAL_DEFINITION_PACKET_RESULT_REVIEW_20260618_v0.json":
        "78aea408a5cf0838a63cd13d73e2c07ed716f2d2863daefe11eccfd7c0582860",
    "formal/docs/release/TOE_NATIVE_PSI_A_U1_CEXCHANGE_FUNCTIONAL_EMBEDDING_PACKET_RESULT_REVIEW_20260625_v0.json":
        "122943f1fbf55720ee78b1d9df662f499cefe91c625f0b6ffe1a595b2a581c16",
    "formal/docs/release/MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_AFTER_PHI_A_AND_PSI_A_RESULT_REVIEW_20260626_v0.json":
        "3d148464b39d50ae052866516d30bd3f167e1b80d276f56f593fc698f9e6734d",
    "formal/docs/release/MASTER_ACTION_SURFACE_SELECTION_AFTER_CK_FAMILY_STATUS_SYNTHESIS_20260626_v0.json":
        "54eae29c2e3567a10b0c1b9163b40c1b5db0d5dcc32ec7ba4f1e5e0f95d099a1",
}

CRITERIA = {
    "direct_blocker_resolution": 3,
    "authority_correctness": 3,
    "scientific_leverage": 3,
    "endpoint_precision": 3,
    "avoids_unselected_theory_change": 2,
    "preserves_claim_boundaries": 2,
    "downstream_native_gr_unlock_value": 2,
    "infrastructure_avoidance": 2,
}

CANDIDATES = [
    {
        "candidate_id": "PRESERVE_CK_FIREWALL_AND_RECONCILE_MASTER_ACTION_AUTHORITY",
        "target": SELECTED_NEXT_TARGET,
        "kind": "BOUNDED_AUTHORITY_RECONCILIATION_WITHOUT_ACTION_REWRITE",
        "scores": {
            "direct_blocker_resolution": 5,
            "authority_correctness": 4,
            "scientific_leverage": 5,
            "endpoint_precision": 5,
            "avoids_unselected_theory_change": 5,
            "preserves_claim_boundaries": 5,
            "downstream_native_gr_unlock_value": 5,
            "infrastructure_avoidance": 5,
        },
        "scientific_endpoint": (
            "Determine whether later admissibility-only C_k authority explicitly "
            "supersedes the displayed multiplier term, leaves the master action "
            "schematic-only, requires new-theory selection, or cannot resolve precedence."
        ),
    },
    {
        "candidate_id": "MAKE_CK_GENUINELY_DYNAMICAL",
        "target": "select_ck_dynamical_embedding_as_new_theory_route",
        "kind": "MATERIAL_THEORY_REDESIGN",
        "scores": {
            "direct_blocker_resolution": 3,
            "authority_correctness": 1,
            "scientific_leverage": 3,
            "endpoint_precision": 2,
            "avoids_unselected_theory_change": 0,
            "preserves_claim_boundaries": 1,
            "downstream_native_gr_unlock_value": 3,
            "infrastructure_avoidance": 1,
        },
        "scientific_endpoint": (
            "Reverse the current firewall and define C_k multiplier or penalty dynamics "
            "as a separately selected theory redesign."
        ),
    },
    {
        "candidate_id": "CLASSIFY_MASTER_ACTION_SCHEMATIC_ONLY",
        "target": "prepare_master_action_schematic_only_classification_packet_v0",
        "kind": "NO_NATIVE_ACTION_CLASSIFICATION",
        "scores": {
            "direct_blocker_resolution": 4,
            "authority_correctness": 5,
            "scientific_leverage": 4,
            "endpoint_precision": 5,
            "avoids_unselected_theory_change": 5,
            "preserves_claim_boundaries": 5,
            "downstream_native_gr_unlock_value": 2,
            "infrastructure_avoidance": 5,
        },
        "scientific_endpoint": (
            "Classify the current master action as a sector inventory or organizing "
            "hypothesis and record that no native continuum action presently exists."
        ),
    },
    {
        "candidate_id": "ACTIVATE_SUPPLIED_STANDARD_GR_COMPARATOR",
        "target": "prepare_supplied_standard_gr_variational_comparator_packet_v0",
        "kind": "SUPPLIED_STANDARD_GR_COMPARATOR_ONLY",
        "scores": {
            "direct_blocker_resolution": 1,
            "authority_correctness": 5,
            "scientific_leverage": 3,
            "endpoint_precision": 5,
            "avoids_unselected_theory_change": 5,
            "preserves_claim_boundaries": 4,
            "downstream_native_gr_unlock_value": 2,
            "infrastructure_avoidance": 5,
        },
        "scientific_endpoint": (
            "Supply the Einstein-Hilbert sector explicitly and reproduce its variation "
            "without making a ToE-native gravity claim."
        ),
    },
]


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _weighted_score(scores: dict[str, int], weights: dict[str, int]) -> int:
    if set(scores) != set(weights):
        raise ValueError("candidate score criteria mismatch")
    if any(value < 0 or value > 5 for value in scores.values()):
        raise ValueError("candidate criterion score outside 0..5")
    return sum(scores[key] * weights[key] for key in weights)


def _rank(weights: dict[str, int]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for candidate in CANDIDATES:
        row = dict(candidate)
        row["weighted_score"] = _weighted_score(candidate["scores"], weights)
        rows.append(row)
    return sorted(rows, key=lambda row: (-row["weighted_score"], row["candidate_id"]))


def _sensitivity() -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for omitted in CRITERIA:
        weights = dict(CRITERIA)
        weights[omitted] = 0
        ranking = _rank(weights)
        rows.append({
            "variant": f"omit_{omitted}",
            "selected_candidate_id": ranking[0]["candidate_id"],
            "selected_score": ranking[0]["weighted_score"],
            "runner_up_candidate_id": ranking[1]["candidate_id"],
            "runner_up_score": ranking[1]["weighted_score"],
        })
    for criterion, baseline_weight in CRITERIA.items():
        for delta in (-1, 1):
            weights = dict(CRITERIA)
            weights[criterion] = max(1, baseline_weight + delta)
            ranking = _rank(weights)
            rows.append({
                "variant": f"{criterion}_{delta:+d}",
                "selected_candidate_id": ranking[0]["candidate_id"],
                "selected_score": ranking[0]["weighted_score"],
                "runner_up_candidate_id": ranking[1]["candidate_id"],
                "runner_up_score": ranking[1]["weighted_score"],
            })
    selected = CANDIDATES[0]["candidate_id"]
    return {
        "variant_count": len(rows),
        "rows": rows,
        "selected_candidate_stable_in_all_variants": all(
            row["selected_candidate_id"] == selected for row in rows
        ),
        "minimum_winning_margin": min(
            row["selected_score"] - row["runner_up_score"] for row in rows
        ),
    }


def _validate_authority() -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for relative_path, expected_hash in AUTHORITY_HASHES.items():
        observed = _sha256((REPO_ROOT / relative_path).read_bytes())
        if observed != expected_hash:
            raise ValueError(f"C_k response-selection authority mismatch: {relative_path}")
        rows.append({"relative_path": relative_path, "sha256": observed})

    review = json.loads(
        (REPO_ROOT / "formal/docs/release/GR_NATIVE_CONTINUUM_METRIC_VARIATION_AND_TENSOR_SURFACE_PACKET_REVIEW_20260717_v0.json").read_text(encoding="utf-8")
    )
    if review.get("verdict") != "BLOCKED_INCOMPLETE_CONTINUUM_ACTION_CONTRACT":
        raise ValueError("native continuum action terminal verdict mismatch")
    if review.get("primary_diagnostic") != "CK_FIREWALL_ACTION_SOURCE_CONFLICT":
        raise ValueError("native continuum action primary diagnostic mismatch")
    if review.get("selected_next_target") != TARGET:
        raise ValueError("terminal review did not authorize fresh response selection")

    action = (
        REPO_ROOT / "formal/docs/paper/TOE_CANDIDATE_MASTER_ACTION_v0.md"
    ).read_text(encoding="utf-8")
    if "sum_k lambda_k * C_k(g, psi, A, phi, rho)" not in action:
        raise ValueError("displayed candidate C_k term missing")

    synthesis = json.loads(
        (REPO_ROOT / "formal/docs/release/MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_AFTER_PHI_A_AND_PSI_A_RESULT_REVIEW_20260626_v0.json").read_text(encoding="utf-8")
    )
    required = {
        "all_C_k_families_admissibility_only": True,
        "C_k_action_embedding_selected": False,
        "C_k_action_variation_authorized": False,
    }
    if {key: synthesis.get(key) for key in required} != required:
        raise ValueError("later C_k firewall posture mismatch")

    exchange = json.loads(
        (REPO_ROOT / "formal/docs/release/TOE_NATIVE_PSI_A_U1_CEXCHANGE_FUNCTIONAL_EMBEDDING_PACKET_RESULT_REVIEW_20260625_v0.json").read_text(encoding="utf-8")
    )
    if exchange.get("multiplier_action_route_blocked") is not True:
        raise ValueError("C_exchange multiplier route is not recorded blocked")
    if exchange.get("penalty_route_unlicensed") is not True:
        raise ValueError("C_exchange penalty route is not recorded unlicensed")

    surface = json.loads(
        (REPO_ROOT / "formal/docs/release/MASTER_ACTION_SURFACE_SELECTION_AFTER_CK_FAMILY_STATUS_SYNTHESIS_20260626_v0.json").read_text(encoding="utf-8")
    )
    if surface.get("master_action_promoted") is not False:
        raise ValueError("master action unexpectedly promoted")
    if surface.get("C_k_action_embedding_selected") is not False:
        raise ValueError("master-action surface unexpectedly embeds C_k")
    return rows


def build_selection() -> dict[str, Any]:
    authority = _validate_authority()
    ranking = _rank(CRITERIA)
    sensitivity = _sensitivity()
    selected_id = "PRESERVE_CK_FIREWALL_AND_RECONCILE_MASTER_ACTION_AUTHORITY"
    if ranking[0]["candidate_id"] != selected_id:
        raise ValueError("unexpected C_k response-selection winner")
    if not sensitivity["selected_candidate_stable_in_all_variants"]:
        raise ValueError("C_k response-selection winner is sensitivity-unstable")
    tool_path = Path(__file__).resolve()
    test_path = REPO_ROOT / TEST_RELATIVE_PATH
    if not test_path.exists():
        raise ValueError("C_k response-selection focused test missing")

    return {
        "schema_id": "TOE_CANDIDATE_MASTER_ACTION_CK_FIREWALL_RESPONSE_SELECTION_20260717_v0",
        "captured_at_utc": "2026-07-17T00:00:00Z",
        "target": TARGET,
        "verdict": "SELECTED_CK_FIREWALL_AUTHORITY_RECONCILIATION_PREPARATION",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": "PREPARATION_ONLY_MASTER_ACTION_AUTHORITY_RECONCILIATION",
        "authority": {
            "terminal_verdict": "BLOCKED_INCOMPLETE_CONTINUUM_ACTION_CONTRACT",
            "terminal_diagnostic": "CK_FIREWALL_ACTION_SOURCE_CONFLICT",
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
        "selection_policy": {
            "criterion_scale": "0..5",
            "weights": CRITERIA,
            "maximum_weighted_score": 100,
            "candidate_count": len(CANDIDATES),
        },
        "ranking": {
            "rows": ranking,
            "selected_candidate_id": ranking[0]["candidate_id"],
            "selected_score": ranking[0]["weighted_score"],
            "runner_up_candidate_id": ranking[1]["candidate_id"],
            "runner_up_score": ranking[1]["weighted_score"],
        },
        "sensitivity_analysis": sensitivity,
        "selected_scientific_obligation": {
            "question": (
                "Does the later admissibility-only C_k authority supersede the displayed "
                "multiplier term, thereby licensing preparation of a new candidate action "
                "without C_k dynamics, or must the existing master action be downgraded "
                "to schematic-only status?"
            ),
            "obligation_class": "AUTHORITY_CHRONOLOGY_AND_PRECEDENCE_RECONCILIATION",
            "packet_must_freeze": [
                "byte-exact original candidate action containing sum_k lambda_k C_k",
                "every later accepted C_k admissibility-only and no-embedding authority",
                "authority levels, consumed-target lineage, and dates without assuming later-date precedence",
                "whether any later artifact explicitly supersedes, amends, or merely conflicts with v0",
                "exactly one terminal resolution",
                "no claim inheritance into any possible successor action",
                "all downstream tetrad, unit, boundary, stress-energy, statistical, and Rep32 gates remain closed",
            ],
            "allowed_terminal_results": [
                "CK_FIREWALL_SUPERSEDES_ACTION_TERM",
                "MASTER_ACTION_REMAINS_SCHEMATIC_ONLY",
                "CK_DYNAMICAL_EMBEDDING_REQUIRES_NEW_THEORY_SELECTION",
                "BLOCKED_AUTHORITY_PRECEDENCE_UNRESOLVED",
            ],
            "possible_successor_classification": (
                "WORKING_FORM_NONCANONICAL_UNPROMOTED_UNVARIED"
            ),
            "stopping_rule": (
                "Prepare one authority-reconciliation packet and stop for independent "
                "review; do not rewrite v0, create a successor action, select C_k dynamics, "
                "execute variation, activate a comparator, or resume gravitomagnetism."
            ),
        },
        "retained_boundaries": {
            "candidate_master_action": "WORKING_FORM_NONCANONICAL_UNPROMOTED",
            "C_k": "ADMISSIBILITY_AUDIT_ONLY",
            "native_continuum_action_contract": "BLOCKED_INCOMPLETE_CONTINUUM_ACTION_CONTRACT",
            "tetrad_spinor_surface": "NOT_EVALUATED",
            "stress_energy_generation": "NOT_EVALUATED",
            "Rep32_transport": "NOT_EVALUATED",
            "GR_gravitomagnetic_recovery": "BLOCKED_FIELD_EQUATION_SURFACE_FAILURE",
        },
        "scope": {
            "response_selection_executed": True,
            "packet_preparation_authorized": True,
            "packet_prepared_now": False,
            "authority_precedence_adjudicated_now": False,
            "v0_action_deleted_or_modified": False,
            "successor_action_created": False,
            "C_k_declared_inactive_inside_v0": False,
            "lambda_k_set_to_zero": False,
            "C_k_dynamical_embedding_selected": False,
            "C_k_action_variation_authorized": False,
            "metric_or_tetrad_variation_executed": False,
            "standard_GR_comparator_activated": False,
            "gravitomagnetic_route_reopened": False,
            "master_action_promoted": False,
            "GR_pillar_completed": False,
            "seam_closed": False,
            "simulation_executed": False,
            "empirical_analysis_executed": False,
            "automation_created": False,
        },
        "claim_ceiling": (
            "Fresh response selection only. It selects preparation of one bounded "
            "authority-reconciliation packet while retaining the C_k firewall and the "
            "terminal incomplete-action block. It creates no precedence ruling, action "
            "rewrite, successor action, C_k dynamics, metric/tetrad variation, comparator "
            "result, GR recovery, master-action promotion, empirical result, or automation."
        ),
    }


def artifact_bytes() -> bytes:
    return (
        json.dumps(build_selection(), indent=2, sort_keys=True, ensure_ascii=True) + "\n"
    ).encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    report_path = REPO_ROOT / REPORT_RELATIVE_PATH
    raw = artifact_bytes()
    if args.check:
        if not report_path.exists() or report_path.read_bytes() != raw:
            raise SystemExit("C_k firewall response selection is stale or missing")
        report = json.loads(raw)
        print(json.dumps({
            "selected": report["ranking"]["selected_candidate_id"],
            "selected_score": report["ranking"]["selected_score"],
            "sensitivity_variants": report["sensitivity_analysis"]["variant_count"],
            "stable": report["sensitivity_analysis"]["selected_candidate_stable_in_all_variants"],
            "status": "CHECKED",
        }, sort_keys=True))
        return 0
    report_path.write_bytes(raw)
    print(report_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

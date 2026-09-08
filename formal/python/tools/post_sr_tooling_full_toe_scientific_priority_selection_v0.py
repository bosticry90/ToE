from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "POST_SR_TOOLING_FULL_TOE_SCIENTIFIC_PRIORITY_SELECTION_20260717_v0.json"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_post_sr_tooling_full_toe_scientific_priority_selection_v0.py"
)
TARGET = "select_next_high_leverage_scientific_obligation_from_full_toe_priority_map"
SELECTED_NEXT_TARGET = "prepare_gr_weak_rotating_source_gravitomagnetic_recovery_packet_v0"

AUTHORITY_HASHES = {
    "formal/docs/release/SR_PILLAR_COORDINATE_CONVENTION_AND_CONSTANT_RESTORATION_PACKET_REVIEW_20260717_v3.json":
        "0dbe441d78de6eba0fe006f7b6b280b655a3feae3e1f9d66775eefae9e49a3b1",
    "formal/docs/lanes/SR_COORDINATE_CONVENTION_AND_RESTORATION_TOOLING_CLOSEOUT_20260717_v0.md":
        "aae7a1e0e7029a778dbc9ab3b88952cc3c619624c2bd2255f151c4040d0548ab",
    "formal/docs/release/SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0.json":
        "6a4273b3f95bca657bbc9dcdbab82d118a8223ab6de55a213374421b560838a1",
    "formal/docs/release/POST_R13_FULL_TOE_PRIORITY_RETURN_SELECTION_20260717_v0.json":
        "bfabe6d69a5bf046683948e21e78e1952e518fdfb94fde5c56369c784a2f1a4f",
    "formal/docs/release/EXTERNAL_RELATED_WORK_AND_METHODS_INTAKE_20260717_v0.json":
        "351fe687ab20a8f83b01ebe8dc807274703acf0cc388805ad5f8481cdbf84ca3",
    "formal/docs/lanes/EXTERNAL_RELATED_WORK_AND_BENCHMARK_INTAKE_20260717_v0.md":
        "a5608b1bbda442e78d177e5668254852dabc2740eb55525eb107f9ecb44a3cb9",
    "formal/docs/paper/DERIVATION_TARGET_GR01_FULL_DERIVATION_DISCHARGE_v0.md":
        "1d9fbe0b49d45aad3781b4217dc108a6f2c16361cd59fa662c8283de10f6ac67",
}

CRITERIA = {
    "pillar_or_seam_blocker_relevance": 3,
    "endpoint_precision": 3,
    "pass_fail_scientific_value": 2,
    "claim_state_change_potential": 3,
    "existing_authoritative_inputs": 2,
    "infrastructure_avoidance": 3,
    "closed_lane_nonreplay": 2,
    "prediction_or_observation_proximity": 2,
}

CANDIDATES = [
    {
        "candidate_id": "GR_WEAK_ROTATING_SOURCE_GRAVITOMAGNETIC_RECOVERY",
        "target": SELECTED_NEXT_TARGET,
        "kind": "BOUNDED_GR_PILLAR_KNOWN_LIMIT_RECOVERY",
        "scores": {
            "pillar_or_seam_blocker_relevance": 5,
            "endpoint_precision": 5,
            "pass_fail_scientific_value": 5,
            "claim_state_change_potential": 4,
            "existing_authoritative_inputs": 4,
            "infrastructure_avoidance": 5,
            "closed_lane_nonreplay": 5,
            "prediction_or_observation_proximity": 4,
        },
        "scientific_endpoint": (
            "Derive the stationary slow-rotation linearized 0i field equation, exterior "
            "gravitomagnetic metric component, and Lense-Thirring nodal-precession "
            "coefficient from the bounded GR sector without fitting that coefficient."
        ),
    },
    {
        "candidate_id": "MASTER_ACTION_DISTINCTIVE_PREDICTION_FEASIBILITY_NO_GO",
        "target": "prepare_master_action_distinctive_prediction_feasibility_no_go_packet_v0",
        "kind": "BOUNDED_PREDICTION_FEASIBILITY_OR_NO_GO",
        "scores": {
            "pillar_or_seam_blocker_relevance": 5,
            "endpoint_precision": 3,
            "pass_fail_scientific_value": 5,
            "claim_state_change_potential": 5,
            "existing_authoritative_inputs": 1,
            "infrastructure_avoidance": 4,
            "closed_lane_nonreplay": 5,
            "prediction_or_observation_proximity": 5,
        },
        "scientific_endpoint": "Prove whether the current unpromoted action determines any parameter-independent observable departure from its standard-sector baseline.",
    },
    {
        "candidate_id": "QFT_GR_SOURCE_CONSERVATION_BIANCHI_COUNTERMODEL",
        "target": "prepare_qft_gr_source_conservation_bianchi_countermodel_packet_v0",
        "kind": "BOUNDED_SEAM_COUNTERMODEL",
        "scores": {
            "pillar_or_seam_blocker_relevance": 5,
            "endpoint_precision": 4,
            "pass_fail_scientific_value": 5,
            "claim_state_change_potential": 5,
            "existing_authoritative_inputs": 3,
            "infrastructure_avoidance": 3,
            "closed_lane_nonreplay": 4,
            "prediction_or_observation_proximity": 3,
        },
        "scientific_endpoint": "Construct or refute one explicit conserved classical source map compatible with the bounded QFT expectation and Bianchi obligations.",
    },
    {
        "candidate_id": "QM_FINITE_EVOLUTION_TO_OBSERVABLE_RECOVERY",
        "target": "prepare_qm_finite_evolution_to_observable_recovery_packet_v0",
        "kind": "BOUNDED_QM_PILLAR_RECOVERY",
        "scores": {
            "pillar_or_seam_blocker_relevance": 3,
            "endpoint_precision": 5,
            "pass_fail_scientific_value": 4,
            "claim_state_change_potential": 3,
            "existing_authoritative_inputs": 4,
            "infrastructure_avoidance": 5,
            "closed_lane_nonreplay": 5,
            "prediction_or_observation_proximity": 2,
        },
        "scientific_endpoint": "Derive one finite-dimensional unitary evolution and observable probability calculation from the bound QM surfaces with an analytic baseline.",
    },
    {
        "candidate_id": "QM_STAT_TRANSPORT_COUNTERMODEL",
        "target": "prepare_qm_stat_transport_countermodel_packet_v0",
        "kind": "BOUNDED_SEAM_COUNTERMODEL",
        "scores": {
            "pillar_or_seam_blocker_relevance": 4,
            "endpoint_precision": 4,
            "pass_fail_scientific_value": 5,
            "claim_state_change_potential": 4,
            "existing_authoritative_inputs": 4,
            "infrastructure_avoidance": 4,
            "closed_lane_nonreplay": 2,
            "prediction_or_observation_proximity": 3,
        },
        "scientific_endpoint": "Produce a finite state/probability transport witness or countermodel for the retained QM-STAT semantic bridge assumptions.",
    },
    {
        "candidate_id": "EM_QFT_SOURCE_EXCHANGE_RECOVERY",
        "target": "prepare_em_qft_source_exchange_recovery_packet_v0",
        "kind": "BOUNDED_SEAM_RECOVERY",
        "scores": {
            "pillar_or_seam_blocker_relevance": 4,
            "endpoint_precision": 4,
            "pass_fail_scientific_value": 4,
            "claim_state_change_potential": 4,
            "existing_authoritative_inputs": 4,
            "infrastructure_avoidance": 4,
            "closed_lane_nonreplay": 2,
            "prediction_or_observation_proximity": 3,
        },
        "scientific_endpoint": "Derive one complete source-current and matter-field exchange identity from the retained psi-A route without importing quantized EM closure.",
    },
]

EXCLUDED_TARGETS = [
    {
        "target_class": "R13_OR_MAXWELL_DIRAC_MECHANISM_CONTINUATION",
        "reason": "R13 is terminated under UNRESOLVED_EVIDENCE_SEMANTICS_BLOCK and requires a fresh priority decision specifically justifying replay.",
    },
    {
        "target_class": "SR_RESTORATION_TOOLING_V4",
        "reason": "The automated restoration lane is closed; v4 is not authorized and does not directly advance physics.",
    },
    {
        "target_class": "GENERAL_UNITS_REGISTRY_OR_CONVENTION_MIGRATION",
        "reason": "Infrastructure/documentation work is subordinate unless a selected physical calculation is blocked by it.",
    },
    {
        "target_class": "GFE_OR_OTHER_DORMANT_COMPARATOR_ADOPTION",
        "reason": "Related work remains non-adopted and cannot displace a live physics obligation without a separate comparator decision.",
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
    rows = []
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
            raise ValueError(f"priority authority hash mismatch: {relative_path}")
        rows.append({"relative_path": relative_path, "sha256": observed})

    sr_review = json.loads(
        (REPO_ROOT / next(path for path in AUTHORITY_HASHES if "PACKET_REVIEW_20260717_v3" in path)).read_text(encoding="utf-8")
    )
    if sr_review.get("verdict") != "BLOCKED_SR_RESTORATION_TOOLING_CONTRACT":
        raise ValueError("SR terminal verdict mismatch")
    if sr_review.get("selected_next_target") != TARGET:
        raise ValueError("SR terminal review did not authorize full-priority selection")

    readiness = json.loads(
        (REPO_ROOT / "formal/docs/release/SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0.json").read_text(encoding="utf-8")
    )
    gr_rows = {
        row["criterion_id"]: row
        for row in readiness["pillar_readiness_rows"]
        if row["pillar_id"] == "PILLAR-GR"
    }
    expected_gr = {
        "physical_objects": "met",
        "governing_equation_or_action": "met",
        "known_limit_recovery": "partial",
        "reproducible_calculation": "missing",
    }
    if {key: gr_rows[key]["status"] for key in expected_gr} != expected_gr:
        raise ValueError("GR readiness basis mismatch")

    benchmark = (REPO_ROOT / "formal/docs/lanes/EXTERNAL_RELATED_WORK_AND_BENCHMARK_INTAKE_20260717_v0.md").read_text(encoding="utf-8")
    for token in (
        "GR-WEAK-ROTATING-SOURCE-BENCHMARK",
        "DORMANT_UNTIL_GR_LANE_INTENTIONALLY_SELECTED",
        "Derive the Lense-Thirring orbital-node precession without fitting its coefficient",
    ):
        if token not in benchmark:
            raise ValueError(f"rotating-source benchmark token missing: {token}")
    return rows


def build_selection() -> dict[str, Any]:
    authority = _validate_authority()
    ranking = _rank(CRITERIA)
    sensitivity = _sensitivity()
    if ranking[0]["candidate_id"] != "GR_WEAK_ROTATING_SOURCE_GRAVITOMAGNETIC_RECOVERY":
        raise ValueError("unexpected scientific priority winner")
    if not sensitivity["selected_candidate_stable_in_all_variants"]:
        raise ValueError("scientific priority winner is sensitivity-unstable")
    tool_path = Path(__file__).resolve()
    test_path = REPO_ROOT / TEST_RELATIVE_PATH
    if not test_path.exists():
        raise ValueError("priority selection test missing")
    return {
        "schema_id": "POST_SR_TOOLING_FULL_TOE_SCIENTIFIC_PRIORITY_SELECTION_20260717_v0",
        "captured_at_utc": "2026-07-17T00:00:00Z",
        "target": TARGET,
        "verdict": "SELECTED_DIRECT_GR_KNOWN_LIMIT_RECOVERY_PREPARATION",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": "PREPARATION_ONLY_DIRECT_GR_PILLAR_RECOVERY",
        "authority": {
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
        "sr_policy_closeout": {
            "physical_convention": "x^0=c t; g=diag(+1,-1,-1,-1); dimensionful target SI",
            "policy_status": "RETAINED_AS_BOUNDED_POLICY",
            "automated_restoration": "BLOCKED_SR_RESTORATION_TOOLING_CONTRACT",
            "equation_specific_review_required": True,
            "migration_executed": False,
            "v4_authorized": False,
        },
        "selection_policy": {
            "criterion_scale": "0..5",
            "weights": CRITERIA,
            "maximum_weighted_score": 100,
            "required_target_properties": [
                "addresses a real pillar or seam blocker",
                "has a precise mathematical or computational endpoint",
                "produces meaningful evidence on success or failure",
                "requires no new general-purpose tool or governance system",
                "can change the project scientific claim state",
            ],
        },
        "ranking": {
            "eligible_candidate_count": len(ranking),
            "rows": ranking,
            "selected_candidate_id": ranking[0]["candidate_id"],
            "selected_score": ranking[0]["weighted_score"],
            "runner_up_candidate_id": ranking[1]["candidate_id"],
            "runner_up_score": ranking[1]["weighted_score"],
        },
        "sensitivity_analysis": sensitivity,
        "excluded_target_classes": EXCLUDED_TARGETS,
        "selected_scientific_obligation": {
            "pillar": "GR",
            "obligation_class": "KNOWN_PHYSICS_RECOVERY",
            "question": (
                "Under stationary, weak-field, slow-rotation, exterior-source assumptions, "
                "does the bounded GR sector derive the canonical gravitomagnetic g_0i field "
                "and Lense-Thirring nodal-precession coefficient without fitting it?"
            ),
            "inputs": [
                "project GR action/equation surface and explicit weak-field assumptions",
                "retained x^0=c t, (+,-,-,-), SI convention policy",
                "stationary compact-source mass density and mass-current T_0i with total angular momentum J",
                "registered GR-WEAK-ROTATING-SOURCE-BENCHMARK as a reference only",
            ],
            "required_derivation_endpoints": [
                "derive the linearized stationary 0i field equation from the bounded GR surface",
                "derive the exterior g_0i gravitomagnetic component and its coefficient from T_0i",
                "derive the orbital-node Lense-Thirring precession without fitting its coefficient",
                "show J=0 removes the gravitomagnetic term and J reversal reverses the precession sign",
                "identify every supplied boundary, gauge, source, and approximation assumption",
            ],
            "success_result": "BOUNDED_GR_ROTATING_WEAK_FIELD_RECOVERY_CANDIDATE_PENDING_RESULT_REVIEW",
            "failure_result": "BOUNDED_NO_GO_OR_EXACT_SUPPLIED_ASSUMPTION_BLOCKER",
            "stopping_rule": (
                "Prepare one derivation contract, stop for independent review, and do not "
                "expand to observational fitting, strong fields, alternative gravity, or a "
                "general symbolic framework."
            ),
        },
        "benchmark_posture": {
            "GR-WEAK-ROTATING-SOURCE-BENCHMARK": "REFERENCE_BOUND_FOR_SELECTED_GR_PREPARATION_ONLY",
            "LARES_2_data_analysis_authorized": False,
            "empirical_fit_authorized": False,
            "modified_gravity_constraint_claim_authorized": False,
            "other_external_comparators_remain_dormant": True,
        },
        "scope_and_authorization": {
            "selected_derivation_executed_now": False,
            "packet_preparation_authorized": True,
            "simulation_authorized": False,
            "empirical_analysis_authorized": False,
            "R13_reopened": False,
            "SR_tooling_reopened": False,
            "v4_authorized": False,
            "repository_migration_authorized": False,
            "new_general_purpose_tool_authorized": False,
            "pillar_completion_claimed": False,
            "seam_closure_claimed": False,
            "master_action_promoted": False,
            "automation_created": False,
        },
        "claim_ceiling": (
            "Full-ToE priority selection and one GR derivation-packet preparation target only. "
            "No rotating-source derivation, calculation, empirical fit, GR-pillar recovery, "
            "seam closure, modified-gravity constraint, master-action promotion, or ToE "
            "validation is created by this selection."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_selection(), indent=2, sort_keys=True, ensure_ascii=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    report_path = REPO_ROOT / REPORT_RELATIVE_PATH
    raw = artifact_bytes()
    if args.check:
        if not report_path.exists() or report_path.read_bytes() != raw:
            raise SystemExit("post-SR full-ToE scientific priority selection is stale or missing")
        report = json.loads(raw)
        print(json.dumps({
            "eligible_candidates": report["ranking"]["eligible_candidate_count"],
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

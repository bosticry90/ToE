from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "GR_FIELD_EQUATION_SURFACE_FAILURE_RESPONSE_SELECTION_20260717_v0.json"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_gr_field_equation_surface_failure_response_selection_v0.py"
)
TARGET = "select_response_to_gr_field_equation_surface_failure_from_full_toe_priority_map"
SELECTED_NEXT_TARGET = (
    "prepare_gr_native_continuum_metric_variation_and_tensor_surface_packet_v0"
)

AUTHORITY_HASHES = {
    "formal/docs/release/GR_WEAK_ROTATING_SOURCE_GRAVITOMAGNETIC_RECOVERY_PACKET_REVIEW_20260717_v0.json":
        "de305a72dc522fe807c037bbe7980d96e3308d0547645ccb9939d1889720d987",
    "formal/docs/paper/TOE_CANDIDATE_MASTER_ACTION_v0.md":
        "23aa11c3784da178097eef8ed7c32f9decf4db038a611e4a16364b9bed2db867",
    "formal/toe_formal/ToeFormal/QFT/DocumentMasterActionMapping.lean":
        "56ad40bfe0443a27b1c35142c52ae2430958dace2b8e62eef8e4e14e31e54ddf",
    "formal/docs/release/MASTER_ACTION_DEPENDENCY_AUDIT_20260503_v0.json":
        "6d737042743316e326a911d059f6a6917ec84c648e8737299c34a639a4eafeff",
    "formal/docs/release/MASTER_ACTION_DEPENDENCY_AUDIT_RESULT_REVIEW_20260503_v0.json":
        "c89782dbf89427ecf7a559cf1f9a501d4f1b2010c38f60c34052f845a39f634f",
    "formal/docs/release/MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_AFTER_PHI_A_AND_PSI_A_RESULT_REVIEW_20260626_v0.json":
        "3d148464b39d50ae052866516d30bd3f167e1b80d276f56f593fc698f9e6734d",
    "formal/toe_formal/ToeFormal/Variational/ActionRep32Def.lean":
        "da375e85850deb5d32da8a60c24d2fd7021c95143f8da036973d9575bd398458",
    "formal/toe_formal/ToeFormal/Variational/FirstVariationRep32Def.lean":
        "8c7a6a3f3aa74f240945e3d2ac23a05c6e5fa6fa310977ba9c03db89f456d920",
    "formal/toe_formal/ToeFormal/Variational/WeakFieldPoissonLimit.lean":
        "b2519245872eaed3d874c25836ce355cca9e3bc0f11914e806a74c691f8d14da",
    "formal/toe_formal/ToeFormal/Variational/GR01BridgePromotion.lean":
        "162cdd0d9596566457ae40c340329b15064e4d0ed17d20deadc48fc2fc431384",
}

CRITERIA = {
    "direct_blocker_attack": 3,
    "endpoint_precision": 3,
    "pass_fail_scientific_value": 3,
    "claim_state_change_potential": 3,
    "existing_authoritative_inputs": 2,
    "infrastructure_avoidance": 2,
    "downstream_gr_unlock_value": 2,
    "no_imported_answer": 2,
}

CANDIDATES = [
    {
        "candidate_id": "GR_NATIVE_CONTINUUM_METRIC_VARIATION_SURFACE",
        "target": SELECTED_NEXT_TARGET,
        "kind": "BOUNDED_GR_NATIVE_ACTION_SURFACE_EXISTENCE_OR_NO_GO",
        "scores": {
            "direct_blocker_attack": 5,
            "endpoint_precision": 5,
            "pass_fail_scientific_value": 5,
            "claim_state_change_potential": 5,
            "existing_authoritative_inputs": 3,
            "infrastructure_avoidance": 4,
            "downstream_gr_unlock_value": 5,
            "no_imported_answer": 5,
        },
        "scientific_endpoint": (
            "Determine whether one exactly bound ToE candidate action is a sufficiently "
            "defined continuum metric functional to authorize a tensor field-equation "
            "variation, or return an exact no-native-surface or incomplete-contract block."
        ),
    },
    {
        "candidate_id": "GR_SUPPLIED_STANDARD_COMPARATOR",
        "target": "prepare_supplied_standard_gr_gravitomagnetic_comparator_packet_v0",
        "kind": "SUPPLIED_STANDARD_GR_COMPARATOR_ONLY",
        "scores": {
            "direct_blocker_attack": 2,
            "endpoint_precision": 5,
            "pass_fail_scientific_value": 4,
            "claim_state_change_potential": 2,
            "existing_authoritative_inputs": 5,
            "infrastructure_avoidance": 5,
            "downstream_gr_unlock_value": 3,
            "no_imported_answer": 1,
        },
        "scientific_endpoint": (
            "Supply the standard linearized Einstein equation explicitly and reproduce the "
            "downstream gravitomagnetic and orbital chain as a comparator only."
        ),
    },
    {
        "candidate_id": "PIVOT_FROM_GR_SURFACE_FAILURE",
        "target": (
            "select_next_non_gr_high_leverage_scientific_obligation_from_full_toe_priority_map"
        ),
        "kind": "PRESERVE_GR_BLOCK_AND_PIVOT",
        "scores": {
            "direct_blocker_attack": 2,
            "endpoint_precision": 3,
            "pass_fail_scientific_value": 4,
            "claim_state_change_potential": 3,
            "existing_authoritative_inputs": 4,
            "infrastructure_avoidance": 5,
            "downstream_gr_unlock_value": 1,
            "no_imported_answer": 5,
        },
        "scientific_endpoint": (
            "Retain the exact GR obstruction and choose a different pillar or seam target."
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
            raise ValueError(f"response-selection authority hash mismatch: {relative_path}")
        rows.append({"relative_path": relative_path, "sha256": observed})

    gr_review = json.loads(
        (REPO_ROOT / "formal/docs/release/GR_WEAK_ROTATING_SOURCE_GRAVITOMAGNETIC_RECOVERY_PACKET_REVIEW_20260717_v0.json").read_text(encoding="utf-8")
    )
    if gr_review.get("verdict") != "BLOCKED_FIELD_EQUATION_SURFACE_FAILURE":
        raise ValueError("terminal rotating-source verdict mismatch")
    if gr_review.get("primary_diagnostic") != "FIELD_EQUATION_SURFACE_FAILURE":
        raise ValueError("terminal rotating-source diagnostic mismatch")
    if gr_review.get("selected_next_target") != TARGET:
        raise ValueError("terminal review did not authorize response selection")
    if gr_review["fail_fast_gate"].get("required_object_present") is not False:
        raise ValueError("terminal review unexpectedly found a native tensor surface")

    action_text = (
        REPO_ROOT / "formal/docs/paper/TOE_CANDIDATE_MASTER_ACTION_v0.md"
    ).read_text(encoding="utf-8")
    for token in (
        "working-form artifact only",
        "explicitly non-canonical",
        "Canonical promotion status (v0)",
        "sum_k lambda_k * C_k",
    ):
        if token not in action_text:
            raise ValueError(f"candidate-action boundary token missing: {token}")

    action_audit = json.loads(
        (REPO_ROOT / "formal/docs/release/MASTER_ACTION_DEPENDENCY_AUDIT_20260503_v0.json").read_text(encoding="utf-8")
    )
    if action_audit.get("audit_status") != "completed_nonpromoted":
        raise ValueError("master-action audit posture mismatch")
    if action_audit["nonclaim_boundaries"].get("master_action_promotion_authorized") is not False:
        raise ValueError("master-action promotion unexpectedly authorized")

    ck_status = json.loads(
        (REPO_ROOT / "formal/docs/release/MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_AFTER_PHI_A_AND_PSI_A_RESULT_REVIEW_20260626_v0.json").read_text(encoding="utf-8")
    )
    if ck_status.get("all_C_k_families_admissibility_only") is not True:
        raise ValueError("C_k admissibility-only policy mismatch")
    if ck_status.get("C_k_action_variation_authorized") is not False:
        raise ValueError("C_k action variation unexpectedly authorized")
    return rows


def build_selection() -> dict[str, Any]:
    authority = _validate_authority()
    ranking = _rank(CRITERIA)
    sensitivity = _sensitivity()
    if ranking[0]["candidate_id"] != "GR_NATIVE_CONTINUUM_METRIC_VARIATION_SURFACE":
        raise ValueError("unexpected GR failure-response winner")
    if not sensitivity["selected_candidate_stable_in_all_variants"]:
        raise ValueError("GR failure-response winner is sensitivity-unstable")
    tool_path = Path(__file__).resolve()
    test_path = REPO_ROOT / TEST_RELATIVE_PATH
    if not test_path.exists():
        raise ValueError("response-selection test missing")

    return {
        "schema_id": "GR_FIELD_EQUATION_SURFACE_FAILURE_RESPONSE_SELECTION_20260717_v0",
        "captured_at_utc": "2026-07-17T00:00:00Z",
        "target": TARGET,
        "verdict": "SELECTED_GR_NATIVE_CONTINUUM_METRIC_VARIATION_SURFACE_PREPARATION",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": "PREPARATION_ONLY_NATIVE_GR_VARIATIONAL_SURFACE_EXISTENCE_OR_NO_GO",
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
        "retained_gr_obstruction": {
            "GR01_bounded_discrete_Newton_Poisson_route": "RETAINED",
            "continuum_metric_tensor_field_equation": "NOT_DERIVED",
            "rotating_source_recovery": "BLOCKED_FIELD_EQUATION_SURFACE_FAILURE",
            "stages_2_through_7_evaluated": False,
            "standard_GR_refuted": False,
            "ToE_native_gravitomagnetism_established": False,
        },
        "selection_policy": {
            "criterion_scale": "0..5",
            "weights": CRITERIA,
            "maximum_weighted_score": 100,
            "route_count": len(CANDIDATES),
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
            "pillar": "GR",
            "obligation_class": "NATIVE_CONTINUUM_VARIATIONAL_SURFACE_EXISTENCE_OR_NO_GO",
            "question": (
                "Does the project possess a sufficiently defined continuum gravitational "
                "action whose metric variation can produce a tensor field equation without "
                "importing the Einstein equation as an assumption?"
            ),
            "packet_must_freeze": [
                "exactly one candidate action source and its authority classification",
                "one gravitational variable: g^munu, g_munu, or tetrad",
                "complete metric-dependence ledger for every selected term",
                "boundary terms and admissible metric variations",
                "stress-energy definition by metric variation or an explicit supplied classification",
                "C_k firewall: admissibility and audit only, not action embedded or varied",
                "exact Rep32 relationship: discretization, reduction, analogy, separate model, or unconnected",
            ],
            "allowed_outcomes": [
                "NATIVE_VARIATIONAL_SURFACE_EXISTS_PENDING_SEPARATE_CALCULATION",
                "SUPPLIED_STANDARD_GR_VARIATIONAL_COMPARATOR_ONLY",
                "NO_NATIVE_CONTINUUM_METRIC_ACTION_SURFACE",
                "BLOCKED_INCOMPLETE_CONTINUUM_ACTION_CONTRACT",
            ],
            "stopping_rule": (
                "Prepare one bounded action-surface existence and variation-contract packet, "
                "stop for independent review, and do not execute metric variation, import the "
                "Einstein equation, reactivate gravitomagnetism, or build general symbolic tooling."
            ),
        },
        "candidate_action_posture": {
            "document_master_action": "WORKING_FORM_NONCANONICAL_NONPROMOTED",
            "ActionRep32": "STRUCTURAL_FIRST_VARIATION_SCAFFOLD_NOT_ANALYTIC_METRIC_VARIATION",
            "document_mapping": "BOUNDED_FREE_SCALAR_TRANSLATION_NOT_GLOBAL_METRIC_VARIATION",
            "provisional_Einstein_scalar_route": "SUPPLIED_STANDARD_GR_SANDBOX_NOT_NATIVE_DERIVATION",
            "C_k": "ADMISSIBILITY_AUDIT_ONLY_NOT_VARIED",
        },
        "scope_and_authorization": {
            "selection_executed": True,
            "packet_preparation_authorized": True,
            "packet_prepared_now": False,
            "metric_variation_executed": False,
            "tensor_field_equation_derived": False,
            "Einstein_equation_imported": False,
            "standard_GR_comparator_authorized": False,
            "rotating_source_lane_reopened": False,
            "gravitomagnetic_calculation_authorized": False,
            "C_k_action_embedding_authorized": False,
            "C_k_action_variation_authorized": False,
            "master_action_promoted": False,
            "GR_pillar_completed": False,
            "seam_closed": False,
            "simulation_executed": False,
            "empirical_analysis_executed": False,
            "automation_created": False,
        },
        "claim_ceiling": (
            "Fresh full-priority response selection only. It selects preparation of a bounded "
            "native continuum metric-variation surface existence-or-no-go packet. It creates no "
            "continuum action, metric variation, tensor field equation, Einstein-equation "
            "derivation, gravitomagnetic recovery, GR-pillar completion, seam closure, master-"
            "action promotion, empirical result, or automation."
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
            raise SystemExit("GR surface-failure response selection is stale or missing")
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

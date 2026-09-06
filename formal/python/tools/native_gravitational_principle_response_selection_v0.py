from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "NATIVE_GRAVITATIONAL_PRINCIPLE_RESPONSE_SELECTION_20260718_v0.json"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_native_gravitational_principle_response_selection_v0.py"
)
TARGET = (
    "select_response_to_no_native_gravitational_principle_from_full_toe_priority_map"
)
SELECTED_NEXT_TARGET = (
    "prepare_native_gravitational_principle_requirements_and_action_selection_packet_v0"
)

AUTHORITY_HASHES = {
    "formal/docs/lanes/MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_SECTOR_CONTRACT_PACKET_REVIEW_20260717_v0.md":
        "554e18d20bb3d6f2076cb4d6ea6c86480ee46d11f39f87c01673f37dfc8ec70c",
    "formal/docs/release/MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_SECTOR_CONTRACT_PACKET_REVIEW_20260717_v0.json":
        "6b902c6c620e15aa68898ae271e2de787186c9ef051e5c16c69edd0ea703ccfd",
    "formal/python/tools/minimal_native_continuum_gravitational_sector_contract_packet_review_v0.py":
        "ef92c485d3543d349af76ea3469027d71c2056e66e02c9cc259101c63955975e",
    "formal/python/tests/test_minimal_native_continuum_gravitational_sector_contract_packet_review_v0.py":
        "5f0a07fc4aa5438a811228e058062952bbdec09b362b5a5320e06307d3c77a80",
    "formal/toe_formal/ToeFormal/Derivation/MinimalNativeContinuumGravitationalSectorContractPacketReviewV0.lean":
        "7e4de22622b0d6c74645777f4899ee5f9ee6c0b04b4ca0fc9018a20a49cd0fec",
    "formal/docs/lanes/MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_SECTOR_CONTRACT_PACKET_20260717_v0.md":
        "5fc170073b11907bb14c05984d577c9b68e0a8d6ebfcf8c7fedf081a4ef292d8",
    "formal/docs/release/MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_SECTOR_CONTRACT_PACKET_20260717_v0.json":
        "2031bc50487bdcd07c5a18dcf2fcdddb611337b5150fbbf416b0d6ab0b9d86d4",
    "formal/docs/release/NATIVE_CONTINUUM_ACTION_ABSENCE_SCIENTIFIC_TARGET_SELECTION_20260717_v0.json":
        "86717db3c1a23c8d9562a398db847668d9422fef0261e682038d25e531d9abab",
    "formal/docs/release/GR_WEAK_ROTATING_SOURCE_GRAVITOMAGNETIC_RECOVERY_PACKET_REVIEW_20260717_v0.json":
        "de305a72dc522fe807c037bbe7980d96e3308d0547645ccb9939d1889720d987",
    "formal/docs/release/MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_AFTER_PHI_A_AND_PSI_A_RESULT_REVIEW_20260626_v0.json":
        "3d148464b39d50ae052866516d30bd3f167e1b80d276f56f593fc698f9e6734d",
    "formal/toe_formal/ToeFormal/Variational/WeakFieldPoissonLimit.lean":
        "b2519245872eaed3d874c25836ce355cca9e3bc0f11914e806a74c691f8d14da",
    "formal/docs/release/QFT_GR_CLASSICAL_EINSTEIN_SCALAR_COUPLING_ROUTE_PACKET_RESULT_REVIEW_20260618_v0.json":
        "0d9eb65ddb9fcf2e6dea8bd4feab58b51fb8db4dd002181bd4004df6d5395509",
    "formal/docs/paper/TOE_CANDIDATE_MASTER_ACTION_v0.md":
        "23aa11c3784da178097eef8ed7c32f9decf4db038a611e4a16364b9bed2db867",
}

CRITERIA = {
    "direct_missing_principle_attack": 3,
    "action_selection_discriminating_power": 3,
    "pass_fail_scientific_value": 3,
    "bounded_endpoint_precision": 3,
    "prevents_arbitrary_theory_choice": 2,
    "preserves_provenance_and_claim_boundaries": 2,
    "distinctiveness_leverage": 2,
    "infrastructure_avoidance": 2,
}

CANDIDATES = [
    {
        "candidate_id": (
            "DEFINE_NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_NO_GO_ENVELOPE"
        ),
        "target": SELECTED_NEXT_TARGET,
        "kind": "REQUIREMENTS_ACTION_SELECTION_AND_NO_GO_PACKET_PREPARATION",
        "scores": {
            "direct_missing_principle_attack": 5,
            "action_selection_discriminating_power": 5,
            "pass_fail_scientific_value": 5,
            "bounded_endpoint_precision": 5,
            "prevents_arbitrary_theory_choice": 5,
            "preserves_provenance_and_claim_boundaries": 5,
            "distinctiveness_leverage": 4,
            "infrastructure_avoidance": 5,
        },
        "scientific_endpoint": (
            "Determine which accepted project commitments constrain gravitational "
            "action families, whether they select only a standard-GR baseline, whether "
            "inequivalent families remain, and where a new distinctive postulate is "
            "logically unavoidable."
        ),
    },
    {
        "candidate_id": "EXPLICITLY_POSTULATE_NATIVE_GRAVITATIONAL_CANDIDATE",
        "target": "select_explicit_native_gravitational_postulate_and_action_family",
        "kind": "NEW_SCIENTIFIC_POSTULATE_AND_THEORY_SELECTION",
        "scores": {
            "direct_missing_principle_attack": 5,
            "action_selection_discriminating_power": 5,
            "pass_fail_scientific_value": 4,
            "bounded_endpoint_precision": 4,
            "prevents_arbitrary_theory_choice": 2,
            "preserves_provenance_and_claim_boundaries": 5,
            "distinctiveness_leverage": 5,
            "infrastructure_avoidance": 4,
        },
        "scientific_endpoint": (
            "Authorize and label one POSTULATED_NATIVE_CANDIDATE action family with an "
            "explicit rationale and discriminator, without representing it as derived."
        ),
    },
    {
        "candidate_id": "ACTIVATE_SUPPLIED_STANDARD_GR_COMPARATOR",
        "target": "prepare_supplied_standard_gr_variational_comparator_packet_v0",
        "kind": "SUPPLIED_STANDARD_GR_COMPARATOR_ONLY",
        "scores": {
            "direct_missing_principle_attack": 2,
            "action_selection_discriminating_power": 1,
            "pass_fail_scientific_value": 4,
            "bounded_endpoint_precision": 5,
            "prevents_arbitrary_theory_choice": 5,
            "preserves_provenance_and_claim_boundaries": 5,
            "distinctiveness_leverage": 1,
            "infrastructure_avoidance": 5,
        },
        "scientific_endpoint": (
            "Supply Einstein-Hilbert gravity explicitly and test downstream variation "
            "and weak rotating-source calculations with no native-gravity claim."
        ),
    },
    {
        "candidate_id": "PIVOT_TO_OTHER_HIGH_LEVERAGE_PHYSICS_OBLIGATION",
        "target": "select_next_non_gr_high_leverage_scientific_obligation",
        "kind": "PRESERVE_GR_BLOCK_AND_PIVOT",
        "scores": {
            "direct_missing_principle_attack": 1,
            "action_selection_discriminating_power": 1,
            "pass_fail_scientific_value": 4,
            "bounded_endpoint_precision": 4,
            "prevents_arbitrary_theory_choice": 5,
            "preserves_provenance_and_claim_boundaries": 5,
            "distinctiveness_leverage": 1,
            "infrastructure_avoidance": 5,
        },
        "scientific_endpoint": (
            "Retain the gravitational-principle block and move to a separately ranked "
            "pillar, seam, no-go, or prediction obligation."
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
            raise ValueError(
                f"native-principle response authority mismatch: {relative_path}"
            )
        rows.append({"relative_path": relative_path, "sha256": observed})

    review = json.loads(
        (
            REPO_ROOT
            / "formal/docs/release/MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_"
            "SECTOR_CONTRACT_PACKET_REVIEW_20260717_v0.json"
        ).read_text(encoding="utf-8")
    )
    if review.get("verdict") != "BLOCKED_NO_NATIVE_GRAVITATIONAL_PRINCIPLE":
        raise ValueError("terminal native-principle verdict mismatch")
    if review.get("primary_diagnostic") != (
        "NO_BOUND_NATIVE_GRAVITATIONAL_PRINCIPLE_OR_POSTULATE"
    ):
        raise ValueError("terminal native-principle diagnostic mismatch")
    if review.get("selected_next_target") != TARGET:
        raise ValueError("terminal review did not authorize fresh response selection")
    if review["contract_design_review"].get("status") != (
        "PASS_COMPLETE_BOUNDED_REVIEW_CONTRACT"
    ):
        raise ValueError("accepted minimal gravitational contract mismatch")
    if review["fail_fast_review"].get("first_failed_gate_order") != 5:
        raise ValueError("native-principle gate order mismatch")
    if review["native_principle_review"].get(
        "project_principle_bound_that_selects_action"
    ) is not False:
        raise ValueError("a project principle unexpectedly selects an action")
    if review["native_principle_review"].get(
        "explicit_postulated_native_candidate_selected"
    ) is not False:
        raise ValueError("a native postulate was unexpectedly selected")
    if any(row.get("authorized_now") for row in review["fresh_response_options"]):
        raise ValueError("terminal review prematurely authorized a response route")
    if review["scope"].get("requirements_no_go_route_selected") is not False:
        raise ValueError("requirements/no-go route was already selected")

    contract = json.loads(
        (
            REPO_ROOT
            / "formal/docs/release/MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_"
            "SECTOR_CONTRACT_PACKET_20260717_v0.json"
        ).read_text(encoding="utf-8")
    )
    if contract.get("verdict") != "PREPARED_PENDING_INDEPENDENT_REVIEW":
        raise ValueError("minimal gravitational contract packet verdict mismatch")
    if contract["scope"].get("gravitational_action_proposed_selected_or_derived") is not False:
        raise ValueError("contract packet unexpectedly proposed a gravitational action")

    prior_selection = json.loads(
        (
            REPO_ROOT
            / "formal/docs/release/NATIVE_CONTINUUM_ACTION_ABSENCE_"
            "SCIENTIFIC_TARGET_SELECTION_20260717_v0.json"
        ).read_text(encoding="utf-8")
    )
    if prior_selection["ranking"].get("runner_up_candidate_id") != (
        "NATIVE_DYNAMICAL_CORE_REQUIREMENTS_AND_NO_GO"
    ):
        raise ValueError("prior requirements/no-go fallback lineage mismatch")

    ck = json.loads(
        (
            REPO_ROOT
            / "formal/docs/release/MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_"
            "AFTER_PHI_A_AND_PSI_A_RESULT_REVIEW_20260626_v0.json"
        ).read_text(encoding="utf-8")
    )
    if ck.get("all_C_k_families_admissibility_only") is not True:
        raise ValueError("external C_k firewall mismatch")
    if ck.get("C_k_action_variation_authorized") is not False:
        raise ValueError("C_k action variation unexpectedly authorized")

    comparator = json.loads(
        (
            REPO_ROOT
            / "formal/docs/release/QFT_GR_CLASSICAL_EINSTEIN_SCALAR_COUPLING_"
            "ROUTE_PACKET_RESULT_REVIEW_20260618_v0.json"
        ).read_text(encoding="utf-8")
    )
    if comparator.get("provisional_classical_sandbox_route_only") is not True:
        raise ValueError("supplied standard-GR comparator boundary mismatch")
    return rows


def build_selection() -> dict[str, Any]:
    authority = _validate_authority()
    ranking = _rank(CRITERIA)
    sensitivity = _sensitivity()
    selected_id = (
        "DEFINE_NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_NO_GO_ENVELOPE"
    )
    if ranking[0]["candidate_id"] != selected_id:
        raise ValueError("unexpected native-principle response-selection winner")
    if not sensitivity["selected_candidate_stable_in_all_variants"]:
        raise ValueError("native-principle response-selection winner is unstable")
    tool_path = Path(__file__).resolve()
    test_path = REPO_ROOT / TEST_RELATIVE_PATH
    if not test_path.exists():
        raise ValueError("native-principle response-selection test missing")

    return {
        "schema_id": "NATIVE_GRAVITATIONAL_PRINCIPLE_RESPONSE_SELECTION_20260718_v0",
        "captured_at_utc": "2026-07-18T00:00:00Z",
        "target": TARGET,
        "verdict": (
            "SELECTED_NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_NO_GO_PREPARATION"
        ),
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": (
            "PREPARATION_ONLY_REQUIREMENTS_ACTION_SELECTION_AND_NO_GO_ENVELOPE"
        ),
        "authority": {
            "terminal_contract_review": "BLOCKED_NO_NATIVE_GRAVITATIONAL_PRINCIPLE",
            "terminal_diagnostic": (
                "NO_BOUND_NATIVE_GRAVITATIONAL_PRINCIPLE_OR_POSTULATE"
            ),
            "contract_design": "PASS_COMPLETE_BOUNDED_REVIEW_CONTRACT",
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
            "pillar": "GR",
            "obligation_class": (
                "NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_ACTION_SELECTION_AND_NO_GO"
            ),
            "question": (
                "Do the project's accepted commitments select or materially narrow a "
                "gravitational action family, collapse only to a supplied standard-GR "
                "baseline, remain underdetermined, or prove that a new distinctive "
                "gravitational postulate is unavoidable?"
            ),
            "packet_must_freeze": [
                "byte-bound accepted project commitments and their authority classes",
                "accepted commitments separated from convenient or standard-GR assumptions",
                "minimal metric, dimension, locality, covariance, and derivative-order hypotheses",
                "external C_k firewall and prohibited action embedding",
                "Newton-Poisson, source-conservation, momentum-current, stability, and no-fitting obligations",
                "requirement-by-requirement action-selection power matrix",
                "standard-GR collapse test under the frozen minimal assumptions",
                "inequivalent-action-family survival and elimination criteria",
                "distinctiveness test for coefficients, cross-pillar links, or observables",
                "exact no-go envelope and the first point where a new postulate is required",
            ],
            "allowed_terminal_results": [
                "NATIVE_PRINCIPLE_SET_SELECTS_ACTION_FAMILY",
                "CURRENT_REQUIREMENTS_COLLAPSE_TO_STANDARD_GR",
                "ACTION_FAMILY_UNDERDETERMINED",
                "DISTINCTIVE_GRAVITATIONAL_POSTULATE_REQUIRED",
                "REQUIREMENT_SET_INCONSISTENT",
                "NO_GO_UNDER_MINIMAL_METRIC_LOCAL_ASSUMPTIONS",
            ],
            "stopping_rule": (
                "Prepare one requirements, action-selection, and no-go packet and stop "
                "for independent review. Do not propose or select an action, authorize "
                "a new postulate, activate the standard-GR comparator, perform variation, "
                "import matter fields, resume frame-dragging, or build new infrastructure."
            ),
        },
        "retained_boundaries": {
            "minimal_gravitational_contract": "ACCEPTED",
            "native_gravitational_principle": "NOT_FOUND",
            "native_gravitational_action": "NOT_SELECTED",
            "explicit_native_postulate": "NOT_AUTHORIZED",
            "matter_action": "NOT_DEFINED",
            "metric_variation": "NOT_EXECUTED",
            "recovery_ladder": "NOT_ENTERED",
            "standard_Einstein_Hilbert_sector": "SUPPLIED_COMPARATOR_ONLY",
            "historical_master_action": "SCHEMATIC_ONLY",
            "C_k": "EXTERNAL_ADMISSIBILITY_AUDIT_ONLY",
            "gravitomagnetic_recovery": "BLOCKED_UPSTREAM",
        },
        "scope": {
            "response_selection_executed": True,
            "packet_preparation_authorized": True,
            "packet_prepared_now": False,
            "requirements_or_no_go_result_derived": False,
            "native_gravitational_principle_created_or_selected": False,
            "native_gravitational_postulate_authorized": False,
            "native_gravitational_action_proposed_or_selected": False,
            "action_family_selected": False,
            "standard_GR_collapse_claimed": False,
            "standard_GR_comparator_activated": False,
            "matter_fields_or_lagrangian_imported": False,
            "metric_or_tetrad_variation_executed": False,
            "stress_energy_derived": False,
            "tensor_field_equation_derived": False,
            "gravitomagnetic_route_reopened": False,
            "C_k_embedded_or_varied": False,
            "master_action_promoted": False,
            "GR_pillar_completed": False,
            "seam_closed": False,
            "simulation_executed": False,
            "empirical_analysis_executed": False,
            "general_tooling_created": False,
            "automation_created": False,
        },
        "claim_ceiling": (
            "Fresh response selection only. It authorizes preparation of one bounded "
            "native-gravitational-principle requirements, action-selection, and no-go "
            "packet. It creates no principle, postulate, action, matter sector, variation, "
            "tensor equation, standard-GR result, frame-dragging result, promotion, "
            "empirical result, general tooling, or automation."
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
            raise SystemExit(
                "native-gravitational-principle response selection is stale or missing"
            )
        report = json.loads(raw)
        print(json.dumps({
            "margin": (
                report["ranking"]["selected_score"]
                - report["ranking"]["runner_up_score"]
            ),
            "minimum_sensitivity_margin": report["sensitivity_analysis"][
                "minimum_winning_margin"
            ],
            "selected": report["ranking"]["selected_candidate_id"],
            "sensitivity_variants": report["sensitivity_analysis"]["variant_count"],
            "status": "CHECKED",
        }, sort_keys=True))
        return 0
    report_path.write_bytes(raw)
    print(report_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

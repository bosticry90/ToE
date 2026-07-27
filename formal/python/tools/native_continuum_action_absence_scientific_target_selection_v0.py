from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "NATIVE_CONTINUUM_ACTION_ABSENCE_SCIENTIFIC_TARGET_SELECTION_20260717_v0.json"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_native_continuum_action_absence_scientific_target_selection_v0.py"
)
TARGET = "select_next_scientific_target_with_native_continuum_action_not_defined"
SELECTED_NEXT_TARGET = (
    "prepare_minimal_native_continuum_gravitational_sector_contract_packet_v0"
)

AUTHORITY_HASHES = {
    "formal/docs/lanes/TOE_CANDIDATE_MASTER_ACTION_CK_FIREWALL_AUTHORITY_RECONCILIATION_PACKET_REVIEW_20260717_v0.md":
        "bc7bae0bf6b1d4e5167968e7d2d3687d02d754a4d309921fb44c4032e9d1ccd1",
    "formal/docs/release/TOE_CANDIDATE_MASTER_ACTION_CK_FIREWALL_AUTHORITY_RECONCILIATION_PACKET_REVIEW_20260717_v0.json":
        "66ed74e9264c82eaa9715cc0369020f93b7956f9f3aa2f9b8b6abb5141fe2e64",
    "formal/python/tools/toe_candidate_master_action_ck_firewall_authority_reconciliation_packet_review_v0.py":
        "c7e4165c246cd12ca2e0ad5df27c2669dda10aa926d68f9a56b78fa636606782",
    "formal/python/tests/test_toe_candidate_master_action_ck_firewall_authority_reconciliation_packet_review_v0.py":
        "e3725dbbb2815d199c293211d628ca6dd739056d999d768127e64db1702734a4",
    "formal/toe_formal/ToeFormal/Derivation/ToeCandidateMasterActionCKFirewallAuthorityReconciliationPacketReviewV0.lean":
        "7f26ff35764241ab0f16155dc55fd1eea4af3d4be3a31947df063efdcc6941a0",
    "formal/docs/release/POST_SR_TOOLING_FULL_TOE_SCIENTIFIC_PRIORITY_SELECTION_20260717_v0.json":
        "ca9d4f032f7d9bd0ce2fef104e6c7d6d1718582ad5f2266ea4a8c3fbd4220179",
    "formal/docs/release/GR_WEAK_ROTATING_SOURCE_GRAVITOMAGNETIC_RECOVERY_PACKET_REVIEW_20260717_v0.json":
        "de305a72dc522fe807c037bbe7980d96e3308d0547645ccb9939d1889720d987",
    "formal/docs/release/GR_NATIVE_CONTINUUM_METRIC_VARIATION_AND_TENSOR_SURFACE_PACKET_REVIEW_20260717_v0.json":
        "4b894a31d1eb9ea29b06f70934913f42a007db31bbf3ac75f2ab8411674d1939",
    "formal/docs/paper/TOE_CANDIDATE_MASTER_ACTION_v0.md":
        "23aa11c3784da178097eef8ed7c32f9decf4db038a611e4a16364b9bed2db867",
    "formal/docs/release/MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_AFTER_PHI_A_AND_PSI_A_RESULT_REVIEW_20260626_v0.json":
        "3d148464b39d50ae052866516d30bd3f167e1b80d276f56f593fc698f9e6734d",
    "formal/toe_formal/ToeFormal/Variational/WeakFieldPoissonLimit.lean":
        "b2519245872eaed3d874c25836ce355cca9e3bc0f11914e806a74c691f8d14da",
    "formal/docs/release/QFT_GR_CLASSICAL_EINSTEIN_SCALAR_COUPLING_ROUTE_PACKET_RESULT_REVIEW_20260618_v0.json":
        "0d9eb65ddb9fcf2e6dea8bd4feab58b51fb8db4dd002181bd4004df6d5395509",
}

CRITERIA = {
    "direct_missing_core_attack": 3,
    "bounded_endpoint_precision": 3,
    "pass_fail_scientific_value": 3,
    "claim_state_change_potential": 3,
    "uses_retained_authority_without_import": 2,
    "avoids_omnibus_master_action": 2,
    "downstream_gr_unlock_value": 2,
    "infrastructure_avoidance": 2,
}

CANDIDATES = [
    {
        "candidate_id": "DEFINE_MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_SECTOR",
        "target": SELECTED_NEXT_TARGET,
        "kind": "BOUNDED_NATIVE_GRAVITATIONAL_ACTION_CONTRACT_EXISTENCE_OR_BLOCK",
        "scores": {
            "direct_missing_core_attack": 5,
            "bounded_endpoint_precision": 5,
            "pass_fail_scientific_value": 5,
            "claim_state_change_potential": 5,
            "uses_retained_authority_without_import": 4,
            "avoids_omnibus_master_action": 5,
            "downstream_gr_unlock_value": 5,
            "infrastructure_avoidance": 4,
        },
        "scientific_endpoint": (
            "Determine whether one complete native continuum gravitational-sector "
            "action contract can be defined with explicit variables, symmetries, units, "
            "boundary treatment, and matter coupling, or return an exact native-principle "
            "or matter-coupling block."
        ),
    },
    {
        "candidate_id": "NATIVE_DYNAMICAL_CORE_REQUIREMENTS_AND_NO_GO",
        "target": (
            "prepare_native_dynamical_core_requirements_and_no_go_packet_v0"
        ),
        "kind": "FUTURE_ACTION_REQUIREMENTS_THEOREM_OR_COUNTERMODEL",
        "scores": {
            "direct_missing_core_attack": 4,
            "bounded_endpoint_precision": 5,
            "pass_fail_scientific_value": 5,
            "claim_state_change_potential": 4,
            "uses_retained_authority_without_import": 5,
            "avoids_omnibus_master_action": 5,
            "downstream_gr_unlock_value": 3,
            "infrastructure_avoidance": 5,
        },
        "scientific_endpoint": (
            "Derive a minimum requirements or no-go surface for future native actions "
            "from retained sector results, symmetry obligations, external C_k policy, "
            "known limits, and unsupported-degree-of-freedom exclusions."
        ),
    },
    {
        "candidate_id": "CONTINUUM_GAUGE_MATTER_EXCHANGE_SECTOR_FIRST",
        "target": "prepare_continuum_gauge_matter_exchange_sector_packet_v0",
        "kind": "NON_GR_SECTOR_FIRST_PHYSICS_OBLIGATION",
        "scores": {
            "direct_missing_core_attack": 2,
            "bounded_endpoint_precision": 4,
            "pass_fail_scientific_value": 5,
            "claim_state_change_potential": 4,
            "uses_retained_authority_without_import": 4,
            "avoids_omnibus_master_action": 5,
            "downstream_gr_unlock_value": 1,
            "infrastructure_avoidance": 5,
        },
        "scientific_endpoint": (
            "Advance one independently defined gauge-matter source and exchange sector "
            "while retaining the absence of a native continuum master action."
        ),
    },
    {
        "candidate_id": "SUPPLIED_STANDARD_GR_VARIATIONAL_COMPARATOR",
        "target": "prepare_supplied_standard_gr_variational_comparator_packet_v0",
        "kind": "SUPPLIED_STANDARD_GR_COMPARATOR_ONLY",
        "scores": {
            "direct_missing_core_attack": 1,
            "bounded_endpoint_precision": 5,
            "pass_fail_scientific_value": 4,
            "claim_state_change_potential": 2,
            "uses_retained_authority_without_import": 5,
            "avoids_omnibus_master_action": 5,
            "downstream_gr_unlock_value": 2,
            "infrastructure_avoidance": 5,
        },
        "scientific_endpoint": (
            "Supply the Einstein-Hilbert sector explicitly and reproduce its variation "
            "and downstream weak-field structure as a comparator with no native claim."
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
    selected_id = "DEFINE_MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_SECTOR"
    return {
        "variant_count": len(rows),
        "rows": rows,
        "selected_candidate_stable_in_all_variants": all(
            row["selected_candidate_id"] == selected_id for row in rows
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
            raise ValueError(f"native-core selection authority mismatch: {relative_path}")
        rows.append({"relative_path": relative_path, "sha256": observed})

    current_review = json.loads(
        (
            REPO_ROOT
            / "formal/docs/release/TOE_CANDIDATE_MASTER_ACTION_CK_FIREWALL_"
            "AUTHORITY_RECONCILIATION_PACKET_REVIEW_20260717_v0.json"
        ).read_text(encoding="utf-8")
    )
    if current_review.get("verdict") != "MASTER_ACTION_REMAINS_SCHEMATIC_ONLY":
        raise ValueError("schematic-only terminal verdict mismatch")
    if current_review.get("selected_next_target") != TARGET:
        raise ValueError("terminal review did not authorize scientific target selection")
    if current_review["retained_status"].get(
        "native_executable_continuum_action"
    ) != "NOT_YET_DEFINED":
        raise ValueError("native continuum action absence mismatch")
    if current_review["scope"].get("successor_action_created") is not False:
        raise ValueError("terminal review unexpectedly created a successor action")

    gr_review = json.loads(
        (
            REPO_ROOT
            / "formal/docs/release/GR_NATIVE_CONTINUUM_METRIC_VARIATION_AND_"
            "TENSOR_SURFACE_PACKET_REVIEW_20260717_v0.json"
        ).read_text(encoding="utf-8")
    )
    if gr_review.get("primary_diagnostic") != "CK_FIREWALL_ACTION_SOURCE_CONFLICT":
        raise ValueError("native GR action-contract obstruction mismatch")

    rotating_review = json.loads(
        (
            REPO_ROOT
            / "formal/docs/release/GR_WEAK_ROTATING_SOURCE_GRAVITOMAGNETIC_"
            "RECOVERY_PACKET_REVIEW_20260717_v0.json"
        ).read_text(encoding="utf-8")
    )
    if rotating_review.get("verdict") != "BLOCKED_FIELD_EQUATION_SURFACE_FAILURE":
        raise ValueError("rotating-source obstruction mismatch")

    action = (
        REPO_ROOT / "formal/docs/paper/TOE_CANDIDATE_MASTER_ACTION_v0.md"
    ).read_text(encoding="utf-8")
    for token in ("working-form artifact only", "explicitly non-canonical"):
        if token not in action:
            raise ValueError(f"schematic action boundary token missing: {token}")

    ck = json.loads(
        (
            REPO_ROOT
            / "formal/docs/release/MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_"
            "AFTER_PHI_A_AND_PSI_A_RESULT_REVIEW_20260626_v0.json"
        ).read_text(encoding="utf-8")
    )
    if ck.get("all_C_k_families_admissibility_only") is not True:
        raise ValueError("external C_k policy mismatch")
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
        raise ValueError("supplied classical comparator boundary mismatch")
    return rows


def build_selection() -> dict[str, Any]:
    authority = _validate_authority()
    ranking = _rank(CRITERIA)
    sensitivity = _sensitivity()
    selected_id = "DEFINE_MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_SECTOR"
    if ranking[0]["candidate_id"] != selected_id:
        raise ValueError("unexpected native-core scientific-target winner")
    if not sensitivity["selected_candidate_stable_in_all_variants"]:
        raise ValueError("native-core scientific-target winner is sensitivity-unstable")
    tool_path = Path(__file__).resolve()
    test_path = REPO_ROOT / TEST_RELATIVE_PATH
    if not test_path.exists():
        raise ValueError("native-core scientific-target selection test missing")

    return {
        "schema_id": (
            "NATIVE_CONTINUUM_ACTION_ABSENCE_SCIENTIFIC_TARGET_SELECTION_"
            "20260717_v0"
        ),
        "captured_at_utc": "2026-07-17T00:00:00Z",
        "target": TARGET,
        "verdict": (
            "SELECTED_MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_SECTOR_PREPARATION"
        ),
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": (
            "PREPARATION_ONLY_MINIMAL_NATIVE_GRAVITATIONAL_ACTION_CONTRACT"
        ),
        "authority": {
            "terminal_master_action_status": "MASTER_ACTION_REMAINS_SCHEMATIC_ONLY",
            "native_executable_continuum_action": "NOT_YET_DEFINED",
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
                "MINIMAL_NATIVE_CONTINUUM_GRAVITATIONAL_ACTION_CONTRACT_"
                "EXISTENCE_OR_BLOCK"
            ),
            "question": (
                "Can the project define one complete native continuum gravitational "
                "action, with declared variables, symmetries, dimensions, boundary "
                "treatment, and matter coupling, from which a tensor field equation "
                "could later be derived without importing standard GR as the answer?"
            ),
            "packet_must_freeze": [
                "one exact proposed native gravitational principle and authority class",
                "continuum spacetime domain, dimension, orientation, and retained signature",
                "one independent gravitational variable: metric or tetrad",
                "diffeomorphism and, if tetrad-based, local Lorentz symmetry contract",
                "complete gravitational action density with constants and dimensions",
                "boundary term and admissible variation contract",
                "minimal matter coupling and variational stress-energy definition",
                "C_k firewall: external admissibility and audit only",
                "Rep32 relationship classified without inherited continuum authority",
                "required Newton-Poisson and future tensor weak-field recovery obligations",
            ],
            "allowed_outcomes": [
                "MINIMAL_NATIVE_GRAVITATIONAL_ACTION_CONTRACT_READY",
                "SUPPLIED_EINSTEIN_HILBERT_SECTOR_ONLY",
                "BLOCKED_NO_NATIVE_GRAVITATIONAL_PRINCIPLE",
                "BLOCKED_MATTER_COUPLING_UNDEFINED",
            ],
            "stopping_rule": (
                "Prepare one bounded gravitational-sector action-contract packet and "
                "stop for independent review. Do not define a successor master action, "
                "perform variation, import the Einstein equation, resume frame-dragging, "
                "or build general symbolic infrastructure."
            ),
        },
        "retained_boundaries": {
            "historical_master_action_v0": "SCHEMATIC_ORGANIZING_SURFACE",
            "successor_master_action": "NOT_AUTHORIZED_OR_CREATED",
            "C_k": "EXTERNAL_ADMISSIBILITY_AUDIT_ONLY",
            "bounded_discrete_Newton_Poisson_route": "RETAINED",
            "native_tensor_field_equation": "NOT_DERIVED",
            "gravitomagnetic_recovery": "BLOCKED_UPSTREAM",
            "standard_GR_sandbox": "SUPPLIED_COMPARATOR_ONLY",
            "Rep32": "SEPARATE_STRUCTURAL_MODEL_WITHOUT_CONTINUUM_AUTHORITY",
        },
        "scope": {
            "scientific_target_selection_executed": True,
            "packet_preparation_authorized": True,
            "packet_prepared_now": False,
            "native_gravitational_action_defined": False,
            "successor_master_action_prepared_or_created": False,
            "C_k_embedded_or_varied": False,
            "metric_or_tetrad_variation_executed": False,
            "stress_energy_derived": False,
            "tensor_field_equation_derived": False,
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
            "Fresh scientific target selection only. It selects preparation of a bounded "
            "minimal native continuum gravitational-sector action-contract packet. It "
            "defines no action, creates no successor master theory, executes no variation, "
            "derives no tensor equation, imports no Einstein equation, reopens no "
            "gravitomagnetic calculation, and creates no promotion, empirical result, "
            "migration, or automation."
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
            raise SystemExit("native-core scientific-target selection is stale or missing")
        report = json.loads(raw)
        print(json.dumps({
            "margin": (
                report["ranking"]["selected_score"]
                - report["ranking"]["runner_up_score"]
            ),
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

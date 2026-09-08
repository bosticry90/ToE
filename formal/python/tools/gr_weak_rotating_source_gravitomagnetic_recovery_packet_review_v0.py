from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "GR_WEAK_ROTATING_SOURCE_GRAVITOMAGNETIC_RECOVERY_PACKET_REVIEW_20260717_v0.json"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_gr_weak_rotating_source_gravitomagnetic_recovery_packet_review_v0.py"
)
REVIEW_CONTRACT_RELATIVE_PATH = (
    "formal/docs/lanes/"
    "GR_WEAK_ROTATING_SOURCE_GRAVITOMAGNETIC_RECOVERY_PACKET_REVIEW_20260717_v0.md"
)
TARGET = "review_gr_weak_rotating_source_gravitomagnetic_recovery_packet_v0_result"
SELECTED_NEXT_TARGET = (
    "select_response_to_gr_field_equation_surface_failure_from_full_toe_priority_map"
)
VERDICT = "BLOCKED_FIELD_EQUATION_SURFACE_FAILURE"
PRIMARY_DIAGNOSTIC = "FIELD_EQUATION_SURFACE_FAILURE"

AUTHORITY_AND_SOURCE_HASHES = {
    "formal/docs/release/GR_WEAK_ROTATING_SOURCE_GRAVITOMAGNETIC_RECOVERY_PACKET_20260717_v0.json":
        "3a6a1f848241f4a467c17000e6a27a44922bc7636ec7be412eafbddc65d2fe9a",
    "formal/docs/lanes/GR_WEAK_ROTATING_SOURCE_GRAVITOMAGNETIC_RECOVERY_PACKET_20260717_v0.md":
        "0e206867019c2c8b66431a6bc3ca161ab6f0b8fae1fa9cdd08f83830cc38c92e",
    "formal/python/tools/gr_weak_rotating_source_gravitomagnetic_recovery_packet_v0.py":
        "ae28f62716b24548b093690bba954613ba95f9a95b7c08b5cb7995841c508f7f",
    "formal/python/tests/test_gr_weak_rotating_source_gravitomagnetic_recovery_packet_v0.py":
        "f9614f56cd822e3e5023632cf42923855fe1f297175a412ab9293f87c9c72321",
    "formal/toe_formal/ToeFormal/Derivation/GRWeakRotatingSourceGravitomagneticRecoveryPacketV0.lean":
        "70d0791b408c71fa17ba2912364b37fc673f14a7567f9aa610135bc164a4400a",
    "formal/toe_formal/ToeFormal/Variational/ActionRep32Def.lean":
        "da375e85850deb5d32da8a60c24d2fd7021c95143f8da036973d9575bd398458",
    "formal/toe_formal/ToeFormal/Variational/FirstVariationRep32Def.lean":
        "8c7a6a3f3aa74f240945e3d2ac23a05c6e5fa6fa310977ba9c03db89f456d920",
    "formal/toe_formal/ToeFormal/Variational/WeakFieldPoissonLimit.lean":
        "b2519245872eaed3d874c25836ce355cca9e3bc0f11914e806a74c691f8d14da",
    "formal/toe_formal/ToeFormal/Variational/GR01BridgePromotion.lean":
        "162cdd0d9596566457ae40c340329b15064e4d0ed17d20deadc48fc2fc431384",
    "formal/docs/paper/DERIVATION_TARGET_GR01_FULL_DERIVATION_DISCHARGE_v0.md":
        "1d9fbe0b49d45aad3781b4217dc108a6f2c16361cd59fa662c8283de10f6ac67",
    "formal/docs/paper/FULL_PILLAR_TARGET_MAP_REBASE_v0.md":
        "2550ca7b24e03f59535133b3856ed2d7d5094a7fd3ab5a96a5a90faaeb8eda25",
    "formal/toe_formal/ToeFormal/Derivation/QFTGRClassicalEinsteinScalarCouplingRoutePacketForProvisionalScalarSource.lean":
        "b88b8941eca415530dcb3082299b56e8c26c6036a0950776f7358c4e00ee7653",
    "formal/toe_formal/ToeFormal/Derivation/QFTGRClassicalEinsteinScalarCouplingRoutePacketResultReview.lean":
        "a9844fb6aa637395ba867d95ffb1315e8c64ec2f8f61ec01b6b695ed5cd2d32d",
    REVIEW_CONTRACT_RELATIVE_PATH:
        "f682ef0aeaa16d544a99ecc856a50f7fc8f9fd4407aadf63ee906848c2be1665",
}


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _validate_authority_and_sources() -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for relative_path, expected_hash in AUTHORITY_AND_SOURCE_HASHES.items():
        observed = _sha256((REPO_ROOT / relative_path).read_bytes())
        if observed != expected_hash:
            raise ValueError(f"GR review authority/source hash mismatch: {relative_path}")
        rows.append({"relative_path": relative_path, "sha256": observed})

    packet = json.loads(
        (REPO_ROOT / "formal/docs/release/GR_WEAK_ROTATING_SOURCE_GRAVITOMAGNETIC_RECOVERY_PACKET_20260717_v0.json").read_text(
            encoding="utf-8"
        )
    )
    if packet.get("verdict") != "PREPARED_PENDING_INDEPENDENT_REVIEW":
        raise ValueError("GR packet preparation verdict mismatch")
    if packet.get("selected_next_target") != TARGET:
        raise ValueError("GR review does not consume packet-selected target")
    if packet["project_source_bindings"]["required_count"] != 3:
        raise ValueError("GR packet source binding count mismatch")

    action = (
        REPO_ROOT / "formal/toe_formal/ToeFormal/Variational/ActionRep32Def.lean"
    ).read_text(encoding="utf-8")
    for token in (
        "structural-only",
        "Leaves analytic derivation of `firstVariationRep32` from an action functional open",
        "def actionRep32 : ActionRep32Scaffold",
        "EL := P_rep32",
    ):
        if token not in action:
            raise ValueError(f"action-surface review token missing: {token}")

    variation = (
        REPO_ROOT / "formal/toe_formal/ToeFormal/Variational/FirstVariationRep32Def.lean"
    ).read_text(encoding="utf-8")
    for token in (
        "structural-only",
        "def P_rep32 : FieldRep32 -> FieldRep32",
        "def firstVariationRep32",
        "theorem P_represents_rep32",
    ):
        if token not in variation:
            raise ValueError(f"first-variation review token missing: {token}")

    weak = (
        REPO_ROOT / "formal/toe_formal/ToeFormal/Variational/WeakFieldPoissonLimit.lean"
    ).read_text(encoding="utf-8")
    for token in (
        "abbrev ScalarField3D",
        "def DiscretePoissonResidual3D",
        "def WeakFieldPoissonLimitStatement3D",
        "No analytic discharge is claimed in this module",
    ):
        if token not in weak:
            raise ValueError(f"weak-field review token missing: {token}")

    bridge = (
        REPO_ROOT / "formal/toe_formal/ToeFormal/Variational/GR01BridgePromotion.lean"
    ).read_text(encoding="utf-8")
    if "No Einstein-field-equation recovery claim" not in bridge:
        raise ValueError("GR bridge nonclaim is missing")

    full_map = (
        REPO_ROOT / "formal/docs/paper/FULL_PILLAR_TARGET_MAP_REBASE_v0.md"
    ).read_text(encoding="utf-8")
    for token in (
        "GR01 weak-field / Poisson target under explicit assumptions",
        "Einstein-equation derivation from action variation",
        "gr01_continuum_limit_source_identification_retained",
        "LOCAL_DONE_PILLAR_TARGET_OPEN",
    ):
        if token not in full_map:
            raise ValueError(f"full-GR target-map token missing: {token}")

    provisional = (
        REPO_ROOT / "formal/toe_formal/ToeFormal/Derivation/QFTGRClassicalEinsteinScalarCouplingRoutePacketForProvisionalScalarSource.lean"
    ).read_text(encoding="utf-8")
    for token in (
        "provisionalClassicalSandboxRouteOnly",
        "toeNativeMatterDerivationClaimed : Bool := false",
        "coupledEinsteinScalarSystemSolved : Bool := false",
        "masterActionPromoted : Bool := false",
    ):
        if token not in provisional:
            raise ValueError(f"provisional Einstein-scalar boundary missing: {token}")

    review_contract = (REPO_ROOT / REVIEW_CONTRACT_RELATIVE_PATH).read_text(
        encoding="utf-8"
    )
    for token in (
        VERDICT,
        PRIMARY_DIAGNOSTIC,
        "UPSTREAM_FAIL_FAST",
        SELECTED_NEXT_TARGET,
    ):
        if token not in review_contract:
            raise ValueError(f"review-contract token missing: {token}")
    return rows


STAGE_ADJUDICATION = [
    {
        "stage": 1,
        "stage_id": "PROJECT_SURFACE_TO_CONTINUUM_TENSOR_AUTHORITY",
        "required_output": "project-authorized continuum tensor metric field equation",
        "status": "FAILED",
        "diagnostic": PRIMARY_DIAGNOSTIC,
    },
] + [
    {
        "stage": stage,
        "stage_id": stage_id,
        "required_output": required_output,
        "status": "NOT_EVALUATED",
        "diagnostic": "UPSTREAM_FAIL_FAST",
    }
    for stage, stage_id, required_output in (
        (2, "LINEARIZE_AND_TRACE_REVERSE", "linearized trace-reversed tensor equation"),
        (3, "STATIONARY_0I_REDUCTION", "stationary 0i source equation"),
        (4, "GREEN_AND_CURRENT_MULTIPOLE", "boundary-fixed current-dipole solution"),
        (5, "EXTERIOR_G0I_EXTRACTION", "computed exterior g_0i coefficient"),
        (6, "METRIC_TO_ORBIT_TRANSPORT", "computed secular nodal coefficient"),
        (7, "POSTCOMPUTATION_ORACLE_COMPARISON", "metric and nodal oracle comparisons"),
    )
]


def build_review() -> dict[str, Any]:
    authority_rows = _validate_authority_and_sources()
    tool_path = Path(__file__).resolve()
    test_path = REPO_ROOT / TEST_RELATIVE_PATH
    if not test_path.exists():
        raise ValueError("GR packet review test is missing")
    packet = json.loads(
        (REPO_ROOT / "formal/docs/release/GR_WEAK_ROTATING_SOURCE_GRAVITOMAGNETIC_RECOVERY_PACKET_20260717_v0.json").read_text(
            encoding="utf-8"
        )
    )
    return {
        "schema_id": "GR_WEAK_ROTATING_SOURCE_GRAVITOMAGNETIC_RECOVERY_PACKET_REVIEW_20260717_v0",
        "captured_at_utc": "2026-07-17T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "primary_diagnostic": PRIMARY_DIAGNOSTIC,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": "FULL_PRIORITY_RESPONSE_SELECTION_ONLY",
        "authority": {
            "consumed_packet_id": packet["schema_id"],
            "consumed_packet_verdict": packet["verdict"],
            "frozen_inputs": authority_rows,
            "generator": {
                "relative_path": tool_path.relative_to(REPO_ROOT).as_posix(),
                "sha256": _sha256(tool_path.read_bytes()),
            },
            "test": {
                "relative_path": TEST_RELATIVE_PATH,
                "sha256": _sha256(test_path.read_bytes()),
            },
        },
        "fail_fast_gate": {
            "question": (
                "Does an authorized project route derive a continuum tensor metric field "
                "equation with an independently normalized 0i component from the current "
                "GR surface?"
            ),
            "answer": False,
            "required_object_present": False,
            "fail_fast_applied": True,
            "diagnostic": PRIMARY_DIAGNOSTIC,
            "derivation_authorized": False,
        },
        "exact_binding_review": [
            {
                "binding_id": "GR_PROJECT_ACTION_REP32_SCAFFOLD",
                "binding_reproduced": True,
                "observed_type": "FieldRep32 structural action scaffold with assigned P_rep32 EL",
                "continuum_metric_tensor_equation_derived": False,
                "finding": "analytic first variation from the action remains open",
            },
            {
                "binding_id": "GR_PROJECT_BOUNDED_DISCRETE_WEAK_FIELD_POISSON",
                "binding_reproduced": True,
                "observed_type": "scalar lattice Poisson residual in 1D/3D",
                "continuum_metric_tensor_equation_derived": False,
                "finding": "no tensor completion, 0i component, or continuum limit",
            },
            {
                "binding_id": "GR_PROJECT_DISCHARGE_BOUNDARY",
                "binding_reproduced": True,
                "observed_type": "bounded/discrete weak-field v0 discharge under explicit bridges",
                "continuum_metric_tensor_equation_derived": False,
                "finding": "scaffold, action-variation, bridge, and remainder blockers remain",
            },
        ],
        "alternative_surface_audit": {
            "authorized_project_derived_continuum_tensor_surface_found": False,
            "provisional_einstein_scalar_route": {
                "equation_recorded": True,
                "classification": "SUPPLIED_STANDARD_GR_PROVISIONAL_CLASSICAL_SANDBOX",
                "toe_native_gravitational_equation_derived": False,
                "coupled_solution_constructed": False,
                "eligible_to_discharge_gate": False,
            },
            "full_gr_target_map": {
                "current_local_result": "GR01 weak-field / Poisson target",
                "full_target": "Einstein-equation derivation from action variation",
                "status": "LOCAL_DONE_PILLAR_TARGET_OPEN",
                "retained_blocker": "gr01_continuum_limit_source_identification_retained",
            },
        },
        "stage_adjudication": {
            "stage_count": 7,
            "failed_count": 1,
            "not_evaluated_count": 6,
            "rows": STAGE_ADJUDICATION,
        },
        "retained_packet_policy_without_execution": {
            "coordinate_signature_si_policy_reproduced": True,
            "source_gauge_boundary_contract_reproduced": True,
            "standard_gr_oracles_remain_comparison_only": True,
            "coefficient_fitting_remains_forbidden": True,
            "planned_control_count": packet["required_controls"]["required_count"],
            "controls_executed": 0,
            "controls_adjudicated": False,
            "downstream_sign_coefficient_and_orbital_checks_adjudicated": False,
        },
        "scientific_interpretation": {
            "standard_GR_refuted": False,
            "standard_Lense_Thirring_result_refuted": False,
            "project_GR_recovery_established": False,
            "finding": (
                "The current project GR authority does not provide the continuum tensor "
                "field equation required to start the gravitomagnetic recovery."
            ),
        },
        "future_options_requiring_fresh_priority_selection": [
            {
                "route_id": "PROJECT_GR_TENSOR_SURFACE_ROUTE",
                "meaning": (
                    "derive a continuum tensor weak-field equation from an explicitly "
                    "authorized gravitational action or theorem surface"
                ),
                "authorized_now": False,
            },
            {
                "route_id": "STANDARD_GR_COMPARATOR_ROUTE",
                "meaning": (
                    "supply standard linearized Einstein gravity explicitly and perform "
                    "only a comparator calculation with no ToE derivation claim"
                ),
                "authorized_now": False,
            },
        ],
        "scope": {
            "independent_packet_review_executed": True,
            "seven_stage_derivation_executed": False,
            "g_0i_calculated": False,
            "nodal_precession_calculated": False,
            "oracle_comparison_executed": False,
            "controls_executed": False,
            "simulation_executed": False,
            "empirical_analysis_executed": False,
            "coefficient_fitting_executed": False,
            "authoritative_physics_equations_modified": False,
            "new_action_or_tensor_bridge_created": False,
            "new_symbolic_tool_created": False,
            "R13_reopened": False,
            "SR_tooling_reopened": False,
            "external_comparator_activated": False,
            "GR_pillar_completed": False,
            "seam_closed": False,
            "master_action_promoted": False,
            "automation_created": False,
        },
        "claim_ceiling": (
            "Independent review establishes only FIELD_EQUATION_SURFACE_FAILURE: "
            "the currently authorized project GR surface does not derive the continuum "
            "tensor equation required to start the rotating-source recovery. No standard-"
            "GR refutation, calculation, recovery, empirical claim, pillar completion, "
            "seam closure, or master-action promotion follows."
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
            raise SystemExit("GR weak rotating-source packet review is stale or missing")
        review = json.loads(raw)
        print(json.dumps({
            "diagnostic": review["primary_diagnostic"],
            "next": review["selected_next_target"],
            "status": "CHECKED",
            "verdict": review["verdict"],
        }, sort_keys=True))
        return 0
    report_path.write_bytes(raw)
    print(report_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

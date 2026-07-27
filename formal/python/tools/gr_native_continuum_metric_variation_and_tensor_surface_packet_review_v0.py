from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "GR_NATIVE_CONTINUUM_METRIC_VARIATION_AND_TENSOR_SURFACE_PACKET_REVIEW_20260717_v0.json"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_gr_native_continuum_metric_variation_and_tensor_surface_packet_review_v0.py"
)
REVIEW_RELATIVE_PATH = (
    "formal/docs/lanes/"
    "GR_NATIVE_CONTINUUM_METRIC_VARIATION_AND_TENSOR_SURFACE_PACKET_REVIEW_20260717_v0.md"
)
TARGET = "review_gr_native_continuum_metric_variation_and_tensor_surface_packet_v0_result"
SELECTED_NEXT_TARGET = (
    "select_response_to_gr_native_continuum_action_contract_block_from_full_toe_priority_map"
)

AUTHORITY_AND_SOURCE_HASHES = {
    "formal/docs/lanes/GR_NATIVE_CONTINUUM_METRIC_VARIATION_AND_TENSOR_SURFACE_PACKET_20260717_v0.md":
        "35b0de6f6f9b41ffdbf9e6544a65392ff2a2964589eb3d4dc3401f4ade7767c2",
    "formal/docs/release/GR_NATIVE_CONTINUUM_METRIC_VARIATION_AND_TENSOR_SURFACE_PACKET_20260717_v0.json":
        "b9c78cb845d88e18cec0537fc1073c4ec181cc02af62609b84d2656eea02b28f",
    "formal/python/tools/gr_native_continuum_metric_variation_and_tensor_surface_packet_v0.py":
        "fba104dbbd18fcbfe17b90f88cb4474435a1dd4578a62702e201d98943253a52",
    "formal/python/tests/test_gr_native_continuum_metric_variation_and_tensor_surface_packet_v0.py":
        "115e84f2438593b7d1c50dc71437c7593a6ed362a88aab87f647667ed074b0ec",
    "formal/toe_formal/ToeFormal/Derivation/GRNativeContinuumMetricVariationAndTensorSurfacePacketV0.lean":
        "4a573bdefe49609a83ac52ca6f09149ad34f3678419268273c8b9be993e37e9f",
    "formal/docs/paper/TOE_CANDIDATE_MASTER_ACTION_v0.md":
        "23aa11c3784da178097eef8ed7c32f9decf4db038a611e4a16364b9bed2db867",
    "formal/docs/release/MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_AFTER_PHI_A_AND_PSI_A_RESULT_REVIEW_20260626_v0.json":
        "3d148464b39d50ae052866516d30bd3f167e1b80d276f56f593fc698f9e6734d",
    REVIEW_RELATIVE_PATH:
        "70b33f70e3389d68b0feea9a8d0f41c9f833b58db6f0a86e8ff81384a74dad92",
}

GATE_RESULTS = [
    {
        "order": 1,
        "gate": "candidate authority",
        "failure_diagnostic": "ACTION_SOURCE_IDENTITY_FAILURE",
        "status": "PASS",
        "finding": "The byte-exact sole source is TOE_CANDIDATE_MASTER_ACTION_v0.",
    },
    {
        "order": 2,
        "gate": "source blending firewall",
        "failure_diagnostic": "ACTION_SOURCE_BLENDING_FAILURE",
        "status": "PASS",
        "finding": (
            "Rep32, DocumentMasterActionMapping, the provisional Einstein-scalar "
            "sandbox, standard Einstein-Hilbert gravity, and stress policies remain excluded."
        ),
    },
    {
        "order": 3,
        "gate": "C_k authority consistency",
        "failure_diagnostic": "CK_FIREWALL_ACTION_SOURCE_CONFLICT",
        "status": "FAIL",
        "finding": (
            "The selected source displays sum_k lambda_k C_k while later accepted "
            "authority makes all C_k families admissibility-only and forbids action "
            "embedding and variation."
        ),
    },
    {
        "order": 4,
        "gate": "action dimensions and constant closure",
        "failure_diagnostic": "ACTION_DIMENSION_AND_CONSTANT_CLOSURE_FAILURE",
        "status": "NOT_EVALUATED",
    },
    {
        "order": 5,
        "gate": "continuum domain and field bundles",
        "failure_diagnostic": "CONTINUUM_DOMAIN_AND_FIELD_BUNDLE_FAILURE",
        "status": "NOT_EVALUATED",
    },
    {
        "order": 6,
        "gate": "tetrad-spinor completeness",
        "failure_diagnostic": "BLOCKED_SPINOR_METRIC_VARIATION_SURFACE",
        "status": "NOT_EVALUATED",
    },
    {
        "order": 7,
        "gate": "hidden metric dependence",
        "failure_diagnostic": "HIDDEN_METRIC_DEPENDENCE_FAILURE",
        "status": "NOT_EVALUATED",
    },
    {
        "order": 8,
        "gate": "boundary variation contract",
        "failure_diagnostic": "BOUNDARY_VARIATION_CONTRACT_FAILURE",
        "status": "NOT_EVALUATED",
    },
    {
        "order": 9,
        "gate": "stress-energy variational definition",
        "failure_diagnostic": "STRESS_ENERGY_VARIATIONAL_DEFINITION_FAILURE",
        "status": "NOT_EVALUATED",
    },
    {
        "order": 10,
        "gate": "Rep32 continuum relationship",
        "failure_diagnostic": "REP32_CONTINUUM_RELATIONSHIP_FAILURE",
        "status": "NOT_EVALUATED",
    },
    {
        "order": 11,
        "gate": "Einstein-equation import or oracle leakage",
        "failure_diagnostic": "EINSTEIN_EQUATION_IMPORT_OR_ORACLE_LEAKAGE",
        "status": "NOT_EVALUATED",
    },
]


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _validate_authority_and_sources() -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for relative_path, expected_hash in AUTHORITY_AND_SOURCE_HASHES.items():
        observed = _sha256((REPO_ROOT / relative_path).read_bytes())
        if observed != expected_hash:
            raise ValueError(f"native GR review authority hash mismatch: {relative_path}")
        rows.append({"relative_path": relative_path, "sha256": observed})

    packet = json.loads(
        (REPO_ROOT / "formal/docs/release/GR_NATIVE_CONTINUUM_METRIC_VARIATION_AND_TENSOR_SURFACE_PACKET_20260717_v0.json").read_text(encoding="utf-8")
    )
    if packet.get("selected_next_target") != TARGET:
        raise ValueError("native GR review did not consume the prepared packet target")
    if packet.get("verdict") != "PREPARED_PENDING_INDEPENDENT_REVIEW":
        raise ValueError("native GR packet preparation verdict mismatch")
    if packet["sole_action_candidate"].get("source_id") != (
        "TOE_CANDIDATE_MASTER_ACTION_v0"
    ):
        raise ValueError("sole action candidate mismatch")
    if packet["sole_action_candidate"].get("source_blending_allowed") is not False:
        raise ValueError("packet unexpectedly allows source blending")
    if packet["C_k_firewall"].get("preparation_finding") != (
        "REGISTERED_SOURCE_POLICY_CONFLICT"
    ):
        raise ValueError("packet did not register C_k source-policy conflict")
    if packet["C_k_firewall"].get("packet_rewrites_action") is not False:
        raise ValueError("packet unexpectedly rewrote the action")

    action = (
        REPO_ROOT / "formal/docs/paper/TOE_CANDIDATE_MASTER_ACTION_v0.md"
    ).read_text(encoding="utf-8")
    if "sum_k lambda_k * C_k(g, psi, A, phi, rho)" not in action:
        raise ValueError("selected action no longer contains the reviewed C_k term")

    ck = json.loads(
        (REPO_ROOT / "formal/docs/release/MASTER_ACTION_CK_FAMILY_STATUS_SYNTHESIS_AFTER_PHI_A_AND_PSI_A_RESULT_REVIEW_20260626_v0.json").read_text(encoding="utf-8")
    )
    required_ck = {
        "all_C_k_families_admissibility_only": True,
        "C_k_action_embedding_selected": False,
        "C_k_action_variation_authorized": False,
    }
    if {key: ck.get(key) for key in required_ck} != required_ck:
        raise ValueError("retained C_k firewall authority mismatch")

    review = (REPO_ROOT / REVIEW_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        "BLOCKED_INCOMPLETE_CONTINUUM_ACTION_CONTRACT",
        "CK_FIREWALL_ACTION_SOURCE_CONFLICT",
        "PROPOSED / COMPLETENESS UNADJUDICATED",
        "No automatic v1 repair is authorized",
    ):
        if token not in review:
            raise ValueError(f"human review token missing: {token}")
    return rows


def build_review() -> dict[str, Any]:
    authority = _validate_authority_and_sources()
    tool_path = Path(__file__).resolve()
    test_path = REPO_ROOT / TEST_RELATIVE_PATH
    if not test_path.exists():
        raise ValueError("native GR review focused test missing")

    failed = [row for row in GATE_RESULTS if row["status"] == "FAIL"]
    passes = [row for row in GATE_RESULTS if row["status"] == "PASS"]
    not_evaluated = [row for row in GATE_RESULTS if row["status"] == "NOT_EVALUATED"]
    if len(failed) != 1 or failed[0]["order"] != 3:
        raise ValueError("unexpected native GR fail-fast gate structure")

    return {
        "schema_id": "GR_NATIVE_CONTINUUM_METRIC_VARIATION_AND_TENSOR_SURFACE_PACKET_REVIEW_20260717_v0",
        "captured_at_utc": "2026-07-17T00:00:00Z",
        "target": TARGET,
        "verdict": "BLOCKED_INCOMPLETE_CONTINUUM_ACTION_CONTRACT",
        "primary_diagnostic": "CK_FIREWALL_ACTION_SOURCE_CONFLICT",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": "FRESH_FULL_PRIORITY_RESPONSE_SELECTION_ONLY",
        "authority": {
            "reviewed_packet_id": (
                "GR_NATIVE_CONTINUUM_METRIC_VARIATION_AND_TENSOR_SURFACE_PACKET_20260717_v0"
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
            "Does the sole selected candidate define one coherent, policy-consistent, "
            "spinor-complete continuum action functional whose full tetrad variation "
            "can be attempted without importing the Einstein equation?"
        ),
        "answer": "NO_REVIEW_STOPS_AT_FIRST_UNRESOLVED_AUTHORITY_CONFLICT",
        "fail_fast_review": {
            "gate_count": len(GATE_RESULTS),
            "pass_count": len(passes),
            "failure_count": len(failed),
            "not_evaluated_count": len(not_evaluated),
            "first_failed_gate_order": 3,
            "first_failed_gate": "C_k authority consistency",
            "rows": GATE_RESULTS,
            "later_gate_may_override_first_failure": False,
        },
        "candidate_authority_review": {
            "status": "PASS",
            "sole_source_id": "TOE_CANDIDATE_MASTER_ACTION_v0",
            "classification": "TOE_NATIVE_CANDIDATE_WORKING_FORM_NONCANONICAL_UNPROMOTED",
            "canonical_authority_inferred": False,
            "empirical_authority_inferred": False,
        },
        "source_blending_review": {
            "status": "PASS",
            "Rep32_imported": False,
            "DocumentMasterActionMapping_imported": False,
            "provisional_Einstein_scalar_sandbox_imported": False,
            "standalone_Einstein_Hilbert_action_imported": False,
            "retained_stress_policy_imported_as_derived_source": False,
        },
        "C_k_conflict_review": {
            "status": "FAIL",
            "source_contains_C_k_multiplier_term": True,
            "retained_policy": "ALL_C_K_FAMILIES_ADMISSIBILITY_ONLY",
            "action_embedding_selected": False,
            "action_variation_authorized": False,
            "multiplier_or_penalty_route_authorized": False,
            "action_term_deleted_or_declared_inactive": False,
            "projected_or_superseding_action_created": False,
            "readiness_possible_while_conflict_unresolved": False,
        },
        "terminal_outcome_reasoning": {
            "selected": "BLOCKED_INCOMPLETE_CONTINUUM_ACTION_CONTRACT",
            "why_incomplete_not_no_surface": (
                "The exact document is presented as a candidate continuum working form; "
                "the review establishes a current contract conflict, not impossibility of "
                "every future native continuum action."
            ),
            "why_not_spinor_primary": (
                "Tetrad-spinor completeness is gate 6 and remains unevaluated because the "
                "C_k conflict fails first at gate 3."
            ),
            "why_not_comparator": (
                "The supplied standard-GR comparator was neither selected nor evaluated."
            ),
        },
        "downstream_gate_posture": {
            "action_dimensions_and_constants": "NOT_EVALUATED",
            "continuum_domain_and_field_bundles": "NOT_EVALUATED",
            "tetrad_spinor_completeness": "NOT_EVALUATED",
            "hidden_metric_dependence": "NOT_EVALUATED",
            "boundary_sufficiency": "NOT_EVALUATED",
            "stress_energy_variational_definition": "NOT_EVALUATED",
            "Rep32_continuum_relationship": "NOT_EVALUATED",
            "Einstein_equation_import_or_oracle_leakage": "NOT_EVALUATED",
            "tetrad_route": "PROPOSED_COMPLETENESS_UNADJUDICATED",
        },
        "retained_scientific_posture": {
            "bounded_discrete_Newton_Poisson_GR": "RETAINED",
            "gravitomagnetic_route": "BLOCKED_FIELD_EQUATION_SURFACE_FAILURE",
            "candidate_master_action": "WORKING_FORM_ORGANIZING_HYPOTHESIS",
            "Rep32": "SEPARATE_STRUCTURAL_MODEL",
            "stress_tensors": "COMPARISON_POLICIES_ONLY",
            "C_k": "ADMISSIBILITY_AUDIT_ONLY",
            "continuum_tensor_field_equation_created": False,
        },
        "fresh_priority_options": [
            {
                "route_id": "AUTHORITATIVE_ACTION_SOURCE_RECONCILIATION_OR_SUPERSESSION",
                "authorized_now": False,
            },
            {
                "route_id": "NO_NATIVE_SURFACE_SECTOR_INVENTORY_CLASSIFICATION",
                "authorized_now": False,
            },
            {
                "route_id": "SUPPLIED_STANDARD_GR_VARIATIONAL_COMPARATOR",
                "authorized_now": False,
            },
            {
                "route_id": "PIVOT_TO_OTHER_HIGH_LEVERAGE_PHYSICS_OBLIGATION",
                "authorized_now": False,
            },
        ],
        "scope": {
            "independent_review_executed": True,
            "automatic_v1_authorized": False,
            "action_rewritten_or_projected": False,
            "metric_variation_executed": False,
            "tetrad_variation_executed": False,
            "spin_connection_variation_executed": False,
            "stress_energy_calculated": False,
            "Einstein_equation_imported": False,
            "Einstein_equation_derived": False,
            "standard_GR_comparator_activated": False,
            "weak_field_calculation_executed": False,
            "gravitomagnetic_calculation_executed": False,
            "C_k_action_embedding_executed": False,
            "C_k_variation_executed": False,
            "master_action_promoted": False,
            "GR_pillar_completed": False,
            "seam_closed": False,
            "simulation_executed": False,
            "empirical_analysis_executed": False,
            "repository_migration_executed": False,
            "automation_created": False,
        },
        "claim_ceiling": (
            "Independent packet review only. It reproduces the sole candidate and "
            "source-blending firewall, then blocks the native continuum action contract "
            "at CK_FIREWALL_ACTION_SOURCE_CONFLICT. All later variational gates remain "
            "unevaluated. No action rewrite, tensor field equation, GR recovery, "
            "comparator result, seam closure, master-action promotion, empirical result, "
            "or automation is created."
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
            raise SystemExit("native continuum variation packet review is stale or missing")
        review = json.loads(raw)
        print(json.dumps({
            "first_failed_gate": review["fail_fast_review"]["first_failed_gate_order"],
            "not_evaluated": review["fail_fast_review"]["not_evaluated_count"],
            "status": "CHECKED",
            "verdict": review["verdict"],
        }, sort_keys=True))
        return 0
    report_path.write_bytes(raw)
    print(report_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_matter_field_content_and_lagrangian_candidate_packet_report import (
    DEFAULT_OUT as FIELD_LAGRANGIAN_PACKET_PATH,
    FIELD_LAGRANGIAN_RESULT as PRIOR_FIELD_LAGRANGIAN_RESULT,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as EXPECTED_FIELD_LAGRANGIAN_OUTCOME,
    REAL_SCALAR_ACTION_FORM,
    SCHEMA_ID as EXPECTED_FIELD_LAGRANGIAN_SCHEMA_ID,
    SELECTED_FUNCTIONAL_CONTRACT,
    SELECTED_REPLACEMENT_CANDIDATE_ID,
    TEST_SPACE,
    WEAK_VARIATIONAL_OBLIGATION,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-16T00:00:00Z"
SCHEMA_ID = "QFT_GR_TOE_MATTER_SECTOR_CANDIDATE_SELECTION_PACKET_20260616_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "QFT_GR_TOE_MATTER_SECTOR_CANDIDATE_SELECTION_PACKET_v0"
MATTER_SECTOR_SELECTION_RESULT = (
    "KNOWN_MATTER_MODEL_IMPORTED_AS_PROVISIONAL_TEST_SECTOR_NO_TOE_DERIVATION_CLAIM"
)
OUTCOME_ID = (
    "QFT_GR_TOE_MATTER_SECTOR_CANDIDATE_SELECTION_PACKET_PREPARED_WITH_KNOWN_"
    "MATTER_MODEL_IMPORTED_AS_PROVISIONAL_TEST_SECTOR_NO_TOE_DERIVATION_CLAIM_"
    "AND_TOE_NATIVE_MATTER_SECTOR_NOT_DEFINED"
)
PACKET_CLASSIFICATION = (
    "qft_gr_toe_matter_sector_candidate_selection_packet_selects_provisional_"
    "real_scalar_test_sector_while_preserving_missing_toe_native_matter_sector"
)
SELECTED_PROVISIONAL_MATTER_SECTOR_ID = "provisional_real_scalar_field_test_sector_v0"
SELECTED_KNOWN_MATTER_MODEL = "real_scalar_field_klein_gordon_type"
SELECTED_ACTION_GENERATED_SOURCE_SUBCLASS_ID = (
    "stress_energy_candidate_generated_by_provisional_real_scalar_lagrangian_v0"
)
SELECTED_FIELD_CONTENT = "real scalar field phi"
SELECTED_FIELD_DOMAIN = "phi in Gamma(M x R) with regularity deferred to action retry"
SELECTED_LAGRANGIAN_DENSITY = (
    "L_m(g, phi, nabla phi) = -1/2 g^{mu nu} nabla_mu phi nabla_nu phi - V(phi)"
)
SELECTED_VARIATIONAL_TARGET = "delta S_m[g, phi](h) = -1/2 <T_phi, h>"
TOE_NATIVE_MATTER_SECTOR_RESULT = "TOE_NATIVE_MATTER_SECTOR_NOT_YET_DEFINED"
EFFECTIVE_QFT_ACTION_ROUTE_RESULT = "EFFECTIVE_QFT_ACTION_ROUTE_RECORDED_NOT_LICENSED"
NEXT_TARGET = "prepare_qft_gr_action_derivability_retry_with_provisional_matter_sector"
NEXT_TARGET_KIND = (
    "qft_gr_action_derivability_retry_with_provisional_matter_sector_preparation"
)
AUTHORIZED_BY_FIELD_LAGRANGIAN_COMMIT = "7e4b54f2"
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_TOE_MATTER_SECTOR_CANDIDATE_SELECTION_PACKET_20260616_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRToeMatterSectorCandidateSelectionPacket.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _route_assessments() -> list[dict[str, Any]]:
    return [
        {
            "route_id": "known_real_scalar_provisional_test_sector",
            "route_kind": "known_matter_model_imported_as_calculation_sandbox",
            "candidate_form": REAL_SCALAR_ACTION_FORM,
            "selection_status": "selected_provisionally",
            "selection_licensed": True,
            "selected_matter_sector_id": SELECTED_PROVISIONAL_MATTER_SECTOR_ID,
            "selected_field_content": SELECTED_FIELD_CONTENT,
            "selected_lagrangian_density": SELECTED_LAGRANGIAN_DENSITY,
            "selected_variational_target": SELECTED_VARIATIONAL_TARGET,
            "toe_derivation_claimed": False,
            "standard_model_derivation_claimed": False,
            "action_derivability_claimed": False,
            "source_admissibility_claimed": False,
            "reason": (
                "A real scalar field is selected only as a known-physics "
                "calculation sandbox for testing action-derivability mechanics. "
                "It does not derive matter from the ToE and does not prove the "
                "arbitrary distributional source candidate is action-derived."
            ),
        },
        {
            "route_id": "abstract_field_bundle_matter_sector",
            "route_kind": "abstract_matter_sector",
            "candidate_form": "psi in Gamma(E), S_m[g, psi] = integral_M L(g, psi, nabla psi, ...) dVol_g",
            "selection_status": "recorded_not_selected",
            "selection_licensed": False,
            "toe_derivation_claimed": False,
            "blocked_by": [
                "field_bundle_E_not_defined",
                "lagrangian_class_not_constrained",
                "specific_calculation_target_not_fixed",
            ],
            "reason": (
                "The abstract field-bundle route is mathematically flexible but "
                "too underdetermined to drive the next concrete calculation."
            ),
        },
        {
            "route_id": "effective_qft_action_route",
            "route_kind": "effective_action_or_generating_functional",
            "candidate_form": "W[g] with <T_{mu nu}> = -2 / sqrt(-g) * delta W / delta g^{mu nu}",
            "selection_status": "recorded_not_licensed",
            "selection_licensed": False,
            "route_result": EFFECTIVE_QFT_ACTION_ROUTE_RESULT,
            "toe_derivation_claimed": False,
            "blocked_by": [
                "qft_state_not_selected",
                "renormalization_scheme_not_selected",
                "effective_action_domain_not_selected",
                "anomaly_policy_not_selected",
            ],
            "reason": (
                "The effective QFT action route remains relevant but requires "
                "state, renormalization, domain, and anomaly control."
            ),
        },
        {
            "route_id": "toe_native_matter_sector",
            "route_kind": "toe_native_matter_sector",
            "candidate_form": "matter sector generated from candidate unifying family equations",
            "selection_status": "not_yet_defined",
            "selection_licensed": False,
            "route_result": TOE_NATIVE_MATTER_SECTOR_RESULT,
            "toe_derivation_claimed": False,
            "blocked_by": [
                "no_preserved_toe_native_matter_sector_artifact",
                "candidate_family_to_matter_degrees_of_freedom_map_missing",
                "native_lagrangian_generation_rule_missing",
            ],
            "reason": (
                "No preserved artifact currently defines a ToE-native matter "
                "sector or derives field content from the candidate family."
            ),
        },
        {
            "route_id": "no_matter_sector_selected",
            "route_kind": "strict_no_selection_route",
            "candidate_form": "no matter sector selected",
            "selection_status": "not_selected_because_provisional_test_sector_selected",
            "selection_licensed": False,
            "toe_derivation_claimed": False,
            "reason": (
                "The packet does not leave QFT-GR without a calculation path; "
                "it selects a provisional scalar sandbox while preserving the "
                "ToE-native blocker."
            ),
        },
    ]


def _selected_sector_contract() -> dict[str, Any]:
    return {
        "matter_sector_id": SELECTED_PROVISIONAL_MATTER_SECTOR_ID,
        "selection_scope": "provisional_calculation_sandbox_only",
        "known_model_imported": True,
        "known_model": SELECTED_KNOWN_MATTER_MODEL,
        "field_content": SELECTED_FIELD_CONTENT,
        "field_domain": SELECTED_FIELD_DOMAIN,
        "matter_action_form": REAL_SCALAR_ACTION_FORM,
        "lagrangian_density": SELECTED_LAGRANGIAN_DENSITY,
        "variational_target": SELECTED_VARIATIONAL_TARGET,
        "source_subclass_id": SELECTED_ACTION_GENERATED_SOURCE_SUBCLASS_ID,
        "source_subclass_scope": (
            "action-generated scalar stress-energy candidate only; not the "
            "original arbitrary distributional source"
        ),
        "toe_derivation_claimed": False,
        "standard_model_derivation_claimed": False,
        "arbitrary_distributional_source_action_derived_claimed": False,
    }


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": "qft_gr_toe_matter_sector_candidate_selection_packet",
        "bounded_focused_validation_only": True,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_aggregate_lean_required": False,
        "full_ci_parity_required": False,
        "full_security_scan_required": False,
        "aggregate_lean_not_run": True,
        "aggregate_lean_health_claimed": False,
        "release_index_path_not_freshly_lean_validated": True,
    }


def build_qft_gr_toe_matter_sector_candidate_selection_packet(
    *,
    field_lagrangian_packet_path: Path = FIELD_LAGRANGIAN_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    field_packet = _read_json(field_lagrangian_packet_path)
    routes = _route_assessments()
    selected_contract = _selected_sector_contract()
    selected_route = routes[0]
    toe_native_route = routes[3]
    effective_route = routes[2]
    acceptance_criteria = {
        "consumes_expected_field_lagrangian_packet": (
            field_packet.get("schema_id") == EXPECTED_FIELD_LAGRANGIAN_SCHEMA_ID
            and field_packet.get("outcome_id") == EXPECTED_FIELD_LAGRANGIAN_OUTCOME
            and field_packet.get("selected_next_target") == CONSUMED_TARGET
        ),
        "prior_packet_blocked_by_missing_toe_matter_model": (
            field_packet.get("field_content_lagrangian_result")
            == PRIOR_FIELD_LAGRANGIAN_RESULT
            and field_packet.get("toe_matter_sector_selection_required") is True
        ),
        "provisional_known_scalar_selected": (
            selected_route["selection_status"] == "selected_provisionally"
            and selected_route["selection_licensed"] is True
            and selected_route["selected_matter_sector_id"]
            == SELECTED_PROVISIONAL_MATTER_SECTOR_ID
        ),
        "toe_native_matter_sector_not_defined": (
            toe_native_route["route_result"] == TOE_NATIVE_MATTER_SECTOR_RESULT
            and toe_native_route["selection_licensed"] is False
        ),
        "effective_qft_route_not_licensed": (
            effective_route["route_result"] == EFFECTIVE_QFT_ACTION_ROUTE_RESULT
            and effective_route["selection_licensed"] is False
        ),
        "no_toe_or_standard_model_derivation_claim": (
            selected_contract["toe_derivation_claimed"] is False
            and selected_contract["standard_model_derivation_claimed"] is False
        ),
        "arbitrary_distributional_source_not_action_derived": (
            selected_contract[
                "arbitrary_distributional_source_action_derived_claimed"
            ]
            is False
        ),
        "next_target_is_action_derivability_retry": NEXT_TARGET
        == "prepare_qft_gr_action_derivability_retry_with_provisional_matter_sector",
        "non_promotion_boundary_preserved": True,
    }
    prepared = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if prepared
        else "REMEDIATE_QFT_GR_TOE_MATTER_SECTOR_CANDIDATE_SELECTION_PACKET"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "accepted": prepared,
        "outcome_id": OUTCOME_ID
        if prepared
        else "QFT_GR_TOE_MATTER_SECTOR_CANDIDATE_SELECTION_PACKET_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "authorized_by_field_lagrangian_artifact_id": field_packet.get("schema_id"),
        "authorized_by_field_lagrangian_commit": AUTHORIZED_BY_FIELD_LAGRANGIAN_COMMIT,
        "candidate_id": SELECTED_REPLACEMENT_CANDIDATE_ID,
        "functional_contract": SELECTED_FUNCTIONAL_CONTRACT,
        "test_space": TEST_SPACE,
        "weak_variational_obligation": WEAK_VARIATIONAL_OBLIGATION,
        "prior_field_lagrangian_result": PRIOR_FIELD_LAGRANGIAN_RESULT,
        "matter_sector_selection_result": MATTER_SECTOR_SELECTION_RESULT,
        "toe_native_matter_sector_result": TOE_NATIVE_MATTER_SECTOR_RESULT,
        "effective_qft_action_route_result": EFFECTIVE_QFT_ACTION_ROUTE_RESULT,
        "known_matter_model_imported_as_provisional_test_sector": True,
        "selected_known_matter_model": SELECTED_KNOWN_MATTER_MODEL,
        "selected_provisional_matter_sector_id": SELECTED_PROVISIONAL_MATTER_SECTOR_ID,
        "selected_action_generated_source_subclass_id": (
            SELECTED_ACTION_GENERATED_SOURCE_SUBCLASS_ID
        ),
        "selected_field_content": SELECTED_FIELD_CONTENT,
        "selected_field_domain": SELECTED_FIELD_DOMAIN,
        "selected_lagrangian_density": SELECTED_LAGRANGIAN_DENSITY,
        "selected_matter_action_form": REAL_SCALAR_ACTION_FORM,
        "selected_variational_target": SELECTED_VARIATIONAL_TARGET,
        "selected_sector_contract": selected_contract,
        "route_assessments": routes,
        "matter_model_selected": True,
        "matter_field_content_selected": True,
        "lagrangian_density_selected": True,
        "action_generated_source_subclass_selected": True,
        "action_derivability_retry_authorized": True,
        "toe_native_matter_sector_defined": False,
        "toe_matter_model_derived": False,
        "toe_matter_sector_selected": False,
        "standard_model_derivation_claimed": False,
        "arbitrary_distributional_source_action_derived_claimed": False,
        "arbitrary_distributional_source_replaced_for_retry": True,
        "mathematical_statement": (
            "The packet selects a known real scalar field action only as a "
            "provisional calculation sandbox: S_m[g, phi] with L_m(g, phi, "
            "nabla phi) = -1/2 g^{mu nu} nabla_mu phi nabla_nu phi - V(phi). "
            "This licenses a retry of action-derivability mechanics for the "
            "action-generated scalar stress-energy subclass T_phi. It does not "
            "derive matter from the ToE, does not derive the Standard Model, "
            "and does not prove the original arbitrary distributional source "
            "candidate is action-derived."
        ),
        "downstream_progression": [
            {
                "stage": "toe_matter_sector_candidate_selection",
                "status": "PROVISIONAL_TEST_SECTOR_SELECTED",
                "decision": MATTER_SECTOR_SELECTION_RESULT,
                "reason": "A known scalar field is selected only for calculation-sandbox use.",
            },
            {
                "stage": "toe_native_matter_sector",
                "status": "NOT_DEFINED",
                "decision": TOE_NATIVE_MATTER_SECTOR_RESULT,
                "reason": "No preserved artifact derives ToE-native matter degrees of freedom.",
            },
            {
                "stage": "effective_qft_action_route",
                "status": "NOT_LICENSED",
                "decision": EFFECTIVE_QFT_ACTION_ROUTE_RESULT,
                "reason": "State, renormalization, domain, and anomaly controls are not supplied.",
            },
            {
                "stage": "action_derivability_retry",
                "status": "NEXT_TARGET_AUTHORIZED",
                "decision": selected_next_target,
                "reason": "The provisional scalar matter action can now be used to test action-derivability mechanics nonpromotionally.",
            },
            {
                "stage": "weak_conservation",
                "status": "NOT_REACHED",
                "decision": "not_reached",
                "reason": "Weak conservation remains downstream of action variation and diffeomorphism structure checks.",
            },
            {
                "stage": "bianchi_compatibility",
                "status": "NOT_REACHED",
                "decision": "not_reached",
                "reason": "Bianchi compatibility is downstream of conservation.",
            },
            {
                "stage": "semiclassical_source_admissibility",
                "status": "NOT_REACHED",
                "decision": "not_reached",
                "reason": "Semiclassical coupling is downstream of source admissibility checks.",
            },
        ],
        "source_admissibility_claimed": False,
        "action_derivability_claimed": False,
        "matter_action_derivation_claimed": False,
        "weak_conservation_claimed": False,
        "conservation_claimed": False,
        "Bianchi_compatibility_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "qft_gr_closure_claimed": False,
        "qft_gr_seam_closed": False,
        "empirical_validation_claimed": False,
        "public_submission_authorized": False,
        "master_action_promoted": False,
        "acceptable_result_outcomes": [
            "ABSTRACT_FIELD_BUNDLE_MATTER_SECTOR_SELECTED_ACTION_RETRY_AUTHORIZED_NONPROMOTIONALLY",
            MATTER_SECTOR_SELECTION_RESULT,
            TOE_NATIVE_MATTER_SECTOR_RESULT,
            EFFECTIVE_QFT_ACTION_ROUTE_RESULT,
            "NO_TOE_MATTER_SECTOR_SELECTED_QFT_GR_ACTION_ROUTE_BLOCKED",
        ],
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "validation_policy": _validation_policy(),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet selects a known real scalar field only as a provisional "
            "calculation sandbox. It preserves that the ToE-native matter sector "
            "is not defined, does not claim Standard Model derivation, does not "
            "claim action derivability, source admissibility, conservation, "
            "Bianchi compatibility, semiclassical coupling, QFT-GR closure, "
            "empirical validation, public submission, or master-action promotion."
        ),
    }


def write_qft_gr_toe_matter_sector_candidate_selection_packet(
    *,
    field_lagrangian_packet_path: Path = FIELD_LAGRANGIAN_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_toe_matter_sector_candidate_selection_packet(
        field_lagrangian_packet_path=field_lagrangian_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QFT-GR ToE matter-sector candidate selection packet JSON."
    )
    parser.add_argument(
        "--field-lagrangian-packet",
        type=Path,
        default=FIELD_LAGRANGIAN_PACKET_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    field_lagrangian_packet_path = (
        ns.field_lagrangian_packet
        if ns.field_lagrangian_packet.is_absolute()
        else (REPO_ROOT / ns.field_lagrangian_packet)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_toe_matter_sector_candidate_selection_packet(
        field_lagrangian_packet_path=field_lagrangian_packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        json.dumps(
            {
                "out": _ptr(out),
                "packet_id": payload["packet_id"],
                "outcome_id": payload["outcome_id"],
                "prepared": payload["prepared"],
                "matter_sector_selection_result": payload[
                    "matter_sector_selection_result"
                ],
                "selected_next_target": payload["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

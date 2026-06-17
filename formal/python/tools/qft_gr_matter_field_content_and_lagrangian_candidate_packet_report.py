from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_matter_action_functional_candidate_packet_report import (
    DEFAULT_OUT as MATTER_ACTION_PACKET_PATH,
    MATTER_ACTION_RESULT as PRIOR_MATTER_ACTION_RESULT,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as EXPECTED_MATTER_ACTION_OUTCOME,
    SCHEMA_ID as EXPECTED_MATTER_ACTION_SCHEMA_ID,
    SELECTED_FUNCTIONAL_CONTRACT,
    SELECTED_REPLACEMENT_CANDIDATE_ID,
    TEST_SPACE,
    WEAK_VARIATIONAL_OBLIGATION,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-16T00:00:00Z"
SCHEMA_ID = "QFT_GR_MATTER_FIELD_CONTENT_AND_LAGRANGIAN_CANDIDATE_PACKET_20260616_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "QFT_GR_MATTER_FIELD_CONTENT_AND_LAGRANGIAN_CANDIDATE_PACKET_v0"
FIELD_LAGRANGIAN_RESULT = "FIELD_CONTENT_AND_LAGRANGIAN_BLOCKED_BY_MISSING_TOE_MATTER_MODEL"
OUTCOME_ID = (
    "QFT_GR_MATTER_FIELD_CONTENT_AND_LAGRANGIAN_CANDIDATE_PACKET_PREPARED_WITH_"
    "FIELD_CONTENT_AND_LAGRANGIAN_BLOCKED_BY_MISSING_TOE_MATTER_MODEL_AND_NO_"
    "ACTION_DERIVABILITY_OR_SOURCE_ADMISSIBILITY"
)
PACKET_CLASSIFICATION = (
    "qft_gr_matter_field_content_and_lagrangian_candidate_packet_records_missing_"
    "toe_matter_model_for_action_generated_source_subclass"
)
GENERIC_MATTER_ACTION_FORM = (
    "S_m[g, psi] = integral_M L_m(g, psi, nabla psi, ...) dVol_g"
)
REAL_SCALAR_ACTION_FORM = (
    "S_m[g, phi] = integral_M (-1/2 g^{mu nu} nabla_mu phi nabla_nu phi - V(phi)) dVol_g"
)
GAUGE_FIELD_ACTION_FORM = (
    "S_m[g, A] = integral_M (-1/4 F_{mu nu} F^{mu nu} + coupling_terms) dVol_g"
)
DIRAC_SPINOR_ACTION_FORM = (
    "S_m[g, psi] = integral_M psi_bar (i gamma^mu nabla_mu - m) psi dVol_g"
)
EFFECTIVE_QFT_ACTION_FORM = (
    "W[g] with <T_{mu nu}> = -2 / sqrt(-g) * delta W / delta g^{mu nu}"
)
NEXT_TARGET = "prepare_qft_gr_toe_matter_sector_candidate_selection_packet"
NEXT_TARGET_KIND = "qft_gr_toe_matter_sector_candidate_selection_packet_preparation"
AUTHORIZED_BY_MATTER_ACTION_COMMIT = "26140cec965d1edf619ddb36a3cd39a7a0648b4b"
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_MATTER_FIELD_CONTENT_AND_LAGRANGIAN_CANDIDATE_PACKET_20260616_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRMatterFieldContentAndLagrangianCandidatePacket.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _matter_model_options() -> list[dict[str, Any]]:
    return [
        {
            "option_id": "generic_matter_field_bundle_and_local_lagrangian_density",
            "candidate_form": GENERIC_MATTER_ACTION_FORM,
            "selection_status": "recorded_not_licensed",
            "selection_licensed": False,
            "would_define_action_generated_source_subclass": True,
            "would_prove_arbitrary_distributional_T_action_derived": False,
            "blocked_by": [
                "toe_matter_field_bundle_not_selected",
                "lagrangian_density_not_supplied",
                "field_variation_policy_not_supplied",
                "metric_variation_rule_not_instantiated",
            ],
            "reason": (
                "A generic matter action would require a selected field bundle, "
                "local Lagrangian density, and field/metric variation policy. "
                "Those data are not licensed by the current QFT-GR chain."
            ),
        },
        {
            "option_id": "real_scalar_klein_gordon_type_route",
            "candidate_form": REAL_SCALAR_ACTION_FORM,
            "selection_status": "candidate_option_recorded_not_selected",
            "selection_licensed": False,
            "would_define_action_generated_source_subclass": True,
            "would_prove_arbitrary_distributional_T_action_derived": False,
            "blocked_by": [
                "scalar_field_not_selected_by_toe_matter_sector",
                "potential_or_mass_term_not_selected",
                "regularity_and_solution_class_not_selected",
                "stress_energy_matching_to_distributional_T_not_supplied",
            ],
            "reason": (
                "The scalar route is the simplest concrete option, but choosing "
                "it would replace the arbitrary pairable distributional source "
                "with a narrower action-generated subclass. No ToE matter-sector "
                "artifact currently licenses that selection."
            ),
        },
        {
            "option_id": "gauge_field_maxwell_type_route",
            "candidate_form": GAUGE_FIELD_ACTION_FORM,
            "selection_status": "candidate_option_recorded_not_selected",
            "selection_licensed": False,
            "would_define_action_generated_source_subclass": True,
            "would_prove_arbitrary_distributional_T_action_derived": False,
            "blocked_by": [
                "gauge_bundle_not_selected",
                "field_strength_domain_not_selected",
                "coupling_current_or_charge_sector_not_selected",
                "stress_energy_matching_to_distributional_T_not_supplied",
            ],
            "reason": (
                "Existing EM/QFT surfaces do not by themselves select a QFT-GR "
                "matter sector or prove the current arbitrary distributional "
                "candidate is generated by a Maxwell-type action."
            ),
        },
        {
            "option_id": "dirac_spinor_field_route",
            "candidate_form": DIRAC_SPINOR_ACTION_FORM,
            "selection_status": "candidate_option_recorded_not_selected",
            "selection_licensed": False,
            "would_define_action_generated_source_subclass": True,
            "would_prove_arbitrary_distributional_T_action_derived": False,
            "blocked_by": [
                "spin_structure_not_selected",
                "spinor_bundle_not_selected",
                "gamma_matrix_convention_not_selected",
                "spin_connection_and_domain_not_selected",
            ],
            "reason": (
                "The spinor route requires additional geometric and field-domain "
                "data before it can serve as a QFT-GR matter action candidate."
            ),
        },
        {
            "option_id": "effective_qft_action_route",
            "candidate_form": EFFECTIVE_QFT_ACTION_FORM,
            "selection_status": "recorded_not_licensed",
            "selection_licensed": False,
            "would_define_action_generated_source_subclass": True,
            "would_prove_arbitrary_distributional_T_action_derived": False,
            "blocked_by": [
                "qft_state_or_state_family_not_selected",
                "renormalization_scheme_not_selected",
                "effective_action_domain_not_selected",
                "anomaly_and_conservation_policy_not_selected",
            ],
            "reason": (
                "An effective/QFT action route would require state, "
                "renormalization, domain, and anomaly data that remain "
                "outside the licensed packet scope."
            ),
        },
        {
            "option_id": "no_field_content_selected",
            "candidate_form": "no ToE matter model selected",
            "selection_status": "blocked_outcome_recorded",
            "selection_licensed": False,
            "would_define_action_generated_source_subclass": False,
            "would_prove_arbitrary_distributional_T_action_derived": False,
            "blocked_by": ["toe_matter_model_missing"],
            "reason": (
                "No field content and Lagrangian can be selected without a "
                "ToE matter-sector candidate or an explicit authorization to "
                "narrow to an action-generated source subclass."
            ),
        },
    ]


def _required_matter_model_data() -> list[dict[str, Any]]:
    return [
        {
            "field_id": "toe_matter_sector_candidate",
            "required": "selected matter sector or explicit action-generated subclass route",
            "status": "missing",
        },
        {
            "field_id": "matter_degrees_of_freedom",
            "required": "fields psi, phi, A, spinor, or effective QFT state family",
            "status": "missing",
        },
        {
            "field_id": "lagrangian_density",
            "required": "L_m(g, psi, nabla psi, ...) or effective action W[g]",
            "status": "missing",
        },
        {
            "field_id": "variational_rule",
            "required": WEAK_VARIATIONAL_OBLIGATION,
            "status": "missing",
        },
        {
            "field_id": "action_generated_source_subclass_contract",
            "required": "stress_energy_candidate_generated_by_selected_matter_lagrangian_v0",
            "status": "not_selected",
        },
        {
            "field_id": "stress_energy_matching_obligation",
            "required": "show selected action variation yields the source tested in weak pairing",
            "status": "not_reached",
        },
        {
            "field_id": "diffeomorphism_or_covariance_structure",
            "required": "needed before downstream conservation/Bianchi checks",
            "status": "not_reached",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": "qft_gr_matter_field_content_and_lagrangian_candidate_packet",
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


def build_qft_gr_matter_field_content_and_lagrangian_candidate_packet(
    *,
    matter_action_packet_path: Path = MATTER_ACTION_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    matter_action_packet = _read_json(matter_action_packet_path)
    options = _matter_model_options()
    required_data = _required_matter_model_data()
    acceptance_criteria = {
        "consumes_expected_matter_action_packet": (
            matter_action_packet.get("schema_id") == EXPECTED_MATTER_ACTION_SCHEMA_ID
            and matter_action_packet.get("outcome_id") == EXPECTED_MATTER_ACTION_OUTCOME
            and matter_action_packet.get("selected_next_target") == CONSUMED_TARGET
        ),
        "prior_matter_action_blocked_by_field_content_and_lagrangian": (
            matter_action_packet.get("matter_action_result")
            == PRIOR_MATTER_ACTION_RESULT
            and matter_action_packet.get("matter_action_functional_candidate_selected")
            is False
        ),
        "required_options_enumerated": [
            row["option_id"] for row in options
        ]
        == [
            "generic_matter_field_bundle_and_local_lagrangian_density",
            "real_scalar_klein_gordon_type_route",
            "gauge_field_maxwell_type_route",
            "dirac_spinor_field_route",
            "effective_qft_action_route",
            "no_field_content_selected",
        ],
        "no_option_selected_without_toe_matter_model": all(
            row["selection_licensed"] is False for row in options
        ),
        "arbitrary_distributional_T_not_promoted_to_action_derived": all(
            row["would_prove_arbitrary_distributional_T_action_derived"] is False
            for row in options
        ),
        "scalar_route_not_selected_as_shortcut": (
            next(
                row
                for row in options
                if row["option_id"] == "real_scalar_klein_gordon_type_route"
            )["selection_status"]
            == "candidate_option_recorded_not_selected"
        ),
        "toe_matter_model_required": {
            row["field_id"]: row["status"] for row in required_data
        }.get("toe_matter_sector_candidate")
        == "missing",
        "next_target_is_matter_sector_candidate_selection": NEXT_TARGET
        == "prepare_qft_gr_toe_matter_sector_candidate_selection_packet",
        "non_promotion_boundary_preserved": True,
    }
    prepared = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if prepared
        else "REMEDIATE_QFT_GR_MATTER_FIELD_CONTENT_AND_LAGRANGIAN_CANDIDATE_PACKET"
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
        else "QFT_GR_MATTER_FIELD_CONTENT_AND_LAGRANGIAN_CANDIDATE_PACKET_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "authorized_by_matter_action_artifact_id": matter_action_packet.get("schema_id"),
        "authorized_by_matter_action_commit": AUTHORIZED_BY_MATTER_ACTION_COMMIT,
        "candidate_id": SELECTED_REPLACEMENT_CANDIDATE_ID,
        "functional_contract": SELECTED_FUNCTIONAL_CONTRACT,
        "test_space": TEST_SPACE,
        "weak_variational_obligation": WEAK_VARIATIONAL_OBLIGATION,
        "prior_matter_action_result": PRIOR_MATTER_ACTION_RESULT,
        "field_content_lagrangian_result": FIELD_LAGRANGIAN_RESULT,
        "matter_model_selected": False,
        "matter_field_content_selected": False,
        "lagrangian_density_selected": False,
        "action_generated_source_subclass_selected": False,
        "action_generated_source_subclass_id": None,
        "arbitrary_distributional_source_retired": False,
        "arbitrary_distributional_source_action_derived_claimed": False,
        "action_derivability_retry_authorized": False,
        "toe_matter_sector_selection_required": True,
        "generic_matter_action_form": GENERIC_MATTER_ACTION_FORM,
        "real_scalar_action_form": REAL_SCALAR_ACTION_FORM,
        "gauge_field_action_form": GAUGE_FIELD_ACTION_FORM,
        "dirac_spinor_action_form": DIRAC_SPINOR_ACTION_FORM,
        "effective_qft_action_form": EFFECTIVE_QFT_ACTION_FORM,
        "matter_model_options": options,
        "required_matter_model_data": required_data,
        "missing_matter_model_data": [
            row["field_id"]
            for row in required_data
            if row["status"] in {"missing", "not_selected"}
        ],
        "mathematical_statement": (
            "A pairable distributional tensor T does not determine matter "
            "degrees of freedom or a Lagrangian. Any selected scalar, gauge, "
            "spinor, generic local, or effective action route would define a "
            "narrower action-generated source subclass, not prove that the "
            "arbitrary distributional candidate is action-derived. Because no "
            "ToE matter-sector candidate is licensed here, no field content or "
            "Lagrangian is selected."
        ),
        "downstream_progression": [
            {
                "stage": "field_content_and_lagrangian_candidate",
                "status": "BLOCKED",
                "decision": FIELD_LAGRANGIAN_RESULT,
                "reason": "No ToE matter-sector model licenses a field/Lagrangian selection.",
            },
            {
                "stage": "action_generated_source_subclass",
                "status": "NOT_SELECTED",
                "decision": "not_selected",
                "reason": "Selecting a scalar/gauge/spinor/effective route would narrow the candidate class and requires matter-sector authorization.",
            },
            {
                "stage": "action_derivability_retry",
                "status": "NOT_AUTHORIZED",
                "decision": "not_reached",
                "reason": "No field content or Lagrangian has been selected.",
            },
            {
                "stage": "toe_matter_sector_candidate_selection",
                "status": "NEXT_TARGET_AUTHORIZED",
                "decision": selected_next_target,
                "reason": "A ToE matter-sector candidate is required before matter action construction can be retried.",
            },
            {
                "stage": "weak_conservation",
                "status": "NOT_REACHED",
                "decision": "not_reached",
                "reason": "Weak conservation remains downstream of an action/diffeomorphism structure.",
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
        "matter_action_functional_claimed": False,
        "matter_action_admissibility_claimed": False,
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
            "MATTER_FIELD_CONTENT_AND_LAGRANGIAN_SELECTED_ACTION_DERIVABILITY_RETRY_AUTHORIZED",
            "ACTION_GENERATED_SOURCE_SUBCLASS_SELECTED_ARBITRARY_DISTRIBUTIONAL_SOURCE_RETIRED",
            "MATTER_FIELD_AND_LAGRANGIAN_OPTIONS_RECORDED_NO_SELECTION_LICENSED",
            FIELD_LAGRANGIAN_RESULT,
        ],
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "validation_policy": _validation_policy(),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet evaluates generic matter, real scalar, gauge-field, "
            "Dirac/spinor, effective QFT action, and no-field-content routes. "
            "It records that no matter field content or Lagrangian is selected "
            "because no ToE matter-sector model is licensed. It does not claim "
            "that arbitrary distributional T is action-derived, does not select "
            "an action-generated source subclass, and does not claim action "
            "derivability, source admissibility, weak conservation, Bianchi "
            "compatibility, semiclassical coupling, QFT-GR closure, empirical "
            "validation, public submission, or master-action promotion."
        ),
    }


def write_qft_gr_matter_field_content_and_lagrangian_candidate_packet(
    *,
    matter_action_packet_path: Path = MATTER_ACTION_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_matter_field_content_and_lagrangian_candidate_packet(
        matter_action_packet_path=matter_action_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR matter field content and Lagrangian candidate "
            "packet JSON."
        )
    )
    parser.add_argument(
        "--matter-action-packet",
        type=Path,
        default=MATTER_ACTION_PACKET_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    matter_action_packet_path = (
        ns.matter_action_packet
        if ns.matter_action_packet.is_absolute()
        else (REPO_ROOT / ns.matter_action_packet)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_matter_field_content_and_lagrangian_candidate_packet(
        matter_action_packet_path=matter_action_packet_path,
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
                "field_content_lagrangian_result": payload[
                    "field_content_lagrangian_result"
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

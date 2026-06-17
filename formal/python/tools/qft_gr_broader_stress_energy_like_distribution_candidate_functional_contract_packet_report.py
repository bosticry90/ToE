from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_source_action_test_action_weak_pairing_domain_calculation_packet_result_review_report import (
    CANDIDATE_SOURCE_ID,
    DEFAULT_OUT as DEFAULT_REVIEW_PATH,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as EXPECTED_REVIEW_OUTCOME,
    REVIEW_ID as EXPECTED_REVIEW_ID,
    SCHEMA_ID as EXPECTED_REVIEW_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-16T00:00:00Z"
SCHEMA_ID = (
    "QFT_GR_BROADER_STRESS_ENERGY_LIKE_DISTRIBUTION_CANDIDATE_FUNCTIONAL_"
    "CONTRACT_PACKET_20260616_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "QFT_GR_BROADER_STRESS_ENERGY_LIKE_DISTRIBUTION_CANDIDATE_FUNCTIONAL_"
    "CONTRACT_PACKET_v0"
)
CONTRACT_RESULT = (
    "CANDIDATE_FUNCTIONAL_CONTRACT_BLOCKED_BY_UNSPECIFIED_REGULARITY_AND_DOMAIN"
)
OUTCOME_ID = (
    "QFT_GR_BROADER_STRESS_ENERGY_LIKE_DISTRIBUTION_CANDIDATE_FUNCTIONAL_"
    "CONTRACT_PACKET_PREPARED_WITH_CANDIDATE_FUNCTIONAL_CONTRACT_BLOCKED_BY_"
    "UNSPECIFIED_REGULARITY_AND_DOMAIN_AND_NO_WEAK_PAIRING_RETRY_OR_SOURCE_"
    "ADMISSIBILITY"
)
PACKET_CLASSIFICATION = (
    "qft_gr_broader_stress_energy_like_distribution_candidate_functional_"
    "contract_packet_blocks_contract_selection_by_unspecified_regularity_and_domain"
)
NEXT_TARGET = (
    "review_qft_gr_broader_stress_energy_like_distribution_candidate_"
    "functional_contract_packet_result"
)
NEXT_TARGET_KIND = "qft_gr_candidate_functional_contract_packet_result_review"
AUTHORIZED_BY_REVIEW_COMMIT = "1a439525e24fc6052bf11a6b1918c7f61d369e31"
TEST_SPACE_ID = "D"
TEST_SPACE = "C_c^infty(M, Sym^2 T*M)"
REQUIRED_FUNCTIONAL_CONTRACT = "T : C_c^infty(M, Sym^2 T*M) -> R"
PAIRING_FORMULA = "<T, h> = integral_M T^{mu nu} h_{mu nu} dVol_g"
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_BROADER_STRESS_ENERGY_LIKE_DISTRIBUTION_CANDIDATE_"
        "FUNCTIONAL_CONTRACT_PACKET_20260616_v0.json"
    )
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRBroaderStressEnergyLikeDistributionCandidateFunctionalContractPacket.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _contract_field_assessment() -> list[dict[str, str]]:
    return [
        {
            "field": "background_spacetime",
            "status": "supplied_as_working_background_only",
            "value": "(M, g)",
            "note": "M is treated as the working smooth spacetime background with metric g; no Einstein equation or source admissibility is inferred.",
        },
        {
            "field": "test_space",
            "status": "supplied_for_contract_test",
            "value": TEST_SPACE,
            "note": "The candidate must act on compactly supported smooth symmetric covariant 2-tensors.",
        },
        {
            "field": "test_space_topology",
            "status": "supplied_as_required_continuity_topology",
            "value": "standard C_c^infty locally convex test-space topology",
            "note": "Continuity must be checked against this topology; no continuity proof is supplied.",
        },
        {
            "field": "candidate_regularity",
            "status": "blocked_unspecified",
            "value": "smooth / locally_integrable / distributional / unspecified not selected",
            "note": "The candidate does not license a regularity class that can select an integral representative or a distributional functional.",
        },
        {
            "field": "tensor_vs_tensor_density_status",
            "status": "blocked_unspecified",
            "value": "tensor_or_density_not_selected",
            "note": "The packet cannot choose dVol_g integration versus a density-based action without this status.",
        },
        {
            "field": "index_placement",
            "status": "blocked_unspecified",
            "value": "contravariant_covariant_or_mixed_not_selected",
            "note": "The contraction with h_{mu nu} requires a licensed index-placement convention.",
        },
        {
            "field": "volume_measure",
            "status": "blocked_by_tensor_density_and_metric_dependence",
            "value": "dVol_g_or_density_based_alternative_not_selected",
            "note": "The integral form is available only after the representative type and metric dependence are fixed.",
        },
        {
            "field": "metric_dependence",
            "status": "blocked_unspecified",
            "value": "metric_dependence_contract_not_supplied",
            "note": "The packet does not decide whether T depends on g, on background structure, or on a metric-independent density.",
        },
        {
            "field": "support_and_locality_assumptions",
            "status": "blocked_unspecified",
            "value": "support_locality_contract_not_supplied",
            "note": "Compact support of h is supplied, but locality/support behavior of T is not.",
        },
        {
            "field": "linearity",
            "status": "blocked_not_verified",
            "value": "linearity_of_T_on_D_not_supplied",
            "note": "The candidate has no map T : D -> R whose linearity can be checked.",
        },
        {
            "field": "continuity",
            "status": "blocked_not_verified",
            "value": "continuity_of_T_on_D_not_supplied",
            "note": "The candidate has no continuity bound or distribution-order contract.",
        },
        {
            "field": "coordinate_or_covariance_behavior",
            "status": "blocked_unspecified",
            "value": "coordinate_covariance_contract_not_supplied",
            "note": "The packet does not promote a coordinate-dependent representative to a covariant source object.",
        },
        {
            "field": "action_derived_or_merely_source_like_status",
            "status": "blocked_downstream_not_selected",
            "value": "action_derived_status_not_reached",
            "note": "Action derivability is downstream of functional-contract selection and remains not reached.",
        },
    ]


def _contract_options() -> list[dict[str, Any]]:
    return [
        {
            "option_id": "distributional_continuous_linear_functional",
            "contract_form": REQUIRED_FUNCTIONAL_CONTRACT,
            "selection_status": "not_selected",
            "required_data": [
                "linear_map_from_D_to_R",
                "continuity_for_standard_C_c_infty_topology",
                "tensor_distribution_order_or_equivalent_bound",
                "coordinate_or_covariance_behavior",
            ],
            "blocked_by": [
                "linearity_of_T_on_D_not_supplied",
                "continuity_of_T_on_D_not_supplied",
                "regularity_or_distribution_order_not_supplied",
            ],
        },
        {
            "option_id": "smooth_or_locally_integrable_tensor_representative",
            "contract_form": PAIRING_FORMULA,
            "selection_status": "not_selected",
            "required_data": [
                "regularity_class_smooth_or_locally_integrable",
                "contravariant_or_metric_raised_tensor_components",
                "volume_measure_dVol_g",
                "local_integrability_on_compact_sets",
            ],
            "blocked_by": [
                "candidate_regularity_not_supplied",
                "index_placement_not_supplied",
                "metric_dependence_or_volume_measure_not_supplied",
            ],
        },
        {
            "option_id": "tensor_density_pairing",
            "contract_form": "pair density-valued T with h without separately selecting dVol_g",
            "selection_status": "not_selected",
            "required_data": [
                "tensor_density_status",
                "density_weight",
                "coordinate_transformation_law",
                "linear_continuous_action_on_D",
            ],
            "blocked_by": [
                "tensor_vs_tensor_density_status_not_supplied",
                "coordinate_or_covariance_behavior_not_supplied",
                "continuity_of_T_on_D_not_supplied",
            ],
        },
    ]


def _missing_data() -> list[str]:
    return [
        "candidate_regularity_class_not_supplied",
        "tensor_vs_tensor_density_status_not_supplied",
        "index_placement_not_supplied",
        "volume_measure_or_density_pairing_not_selected",
        "metric_dependence_contract_not_supplied",
        "support_and_locality_assumptions_not_supplied",
        "linear_map_T_from_D_to_R_not_supplied",
        "continuity_bound_or_distribution_order_not_supplied",
        "coordinate_or_covariance_behavior_not_supplied",
        "action_derived_or_merely_source_like_status_not_supplied",
    ]


def _downstream_progression() -> list[dict[str, str]]:
    return [
        {
            "stage": "functional_contract",
            "status": "blocked",
            "decision": CONTRACT_RESULT,
            "reason": "No regularity/domain contract selects a continuous linear functional or integral representative.",
        },
        {
            "stage": "weak_pairing_retry",
            "status": "NOT_AUTHORIZED",
            "decision": "not_reached",
            "reason": "The candidate functional contract is blocked.",
        },
        {
            "stage": "action_derivability",
            "status": "NOT_REACHED",
            "decision": "not_reached",
            "reason": "Weak pairing retry is not authorized.",
        },
        {
            "stage": "weak_conservation",
            "status": "NOT_REACHED",
            "decision": "not_reached",
            "reason": "Action derivability is not reached.",
        },
        {
            "stage": "bianchi_compatibility",
            "status": "NOT_REACHED",
            "decision": "not_reached",
            "reason": "Weak conservation is not reached.",
        },
        {
            "stage": "semiclassical_source_admissibility",
            "status": "NOT_REACHED",
            "decision": "not_reached",
            "reason": "Bianchi compatibility is not reached.",
        },
    ]


def _mathematical_acceptance_outputs() -> dict[str, bool]:
    return {
        "definition_supplied": True,
        "proposition_or_contract_criterion_stated": True,
        "symbolic_pairing_form_recorded": True,
        "well_definedness_precheck_attempted": True,
        "counterexample_or_obstruction_recorded": True,
        "calculation_blocked_by_missing_formal_input": True,
        "weak_pairing_completed": False,
    }


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": "qft_gr_candidate_functional_contract_packet",
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


def build_qft_gr_broader_stress_energy_like_distribution_candidate_functional_contract_packet(
    *,
    review_path: Path = DEFAULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(review_path)
    fields = _contract_field_assessment()
    options = _contract_options()
    missing_data = _missing_data()
    outputs = _mathematical_acceptance_outputs()
    progression = _downstream_progression()
    blocked_fields = [
        row["field"] for row in fields if row["status"].startswith("blocked")
    ]
    acceptance_criteria = {
        "consumes_expected_result_review": (
            review.get("schema_id") == EXPECTED_REVIEW_SCHEMA_ID
            and review.get("review_id") == EXPECTED_REVIEW_ID
            and review.get("outcome_id") == EXPECTED_REVIEW_OUTCOME
            and review.get("selected_next_target") == CONSUMED_TARGET
        ),
        "test_space_and_contract_forms_stated": (
            TEST_SPACE in REQUIRED_FUNCTIONAL_CONTRACT
            and options[0]["contract_form"] == REQUIRED_FUNCTIONAL_CONTRACT
            and options[1]["contract_form"] == PAIRING_FORMULA
        ),
        "required_contract_fields_assessed": (
            len(fields) >= 13
            and "candidate_regularity" in {row["field"] for row in fields}
            and "continuity" in {row["field"] for row in fields}
            and "linearity" in {row["field"] for row in fields}
        ),
        "contract_selection_blocked_by_unspecified_regularity_and_domain": (
            CONTRACT_RESULT.endswith("UNSPECIFIED_REGULARITY_AND_DOMAIN")
            and len(blocked_fields) >= 8
            and "candidate_regularity_class_not_supplied" in missing_data
            and "linear_map_T_from_D_to_R_not_supplied" in missing_data
            and "continuity_bound_or_distribution_order_not_supplied" in missing_data
        ),
        "no_contract_option_selected": all(
            option["selection_status"] == "not_selected" for option in options
        ),
        "weak_pairing_retry_not_authorized": (
            progression[1]["stage"] == "weak_pairing_retry"
            and progression[1]["status"] == "NOT_AUTHORIZED"
        ),
        "downstream_stages_not_reached": all(
            row["status"] == "NOT_REACHED" for row in progression[2:]
        ),
        "non_promotion_boundary_preserved": True,
    }
    prepared = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if prepared
        else "REMEDIATE_QFT_GR_CANDIDATE_FUNCTIONAL_CONTRACT_PACKET"
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
        else "QFT_GR_BROADER_STRESS_ENERGY_LIKE_DISTRIBUTION_CANDIDATE_FUNCTIONAL_CONTRACT_PACKET_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "authorized_by_result_review_artifact_id": review.get("schema_id"),
        "authorized_by_result_review_commit": AUTHORIZED_BY_REVIEW_COMMIT,
        "candidate_source_id": CANDIDATE_SOURCE_ID,
        "contract_question": (
            "Can broader_stress_energy_like_distribution_candidate_not_source_"
            "admissible_v0 be specified as a mathematical object that acts on "
            "D = C_c^infty(M, Sym^2 T*M)?"
        ),
        "contract_result": CONTRACT_RESULT,
        "candidate_functional_contract_constructed": False,
        "candidate_functional_contract_rejected": False,
        "multiple_candidate_functional_contract_options_recorded": True,
        "contract_option_selected": False,
        "working_background": "(M, g)",
        "test_space_id": TEST_SPACE_ID,
        "test_space": TEST_SPACE,
        "required_functional_contract": REQUIRED_FUNCTIONAL_CONTRACT,
        "smooth_or_locally_integrable_pairing_formula": PAIRING_FORMULA,
        "contract_field_assessment": fields,
        "blocked_contract_fields": blocked_fields,
        "blocked_contract_field_count": len(blocked_fields),
        "contract_options": options,
        "missing_mathematical_data": missing_data,
        "missing_mathematical_data_count": len(missing_data),
        "mathematical_acceptance_outputs": outputs,
        "proposition_statement": (
            "A candidate source is eligible for weak-pairing retry only after "
            "it supplies either a continuous linear functional T : D -> R for "
            "D = C_c^infty(M, Sym^2 T*M), or a smooth/locally integrable "
            "representative whose integral pairing with h in D is well-defined."
        ),
        "downstream_progression": progression,
        "well_defined_pairing": "not_reached",
        "weak_pairing_retry_authorized": False,
        "source_is_action_derived": "not_reached",
        "weak_conservation_verified": "not_reached",
        "bianchi_compatible_source": "not_reached",
        "semiclassical_source_admissible": "not_reached",
        "weak_pairing_completed": False,
        "source_admissibility_claimed": False,
        "action_derivability_claimed": False,
        "conservation_claimed": False,
        "Bianchi_compatibility_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "qft_gr_closure_claimed": False,
        "qft_gr_seam_closed": False,
        "empirical_validation_claimed": False,
        "public_submission_authorized": False,
        "master_action_promoted": False,
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "validation_policy": _validation_policy(),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet defines the functional-contract obligation for the "
            "candidate source and records that contract selection is blocked by "
            "unspecified regularity and domain data. It does not complete weak "
            "pairing, authorize weak-pairing retry, derive an action, prove "
            "conservation, establish Bianchi compatibility, derive a "
            "semiclassical Einstein equation, close QFT-GR, authorize public "
            "submission, or promote the master action."
        ),
    }


def write_qft_gr_broader_stress_energy_like_distribution_candidate_functional_contract_packet(
    *,
    review_path: Path = DEFAULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_broader_stress_energy_like_distribution_candidate_functional_contract_packet(
        review_path=review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR broader stress-energy-like distribution "
            "candidate functional-contract packet JSON."
        )
    )
    parser.add_argument("--review", type=Path, default=DEFAULT_REVIEW_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    review_path = ns.review if ns.review.is_absolute() else (REPO_ROOT / ns.review)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_broader_stress_energy_like_distribution_candidate_functional_contract_packet(
        review_path=review_path,
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
                "contract_result": payload["contract_result"],
                "selected_next_target": payload["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

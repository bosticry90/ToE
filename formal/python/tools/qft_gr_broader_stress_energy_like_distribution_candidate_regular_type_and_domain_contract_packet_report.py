from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_broader_stress_energy_like_distribution_candidate_functional_contract_packet_report import (
    CONTRACT_RESULT as PRIOR_CONTRACT_RESULT,
    PAIRING_FORMULA,
    REQUIRED_FUNCTIONAL_CONTRACT,
    TEST_SPACE,
)
from formal.python.tools.qft_gr_broader_stress_energy_like_distribution_candidate_functional_contract_packet_result_review_report import (
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
    "QFT_GR_BROADER_STRESS_ENERGY_LIKE_DISTRIBUTION_CANDIDATE_REGULAR_TYPE_"
    "AND_DOMAIN_CONTRACT_PACKET_20260616_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "QFT_GR_BROADER_STRESS_ENERGY_LIKE_DISTRIBUTION_CANDIDATE_REGULAR_TYPE_"
    "AND_DOMAIN_CONTRACT_PACKET_v0"
)
REGULAR_TYPE_DOMAIN_RESULT = (
    "CANDIDATE_DEFINITION_INSUFFICIENT_FOR_REGULARITY_OR_DOMAIN_SELECTION"
)
OUTCOME_ID = (
    "QFT_GR_BROADER_STRESS_ENERGY_LIKE_DISTRIBUTION_CANDIDATE_REGULAR_TYPE_"
    "AND_DOMAIN_CONTRACT_PACKET_PREPARED_WITH_CANDIDATE_DEFINITION_INSUFFICIENT_"
    "FOR_REGULARITY_OR_DOMAIN_SELECTION_AND_NO_WEAK_PAIRING_RETRY_OR_SOURCE_"
    "ADMISSIBILITY"
)
PACKET_CLASSIFICATION = (
    "qft_gr_broader_stress_energy_like_distribution_candidate_regular_type_and_"
    "domain_contract_packet_records_candidate_definition_insufficient_for_"
    "regularity_or_domain_selection"
)
NEXT_TARGET = "prepare_qft_gr_candidate_definition_revision_or_replacement_packet"
NEXT_TARGET_KIND = "qft_gr_candidate_definition_revision_or_replacement_packet_preparation"
AUTHORIZED_BY_REVIEW_COMMIT = "86e3fb1f736c1ff86d9d287728a530312c2ed689"
SMOOTH_OR_LOCALLY_INTEGRABLE_CONTRACT = "T^{mu nu} in L^1_loc(M, Sym^2 TM)"
DISTRIBUTIONAL_CONTRACT = "T in D'(M, Sym^2 TM), equivalently T : D -> R continuous linear"
DENSITY_CONTRACT = "tensor-density T pairs directly with compactly supported test tensors"
OPERATOR_EXPECTATION_CONTRACT = (
    "renormalized expectation candidate from an operator-valued distribution"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_BROADER_STRESS_ENERGY_LIKE_DISTRIBUTION_CANDIDATE_"
        "REGULAR_TYPE_AND_DOMAIN_CONTRACT_PACKET_20260616_v0.json"
    )
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRBroaderStressEnergyLikeDistributionCandidateRegularTypeAndDomainContractPacket.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _regularity_option_assessments() -> list[dict[str, Any]]:
    return [
        {
            "option_id": "smooth_symmetric_tensor_field",
            "hierarchy_order": 1,
            "candidate_type": "smooth symmetric tensor field",
            "domain_contract": "T in C^infty(M, Sym^2 TM)",
            "pairing_route": PAIRING_FORMULA,
            "selection_status": "not_selected",
            "selection_licensed": False,
            "unselected_reason": (
                "The candidate definition does not supply smoothness, a "
                "contravariant symmetric tensor type, index placement, or "
                "metric dependence."
            ),
            "missing_license_fields": [
                "smooth_regular_representative",
                "symmetric_contravariant_tensor_type",
                "index_placement",
                "metric_dependence",
            ],
        },
        {
            "option_id": "locally_integrable_tensor_field",
            "hierarchy_order": 2,
            "candidate_type": "locally integrable tensor field",
            "domain_contract": SMOOTH_OR_LOCALLY_INTEGRABLE_CONTRACT,
            "pairing_route": PAIRING_FORMULA,
            "selection_status": "not_selected",
            "selection_licensed": False,
            "unselected_reason": (
                "The candidate definition does not supply local integrability "
                "on compact sets, tensor character, index placement, or a "
                "volume-measure contract."
            ),
            "missing_license_fields": [
                "L1_loc_regular_representative",
                "tensor_character",
                "index_placement",
                "dVol_g_or_measure_contract",
            ],
        },
        {
            "option_id": "tensor_valued_distribution",
            "hierarchy_order": 3,
            "candidate_type": "tensor-valued distribution",
            "domain_contract": DISTRIBUTIONAL_CONTRACT,
            "pairing_route": REQUIRED_FUNCTIONAL_CONTRACT,
            "selection_status": "not_selected",
            "selection_licensed": False,
            "unselected_reason": (
                "The candidate definition does not supply a continuous linear "
                "map on D, a distribution order/bound, or covariance behavior."
            ),
            "missing_license_fields": [
                "linear_map_T_from_D_to_R",
                "continuity_for_C_c_infty_topology",
                "distribution_order_or_bound",
                "coordinate_or_covariance_behavior",
            ],
        },
        {
            "option_id": "tensor_density",
            "hierarchy_order": 4,
            "candidate_type": "tensor density",
            "domain_contract": DENSITY_CONTRACT,
            "pairing_route": "density pairing without an additional dVol_g factor",
            "selection_status": "not_selected",
            "selection_licensed": False,
            "unselected_reason": (
                "The candidate definition does not supply density weight, "
                "density-valued tensor status, or coordinate transformation law."
            ),
            "missing_license_fields": [
                "tensor_density_status",
                "density_weight",
                "coordinate_transformation_law",
                "direct_density_pairing_contract",
            ],
        },
        {
            "option_id": "operator_valued_distribution_expectation_candidate",
            "hierarchy_order": 5,
            "candidate_type": "operator-valued distribution expectation candidate",
            "domain_contract": OPERATOR_EXPECTATION_CONTRACT,
            "pairing_route": (
                "state plus renormalization map would have to produce a "
                "c-number tensor distribution before weak-pairing retry"
            ),
            "selection_status": "not_selected",
            "selection_licensed": False,
            "unselected_reason": (
                "The candidate definition does not supply operator domain, "
                "state domain, renormalized expectation map, or a c-number "
                "distribution output contract."
            ),
            "missing_license_fields": [
                "operator_domain",
                "state_domain",
                "renormalized_expectation_map",
                "c_number_distribution_output_contract",
            ],
        },
        {
            "option_id": "undefined_or_insufficiently_specified",
            "hierarchy_order": 6,
            "candidate_type": "undefined / insufficiently specified",
            "domain_contract": "no regular type or domain contract selected",
            "pairing_route": "weak-pairing retry not licensed",
            "selection_status": "diagnostic_result",
            "selection_licensed": True,
            "unselected_reason": "",
            "missing_license_fields": [],
        },
    ]


def _domain_option_assessments() -> list[dict[str, Any]]:
    return [
        {
            "domain_option_id": "smooth_or_l1loc_tensor_domain",
            "contract_form": SMOOTH_OR_LOCALLY_INTEGRABLE_CONTRACT,
            "test_space": TEST_SPACE,
            "pairing_formula": PAIRING_FORMULA,
            "uses_dVol_g": True,
            "selection_status": "not_selected",
            "blocked_by": [
                "regular_representative_not_supplied",
                "index_placement_not_supplied",
                "metric_volume_contract_not_supplied",
            ],
        },
        {
            "domain_option_id": "distributional_tensor_domain",
            "contract_form": DISTRIBUTIONAL_CONTRACT,
            "test_space": TEST_SPACE,
            "pairing_formula": REQUIRED_FUNCTIONAL_CONTRACT,
            "uses_dVol_g": False,
            "selection_status": "not_selected",
            "blocked_by": [
                "linear_map_not_supplied",
                "continuity_bound_not_supplied",
                "distribution_order_not_supplied",
            ],
        },
        {
            "domain_option_id": "tensor_density_domain",
            "contract_form": DENSITY_CONTRACT,
            "test_space": TEST_SPACE,
            "pairing_formula": "direct tensor-density pairing, not tensor times dVol_g",
            "uses_dVol_g": False,
            "selection_status": "not_selected",
            "blocked_by": [
                "density_weight_not_supplied",
                "density_transformation_law_not_supplied",
                "direct_pairing_contract_not_supplied",
            ],
        },
        {
            "domain_option_id": "operator_expectation_domain",
            "contract_form": OPERATOR_EXPECTATION_CONTRACT,
            "test_space": TEST_SPACE,
            "pairing_formula": "not available until a c-number distribution is produced",
            "uses_dVol_g": False,
            "selection_status": "not_selected",
            "blocked_by": [
                "operator_domain_not_supplied",
                "state_domain_not_supplied",
                "renormalized_expectation_map_not_supplied",
            ],
        },
    ]


def _missing_candidate_definition_data() -> list[str]:
    return [
        "smooth_regular_representative_not_supplied",
        "L1_loc_regular_representative_not_supplied",
        "tensor_valued_distribution_map_not_supplied",
        "tensor_density_status_not_supplied",
        "operator_valued_distribution_expectation_contract_not_supplied",
        "index_placement_not_supplied",
        "metric_dependence_not_supplied",
        "dVol_g_or_density_pairing_contract_not_supplied",
        "linearity_on_test_space_not_supplied",
        "continuity_for_test_space_topology_not_supplied",
        "coordinate_or_covariance_behavior_not_supplied",
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": "qft_gr_candidate_regular_type_and_domain_contract_packet",
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


def build_qft_gr_broader_stress_energy_like_distribution_candidate_regular_type_and_domain_contract_packet(
    *,
    review_path: Path = DEFAULT_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review = _read_json(review_path)
    regularity_options = _regularity_option_assessments()
    domain_options = _domain_option_assessments()
    missing_data = _missing_candidate_definition_data()
    regular_contract_options = [
        row for row in regularity_options if row["option_id"] != "undefined_or_insufficiently_specified"
    ]
    acceptance_criteria = {
        "consumes_expected_result_review": (
            review.get("schema_id") == EXPECTED_REVIEW_SCHEMA_ID
            and review.get("review_id") == EXPECTED_REVIEW_ID
            and review.get("outcome_id") == EXPECTED_REVIEW_OUTCOME
            and review.get("selected_next_target") == CONSUMED_TARGET
        ),
        "regularity_options_enumerated": [
            row["option_id"] for row in regularity_options
        ]
        == [
            "smooth_symmetric_tensor_field",
            "locally_integrable_tensor_field",
            "tensor_valued_distribution",
            "tensor_density",
            "operator_valued_distribution_expectation_candidate",
            "undefined_or_insufficiently_specified",
        ],
        "domain_options_enumerated": [
            row["domain_option_id"] for row in domain_options
        ]
        == [
            "smooth_or_l1loc_tensor_domain",
            "distributional_tensor_domain",
            "tensor_density_domain",
            "operator_expectation_domain",
        ],
        "smooth_and_l1loc_route_contract_stated": (
            domain_options[0]["contract_form"] == SMOOTH_OR_LOCALLY_INTEGRABLE_CONTRACT
            and domain_options[0]["pairing_formula"] == PAIRING_FORMULA
            and domain_options[0]["uses_dVol_g"] is True
        ),
        "distributional_route_contract_stated": (
            domain_options[1]["contract_form"] == DISTRIBUTIONAL_CONTRACT
            and domain_options[1]["pairing_formula"] == REQUIRED_FUNCTIONAL_CONTRACT
        ),
        "density_route_distinguishes_volume_structure": (
            domain_options[2]["pairing_formula"]
            == "direct tensor-density pairing, not tensor times dVol_g"
            and domain_options[2]["uses_dVol_g"] is False
        ),
        "no_regular_contract_route_selected": all(
            row["selection_status"] == "not_selected"
            and row["selection_licensed"] is False
            and row["unselected_reason"]
            for row in regular_contract_options
        ),
        "insufficient_specification_selected_as_diagnostic": (
            regularity_options[-1]["option_id"] == "undefined_or_insufficiently_specified"
            and regularity_options[-1]["selection_status"] == "diagnostic_result"
        ),
        "candidate_definition_missing_data_recorded": len(missing_data) >= 10
        and "tensor_valued_distribution_map_not_supplied" in missing_data
        and "operator_valued_distribution_expectation_contract_not_supplied"
        in missing_data,
        "weak_pairing_retry_not_authorized": True,
        "revision_or_replacement_packet_selected": NEXT_TARGET
        == "prepare_qft_gr_candidate_definition_revision_or_replacement_packet",
        "non_promotion_boundary_preserved": True,
    }
    prepared = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if prepared
        else "REMEDIATE_QFT_GR_CANDIDATE_REGULAR_TYPE_AND_DOMAIN_CONTRACT_PACKET"
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
        else "QFT_GR_BROADER_STRESS_ENERGY_LIKE_DISTRIBUTION_CANDIDATE_REGULAR_TYPE_AND_DOMAIN_CONTRACT_PACKET_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "authorized_by_result_review_artifact_id": review.get("schema_id"),
        "authorized_by_result_review_commit": AUTHORIZED_BY_REVIEW_COMMIT,
        "candidate_source_id": CANDIDATE_SOURCE_ID,
        "prior_contract_result": PRIOR_CONTRACT_RESULT,
        "regular_type_domain_result": REGULAR_TYPE_DOMAIN_RESULT,
        "candidate_definition_status": "insufficiently_specified_for_regular_type_or_domain_selection",
        "selected_regular_type": None,
        "selected_domain_contract": None,
        "selected_contract_route": None,
        "regular_type_selected": False,
        "domain_contract_selected": False,
        "weak_pairing_retry_authorized": False,
        "weak_pairing_retry_target": None,
        "candidate_revision_or_replacement_required": True,
        "test_space": TEST_SPACE,
        "required_functional_contract": REQUIRED_FUNCTIONAL_CONTRACT,
        "smooth_or_locally_integrable_contract": SMOOTH_OR_LOCALLY_INTEGRABLE_CONTRACT,
        "smooth_or_locally_integrable_pairing_formula": PAIRING_FORMULA,
        "distributional_contract": DISTRIBUTIONAL_CONTRACT,
        "density_contract": DENSITY_CONTRACT,
        "operator_expectation_contract": OPERATOR_EXPECTATION_CONTRACT,
        "regularity_option_assessments": regularity_options,
        "domain_option_assessments": domain_options,
        "missing_candidate_definition_data": missing_data,
        "missing_candidate_definition_data_count": len(missing_data),
        "acceptable_result_outcomes": [
            "CANDIDATE_REGULAR_TYPE_AND_DOMAIN_SELECTED_WEAK_PAIRING_RETRY_AUTHORIZED",
            "CANDIDATE_REGULARITY_AND_DOMAIN_OPTIONS_RECORDED_NO_SELECTION_LICENSED",
            "CANDIDATE_DEFINITION_INSUFFICIENT_FOR_REGULARITY_OR_DOMAIN_SELECTION",
            "CANDIDATE_REQUIRES_REVISION_BEFORE_FUNCTIONAL_CONTRACT_SELECTION",
        ],
        "downstream_progression": [
            {
                "stage": "regular_type_and_domain_selection",
                "status": "blocked",
                "decision": REGULAR_TYPE_DOMAIN_RESULT,
                "reason": "No regular type or domain contract is licensed by the candidate definition.",
            },
            {
                "stage": "weak_pairing_retry",
                "status": "NOT_AUTHORIZED",
                "decision": "not_reached",
                "reason": "No regular type or domain contract was selected.",
            },
            {
                "stage": "action_derivability",
                "status": "NOT_REACHED",
                "decision": "not_reached",
                "reason": "Weak-pairing retry is not authorized.",
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
        ],
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
            "This packet evaluates smooth tensor, locally integrable tensor, "
            "tensor-valued distribution, tensor-density, and operator-expectation "
            "candidate routes and records that none is licensed by the current "
            "candidate definition. It selects only candidate definition revision "
            "or replacement; it does not authorize weak-pairing retry, source "
            "admissibility, action derivability, conservation, Bianchi "
            "compatibility, semiclassical coupling, QFT-GR closure, public "
            "submission, or master-action promotion."
        ),
    }


def write_qft_gr_broader_stress_energy_like_distribution_candidate_regular_type_and_domain_contract_packet(
    *,
    review_path: Path = DEFAULT_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_broader_stress_energy_like_distribution_candidate_regular_type_and_domain_contract_packet(
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
            "candidate regular type and domain contract packet JSON."
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
    payload = write_qft_gr_broader_stress_energy_like_distribution_candidate_regular_type_and_domain_contract_packet(
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
                "regular_type_domain_result": payload["regular_type_domain_result"],
                "selected_next_target": payload["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

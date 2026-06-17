from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_broader_stress_energy_like_distribution_candidate_functional_contract_packet_report import (
    CANDIDATE_SOURCE_ID,
    CONTRACT_RESULT as EXPECTED_CONTRACT_RESULT,
    DEFAULT_OUT as DEFAULT_PACKET_PATH,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as EXPECTED_PACKET_OUTCOME,
    PACKET_ID as EXPECTED_PACKET_ID,
    PAIRING_FORMULA,
    REQUIRED_FUNCTIONAL_CONTRACT,
    SCHEMA_ID as EXPECTED_PACKET_SCHEMA_ID,
    TEST_SPACE,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-16T00:00:00Z"
SCHEMA_ID = (
    "QFT_GR_BROADER_STRESS_ENERGY_LIKE_DISTRIBUTION_CANDIDATE_FUNCTIONAL_"
    "CONTRACT_PACKET_RESULT_REVIEW_20260616_v0"
)
ARTIFACT_ID = SCHEMA_ID
REVIEW_ID = (
    "QFT_GR_BROADER_STRESS_ENERGY_LIKE_DISTRIBUTION_CANDIDATE_FUNCTIONAL_"
    "CONTRACT_PACKET_RESULT_REVIEW_v0"
)
REVIEWED_COMMIT = "352ffab153c8146ce1e66094631838791e126021"
REVIEWED_LIVE_TARGET_BEFORE_REVIEW = CONSUMED_TARGET
OUTCOME_ID = (
    "QFT_GR_BROADER_STRESS_ENERGY_LIKE_DISTRIBUTION_CANDIDATE_FUNCTIONAL_"
    "CONTRACT_PACKET_RESULT_REVIEW_ACCEPTS_BLOCKED_UNSPECIFIED_REGULARITY_AND_"
    "DOMAIN_AND_AUTHORIZES_REGULAR_TYPE_AND_DOMAIN_CONTRACT_PACKET_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_broader_stress_energy_like_distribution_candidate_functional_"
    "contract_packet_result_review_accepts_blocked_unspecified_regularity_and_"
    "domain_and_authorizes_regular_type_and_domain_contract_packet_only"
)
NEXT_TARGET = (
    "prepare_qft_gr_broader_stress_energy_like_distribution_candidate_regular_"
    "type_and_domain_contract_packet"
)
NEXT_TARGET_KIND = "qft_gr_candidate_regular_type_and_domain_contract_packet_preparation"
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_BROADER_STRESS_ENERGY_LIKE_DISTRIBUTION_CANDIDATE_"
        "FUNCTIONAL_CONTRACT_PACKET_RESULT_REVIEW_20260616_v0.json"
    )
)
LEAN_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRBroaderStressEnergyLikeDistributionCandidateFunctionalContractPacketResultReview.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The functional-contract packet correctly blocks contract "
                "selection on unspecified regularity and domain data, so the "
                "next bounded mathematical packet must decide the candidate's "
                "regular type and domain contract."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": "The functional-contract packet result-review target is consumed here.",
        },
        {
            "target": "retry_qft_gr_weak_pairing_calculation",
            "decision": "not_authorized",
            "reason": "Weak-pairing retry remains blocked until a regular type and domain contract is selected.",
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "No functional contract, weak pairing, or admissible source is constructed.",
        },
        {
            "target": "derive_qft_gr_source_action",
            "decision": "not_authorized",
            "reason": "Action derivability is downstream of weak pairing and is not reached.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "QFT-GR closure remains unclaimed.",
        },
    ]


def _regular_type_options() -> list[str]:
    return [
        "smooth_symmetric_tensor_field",
        "locally_integrable_tensor_field",
        "tensor_valued_distribution",
        "tensor_density",
        "operator_valued_distribution_expectation_candidate",
        "undefined_or_insufficiently_specified",
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": "qft_gr_candidate_functional_contract_packet_result_review",
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


def build_qft_gr_broader_stress_energy_like_distribution_candidate_functional_contract_packet_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    candidate_next_targets = _candidate_next_targets()
    missing_data = set(packet.get("missing_mathematical_data", []))
    outputs = packet.get("mathematical_acceptance_outputs", {})
    progression = packet.get("downstream_progression", [])
    acceptance_criteria = {
        "consumes_expected_functional_contract_packet": (
            packet.get("schema_id") == EXPECTED_PACKET_SCHEMA_ID
            and packet.get("packet_id") == EXPECTED_PACKET_ID
            and packet.get("outcome_id") == EXPECTED_PACKET_OUTCOME
            and packet.get("selected_next_target") == CONSUMED_TARGET
        ),
        "blocked_result_is_exact": (
            packet.get("contract_result") == EXPECTED_CONTRACT_RESULT
            and packet.get("candidate_functional_contract_constructed") is False
            and packet.get("contract_option_selected") is False
        ),
        "contract_material_was_substantive": (
            packet.get("test_space") == TEST_SPACE
            and packet.get("required_functional_contract")
            == REQUIRED_FUNCTIONAL_CONTRACT
            and packet.get("smooth_or_locally_integrable_pairing_formula")
            == PAIRING_FORMULA
            and outputs.get("definition_supplied") is True
            and outputs.get("proposition_or_contract_criterion_stated") is True
            and outputs.get("well_definedness_precheck_attempted") is True
        ),
        "missing_regular_type_and_domain_data_recorded": {
            "candidate_regularity_class_not_supplied",
            "tensor_vs_tensor_density_status_not_supplied",
            "index_placement_not_supplied",
            "linear_map_T_from_D_to_R_not_supplied",
            "continuity_bound_or_distribution_order_not_supplied",
            "coordinate_or_covariance_behavior_not_supplied",
        }.issubset(missing_data),
        "weak_pairing_retry_not_authorized": (
            packet.get("weak_pairing_retry_authorized") is False
            and packet.get("weak_pairing_completed") is False
            and packet.get("well_defined_pairing") == "not_reached"
        ),
        "downstream_stages_not_reached": all(
            row.get("status") == "NOT_REACHED"
            for row in progression
            if row.get("stage")
            in {
                "action_derivability",
                "weak_conservation",
                "bianchi_compatibility",
                "semiclassical_source_admissibility",
            }
        ),
        "non_promotion_boundary_preserved": all(
            packet.get(key) is False
            for key in [
                "source_admissibility_claimed",
                "action_derivability_claimed",
                "conservation_claimed",
                "Bianchi_compatibility_claimed",
                "semiclassical_einstein_equation_derived",
                "qft_gr_closure_claimed",
                "qft_gr_seam_closed",
                "empirical_validation_claimed",
                "public_submission_authorized",
                "master_action_promoted",
            ]
        ),
        "regular_type_and_domain_packet_selected_only": [
            row["target"]
            for row in candidate_next_targets
            if row.get("decision") == "selected"
        ]
        == [NEXT_TARGET],
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_QFT_GR_CANDIDATE_FUNCTIONAL_CONTRACT_PACKET_RESULT_REVIEW"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "review_id": REVIEW_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "result_review_accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "QFT_GR_BROADER_STRESS_ENERGY_LIKE_DISTRIBUTION_CANDIDATE_FUNCTIONAL_CONTRACT_PACKET_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "reviewed_artifact_id": packet.get("schema_id"),
        "reviewed_commit": REVIEWED_COMMIT,
        "reviewed_live_target_before_review": REVIEWED_LIVE_TARGET_BEFORE_REVIEW,
        "reviewed_packet_id": packet.get("packet_id"),
        "review_outcome": OUTCOME_ID if accepted else "REQUIRES_REMEDIATION",
        "candidate_source_id": CANDIDATE_SOURCE_ID,
        "contract_result": packet.get("contract_result"),
        "contract_result_accepted": accepted,
        "test_space": packet.get("test_space"),
        "required_functional_contract": packet.get("required_functional_contract"),
        "smooth_or_locally_integrable_pairing_formula": packet.get(
            "smooth_or_locally_integrable_pairing_formula"
        ),
        "candidate_functional_contract_constructed": False,
        "candidate_functional_contract_rejected": False,
        "contract_option_selected": False,
        "multiple_candidate_functional_contract_options_recorded": True,
        "missing_regular_type_and_domain_data_confirmed": accepted,
        "next_packet_required_question": (
            "What mathematical regular type and domain contract, if any, is "
            "licensed for broader_stress_energy_like_distribution_candidate_"
            "not_source_admissible_v0?"
        ),
        "regular_type_options_to_assess": _regular_type_options(),
        "acceptable_next_packet_outcomes": [
            "CANDIDATE_REGULARITY_AND_DOMAIN_SELECTED_WEAK_PAIRING_RETRY_AUTHORIZED",
            "CANDIDATE_REGULARITY_AND_DOMAIN_OPTIONS_RECORDED_NO_SELECTION_LICENSED",
            "CANDIDATE_DEFINITION_INSUFFICIENT_FOR_REGULARITY_OR_DOMAIN_SELECTION",
        ],
        "weak_pairing_retry_authorized": False,
        "weak_pairing_completed": False,
        "well_defined_pairing": "not_reached",
        "action_derivability_status": packet.get("source_is_action_derived"),
        "weak_conservation_status": packet.get("weak_conservation_verified"),
        "bianchi_compatibility_status": packet.get("bianchi_compatible_source"),
        "semiclassical_source_admissibility_status": packet.get(
            "semiclassical_source_admissible"
        ),
        "candidate_next_targets": candidate_next_targets,
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
        "lean_review_file": _ptr(LEAN_REVIEW_PATH),
        "validation_policy": _validation_policy(),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This review accepts the candidate functional-contract packet as a "
            "negative mathematical result: the contract is blocked by "
            "unspecified regularity and domain data. It authorizes only a "
            "regular type and domain contract packet, not weak-pairing retry, "
            "source admissibility, action derivability, conservation, Bianchi "
            "compatibility, semiclassical coupling, QFT-GR closure, public "
            "submission, or master-action promotion."
        ),
    }


def write_qft_gr_broader_stress_energy_like_distribution_candidate_functional_contract_packet_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_broader_stress_energy_like_distribution_candidate_functional_contract_packet_result_review(
        packet_path=packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR candidate functional-contract packet result-review JSON."
        )
    )
    parser.add_argument("--packet", type=Path, default=DEFAULT_PACKET_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    packet_path = ns.packet if ns.packet.is_absolute() else (REPO_ROOT / ns.packet)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_broader_stress_energy_like_distribution_candidate_functional_contract_packet_result_review(
        packet_path=packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        json.dumps(
            {
                "out": _ptr(out),
                "review_id": payload["review_id"],
                "outcome_id": payload["outcome_id"],
                "accepted": payload["accepted"],
                "selected_next_target": payload["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

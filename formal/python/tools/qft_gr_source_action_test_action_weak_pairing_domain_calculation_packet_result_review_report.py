from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_source_action_test_action_weak_pairing_domain_calculation_packet_report import (
    CALCULATION_RESULT as EXPECTED_CALCULATION_RESULT,
    DEFAULT_OUT as DEFAULT_PACKET_PATH,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as EXPECTED_PACKET_OUTCOME,
    PACKET_ID as EXPECTED_PACKET_ID,
    SCHEMA_ID as EXPECTED_PACKET_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-16T00:00:00Z"
SCHEMA_ID = (
    "QFT_GR_SOURCE_ACTION_TEST_ACTION_WEAK_PAIRING_DOMAIN_CALCULATION_PACKET_"
    "RESULT_REVIEW_20260616_v0"
)
ARTIFACT_ID = SCHEMA_ID
REVIEW_ID = (
    "QFT_GR_SOURCE_ACTION_TEST_ACTION_WEAK_PAIRING_DOMAIN_CALCULATION_PACKET_"
    "RESULT_REVIEW_v0"
)
REVIEWED_COMMIT = "e8aec546c5236ae1421108048326572784703003"
REVIEWED_LIVE_TARGET_BEFORE_REVIEW = CONSUMED_TARGET
OUTCOME_ID = (
    "QFT_GR_SOURCE_ACTION_TEST_ACTION_WEAK_PAIRING_DOMAIN_CALCULATION_PACKET_"
    "RESULT_REVIEW_ACCEPTS_BLOCKED_MISSING_CANDIDATE_FUNCTIONAL_CONTRACT_"
    "AND_AUTHORIZES_CANDIDATE_FUNCTIONAL_CONTRACT_PACKET_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_source_action_test_action_weak_pairing_domain_calculation_packet_"
    "result_review_accepts_blocked_missing_candidate_functional_contract_and_"
    "authorizes_candidate_functional_contract_packet_only"
)
NEXT_TARGET = (
    "prepare_qft_gr_broader_stress_energy_like_distribution_candidate_"
    "functional_contract_packet"
)
NEXT_TARGET_KIND = "qft_gr_candidate_source_functional_contract_packet_preparation"
CANDIDATE_SOURCE_ID = (
    "broader_stress_energy_like_distribution_candidate_not_source_admissible_v0"
)
REQUIRED_FUNCTIONAL_CONTRACT = "T : C_c^infty(M, Sym^2 T*M) -> R"
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_SOURCE_ACTION_TEST_ACTION_WEAK_PAIRING_DOMAIN_CALCULATION_"
        "PACKET_RESULT_REVIEW_20260616_v0.json"
    )
)
LEAN_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRSourceActionTestActionWeakPairingDomainCalculationPacketResultReview.lean"
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
                "The calculation packet correctly blocks weak pairing on the "
                "missing candidate functional/domain contract, so the next "
                "bounded mathematical packet must supply, block, or refute "
                "that contract."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": "The calculation packet result-review target is consumed here.",
        },
        {
            "target": "retry_qft_gr_weak_pairing_calculation",
            "decision": "not_authorized",
            "reason": "Retry is blocked until a candidate functional contract is supplied.",
        },
        {
            "target": "derive_qft_gr_source_action",
            "decision": "not_authorized",
            "reason": "Action derivability is downstream of weak pairing and is not reached.",
        },
        {
            "target": "claim_qft_gr_source_admissibility",
            "decision": "not_authorized",
            "reason": "No weak-pairing contract or admissible source is constructed.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "QFT-GR closure remains unclaimed.",
        },
    ]


def _contract_obligations() -> list[str]:
    return [
        "background_spacetime_assumptions",
        "test_space_topology",
        "regularity_class_of_T",
        "tensor_vs_tensor_density_status",
        "index_placement",
        "metric_dependence",
        "support_and_locality_assumptions",
        "linearity",
        "continuity",
        "coordinate_or_covariance_behavior",
        "action_derived_or_merely_source_like_status",
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": "qft_gr_weak_pairing_calculation_packet_result_review",
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


def build_qft_gr_source_action_test_action_weak_pairing_domain_calculation_packet_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    progression = packet.get("calculation_progression", [])
    outputs = packet.get("mathematical_acceptance_outputs", {})
    candidate_next_targets = _candidate_next_targets()
    acceptance_criteria = {
        "consumes_expected_calculation_packet": (
            packet.get("schema_id") == EXPECTED_PACKET_SCHEMA_ID
            and packet.get("packet_id") == EXPECTED_PACKET_ID
            and packet.get("outcome_id") == EXPECTED_PACKET_OUTCOME
            and packet.get("selected_next_target") == CONSUMED_TARGET
        ),
        "weak_pairing_attempted_at_definition_proposition_domain_level": (
            outputs.get("definition_supplied") is True
            and outputs.get("lemma_or_proposition_stated") is True
            and outputs.get("well_definedness_proof_attempted") is True
            and "T : D -> R"
            in packet.get("weak_pairing_definition", {}).get(
                "distributional_requirement", ""
            )
        ),
        "blocker_is_missing_candidate_functional_contract": (
            packet.get("calculation_result") == EXPECTED_CALCULATION_RESULT
            and packet.get("well_defined_pairing") == "blocked"
            and packet.get("missing_mathematical_data_count", 0) >= 4
            and "continuous_linear_functional_T_from_test_space_D_to_R_not_supplied"
            in packet.get("missing_mathematical_data", [])
        ),
        "weak_pairing_not_marked_false_for_underspecification": (
            packet.get("well_defined_pairing") == "blocked"
            and all(
                row.get("decision") != "false"
                for row in progression
                if row.get("stage") == "weak_pairing"
            )
        ),
        "downstream_stages_not_reached": all(
            row.get("status") == "NOT_REACHED"
            for row in progression
            if row.get("stage") != "weak_pairing"
        ),
        "non_promotion_boundary_preserved": all(
            packet.get(key) is False
            for key in [
                "source_admissibility_claimed",
                "Bianchi_compatibility_claimed",
                "semiclassical_einstein_equation_derived",
                "qft_gr_closure_claimed",
                "qft_gr_seam_closed",
                "empirical_validation_claimed",
                "public_submission_authorized",
                "master_action_promoted",
            ]
        ),
        "candidate_functional_contract_packet_selected_only": [
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
        else "REMEDIATE_QFT_GR_WEAK_PAIRING_CALCULATION_PACKET_RESULT_REVIEW"
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
        else "QFT_GR_SOURCE_ACTION_TEST_ACTION_WEAK_PAIRING_DOMAIN_CALCULATION_PACKET_RESULT_REVIEW_REQUIRES_REMEDIATION",
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
        "calculation_result": packet.get("calculation_result"),
        "calculation_result_accepted": accepted,
        "weak_pairing_attempted": True,
        "weak_pairing_decision": packet.get("well_defined_pairing"),
        "weak_pairing_not_false_due_to_underspecification": True,
        "missing_candidate_functional_contract_confirmed": accepted,
        "required_functional_contract": REQUIRED_FUNCTIONAL_CONTRACT,
        "contract_packet_required_obligations": _contract_obligations(),
        "contract_packet_required_obligation_count": len(_contract_obligations()),
        "action_derivability_status": packet.get("source_is_action_derived"),
        "weak_conservation_status": packet.get("weak_conservation_verified"),
        "bianchi_compatibility_status": packet.get("bianchi_compatible_source"),
        "semiclassical_source_admissibility_status": packet.get(
            "semiclassical_source_admissible"
        ),
        "downstream_status_when_weak_pairing_blocked": packet.get(
            "downstream_status_when_weak_pairing_blocked"
        ),
        "candidate_next_targets": candidate_next_targets,
        "source_admissibility_claimed": False,
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
            "This review accepts the weak-pairing calculation packet as a "
            "blocked mathematical failure diagnosis: the current candidate "
            "lacks the functional/domain contract required to decide weak "
            "pairability. It authorizes only a candidate functional-contract "
            "packet, not weak-pairing retry, action derivability, source "
            "admissibility, Bianchi compatibility, semiclassical coupling, "
            "QFT-GR closure, public submission, or master-action promotion."
        ),
    }


def write_qft_gr_source_action_test_action_weak_pairing_domain_calculation_packet_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = (
        build_qft_gr_source_action_test_action_weak_pairing_domain_calculation_packet_result_review(
            packet_path=packet_path,
            captured_at_utc=captured_at_utc,
        )
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR source-action/test-action/weak-pairing "
            "calculation packet result-review JSON."
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
    payload = write_qft_gr_source_action_test_action_weak_pairing_domain_calculation_packet_result_review(
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

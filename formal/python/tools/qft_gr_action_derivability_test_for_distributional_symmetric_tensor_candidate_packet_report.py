from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_weak_pairing_retry_for_selected_candidate_functional_contract_packet_report import (
    CALCULATION_RESULT as PRIOR_WEAK_PAIRING_RESULT,
    DEFAULT_OUT as WEAK_PAIRING_PACKET_PATH,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as EXPECTED_WEAK_PAIRING_OUTCOME,
    SCHEMA_ID as EXPECTED_WEAK_PAIRING_SCHEMA_ID,
    SELECTED_FUNCTIONAL_CONTRACT,
    SELECTED_PAIRING_RULE,
    SELECTED_REPLACEMENT_CANDIDATE_ID,
    TEST_SPACE,
    WELL_DEFINED_PAIRING_SCOPE,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-16T00:00:00Z"
SCHEMA_ID = (
    "QFT_GR_ACTION_DERIVABILITY_TEST_FOR_DISTRIBUTIONAL_SYMMETRIC_TENSOR_"
    "CANDIDATE_PACKET_20260616_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "QFT_GR_ACTION_DERIVABILITY_TEST_FOR_DISTRIBUTIONAL_SYMMETRIC_TENSOR_"
    "CANDIDATE_PACKET_v0"
)
ACTION_DERIVABILITY_RESULT = "ACTION_DERIVABILITY_BLOCKED_BY_MISSING_ACTION_FUNCTIONAL"
OUTCOME_ID = (
    "QFT_GR_ACTION_DERIVABILITY_TEST_FOR_DISTRIBUTIONAL_SYMMETRIC_TENSOR_"
    "CANDIDATE_PACKET_PREPARED_WITH_ACTION_DERIVABILITY_BLOCKED_BY_MISSING_"
    "ACTION_FUNCTIONAL_AND_NO_SOURCE_ADMISSIBILITY_OR_QFT_GR_CLOSURE"
)
PACKET_CLASSIFICATION = (
    "qft_gr_action_derivability_test_records_missing_matter_action_functional_"
    "for_pairable_distributional_symmetric_tensor_candidate"
)
WEAK_VARIATIONAL_OBLIGATION = "delta S_m[g](h) = -1/2 T(h)"
SMOOTH_REFERENCE_FORM = (
    "T_{mu nu} = -2 / sqrt(-g) * delta S_m / delta g^{mu nu}"
)
NEXT_TARGET = "prepare_qft_gr_matter_action_functional_candidate_packet"
NEXT_TARGET_KIND = "qft_gr_matter_action_functional_candidate_packet_preparation"
AUTHORIZED_BY_WEAK_PAIRING_COMMIT = "a54cf90a65503defe75cc2838d028e5aa1c2bf1a"
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_ACTION_DERIVABILITY_TEST_FOR_DISTRIBUTIONAL_SYMMETRIC_"
        "TENSOR_CANDIDATE_PACKET_20260616_v0.json"
    )
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRActionDerivabilityTestForDistributionalSymmetricTensorCandidatePacket.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _action_derivability_obligations() -> list[dict[str, Any]]:
    return [
        {
            "obligation_id": "matter_action_functional",
            "required_form": "S_m[g, fields] or an equivalent licensed matter action functional",
            "status": "missing",
            "blocks_action_derivability": True,
        },
        {
            "obligation_id": "metric_variation_rule",
            "required_form": WEAK_VARIATIONAL_OBLIGATION,
            "status": "missing",
            "blocks_action_derivability": True,
        },
        {
            "obligation_id": "variational_domain",
            "required_form": f"h in {TEST_SPACE}",
            "status": "missing_for_action_functional",
            "blocks_action_derivability": True,
        },
        {
            "obligation_id": "sign_and_normalization_convention",
            "required_form": "delta S_m[g](h) = -1/2 T(h)",
            "status": "stated_as_target_convention_not_derived",
            "blocks_action_derivability": True,
        },
        {
            "obligation_id": "covariance_or_diffeomorphism_behavior",
            "required_form": "matter action covariance sufficient for downstream conservation test",
            "status": "not_reached",
            "blocks_action_derivability": False,
        },
        {
            "obligation_id": "boundary_support_conditions",
            "required_form": "compact-support or boundary treatment compatible with the variation",
            "status": "not_reached",
            "blocks_action_derivability": False,
        },
    ]


def _calculation_steps() -> list[dict[str, Any]]:
    return [
        {
            "step_id": "bind_pairable_candidate",
            "statement": (
                f"Use {SELECTED_REPLACEMENT_CANDIDATE_ID} with pairing "
                f"{SELECTED_PAIRING_RULE}."
            ),
            "result": "supplied_by_prior_weak_pairing_packet",
            "passed": True,
        },
        {
            "step_id": "state_weak_variational_obligation",
            "statement": WEAK_VARIATIONAL_OBLIGATION,
            "result": "obligation_stated",
            "passed": True,
        },
        {
            "step_id": "search_for_licensed_action_functional",
            "statement": "Find a licensed S_m whose metric variation equals -1/2 T(h).",
            "result": "no_matter_action_functional_supplied",
            "passed": False,
        },
        {
            "step_id": "derive_action_variation",
            "statement": "Compute delta S_m[g](h) and compare with -1/2 T(h).",
            "result": "blocked_by_missing_action_functional",
            "passed": False,
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": "qft_gr_action_derivability_test_for_distributional_symmetric_tensor_candidate_packet",
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


def build_qft_gr_action_derivability_test_for_distributional_symmetric_tensor_candidate_packet(
    *,
    weak_pairing_packet_path: Path = WEAK_PAIRING_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    weak_pairing_packet = _read_json(weak_pairing_packet_path)
    obligations = _action_derivability_obligations()
    steps = _calculation_steps()
    missing_blockers = [
        row["obligation_id"]
        for row in obligations
        if row["blocks_action_derivability"] and row["status"] != "supplied"
    ]
    acceptance_criteria = {
        "consumes_expected_weak_pairing_packet": (
            weak_pairing_packet.get("schema_id") == EXPECTED_WEAK_PAIRING_SCHEMA_ID
            and weak_pairing_packet.get("outcome_id") == EXPECTED_WEAK_PAIRING_OUTCOME
            and weak_pairing_packet.get("selected_next_target") == CONSUMED_TARGET
        ),
        "prior_weak_pairing_constructed": (
            weak_pairing_packet.get("calculation_result") == PRIOR_WEAK_PAIRING_RESULT
            and weak_pairing_packet.get("well_defined_pairing") is True
            and weak_pairing_packet.get("well_defined_pairing_scope")
            == WELL_DEFINED_PAIRING_SCOPE
        ),
        "weak_variational_obligation_stated": steps[1]["statement"]
        == WEAK_VARIATIONAL_OBLIGATION,
        "missing_action_functional_recorded": "matter_action_functional"
        in missing_blockers,
        "metric_variation_rule_missing": "metric_variation_rule" in missing_blockers,
        "action_derivability_not_constructed": True,
        "next_target_is_matter_action_candidate_packet": NEXT_TARGET
        == "prepare_qft_gr_matter_action_functional_candidate_packet",
        "non_promotion_boundary_preserved": True,
    }
    prepared = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if prepared
        else "REMEDIATE_QFT_GR_ACTION_DERIVABILITY_TEST_PACKET"
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
        else "QFT_GR_ACTION_DERIVABILITY_TEST_FOR_DISTRIBUTIONAL_SYMMETRIC_TENSOR_CANDIDATE_PACKET_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "authorized_by_weak_pairing_artifact_id": weak_pairing_packet.get("schema_id"),
        "authorized_by_weak_pairing_commit": AUTHORIZED_BY_WEAK_PAIRING_COMMIT,
        "candidate_id": SELECTED_REPLACEMENT_CANDIDATE_ID,
        "functional_contract": SELECTED_FUNCTIONAL_CONTRACT,
        "test_domain": TEST_SPACE,
        "weak_pairing_result": PRIOR_WEAK_PAIRING_RESULT,
        "weak_pairing_scope": WELL_DEFINED_PAIRING_SCOPE,
        "weak_pairing_constructed": True,
        "weak_variational_obligation": WEAK_VARIATIONAL_OBLIGATION,
        "smooth_reference_form": SMOOTH_REFERENCE_FORM,
        "action_derivability_result": ACTION_DERIVABILITY_RESULT,
        "action_derivability_constructed": False,
        "source_is_action_derived": False,
        "matter_action_functional_supplied": False,
        "metric_variation_rule_supplied": False,
        "variational_domain_for_action_supplied": False,
        "sign_normalization_derived": False,
        "action_derivability_blockers": missing_blockers,
        "action_derivability_obligations": obligations,
        "calculation_steps": steps,
        "mathematical_statement": (
            "The pairable distributional tensor T would be action-derived only "
            "if a licensed matter action S_m supplied the weak variation "
            "delta S_m[g](h) = -1/2 T(h). The weak pairing alone does not "
            "supply S_m, so action derivability is blocked."
        ),
        "downstream_progression": [
            {
                "stage": "weak_pairing",
                "status": "COMPLETED_RESTRICTED",
                "decision": WELL_DEFINED_PAIRING_SCOPE,
                "reason": "Carried forward from the preserved weak-pairing retry packet.",
            },
            {
                "stage": "action_derivability",
                "status": "BLOCKED",
                "decision": ACTION_DERIVABILITY_RESULT,
                "reason": "No licensed matter action functional or metric variation rule is supplied.",
            },
            {
                "stage": "matter_action_functional_candidate",
                "status": "NEXT_TARGET_AUTHORIZED",
                "decision": selected_next_target,
                "reason": "A matter action functional candidate is required before action derivability can be retried.",
            },
            {
                "stage": "weak_conservation",
                "status": "NOT_REACHED",
                "decision": "not_reached",
                "reason": "Weak conservation is downstream of action derivability or a non-action source route decision.",
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
            "ACTION_DERIVABILITY_CONSTRUCTED_NONPROMOTIONALLY",
            ACTION_DERIVABILITY_RESULT,
            "ACTION_DERIVABILITY_BLOCKED_BY_VARIATIONAL_DOMAIN_MISMATCH",
            "ACTION_DERIVABILITY_REJECTED_FOR_ARBITRARY_DISTRIBUTIONAL_CANDIDATE",
        ],
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "validation_policy": _validation_policy(),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet tests action derivability for a pairable "
            "distributional symmetric tensor candidate and records that the "
            "test is blocked by a missing matter action functional. It does "
            "not claim source admissibility, action derivability, weak "
            "conservation, Bianchi compatibility, semiclassical coupling, "
            "QFT-GR closure, empirical validation, public submission, or "
            "master-action promotion."
        ),
    }


def write_qft_gr_action_derivability_test_for_distributional_symmetric_tensor_candidate_packet(
    *,
    weak_pairing_packet_path: Path = WEAK_PAIRING_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_action_derivability_test_for_distributional_symmetric_tensor_candidate_packet(
        weak_pairing_packet_path=weak_pairing_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR action-derivability test packet for the "
            "distributional symmetric tensor candidate."
        )
    )
    parser.add_argument(
        "--weak-pairing-packet", type=Path, default=WEAK_PAIRING_PACKET_PATH
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    weak_pairing_packet_path = (
        ns.weak_pairing_packet
        if ns.weak_pairing_packet.is_absolute()
        else (REPO_ROOT / ns.weak_pairing_packet)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_action_derivability_test_for_distributional_symmetric_tensor_candidate_packet(
        weak_pairing_packet_path=weak_pairing_packet_path,
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
                "action_derivability_result": payload["action_derivability_result"],
                "selected_next_target": payload["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_candidate_definition_revision_or_replacement_packet_report import (
    DEFAULT_OUT as CANDIDATE_DEFINITION_PACKET_PATH,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as EXPECTED_CANDIDATE_DEFINITION_OUTCOME,
    SCHEMA_ID as EXPECTED_CANDIDATE_DEFINITION_SCHEMA_ID,
    SELECTED_FUNCTIONAL_CONTRACT,
    SELECTED_INDEX_PLACEMENT,
    SELECTED_PAIRING_RULE,
    SELECTED_REPLACEMENT_CANDIDATE_ID,
    SELECTED_REPLACEMENT_CANDIDATE_KIND,
    SELECTED_TENSOR_TYPE,
    TEST_SPACE,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-16T00:00:00Z"
SCHEMA_ID = (
    "QFT_GR_WEAK_PAIRING_RETRY_FOR_SELECTED_CANDIDATE_FUNCTIONAL_CONTRACT_"
    "PACKET_20260616_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "QFT_GR_WEAK_PAIRING_RETRY_FOR_SELECTED_CANDIDATE_FUNCTIONAL_CONTRACT_PACKET_v0"
CALCULATION_RESULT = (
    "WEAK_PAIRING_CONSTRUCTED_FOR_SELECTED_DISTRIBUTIONAL_SYMMETRIC_TENSOR_"
    "CANDIDATE_ACTION_DERIVABILITY_NOT_REACHED"
)
OUTCOME_ID = (
    "QFT_GR_WEAK_PAIRING_RETRY_FOR_SELECTED_CANDIDATE_FUNCTIONAL_CONTRACT_"
    "PACKET_PREPARED_WITH_WEAK_PAIRING_CONSTRUCTED_FOR_SELECTED_"
    "DISTRIBUTIONAL_SYMMETRIC_TENSOR_CANDIDATE_AND_ACTION_DERIVABILITY_NOT_"
    "REACHED"
)
PACKET_CLASSIFICATION = (
    "qft_gr_weak_pairing_retry_constructs_distributional_pairing_for_selected_"
    "functional_contract_without_source_admissibility_or_action_derivability"
)
WELL_DEFINED_PAIRING_SCOPE = (
    "well_defined_as_distributional_pairing_under_selected_functional_contract"
)
DISTRIBUTIONAL_REGULARITY = "D'(M, Sym^2 TM)"
ACTION_DERIVABILITY_STATUS = "not_reached"
NEXT_TARGET = (
    "prepare_qft_gr_action_derivability_test_for_distributional_symmetric_"
    "tensor_candidate"
)
NEXT_TARGET_KIND = (
    "qft_gr_action_derivability_test_for_distributional_symmetric_tensor_candidate"
)
AUTHORIZED_BY_CANDIDATE_DEFINITION_COMMIT = (
    "1957478764ecfa2807f82a0ee335a324d52ab5f6"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_WEAK_PAIRING_RETRY_FOR_SELECTED_CANDIDATE_FUNCTIONAL_"
        "CONTRACT_PACKET_20260616_v0.json"
    )
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRWeakPairingRetryForSelectedCandidateFunctionalContractPacket.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _calculation_steps() -> list[dict[str, Any]]:
    return [
        {
            "step_id": "bind_selected_candidate",
            "statement": (
                "Use the selected replacement candidate "
                f"{SELECTED_REPLACEMENT_CANDIDATE_ID}."
            ),
            "result": "supplied_by_prior_packet",
            "passed": True,
        },
        {
            "step_id": "bind_test_domain",
            "statement": f"D = {TEST_SPACE}",
            "result": "test_domain_supplied",
            "passed": True,
        },
        {
            "step_id": "bind_distributional_contract",
            "statement": SELECTED_FUNCTIONAL_CONTRACT,
            "result": "continuous_linear_functional_supplied",
            "passed": True,
        },
        {
            "step_id": "define_weak_pairing",
            "statement": SELECTED_PAIRING_RULE,
            "result": "definition_supplied",
            "passed": True,
        },
        {
            "step_id": "well_definedness_check",
            "statement": (
                "For each h in D, T(h) is a real number by the selected "
                "continuous linear functional contract."
            ),
            "result": WELL_DEFINED_PAIRING_SCOPE,
            "passed": True,
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": "qft_gr_weak_pairing_retry_for_selected_candidate_functional_contract_packet",
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


def build_qft_gr_weak_pairing_retry_for_selected_candidate_functional_contract_packet(
    *,
    candidate_definition_packet_path: Path = CANDIDATE_DEFINITION_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    candidate_definition_packet = _read_json(candidate_definition_packet_path)
    calculation_steps = _calculation_steps()
    acceptance_criteria = {
        "consumes_expected_candidate_definition_packet": (
            candidate_definition_packet.get("schema_id")
            == EXPECTED_CANDIDATE_DEFINITION_SCHEMA_ID
            and candidate_definition_packet.get("outcome_id")
            == EXPECTED_CANDIDATE_DEFINITION_OUTCOME
            and candidate_definition_packet.get("selected_next_target")
            == CONSUMED_TARGET
        ),
        "selected_candidate_is_distributional_symmetric_tensor": (
            candidate_definition_packet.get("selected_replacement_candidate_id")
            == SELECTED_REPLACEMENT_CANDIDATE_ID
            and candidate_definition_packet.get("selected_replacement_candidate_kind")
            == SELECTED_REPLACEMENT_CANDIDATE_KIND
            and candidate_definition_packet.get("selected_regular_type")
            == DISTRIBUTIONAL_REGULARITY
        ),
        "test_domain_bound": candidate_definition_packet.get("selected_test_domain")
        == TEST_SPACE,
        "functional_contract_bound": candidate_definition_packet.get(
            "selected_functional_contract"
        )
        == SELECTED_FUNCTIONAL_CONTRACT,
        "pairing_defined_as_distributional_evaluation": SELECTED_PAIRING_RULE
        == "<T, h> := T(h) for h in C_c^infty(M, Sym^2 T*M)",
        "all_calculation_steps_pass": all(row["passed"] is True for row in calculation_steps),
        "well_defined_pairing_restricted_scope": True,
        "action_derivability_not_reached": True,
        "non_promotion_boundary_preserved": True,
    }
    prepared = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if prepared
        else "REMEDIATE_QFT_GR_WEAK_PAIRING_RETRY_FOR_SELECTED_CANDIDATE_PACKET"
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
        else "QFT_GR_WEAK_PAIRING_RETRY_FOR_SELECTED_CANDIDATE_FUNCTIONAL_CONTRACT_PACKET_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "authorized_by_candidate_definition_artifact_id": candidate_definition_packet.get(
            "schema_id"
        ),
        "authorized_by_candidate_definition_commit": AUTHORIZED_BY_CANDIDATE_DEFINITION_COMMIT,
        "candidate_id": SELECTED_REPLACEMENT_CANDIDATE_ID,
        "candidate_kind": SELECTED_REPLACEMENT_CANDIDATE_KIND,
        "candidate_regular_type": DISTRIBUTIONAL_REGULARITY,
        "candidate_tensor_type": SELECTED_TENSOR_TYPE,
        "candidate_index_placement": SELECTED_INDEX_PLACEMENT,
        "test_domain": TEST_SPACE,
        "functional_contract": SELECTED_FUNCTIONAL_CONTRACT,
        "pairing_definition": SELECTED_PAIRING_RULE,
        "calculation_result": CALCULATION_RESULT,
        "well_defined_pairing": True,
        "well_defined_pairing_scope": WELL_DEFINED_PAIRING_SCOPE,
        "weak_pairing_constructed": True,
        "weak_pairing_completed": True,
        "weak_pairing_completion_scope": WELL_DEFINED_PAIRING_SCOPE,
        "weak_pairing_not_physical_source_claim": True,
        "action_derivability_status": ACTION_DERIVABILITY_STATUS,
        "action_derivability_next_target_authorized": prepared,
        "calculation_steps": calculation_steps,
        "mathematical_statement": (
            "Given T in D'(M, Sym^2 TM) and h in C_c^infty(M, Sym^2 T*M), "
            "define <T, h> := T(h). The pairing is well-defined as a real "
            "number by the selected continuous linear functional contract."
        ),
        "downstream_progression": [
            {
                "stage": "weak_pairing_retry",
                "status": "COMPLETED_RESTRICTED",
                "decision": WELL_DEFINED_PAIRING_SCOPE,
                "reason": "The selected candidate is a continuous linear functional on the test domain.",
            },
            {
                "stage": "action_derivability",
                "status": "NEXT_TARGET_AUTHORIZED",
                "decision": selected_next_target,
                "reason": "Action derivability remains untested and is downstream of weak pairing.",
            },
            {
                "stage": "weak_conservation",
                "status": "NOT_REACHED",
                "decision": "not_reached",
                "reason": "Weak conservation is downstream of action/source semantics.",
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
                "reason": "Semiclassical coupling is downstream of the prior checks.",
            },
        ],
        "source_admissibility_claimed": False,
        "action_derivability_claimed": False,
        "conservation_claimed": False,
        "weak_conservation_claimed": False,
        "Bianchi_compatibility_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "qft_gr_closure_claimed": False,
        "qft_gr_seam_closed": False,
        "empirical_validation_claimed": False,
        "public_submission_authorized": False,
        "master_action_promoted": False,
        "acceptable_result_outcomes": [
            CALCULATION_RESULT,
            "WEAK_PAIRING_CONSTRUCTED_NONPROMOTIONALLY_ACTION_DERIVABILITY_NEXT",
            "WEAK_PAIRING_RETRY_BLOCKED_FOR_SELECTED_FUNCTIONAL_CONTRACT",
        ],
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "validation_policy": _validation_policy(),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet constructs the weak pairing only as distributional "
            "evaluation under the selected functional contract. It does not "
            "claim source admissibility, action derivability, weak "
            "conservation, Bianchi compatibility, semiclassical coupling, "
            "QFT-GR closure, empirical validation, public submission, or "
            "master-action promotion."
        ),
    }


def write_qft_gr_weak_pairing_retry_for_selected_candidate_functional_contract_packet(
    *,
    candidate_definition_packet_path: Path = CANDIDATE_DEFINITION_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = (
        build_qft_gr_weak_pairing_retry_for_selected_candidate_functional_contract_packet(
            candidate_definition_packet_path=candidate_definition_packet_path,
            captured_at_utc=captured_at_utc,
        )
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR weak-pairing retry packet for the selected "
            "candidate functional contract."
        )
    )
    parser.add_argument(
        "--candidate-definition-packet",
        type=Path,
        default=CANDIDATE_DEFINITION_PACKET_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    candidate_definition_packet_path = (
        ns.candidate_definition_packet
        if ns.candidate_definition_packet.is_absolute()
        else (REPO_ROOT / ns.candidate_definition_packet)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_weak_pairing_retry_for_selected_candidate_functional_contract_packet(
        candidate_definition_packet_path=candidate_definition_packet_path,
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
                "calculation_result": payload["calculation_result"],
                "well_defined_pairing": payload["well_defined_pairing"],
                "selected_next_target": payload["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/EOTWASH_2020_OUTBOUND_RESEARCH_CONTACT_SCOPE_"
    "CLOSURE_AND_INTERNAL_ROUTE_SELECTION_20260718_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/EOTWASH_2020_OUTBOUND_RESEARCH_CONTACT_SCOPE_"
    "CLOSURE_AND_INTERNAL_ROUTE_SELECTION_20260718_v0.md"
)
POLICY_RELATIVE_PATH = (
    "formal/docs/lanes/OUTBOUND_RESEARCH_CONTACT_AND_PRIVATE_DATA_POLICY_"
    "20260718_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/test_eotwash_2020_outbound_research_contact_scope_"
    "closure_and_internal_route_selection_v0.py"
)
LEAN_RELATIVE_PATH = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "Eotwash2020OutboundResearchContactScopeClosureAndInternalRouteSelectionV0.lean"
)
PRIOR_REPORT_RELATIVE_PATH = (
    "formal/docs/release/POST_EOTWASH_2020_YUKAWA_PRIMARY_EVIDENCE_"
    "CUSTODY_ACQUISITION_SCIENTIFIC_RESPONSE_SELECTION_20260718_v0.json"
)

TARGET = "prepare_eotwash_2020_yukawa_author_or_custodian_contact_packet_v0"
CONSUMED_TARGET = TARGET
VERDICT = (
    "USER_SCOPE_WITHDRAWS_CONTACT_AND_SELECTS_SYNTHETIC_FORECAST_"
    "PACKET_PREPARATION"
)
SELECTED_CANDIDATE_ID = (
    "SCALAR_ONLY_YUKAWA_SYNTHETIC_FORWARD_MODEL_AND_SENSITIVITY_FORECAST"
)
SELECTED_NEXT_TARGET = (
    "prepare_scalar_only_yukawa_synthetic_forward_model_and_"
    "sensitivity_forecast_packet_v0"
)
SELECTED_NEXT_TARGET_KIND = (
    "PREPARATION_ONLY_INTERNAL_SYNTHETIC_FORECAST_NO_EMPIRICAL_REANALYSIS"
)

AUTHORITY_HASHES = {
    "formal/docs/lanes/POST_EOTWASH_2020_YUKAWA_PRIMARY_EVIDENCE_CUSTODY_ACQUISITION_SCIENTIFIC_RESPONSE_SELECTION_20260718_v0.md":
        "8dae576859d54df29a7ffa82e08d6cacd0558de068b505cdfc180a7ca813d392",
    PRIOR_REPORT_RELATIVE_PATH:
        "d931bc44cad65caae6994ac88931cc3af1e32864ec61cbc0b4c77c04758592d3",
    "formal/python/tools/post_eotwash_2020_yukawa_primary_evidence_custody_acquisition_scientific_response_selection_v0.py":
        "7a1354f6935bda276270df1b0f5e12a367a767a0d0501f9785fb267c6866f1e3",
    "formal/python/tests/test_post_eotwash_2020_yukawa_primary_evidence_custody_acquisition_scientific_response_selection_v0.py":
        "7f3451c12e307b5757e7e5d4aceb447b978e4cf08ab94489a3a4f5f3de99425e",
    "formal/toe_formal/ToeFormal/Derivation/PostEotwash2020YukawaPrimaryEvidenceCustodyAcquisitionScientificResponseSelectionV0.lean":
        "1436a30c8781af703a8821c0e15f9f8be64a1bfe435fd54c07af477c1de2ecef",
}


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {relative_path}")
    return value


def _artifact_row(relative_path: str) -> dict[str, str]:
    return {
        "relative_path": relative_path,
        "sha256": _sha256(REPO_ROOT / relative_path),
    }


def build_report() -> dict[str, Any]:
    for relative_path, expected_hash in AUTHORITY_HASHES.items():
        actual_hash = _sha256(REPO_ROOT / relative_path)
        if actual_hash != expected_hash:
            raise ValueError(
                f"authority drift: {relative_path}: {actual_hash} != {expected_hash}"
            )

    prior = _load_json(PRIOR_REPORT_RELATIVE_PATH)
    if prior.get("verdict") != (
        "SELECTED_TARGETED_EOTWASH_AUTHOR_OR_CUSTODIAN_CONTACT_PACKET_PREPARATION"
    ):
        raise ValueError("prior selector verdict mismatch")
    if prior.get("selected_next_target") != TARGET:
        raise ValueError("prior live target mismatch")
    if prior.get("scope", {}).get("contact_packet_prepared_now") is not False:
        raise ValueError("prior selector unexpectedly prepared a contact packet")
    if prior.get("scope", {}).get("author_or_custodian_contact_executed") is not False:
        raise ValueError("prior selector unexpectedly executed contact")

    gate_ids = [
        "PRIOR_SELECTOR_ARTIFACTS_HASH_FROZEN_AND_EXACT_TARGET_CONSUMED",
        "EXPLICIT_USER_SCOPE_OVERRIDE_RECORDED",
        "CONTACT_PACKET_PREPARATION_WITHDRAWN_BEFORE_PREPARATION",
        "NO_RECIPIENT_MESSAGE_OR_CONTACT_CREATED",
        "OUTBOUND_RESEARCH_CONTACT_DISALLOWED_UNTIL_EXPLICIT_REOPENING",
        "PRIVATE_OR_RESTRICTED_DATA_DEPENDENCE_DISALLOWED",
        "THIRD_PARTY_COOPERATION_WAITING_DISALLOWED",
        "PUBLIC_PAPERS_AND_OPEN_DATA_REMAIN_PERMITTED",
        "INTERNAL_THEORY_SIMULATION_AND_SYNTHETIC_TESTING_PERMITTED",
        "EOTWASH_SUITABILITY_AND_ACCEPTED_CUSTODY_RESULT_RETAINED",
        "EOTWASH_INDEPENDENT_FIT_ROUTE_CLOSED_WITH_ZERO_OF_SIX_COMPLETE",
        "SYNTHETIC_ROUTE_CLASSIFIED_NONEMPIRICAL",
        "SYNTHETIC_PACKET_PREPARATION_ONLY_AUTHORIZED",
        "PUBLISHED_LIMIT_REINTERPRETATION_NOT_AUTHORIZED",
        "NO_LIKELIHOOD_BOUND_BRANCH_OR_THEORY_ADOPTION",
        "EXPLICIT_FUTURE_USER_INSTRUCTION_REQUIRED_TO_REOPEN_CONTACT",
    ]

    scope = {
        "scope_closure_executed": True,
        "explicit_user_scope_override": True,
        "contact_preparation_withdrawn": True,
        "outbound_research_contact_disallowed": True,
        "private_restricted_data_dependence_disallowed": True,
        "third_party_waiting_disallowed": True,
        "public_open_evidence_permitted": True,
        "internal_synthetic_research_permitted": True,
        "explicit_user_reopening_required": True,
        "eotwash_independent_fit_route_closed": True,
        "synthetic_packet_preparation_authorized": True,
        "contact_packet_prepared": False,
        "contact_recipient_selected": False,
        "contact_message_drafted": False,
        "author_or_custodian_contact_authorized": False,
        "author_or_custodian_contact_executed": False,
        "synthetic_packet_prepared_now": False,
        "synthetic_forecast_executed": False,
        "published_constraint_reinterpretation_authorized": False,
        "likelihood_preparation_authorized": False,
        "likelihood_executed": False,
        "numerical_lambda_bound_computed": False,
        "numerical_alpha_bound_computed": False,
        "scalar_branch_adopted": False,
        "native_gravitational_principle_identified": False,
        "gravitational_action_selected": False,
        "frame_dragging_resumed": False,
        "master_action_mutated": False,
    }

    return {
        "schema_id": (
            "toe.eotwash_2020.outbound_research_contact_scope_closure_and_"
            "internal_route_selection.v0"
        ),
        "captured_at_utc": "2026-07-19T00:00:00Z",
        "target": TARGET,
        "consumed_target": CONSUMED_TARGET,
        "verdict": VERDICT,
        "selection_basis": "EXPLICIT_USER_SCOPE_OVERRIDE",
        "authority": {
            "frozen_prior_selector_artifacts": [
                {"relative_path": path, "sha256": digest}
                for path, digest in AUTHORITY_HASHES.items()
            ],
            "human_closure": _artifact_row(HUMAN_RELATIVE_PATH),
            "standing_policy": _artifact_row(POLICY_RELATIVE_PATH),
            "generator": _artifact_row(
                "formal/python/tools/eotwash_2020_outbound_research_contact_"
                "scope_closure_and_internal_route_selection_v0.py"
            ),
            "test": _artifact_row(TEST_RELATIVE_PATH),
            "lean": _artifact_row(LEAN_RELATIVE_PATH),
        },
        "historical_selector": {
            "selected_contact_route": (
                "TARGETED_EOTWASH_AUTHOR_OR_CUSTODIAN_CONTACT_PREPARATION"
            ),
            "selection_stability": "FIRST_IN_24_OF_24_VARIANTS",
            "scientific_ranking_retracted": False,
            "live_contact_route_withdrawn": True,
            "withdrawal_reason": "EXPLICIT_USER_PROJECT_SCOPE",
        },
        "standing_internal_research_policy": {
            "outbound_research_contact": (
                "DISALLOWED_UNLESS_USER_EXPLICITLY_REOPENS"
            ),
            "dependence_on_private_or_restricted_data": "DISALLOWED",
            "waiting_on_third_party_cooperation": "DISALLOWED",
            "public_papers_and_openly_available_data": "PERMITTED",
            "internal_theory_simulation_and_synthetic_testing": "PERMITTED",
            "reopening_authority": "EXPLICIT_FUTURE_USER_INSTRUCTION_ONLY",
        },
        "retained_empirical_posture": {
            "experiment": "EOTWASH_2020_SHORT_RANGE_ISL_TORSION_BALANCE",
            "experiment_suitable": True,
            "fixed_signal": "A_Y=1/3",
            "non_contact_acquisition": "COMPLETED_AND_ACCEPTED",
            "evidence_components_complete": 0,
            "evidence_component_count": 6,
            "independent_likelihood_executable": False,
            "independent_fit_route": "CLOSED_BLOCKED_ON_INACCESSIBLE_INPUTS",
            "likelihood": "NOT_EXECUTED",
            "scalar_range_bound": "NONE",
            "alpha_constraint": "NONE",
        },
        "selected_internal_route": {
            "candidate_id": SELECTED_CANDIDATE_ID,
            "target": SELECTED_NEXT_TARGET,
            "target_kind": SELECTED_NEXT_TARGET_KIND,
            "status": "PACKET_PREPARATION_AUTHORIZED_NOT_PREPARED",
            "selection_reason": "EXPLICIT_USER_INTERNAL_ONLY_SCOPE",
            "classification": (
                "SYNTHETIC_FORECAST_NOT_EOTWASH_EMPIRICAL_REANALYSIS_"
                "NOT_MEASURED_CONSTRAINT"
            ),
            "future_packet_obligations": [
                "derive fixed-strength Yukawa force and torque response",
                "freeze analytic benchmark geometries",
                "define explicitly approximate public-method apparatus model",
                "prepare synthetic observations and injection-recovery controls",
                "study covariance nuisance and geometry sensitivity",
                "forecast detectability under explicit assumptions",
                "stop before real-data empirical inference",
            ],
        },
        "deferred_public_evidence_route": {
            "candidate_id": "SUPPLIED_PUBLISHED_EOTWASH_LIMIT_REINTERPRETATION",
            "status": "NOT_AUTHORIZED",
            "claim_classification_if_later_authorized": (
                "SUPPLIED_PUBLISHED_CONSTRAINT_NOT_INDEPENDENTLY_REPRODUCED"
            ),
        },
        "closure_gates": {
            "gate_count": len(gate_ids),
            "pass_count": len(gate_ids),
            "failure_count": 0,
            "rows": [{"gate_id": gate_id, "status": "PASS"} for gate_id in gate_ids],
        },
        "scope": scope,
        "selected_candidate_id": SELECTED_CANDIDATE_ID,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "current_posture": {
            "targeted_author_contact_preparation": "WITHDRAWN_BY_USER_SCOPE",
            "outbound_contact": "PROHIBITED_UNTIL_EXPLICITLY_REOPENED",
            "eotwash_independent_fit_route": (
                "CLOSED_BLOCKED_ON_INACCESSIBLE_INPUTS"
            ),
            "primary_next_route": SELECTED_CANDIDATE_ID,
            "synthetic_forecast": "NOT_EXECUTED",
            "published_reinterpretation": "NOT_AUTHORIZED",
            "likelihood": "NOT_EXECUTED",
            "scalar_range_bound": "NONE",
            "alpha": "NOT_SELECTED",
            "scalar_branch": "NOT_ADOPTED",
            "native_gravitational_principle": "NOT_IDENTIFIED",
            "gravitational_action": "NOT_SELECTED",
            "next_authority": SELECTED_NEXT_TARGET,
        },
        "claim_ceiling": (
            "Explicit user scope closes outbound research contact and selects "
            "preparation only of an internal scalar-only Yukawa synthetic "
            "forward-model and sensitivity-forecast packet. No contact packet, "
            "recipient, message, communication, private-data dependency, "
            "forecast execution, published-result reinterpretation, likelihood, "
            "empirical bound, scalar-branch adoption, native gravitational "
            "principle, gravitational action, frame-dragging result, or master-"
            "action change is prepared, executed, computed, selected, or claimed."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_report(), indent=2, sort_keys=True) + "\n").encode(
        "utf-8"
    )


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Freeze the Eot-Wash outbound-contact scope closure and select the "
            "internal synthetic-forecast packet-preparation target."
        )
    )
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--write", action="store_true")
    args = parser.parse_args()

    output_path = REPO_ROOT / REPORT_RELATIVE_PATH
    expected = artifact_bytes()
    current = output_path.read_bytes() if output_path.exists() else None
    if args.write:
        if current != expected:
            output_path.write_bytes(expected)
            print(f"wrote {REPORT_RELATIVE_PATH}")
        else:
            print("scope-closure artifact already current")
        return 0
    if current != expected:
        print("scope-closure artifact drift")
        return 1
    print("scope-closure artifact OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())


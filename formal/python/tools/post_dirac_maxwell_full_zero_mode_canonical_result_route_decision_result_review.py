from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
import unicodedata
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
PACKET_RELATIVE_PATH = "formal/output/POST-DIRAC-MAXWELL-FULL-ZERO-MODE-CANONICAL-RESULT-ROUTE-DECISION-PACKET-v0.json"
MANIFEST_RELATIVE_PATH = "formal/output/POST-DIRAC-MAXWELL-FULL-ZERO-MODE-CANONICAL-RESULT-ROUTE-DECISION-MANIFEST-v0.json"
PREPARATION_REPORT_RELATIVE_PATH = "formal/docs/release/POST_DIRAC_MAXWELL_FULL_ZERO_MODE_CANONICAL_RESULT_ROUTE_DECISION_PACKET_20260713_v0.json"
PREPARATION_GENERATOR_RELATIVE_PATH = "formal/python/tools/post_dirac_maxwell_full_zero_mode_canonical_result_route_decision.py"
REVIEW_REPORT_RELATIVE_PATH = "formal/docs/release/POST_DIRAC_MAXWELL_FULL_ZERO_MODE_CANONICAL_RESULT_ROUTE_DECISION_PACKET_RESULT_REVIEW_20260713_v0.json"
PACKET_PATH = REPO_ROOT / PACKET_RELATIVE_PATH
REVIEW_REPORT_PATH = REPO_ROOT / REVIEW_REPORT_RELATIVE_PATH

CAPTURED_AT_UTC = "2026-07-13T00:00:00Z"
REVIEW_TARGET = "review_post_dirac_maxwell_full_zero_mode_canonical_result_route_decision_packet_v0_result"
ACCEPTED_TARGET = "prepare_dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_packet_v0"
BLOCKED_TARGET = "prepare_post_dirac_maxwell_full_zero_mode_canonical_result_route_decision_packet_v1"
REVIEW_SCHEMA_ID = "POST_DIRAC_MAXWELL_FULL_ZERO_MODE_CANONICAL_RESULT_ROUTE_DECISION_PACKET_RESULT_REVIEW_20260713_v0"
PREPARATION_COMMIT = "519bdff5a72f7310e51a11a56d77c3a76dd0a435"
PREPARATION_PARENT = "1824e2db6e79a39ef21453d8bb080ebbb54b99ae"
EXPECTED_HASHES = {
    PREPARATION_GENERATOR_RELATIVE_PATH: "314a4bb0ee644dd81266a16e08f2e91f9ba2c9479f93bddb86f460c9a27c570f",
    PACKET_RELATIVE_PATH: "b79b888bd5854caf630a97c4edca6c8ead00ab4fd8d8a9dcda49b8ac2323a425",
    MANIFEST_RELATIVE_PATH: "48a2d25bcf08b04f60e198d19d4efd89aa789ec10e933e643ea75eeda89ab550",
    PREPARATION_REPORT_RELATIVE_PATH: "e556823c55a50ae7561c873366e2c3475fb7be6c72dc82020a7061f733395633",
}
PROMPT_RELATIVE_PATH = "Prompt.txt"
PROMPT_SHA256 = "2bc6996ea28e96c50e688ed3d30ee24808af411a244eb594aad89ff80fda8433"

CANONICAL_REVIEW_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_CANONICAL_SIMULATION_RESULT_REVIEW_20260713_v0.json"
ANALYTIC_REVIEW_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_REDUCTION_WITH_TRANSVERSE_FIELDS_PACKET_RESULT_REVIEW_20260713_v0.json"
GUARDRAIL_REVIEW_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DISCRETE_NUMERICAL_GUARDRAIL_PACKET_RESULT_REVIEW_20260713_v0.json"
SCALAR_ROBUSTNESS_REVIEW_RELATIVE_PATH = "formal/docs/release/SCALAR_STRESS_ENERGY_COVARIANT_DIVERGENCE_IDENTITY_MULTI_BACKGROUND_ROBUSTNESS_CALCULATION_RESULT_REVIEW_20260710_v0.json"
EINSTEIN_SCALAR_ROUTE_REVIEW_RELATIVE_PATH = "formal/docs/release/QFT_GR_CLASSICAL_EINSTEIN_SCALAR_COUPLING_ROUTE_PACKET_RESULT_REVIEW_20260618_v0.json"
FIRST_UNIT_SELECTOR_REVIEW_RELATIVE_PATH = "formal/docs/release/PILLAR_SEAM_UNIT_MAPPING_LEDGER_FIRST_UNIT_SELECTOR_PACKET_RESULT_REVIEW_20260713_v0.json"
SOURCE_HASHES = {
    CANONICAL_REVIEW_RELATIVE_PATH: "9b518024fa8a13b73d19e01576375484d5acc24e4f5896adaa612b46f500e040",
    ANALYTIC_REVIEW_RELATIVE_PATH: "e4a830678d863319d5509bf43e332a778708b7b82bd6db5903be5a389fef34de",
    GUARDRAIL_REVIEW_RELATIVE_PATH: "b881d23e9bd201b09bb023a1e897306afff681bd57ccb224a9c6baf562be57b6",
    SCALAR_ROBUSTNESS_REVIEW_RELATIVE_PATH: "cca24f7a9d72d035b974a781213235dc7e8f0685a63bb5189ee465b1c3aa17a0",
    EINSTEIN_SCALAR_ROUTE_REVIEW_RELATIVE_PATH: "0d9eb65ddb9fcf2e6dea8bd4feab58b51fb8db4dd002181bd4004df6d5395509",
    FIRST_UNIT_SELECTOR_REVIEW_RELATIVE_PATH: "e84d7a00a29a21dae59a8d3fb26f56a6a97cf3b6021766a6b176fde81a3d610d",
}
WEIGHT_MAP = {
    "current_result_information_gain": 5,
    "accepted_infrastructure_reuse": 5,
    "falsifiable_discrimination": 5,
    "analytic_readiness": 4,
    "numerical_readiness": 4,
    "bounded_scope": 3,
    "seam_method_leverage": 3,
    "project_portfolio_value": 2,
}
INDEPENDENT_SCORES = {
    "DESCENDANT_NECESSITY_ROBUSTNESS": [2, 2, 2, 1, 2, 2, 2, 1],
    "DIMENSIONAL_ASCENT_2P1": [2, 1, 2, 0, 0, 1, 2, 1],
    "FIXED_CURVED_BACKGROUND_EXTENSION": [2, 1, 2, 0, 0, 1, 2, 1],
    "DYNAMIC_EINSTEIN_SCALAR": [1, 0, 2, 1, 0, 0, 2, 2],
    "NEXT_UNIT_PILLAR_TARGET": [1, 0, 1, 2, 0, 2, 2, 2],
}
THRESHOLDS = [40, 42, 44, 46, 48]
EXPECTED_PROPOSITIONS = {
    "P_CANONICAL_RESULT_ACCEPTED": (CANONICAL_REVIEW_RELATIVE_PATH, "/verdict", "ACCEPT_BOUNDED_SCIENTIFIC_RESULT"),
    "P_CANONICAL_E_REPRO_SCOPE": (CANONICAL_REVIEW_RELATIVE_PATH, "/accepted_claim_label", "E-REPRO"),
    "P_TRANSVERSE_SIGNAL_ACTIVE": (CANONICAL_REVIEW_RELATIVE_PATH, "/result_metrics/transverse_signal", 6.826809919994493e-08),
    "P_EXCHANGE_SIGNAL_SEPARATED": (CANONICAL_REVIEW_RELATIVE_PATH, "/result_metrics/exchange_ratio", 352.6967159703898),
    "P_COMPLETE_MATRIX_REPRODUCED": (CANONICAL_REVIEW_RELATIVE_PATH, "/independent_reproduction/all_fifty_records_reproduced", True),
    "P_NONPROMOTION_BOUNDARY": (CANONICAL_REVIEW_RELATIVE_PATH, "/authority_rotation/pillar_completion_authorized", False),
    "P_ANALYTIC_DESCENDANT_REDUCTION_ACCEPTED": (ANALYTIC_REVIEW_RELATIVE_PATH, "/authority_rotation/full_zero_mode_analytic_repair_accepted", True),
    "P_NUMERICAL_GUARDRAIL_ACCEPTED": (GUARDRAIL_REVIEW_RELATIVE_PATH, "/authority_rotation/numerical_guardrail_accepted", True),
    "P_SCALAR_FIXED_BACKGROUND_ROBUSTNESS_ACCEPTED": (SCALAR_ROBUSTNESS_REVIEW_RELATIVE_PATH, "/accepted_e_repro", True),
    "P_EINSTEIN_SCALAR_ROUTE_ONLY": (EINSTEIN_SCALAR_ROUTE_REVIEW_RELATIVE_PATH, "/provisional_classical_sandbox_route_only", True),
    "P_EINSTEIN_SCALAR_NOT_SOLVED": (EINSTEIN_SCALAR_ROUTE_REVIEW_RELATIVE_PATH, "/coupled_einstein_scalar_system_solved", False),
    "P_FIRST_UNIT_SELECTOR_ACCEPTED": (FIRST_UNIT_SELECTOR_REVIEW_RELATIVE_PATH, "/accepted", True),
}


def _normalize(value: Any) -> Any:
    if isinstance(value, str):
        return unicodedata.normalize("NFC", value)
    if isinstance(value, list):
        return [_normalize(item) for item in value]
    if isinstance(value, dict):
        return {_normalize(str(key)): _normalize(item) for key, item in value.items()}
    return value


def canonical_json_bytes(payload: Any) -> bytes:
    return (json.dumps(_normalize(payload), allow_nan=False, ensure_ascii=False, indent=2, sort_keys=True) + "\n").encode("utf-8")


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha256_path(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected object: {path}")
    return value


def _json_pointer(document: Any, pointer: str) -> Any:
    current = document
    for raw_part in pointer[1:].split("/"):
        part = raw_part.replace("~1", "/").replace("~0", "~")
        current = current[int(part)] if isinstance(current, list) else current[part]
    return current


def custody() -> dict[str, Any]:
    commit = subprocess.run(["git", "rev-parse", PREPARATION_COMMIT], cwd=REPO_ROOT, capture_output=True, text=True, check=False).stdout.strip()
    parent = subprocess.run(["git", "rev-parse", f"{PREPARATION_COMMIT}^"], cwd=REPO_ROOT, capture_output=True, text=True, check=False).stdout.strip()
    working = {path: sha256_path(REPO_ROOT / path) for path in EXPECTED_HASHES}
    committed: dict[str, str] = {}
    for path in EXPECTED_HASHES:
        result = subprocess.run(["git", "show", f"{PREPARATION_COMMIT}:{path}"], cwd=REPO_ROOT, capture_output=True, check=False)
        committed[path] = sha256_bytes(result.stdout) if result.returncode == 0 else "MISSING"
    passed = commit == PREPARATION_COMMIT and parent == PREPARATION_PARENT and working == EXPECTED_HASHES and committed == EXPECTED_HASHES
    return {
        "commit": commit,
        "parent": parent,
        "working_hashes": working,
        "commit_hashes": committed,
        "expected_hashes": EXPECTED_HASHES,
        "passed": passed,
    }


def independent_evidence_audit(packet: dict[str, Any]) -> dict[str, Any]:
    sources = {path: load_json(REPO_ROOT / path) for path in SOURCE_HASHES}
    source_hashes_match = all(sha256_path(REPO_ROOT / path) == digest for path, digest in SOURCE_HASHES.items())
    records = {item["proposition_id"]: item for item in packet["evidence_records"]}
    checks = []
    for proposition_id, (source_path, pointer, expected_value) in EXPECTED_PROPOSITIONS.items():
        record = records.get(proposition_id, {})
        observed = _json_pointer(sources[source_path], pointer)
        passed = (
            record.get("source_path") == source_path
            and record.get("source_hash") == SOURCE_HASHES[source_path]
            and record.get("source_locator", {}).get("pointer") == pointer
            and record.get("evidence_role") == "REPOSITORY_STATE_EVIDENCE"
            and record.get("route_support_eligible") is True
            and observed == expected_value
            and record.get("expected_source_value") == expected_value
        )
        checks.append({"proposition_id": proposition_id, "source_path": source_path, "pointer": pointer, "observed_value": observed, "passed": passed})
    bound_ids = {
        proposition_id
        for candidate in packet["scored_candidates"]
        for row in candidate["criterion_scores"]
        for proposition_id in row["exact_supporting_proposition_ids"]
    }
    return {
        "source_hashes_match": source_hashes_match,
        "proposition_count": len(checks),
        "proposition_checks": checks,
        "all_propositions_match": all(item["passed"] for item in checks),
        "all_score_support_ids_are_known": bound_ids.issubset(EXPECTED_PROPOSITIONS),
    }


def independent_scoring(packet: dict[str, Any]) -> dict[str, Any]:
    ordered_weights = list(WEIGHT_MAP.values())
    totals = {
        candidate: sum(weight * score for weight, score in zip(ordered_weights, scores, strict=True))
        for candidate, scores in INDEPENDENT_SCORES.items()
    }
    packet_scores = {
        item["candidate_id"]: {
            "scores": [row["score"] for row in item["criterion_scores"]],
            "total": item["weighted_total"],
        }
        for item in packet["scored_candidates"]
    }
    score_vectors_match = all(packet_scores.get(candidate, {}).get("scores") == scores for candidate, scores in INDEPENDENT_SCORES.items())
    totals_match = all(packet_scores.get(candidate, {}).get("total") == total for candidate, total in totals.items())
    selected_by_threshold: dict[str, str | None] = {}
    for threshold in THRESHOLDS:
        eligible = [
            candidate
            for candidate, total in totals.items()
            if total >= threshold
            and INDEPENDENT_SCORES[candidate][0] >= 1
            and INDEPENDENT_SCORES[candidate][2] >= 1
            and INDEPENDENT_SCORES[candidate][5] >= 1
        ]
        selected_by_threshold[str(threshold)] = max(eligible, key=lambda candidate: totals[candidate]) if eligible else None
    return {
        "criterion_weights": WEIGHT_MAP,
        "score_vectors": INDEPENDENT_SCORES,
        "weighted_totals": totals,
        "packet_score_vectors_match": score_vectors_match,
        "packet_totals_match": totals_match,
        "selected_by_threshold": selected_by_threshold,
        "stable_selection": set(selected_by_threshold.values()) == {"DESCENDANT_NECESSITY_ROBUSTNESS"},
        "canonical_selected_candidate": selected_by_threshold["44"],
    }


DECISION_IDS = [
    "immutable_post_result_route_decision_preparation_is_bound",
    "accepted_canonical_E_REPRO_result_is_the_exact_live_authority",
    "all_six_planning_sources_and_twelve_propositions_are_independently_bound",
    "exact_five_candidate_identity_is_reproduced",
    "all_eight_criterion_weights_are_recomputed",
    "all_forty_scores_are_recomputed",
    "all_five_weighted_totals_are_recomputed",
    "every_score_support_id_resolves_to_an_eligible_proposition",
    "user_recommendation_and_external_context_did_not_enter_scoring",
    "descendant_necessity_robustness_is_independent_highest_score",
    "selection_is_stable_from_40_through_48",
    "selected_route_axes_comparators_observables_and_outcomes_are_bounded",
    "invalid_truncation_is_comparator_only_not_a_rival_model",
    "ten_mutation_controls_and_no_oracle_boundary_hold",
    "completed_tranches_and_canonical_result_are_not_reopened",
    "only_descendant_necessity_robustness_preparation_is_authorized",
    "pillar_seam_empirical_C_k_CCFT_master_action_and_repository_nonpromotions_hold",
    "Prompt_is_preserved",
]


def build_review_report() -> dict[str, Any]:
    packet = load_json(PACKET_PATH)
    custody_result = custody()
    evidence = independent_evidence_audit(packet)
    scoring = independent_scoring(packet)
    candidates = [item["candidate_id"] for item in packet["scored_candidates"]]
    selected_route = packet["selected_route_definition"]
    controls = packet["mutation_controls"]
    boundary = packet["boundary"]
    decisions = {
        "immutable_post_result_route_decision_preparation_is_bound": custody_result["passed"],
        "accepted_canonical_E_REPRO_result_is_the_exact_live_authority": evidence["source_hashes_match"] and packet["target"] == "prepare_post_dirac_maxwell_full_zero_mode_canonical_result_route_decision_packet_v0",
        "all_six_planning_sources_and_twelve_propositions_are_independently_bound": evidence["source_hashes_match"] and evidence["proposition_count"] == 12 and evidence["all_propositions_match"],
        "exact_five_candidate_identity_is_reproduced": candidates == list(INDEPENDENT_SCORES),
        "all_eight_criterion_weights_are_recomputed": packet["criterion_weights"] == WEIGHT_MAP,
        "all_forty_scores_are_recomputed": scoring["packet_score_vectors_match"] and sum(len(item["criterion_scores"]) for item in packet["scored_candidates"]) == 40,
        "all_five_weighted_totals_are_recomputed": scoring["packet_totals_match"],
        "every_score_support_id_resolves_to_an_eligible_proposition": evidence["all_score_support_ids_are_known"],
        "user_recommendation_and_external_context_did_not_enter_scoring": packet["user_recommendation"]["used_as_score_input"] is False and packet["external_literature_used_as_score_input"] is False,
        "descendant_necessity_robustness_is_independent_highest_score": scoring["canonical_selected_candidate"] == "DESCENDANT_NECESSITY_ROBUSTNESS" and scoring["weighted_totals"]["DESCENDANT_NECESSITY_ROBUSTNESS"] == 56,
        "selection_is_stable_from_40_through_48": scoring["stable_selection"],
        "selected_route_axes_comparators_observables_and_outcomes_are_bounded": len(selected_route["bounded_parameter_axes"]) == 5 and len(selected_route["required_comparators"]) == 2 and len(selected_route["required_observables"]) == 4 and len(selected_route["required_outcome_classes"]) == 5,
        "invalid_truncation_is_comparator_only_not_a_rival_model": selected_route["invalid_comparator_is_not_a_rival_physical_model"] is True,
        "ten_mutation_controls_and_no_oracle_boundary_hold": len(controls) == 10 and all(item["passed"] for item in controls) and "expected_winner" not in packet,
        "completed_tranches_and_canonical_result_are_not_reopened": packet["completed_tranches_reopened"] is False and packet["canonical_rerun_authorized"] is False and boundary["canonical_result_recalibrated"] is False,
        "only_descendant_necessity_robustness_preparation_is_authorized": packet["post_acceptance_target"] == ACCEPTED_TARGET and boundary["only_route_specific_preparation_authorized_after_review"] is True and boundary["robustness_execution_authorized"] is False and boundary["new_parameter_values_frozen"] is False,
        "pillar_seam_empirical_C_k_CCFT_master_action_and_repository_nonpromotions_hold": boundary["pillar_completion_claimed"] is False and boundary["seam_admissibility_or_closure_claimed"] is False and boundary["empirical_adequacy_claimed"] is False and boundary["new_physics_claimed"] is False and boundary["C_k_audit_only"] is True and boundary["CCFT_resumed"] is False and boundary["master_action_promoted"] is False and boundary["repository_wide_green_claimed"] is False,
        "Prompt_is_preserved": sha256_path(REPO_ROOT / PROMPT_RELATIVE_PATH) == PROMPT_SHA256,
    }
    ordered = [{"decision_id": item, "passed": decisions[item]} for item in DECISION_IDS]
    failed = [item["decision_id"] for item in ordered if not item["passed"]]
    accepted = not failed
    return {
        "schema_id": REVIEW_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "review_target": REVIEW_TARGET,
        "accepted": accepted,
        "verdict": "ACCEPT_ROUTE_DECISION" if accepted else "B-BLOCKED",
        "selected_candidate_id": "DESCENDANT_NECESSITY_ROBUSTNESS" if accepted else None,
        "selected_candidate_label": "descendant necessity and parameter robustness" if accepted else None,
        "selected_next_target": ACCEPTED_TARGET if accepted else BLOCKED_TARGET,
        "selected_next_target_kind": ACCEPTED_TARGET if accepted else BLOCKED_TARGET,
        "decision_count": len(DECISION_IDS),
        "passed_decision_count": len(DECISION_IDS) - len(failed),
        "failed_decision_ids": failed,
        "decisions": ordered,
        "preparation_custody": custody_result,
        "independent_evidence_audit": evidence,
        "independent_scoring": scoring,
        "authority_rotation": {
            "post_result_route_decision_accepted": accepted,
            "descendant_necessity_robustness_preparation_authorized": accepted,
            "robustness_design_accepted": False,
            "robustness_parameter_family_frozen": False,
            "robustness_execution_authorized": False,
            "canonical_result_reopened": False,
            "pillar_completion_authorized": False,
            "seam_admissibility_or_closure_authorized": False,
            "empirical_adequacy_authorized": False,
            "C_k_dynamics_authorized": False,
            "CCFT_validation_authorized": False,
            "master_action_promotion_authorized": False,
        },
        "claim": "Independent proposition and score reconstruction selects a bounded descendant-necessity and parameter-robustness preparation; no robustness execution or broader authority promotion is authorized." if accepted else "The post-result route decision is blocked.",
        "nonclaims": [
            "no canonical result recalibration or rerun",
            "no robustness parameter family frozen or executed",
            "no pillar completion or seam admissibility or closure",
            "no empirical adequacy or new physics",
            "no C_k dynamics, CCFT validation, or master-action promotion",
            "no repository-wide green claim",
        ],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Independently review the post-canonical-result Maxwell-Dirac route decision.")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    try:
        report = build_review_report()
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    expected = canonical_json_bytes(report)
    if args.write:
        REVIEW_REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
        REVIEW_REPORT_PATH.write_bytes(expected)
        print(f"wrote post-result route-decision review: {report['verdict']}; descendant robustness 56/62")
        return 0 if report["accepted"] else 2
    if args.check:
        if not REVIEW_REPORT_PATH.is_file() or REVIEW_REPORT_PATH.read_bytes() != expected:
            print("stale or missing post-result route-decision review", file=sys.stderr)
            return 1
        print(f"post-result route-decision review verified: {report['verdict']}; descendant robustness selected")
        return 0 if report["accepted"] else 2
    sys.stdout.buffer.write(expected)
    return 0 if report["accepted"] else 2


if __name__ == "__main__":
    raise SystemExit(main())

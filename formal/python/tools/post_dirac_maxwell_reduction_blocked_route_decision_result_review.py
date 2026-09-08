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
from formal.python.tools.prompt_dependency_identity import (
    identity_sha256_path,
    prompt_dependency_is_nonblocking,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
PACKET_RELATIVE_PATH = "formal/output/POST-DIRAC-MAXWELL-REDUCTION-BLOCKED-ROUTE-DECISION-PACKET-v0.json"
MANIFEST_RELATIVE_PATH = "formal/output/POST-DIRAC-MAXWELL-REDUCTION-BLOCKED-ROUTE-DECISION-MANIFEST-v0.json"
PREPARATION_REPORT_RELATIVE_PATH = "formal/docs/release/POST_DIRAC_MAXWELL_REDUCTION_BLOCKED_ROUTE_DECISION_PACKET_20260713_v0.json"
REVIEW_REPORT_RELATIVE_PATH = "formal/docs/release/POST_DIRAC_MAXWELL_REDUCTION_BLOCKED_ROUTE_DECISION_PACKET_RESULT_REVIEW_20260713_v0.json"
PREPARATION_GENERATOR_RELATIVE_PATH = "formal/python/tools/post_dirac_maxwell_reduction_blocked_route_decision.py"
PACKET_PATH = REPO_ROOT / PACKET_RELATIVE_PATH
REVIEW_REPORT_PATH = REPO_ROOT / REVIEW_REPORT_RELATIVE_PATH

CAPTURED_AT_UTC = "2026-07-13T00:00:00Z"
REVIEW_TARGET = "review_post_dirac_maxwell_reduction_blocked_route_decision_packet_v0_result"
ACCEPTED_TARGET = "prepare_dirac_maxwell_full_zero_mode_reduction_with_transverse_fields_packet_v0"
BLOCKED_TARGET = "prepare_post_dirac_maxwell_reduction_blocked_route_decision_packet_v1"
REVIEW_SCHEMA_ID = "POST_DIRAC_MAXWELL_REDUCTION_BLOCKED_ROUTE_DECISION_PACKET_RESULT_REVIEW_20260713_v0"
PREPARATION_COMMIT = "2ced60dc0aaf44f54386872d0de6f5ec1f17c481"
PREPARATION_PARENT = "677294016ca6e1b855b024470025fd631755b6e8"
EXPECTED_HASHES = {
    PREPARATION_GENERATOR_RELATIVE_PATH: "88257fb53c68e117c6baf276c1aa3423129814a802a073f1be3a925f31bc97bb",
    PACKET_RELATIVE_PATH: "877796d69cb09211b3160a72d2cee948703ec5985279c84bbae9983eb938a23e",
    MANIFEST_RELATIVE_PATH: "e0d077ae88606f438717cb48138927088c080fcb171270917c17b0b6d121fc37",
    PREPARATION_REPORT_RELATIVE_PATH: "552ebe36ec3f3d2e3739e01d9add879501e976e83ae5b0d06a1ed9561ec0d11e",
}
PROMPT_RELATIVE_PATH = "Prompt.txt"
PROMPT_DEPENDENCY_ROLE = "DEMOTE_TO_NONBLOCKING_PROVENANCE"
PROMPT_SHA256 = "2bc6996ea28e96c50e688ed3d30ee24808af411a244eb594aad89ff80fda8433"
WEIGHT_MAP = {
    "parent_action_fidelity": 5,
    "blocker_resolution_directness": 5,
    "accepted_foundation_reuse": 4,
    "seam_scientific_value": 4,
    "analytic_closure_readiness": 5,
    "numerical_tractability": 3,
    "bounded_scope": 3,
    "benchmark_continuity": 2,
}
INDEPENDENT_SCORES = {
    "REPAIR_REDUCTION": [2, 2, 2, 2, 1, 1, 1, 2],
    "ADOPT_NATIVE_1P1": [0, 1, 1, 1, 2, 2, 2, 1],
    "MOVE_TO_2P1": [2, 1, 2, 2, 0, 0, 1, 2],
    "CHANGE_MATTER_SECTOR": [0, 1, 0, 1, 2, 2, 2, 0],
}
THRESHOLDS = [40, 42, 44, 46, 48]


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
    return identity_sha256_path(path, repo_root=REPO_ROOT)


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected object: {path}")
    return value


def custody() -> dict[str, Any]:
    commit = subprocess.run(["git", "rev-parse", PREPARATION_COMMIT], cwd=REPO_ROOT, capture_output=True, text=True, check=False).stdout.strip()
    parent = subprocess.run(["git", "rev-parse", f"{PREPARATION_COMMIT}^"], cwd=REPO_ROOT, capture_output=True, text=True, check=False).stdout.strip()
    working = {path: sha256_path(REPO_ROOT / path) for path in EXPECTED_HASHES}
    committed: dict[str, str] = {}
    for path in EXPECTED_HASHES:
        result = subprocess.run(["git", "show", f"{PREPARATION_COMMIT}:{path}"], cwd=REPO_ROOT, capture_output=True, check=False)
        committed[path] = sha256_bytes(result.stdout) if result.returncode == 0 else "MISSING"
    passed = commit == PREPARATION_COMMIT and parent == PREPARATION_PARENT and working == EXPECTED_HASHES and committed == EXPECTED_HASHES
    return {"commit": commit, "parent": parent, "working_hashes": working, "commit_hashes": committed, "expected_hashes": EXPECTED_HASHES, "passed": passed}


def independent_scoring(packet: dict[str, Any]) -> dict[str, Any]:
    ordered_weights = list(WEIGHT_MAP.values())
    totals = {candidate: sum(weight * score for weight, score in zip(ordered_weights, scores, strict=True)) for candidate, scores in INDEPENDENT_SCORES.items()}
    packet_scores = {
        item["candidate_id"]: {
            "scores": [row["score"] for row in item["criterion_scores"]],
            "total": item["weighted_total"],
            "all_support_bound": all(row["exact_supporting_proposition_ids"] for row in item["criterion_scores"]),
        }
        for item in packet["scored_candidates"]
    }
    score_vectors_match = all(packet_scores.get(candidate, {}).get("scores") == scores for candidate, scores in INDEPENDENT_SCORES.items())
    totals_match = all(packet_scores.get(candidate, {}).get("total") == total for candidate, total in totals.items())
    selected_by_threshold = {}
    for threshold in THRESHOLDS:
        eligible = [candidate for candidate, total in totals.items() if total >= threshold and INDEPENDENT_SCORES[candidate][1] >= 1]
        selected_by_threshold[str(threshold)] = max(eligible, key=lambda candidate: totals[candidate]) if eligible else None
    return {
        "criterion_weights": WEIGHT_MAP,
        "score_vectors": INDEPENDENT_SCORES,
        "weighted_totals": totals,
        "packet_score_vectors_match": score_vectors_match,
        "packet_totals_match": totals_match,
        "all_packet_scores_bind_propositions": all(item["all_support_bound"] for item in packet_scores.values()),
        "selected_by_threshold": selected_by_threshold,
        "stable_selection": set(selected_by_threshold.values()) == {"REPAIR_REDUCTION"},
        "canonical_selected_candidate": selected_by_threshold["44"],
    }


DECISION_IDS = [
    "immutable_route_decision_preparation_bound",
    "exact_four_candidate_identity_reproduced",
    "all_eight_criterion_weights_recomputed",
    "all_thirty_two_scores_recomputed",
    "all_weighted_totals_recomputed",
    "every_packet_score_binds_repository_propositions",
    "user_recommendation_did_not_enter_scoring",
    "external_context_did_not_enter_scoring",
    "repair_reduction_is_independent_highest_score",
    "selection_is_stable_from_40_through_48",
    "mutation_controls_and_no_oracle_boundary_hold",
    "restricted_sector_hunting_is_not_default_repair",
    "only_full_zero_mode_repair_preparation_is_authorized",
    "Prompt_and_all_nonpromotion_boundaries_hold",
]


def build_review_report() -> dict[str, Any]:
    packet = load_json(PACKET_PATH)
    custody_result = custody()
    scoring = independent_scoring(packet)
    candidates = [item["candidate_id"] for item in packet["scored_candidates"]]
    controls = packet["mutation_controls"]
    boundary = packet["boundary"]
    decisions = {
        "immutable_route_decision_preparation_bound": custody_result["passed"],
        "exact_four_candidate_identity_reproduced": candidates == list(INDEPENDENT_SCORES),
        "all_eight_criterion_weights_recomputed": packet["criterion_weights"] == WEIGHT_MAP,
        "all_thirty_two_scores_recomputed": scoring["packet_score_vectors_match"] and sum(len(item["criterion_scores"]) for item in packet["scored_candidates"]) == 32,
        "all_weighted_totals_recomputed": scoring["packet_totals_match"],
        "every_packet_score_binds_repository_propositions": scoring["all_packet_scores_bind_propositions"],
        "user_recommendation_did_not_enter_scoring": packet["user_recommendation"]["used_as_score_input"] is False,
        "external_context_did_not_enter_scoring": all(item["route_support_eligible"] is False for item in packet["external_context"]),
        "repair_reduction_is_independent_highest_score": scoring["canonical_selected_candidate"] == "REPAIR_REDUCTION" and scoring["weighted_totals"]["REPAIR_REDUCTION"] == 51,
        "selection_is_stable_from_40_through_48": scoring["stable_selection"],
        "mutation_controls_and_no_oracle_boundary_hold": len(controls) == 8 and all(item["passed"] for item in controls) and "expected_winner" not in packet,
        "restricted_sector_hunting_is_not_default_repair": packet["restricted_spinor_sector_default_repair"] is False,
        "only_full_zero_mode_repair_preparation_is_authorized": packet["post_acceptance_target"] == ACCEPTED_TARGET and boundary["numerical_guardrail_authorized"] is False and boundary["execution_authorized"] is False,
        "Prompt_and_all_nonpromotion_boundaries_hold": prompt_dependency_is_nonblocking(PROMPT_DEPENDENCY_ROLE) and boundary["C_k_audit_only"] is True and boundary["CCFT_resumed"] is False and boundary["master_action_promoted"] is False,
    }
    ordered = [{"decision_id": item, "passed": decisions[item]} for item in DECISION_IDS]
    failed = [item["decision_id"] for item in ordered if not item["passed"]]
    accepted = not failed
    return {
        "schema_id": REVIEW_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "review_target": REVIEW_TARGET,
        "accepted": accepted,
        "verdict": "ACCEPT" if accepted else "B-BLOCKED",
        "selected_candidate_id": "REPAIR_REDUCTION" if accepted else None,
        "selected_candidate_label": "repair reduction" if accepted else None,
        "selected_next_target": ACCEPTED_TARGET if accepted else BLOCKED_TARGET,
        "selected_next_target_kind": ACCEPTED_TARGET if accepted else BLOCKED_TARGET,
        "decision_count": len(DECISION_IDS),
        "passed_decision_count": len(DECISION_IDS) - len(failed),
        "failed_decision_ids": failed,
        "decisions": ordered,
        "preparation_custody": custody_result,
        "independent_scoring": scoring,
        "authority_rotation": {
            "route_decision_accepted": accepted,
            "full_zero_mode_repair_preparation_authorized": accepted,
            "numerical_guardrail_authorized": False,
            "execution_authorized": False,
            "pure_1p1_truncation_rehabilitated": False,
            "pillar_or_seam_completion_claimed": False,
        },
        "claim": "Independent rescoring selects repair reduction by retaining A2 and A3; only the full zero-mode analytic repair preparation is authorized." if accepted else "The route decision is blocked.",
        "nonclaims": ["no numerical guardrail or execution", "no restricted-sector default", "no pure 1+1 truncation recovery", "no QFT, pillar completion, seam closure, C_k dynamics, CCFT, or master-action promotion"],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Review the post-block Maxwell-Dirac route decision.")
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
        print(f"wrote route-decision review: {report['verdict']}; repair reduction 51/62")
        return 0 if report["accepted"] else 2
    if args.check:
        if not REVIEW_REPORT_PATH.is_file() or REVIEW_REPORT_PATH.read_bytes() != expected:
            print("stale or missing route-decision review", file=sys.stderr)
            return 1
        print(f"route-decision review verified: {report['verdict']}; repair reduction selected")
        return 0 if report["accepted"] else 2
    sys.stdout.buffer.write(expected)
    return 0 if report["accepted"] else 2


if __name__ == "__main__":
    raise SystemExit(main())

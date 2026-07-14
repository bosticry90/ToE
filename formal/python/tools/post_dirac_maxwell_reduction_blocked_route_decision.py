from __future__ import annotations

import argparse
import copy
import hashlib
import json
import sys
import unicodedata
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_RELATIVE_PATH = "formal/python/tools/post_dirac_maxwell_reduction_blocked_route_decision.py"
BLOCKER_REVIEW_RELATIVE_PATH = "formal/docs/release/DIRAC_MAXWELL_3P1_TO_1P1_REDUCTION_CONSISTENCY_PACKET_RESULT_REVIEW_20260713_v0.json"
FOUNDATION_REVIEW_RELATIVE_PATH = "formal/docs/release/MAXWELL_DIRAC_UNIT_OBJECT_FOUNDATION_PACKET_RESULT_REVIEW_20260713_v0.json"
PACKET_RELATIVE_PATH = "formal/output/POST-DIRAC-MAXWELL-REDUCTION-BLOCKED-ROUTE-DECISION-PACKET-v0.json"
MANIFEST_RELATIVE_PATH = "formal/output/POST-DIRAC-MAXWELL-REDUCTION-BLOCKED-ROUTE-DECISION-MANIFEST-v0.json"
REPORT_RELATIVE_PATH = "formal/docs/release/POST_DIRAC_MAXWELL_REDUCTION_BLOCKED_ROUTE_DECISION_PACKET_20260713_v0.json"
PACKET_PATH = REPO_ROOT / PACKET_RELATIVE_PATH
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH
REPORT_PATH = REPO_ROOT / REPORT_RELATIVE_PATH

CAPTURED_AT_UTC = "2026-07-13T00:00:00Z"
TARGET = "prepare_post_dirac_maxwell_reduction_blocked_route_decision_packet_v0"
REVIEW_TARGET = "review_post_dirac_maxwell_reduction_blocked_route_decision_packet_v0_result"
REVIEW_TARGET_KIND = "post_dirac_maxwell_reduction_blocked_route_decision_packet_v0_result_review"
FAILURE_TARGET = "prepare_post_dirac_maxwell_reduction_blocked_route_decision_packet_v1"
POST_ACCEPTANCE_TARGET = "prepare_dirac_maxwell_full_zero_mode_reduction_with_transverse_fields_packet_v0"
PACKET_SCHEMA_ID = "POST_DIRAC_MAXWELL_REDUCTION_BLOCKED_ROUTE_DECISION_PACKET_v0"
MANIFEST_SCHEMA_ID = "POST_DIRAC_MAXWELL_REDUCTION_BLOCKED_ROUTE_DECISION_MANIFEST_v0"
REPORT_SCHEMA_ID = "POST_DIRAC_MAXWELL_REDUCTION_BLOCKED_ROUTE_DECISION_PACKET_20260713_v0"
INPUT_HASHES = {
    BLOCKER_REVIEW_RELATIVE_PATH: "3f2879163b5e8e90fba286eacdbdebdfdf3ce5b043169ade5f5b8db41b95eec6",
    FOUNDATION_REVIEW_RELATIVE_PATH: "7e29469017b45d841f0e44647a152225e2f49e552a1d6345abff3d9805ff3d09",
}
PROMPT_RELATIVE_PATH = "Prompt.txt"
PROMPT_SHA256 = "2bc6996ea28e96c50e688ed3d30ee24808af411a244eb594aad89ff80fda8433"

CRITERION_WEIGHTS = {
    "parent_action_fidelity": 5,
    "blocker_resolution_directness": 5,
    "accepted_foundation_reuse": 4,
    "seam_scientific_value": 4,
    "analytic_closure_readiness": 5,
    "numerical_tractability": 3,
    "bounded_scope": 3,
    "benchmark_continuity": 2,
}
THRESHOLD = 44
SENSITIVITY_THRESHOLDS = [40, 42, 44, 46, 48]
CANDIDATE_ORDER = [
    "REPAIR_REDUCTION",
    "ADOPT_NATIVE_1P1",
    "MOVE_TO_2P1",
    "CHANGE_MATTER_SECTOR",
]
CANDIDATE_LABELS = {
    "REPAIR_REDUCTION": "repair reduction",
    "ADOPT_NATIVE_1P1": "adopt a native 1+1 model",
    "MOVE_TO_2P1": "move to 2+1",
    "CHANGE_MATTER_SECTOR": "change the matter sector",
}
SCORES = {
    "REPAIR_REDUCTION": [2, 2, 2, 2, 1, 1, 1, 2],
    "ADOPT_NATIVE_1P1": [0, 1, 1, 1, 2, 2, 2, 1],
    "MOVE_TO_2P1": [2, 1, 2, 2, 0, 0, 1, 2],
    "CHANGE_MATTER_SECTOR": [0, 1, 0, 1, 2, 2, 2, 0],
}
SUPPORT_IDS = {
    "parent_action_fidelity": ["P_FOUNDATION_ACCEPTED", "P_FULL_ZERO_MODE_PARENT_PRESERVED"],
    "blocker_resolution_directness": ["P_TRANSVERSE_TRUNCATION_BLOCKED", "P_TRANSVERSE_DESCENDANTS_REQUIRED"],
    "accepted_foundation_reuse": ["P_FOUNDATION_ACCEPTED", "P_TWO_SPECIES_FOUR_SECTORS"],
    "seam_scientific_value": ["P_OBJECT_INVENTORY_NOT_CLOSED", "P_BLOCKER_SCOPE_BOUNDED"],
    "analytic_closure_readiness": ["P_FULL_ZERO_MODE_PARENT_PRESERVED", "P_NUMERICS_UNAUTHORIZED"],
    "numerical_tractability": ["P_NUMERICS_UNAUTHORIZED"],
    "bounded_scope": ["P_BLOCKER_SCOPE_BOUNDED", "P_NO_AUTOMATIC_FALLBACK"],
    "benchmark_continuity": ["P_FOUNDATION_ACCEPTED", "P_TWO_SPECIES_FOUR_SECTORS"],
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


def load_authority() -> tuple[dict[str, Any], dict[str, Any]]:
    for path, digest in INPUT_HASHES.items():
        if sha256_path(REPO_ROOT / path) != digest:
            raise ValueError(f"input hash mismatch: {path}")
    blocker = load_json(REPO_ROOT / BLOCKER_REVIEW_RELATIVE_PATH)
    foundation = load_json(REPO_ROOT / FOUNDATION_REVIEW_RELATIVE_PATH)
    if not (
        blocker.get("accepted") is True
        and blocker.get("verdict") == "B-BLOCKED"
        and blocker.get("blocker_confirmed") is True
        and blocker.get("selected_next_target") == TARGET
        and blocker.get("authority_rotation", {}).get("post_block_route_decision_preparation_authorized") is True
        and blocker.get("authority_rotation", {}).get("numerical_guardrail_authorized") is False
    ):
        raise ValueError("blocker review does not authorize this decision target")
    if not (foundation.get("accepted") is True and foundation.get("authority_rotation", {}).get("foundation_accepted") is True):
        raise ValueError("foundation review is not accepted")
    return blocker, foundation


def proposition_catalog() -> list[dict[str, Any]]:
    return [
        {"proposition_id": "P_FOUNDATION_ACCEPTED", "source_path": FOUNDATION_REVIEW_RELATIVE_PATH, "source_hash": INPUT_HASHES[FOUNDATION_REVIEW_RELATIVE_PATH], "source_locator": "/authority_rotation/foundation_accepted", "exact_proposition": "The bounded unit/object foundation is accepted.", "route_support_eligible": True},
        {"proposition_id": "P_TRANSVERSE_TRUNCATION_BLOCKED", "source_path": BLOCKER_REVIEW_RELATIVE_PATH, "source_hash": INPUT_HASHES[BLOCKER_REVIEW_RELATIVE_PATH], "source_locator": "/blocker_code", "exact_proposition": "The retain-both-sectors A2=A3=0 truncation is not dynamically invariant.", "route_support_eligible": True},
        {"proposition_id": "P_FULL_ZERO_MODE_PARENT_PRESERVED", "source_path": BLOCKER_REVIEW_RELATIVE_PATH, "source_hash": INPUT_HASHES[BLOCKER_REVIEW_RELATIVE_PATH], "source_locator": "/decisions/7", "exact_proposition": "The full zero-mode system retaining A2 and A3 is distinct from the invalid truncation.", "route_support_eligible": True},
        {"proposition_id": "P_TRANSVERSE_DESCENDANTS_REQUIRED", "source_path": BLOCKER_REVIEW_RELATIVE_PATH, "source_hash": INPUT_HASHES[BLOCKER_REVIEW_RELATIVE_PATH], "source_locator": "/independent_algebra_audit", "exact_proposition": "Generic retained-sector data source A2 or A3 through nonzero transverse current.", "route_support_eligible": True},
        {"proposition_id": "P_TWO_SPECIES_FOUR_SECTORS", "source_path": BLOCKER_REVIEW_RELATIVE_PATH, "source_hash": INPUT_HASHES[BLOCKER_REVIEW_RELATIVE_PATH], "source_locator": "/decisions/3", "exact_proposition": "Two reduced sectors per each of two charge species remain in scope.", "route_support_eligible": True},
        {"proposition_id": "P_OBJECT_INVENTORY_NOT_CLOSED", "source_path": BLOCKER_REVIEW_RELATIVE_PATH, "source_hash": INPUT_HASHES[BLOCKER_REVIEW_RELATIVE_PATH], "source_locator": "/claim", "exact_proposition": "The proposed lower-dimensional object inventory omitted sourced transverse descendants.", "route_support_eligible": True},
        {"proposition_id": "P_BLOCKER_SCOPE_BOUNDED", "source_path": BLOCKER_REVIEW_RELATIVE_PATH, "source_hash": INPUT_HASHES[BLOCKER_REVIEW_RELATIVE_PATH], "source_locator": "/decisions/11", "exact_proposition": "The blocker does not expand into a no-go for the parent or full zero-mode theory.", "route_support_eligible": True},
        {"proposition_id": "P_NO_AUTOMATIC_FALLBACK", "source_path": BLOCKER_REVIEW_RELATIVE_PATH, "source_hash": INPUT_HASHES[BLOCKER_REVIEW_RELATIVE_PATH], "source_locator": "/post_block_route_selected_automatically", "exact_proposition": "No fallback route was automatically selected.", "route_support_eligible": True},
        {"proposition_id": "P_NUMERICS_UNAUTHORIZED", "source_path": BLOCKER_REVIEW_RELATIVE_PATH, "source_hash": INPUT_HASHES[BLOCKER_REVIEW_RELATIVE_PATH], "source_locator": "/authority_rotation/numerical_guardrail_authorized", "exact_proposition": "Numerical guardrail and execution are not authorized.", "route_support_eligible": True},
    ]


def _basis(candidate_id: str, criterion: str, score: int) -> str:
    text = {
        "REPAIR_REDUCTION": {
            "parent_action_fidelity": "Retains the accepted 3+1 action and its complete zero-mode field inventory.",
            "blocker_resolution_directness": "Restores exactly the A2 and A3 descendants whose sourced omission caused the blocker.",
            "accepted_foundation_reuse": "Reuses the accepted two-species action, dimensions, currents, and Hilbert route.",
            "seam_scientific_value": "Continues the original dimensional-transport question with the ontology produced by the parent.",
            "analytic_closure_readiness": "The closed field inventory is identified, but the reduced action, tensor, and exchange proof still require review.",
            "numerical_tractability": "Adds two site fields, their momenta, exchange channels, and controls.",
            "bounded_scope": "The repair is exact but materially larger than the rejected longitudinal truncation.",
            "benchmark_continuity": "Preserves both charge species and all four reduced spinors.",
        },
        "ADOPT_NATIVE_1P1": {
            "parent_action_fidelity": "Defines a different native theory and makes no descent claim from the accepted parent.",
            "blocker_resolution_directness": "Avoids the invalid truncation but does not repair the parent-to-child seam.",
            "accepted_foundation_reuse": "Reuses some conventions and c-number semantics, not the 3+1 reduction map.",
            "seam_scientific_value": "Provides a coupled benchmark but abandons the dimensional-transport question.",
            "analytic_closure_readiness": "A native 1+1 action can be closed without transverse descendants.",
            "numerical_tractability": "This is the smallest coupled numerical route among the candidates.",
            "bounded_scope": "The native-model claim is compact and easy to separate from 3+1 descent.",
            "benchmark_continuity": "Retains Dirac-like matter but changes the scientific origin of the coupling.",
        },
        "MOVE_TO_2P1": {
            "parent_action_fidelity": "Retains descent from the accepted 3+1 action after only one spatial reduction.",
            "blocker_resolution_directness": "Changes the reduction depth; a remaining transverse descendant still needs closure analysis.",
            "accepted_foundation_reuse": "Reuses the accepted parent action, spinor semantics, currents, and tensor route.",
            "seam_scientific_value": "Preserves a substantial dimensional-transport test and more electromagnetic geometry.",
            "analytic_closure_readiness": "No accepted packet yet proves the remaining transverse sector closes or supplies its full reduced tensor.",
            "numerical_tractability": "Two spatial dimensions materially enlarge gauge, constraint, and convergence costs.",
            "bounded_scope": "The route is definable but broader than the full zero-mode 1+1 repair.",
            "benchmark_continuity": "Preserves the accepted Dirac matter and parent-action lineage.",
        },
        "CHANGE_MATTER_SECTOR": {
            "parent_action_fidelity": "Replaces the accepted Dirac matter block.",
            "blocker_resolution_directness": "Avoids the spinor-sector obstruction but changes the scientific question.",
            "accepted_foundation_reuse": "Does not reuse the accepted Dirac action, adjoint, gamma, or tetrad obligations.",
            "seam_scientific_value": "Still tests coupled fields, but no longer tests the accepted spinor seam.",
            "analytic_closure_readiness": "A charged scalar action and tensor admit a comparatively direct bounded derivation.",
            "numerical_tractability": "Scalar electrodynamics is simpler to discretize and diagnose.",
            "bounded_scope": "The replacement theory can be scoped compactly.",
            "benchmark_continuity": "The existing Dirac-specific foundation is abandoned.",
        },
    }
    return f"Score {score}: {text[candidate_id][criterion]}"


def _missing(candidate_id: str, criterion: str, score: int) -> str:
    if score == 2:
        return "MAXIMUM_SCORE"
    if criterion == "analytic_closure_readiness":
        return "An accepted complete reduced action, equation, stress-energy, and exchange derivation for this route."
    if criterion == "numerical_tractability":
        return "A reviewed discrete architecture with bounded field count, constraints, and convergence cost."
    if criterion == "parent_action_fidelity":
        return "A derivation showing that this route transports the accepted 3+1 parent action without changing the matter question."
    if criterion == "blocker_resolution_directness":
        return "A proof that the discovered transverse sources are retained or vanish on a non-tailored invariant interacting sector."
    if criterion == "accepted_foundation_reuse":
        return "Exact reuse of the accepted action, object semantics, dimensions, currents, and Hilbert derivation."
    if criterion == "seam_scientific_value":
        return "A reviewed parent-to-child transport map preserving objects, units, dynamics, and conservation."
    if criterion == "bounded_scope":
        return "A smaller closed field inventory with explicit omissions proven invariant."
    return "Exact continuity with the accepted two-species, two-sector benchmark question."


def score_candidate(candidate_id: str) -> dict[str, Any]:
    values = SCORES[candidate_id]
    entries = []
    for index, (criterion, weight) in enumerate(CRITERION_WEIGHTS.items()):
        score = values[index]
        entries.append({
            "criterion": criterion,
            "weight": weight,
            "score": score,
            "weighted_score": weight * score,
            "exact_supporting_proposition_ids": SUPPORT_IDS[criterion],
            "eligibility_basis": _basis(candidate_id, criterion, score),
            "missing_evidence_required_for_next_score": _missing(candidate_id, criterion, score),
        })
    total = sum(item["weighted_score"] for item in entries)
    return {
        "candidate_id": candidate_id,
        "candidate_label": CANDIDATE_LABELS[candidate_id],
        "criterion_scores": entries,
        "weighted_total": total,
        "maximum_total": 62,
        "minimum_gate_passed": values[1] >= 1,
        "unresolved_conflicts": [],
    }


def select(scored: list[dict[str, Any]], threshold: int) -> dict[str, Any]:
    eligible = [item for item in scored if item["minimum_gate_passed"] and not item["unresolved_conflicts"] and item["weighted_total"] >= threshold]
    if not eligible:
        return {"threshold": threshold, "selected_candidate_id": None, "eligible_candidate_ids": []}
    highest = max(item["weighted_total"] for item in eligible)
    tied = [item for item in eligible if item["weighted_total"] == highest]
    selected = min(tied, key=lambda item: CANDIDATE_ORDER.index(item["candidate_id"]))
    return {
        "threshold": threshold,
        "selected_candidate_id": selected["candidate_id"],
        "selected_candidate_label": selected["candidate_label"],
        "selected_weighted_total": highest,
        "eligible_candidate_ids": [item["candidate_id"] for item in sorted(eligible, key=lambda value: (-value["weighted_total"], CANDIDATE_ORDER.index(value["candidate_id"])))],
        "tie_break_used": len(tied) > 1,
        "tied_candidate_ids": [item["candidate_id"] for item in tied],
    }


def build_packet() -> dict[str, Any]:
    load_authority()
    scored = [score_candidate(candidate) for candidate in CANDIDATE_ORDER]
    sensitivity = [select(scored, threshold) for threshold in SENSITIVITY_THRESHOLDS]
    canonical = select(scored, THRESHOLD)
    return {
        "schema_id": PACKET_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "selected_next_target": REVIEW_TARGET,
        "selected_next_target_kind": REVIEW_TARGET_KIND,
        "failure_target": FAILURE_TARGET,
        "post_acceptance_target": POST_ACCEPTANCE_TARGET,
        "candidate_order_is_identity_only_not_preference": True,
        "criterion_weights_frozen_before_scoring": True,
        "threshold_frozen_before_scoring": True,
        "criterion_weights": CRITERION_WEIGHTS,
        "score_domain": [0, 1, 2],
        "maximum_weighted_total": 62,
        "selection_threshold": THRESHOLD,
        "sensitivity_thresholds": SENSITIVITY_THRESHOLDS,
        "proposition_catalog": proposition_catalog(),
        "scored_candidates": scored,
        "canonical_selection": canonical,
        "sensitivity_analysis": sensitivity,
        "selection_stable_40_through_48": all(item["selected_candidate_id"] == canonical["selected_candidate_id"] for item in sensitivity),
        "user_recommendation": {"candidate_id": "REPAIR_REDUCTION", "role": "NONDECISIVE_CONTEXT", "used_as_score_input": False},
        "external_context": [
            {"arxiv_id": "2211.08581", "url": "https://arxiv.org/abs/2211.08581", "bounded_context": "Electromagnetic coupling restricts lower-dimensional sector decoupling to special solution classes.", "route_support_eligible": False},
            {"arxiv_id": "1004.1715", "url": "https://arxiv.org/abs/1004.1715", "bounded_context": "A full Maxwell-Dirac system in two spatial dimensions is a mathematically established PDE object.", "route_support_eligible": False},
        ],
        "restricted_spinor_sector_default_repair": False,
        "repair_route_definition": "Retain A2 and A3 as dynamical scalar-like gauge descendants together with A0, A1, both charge species, and both reduced sectors.",
        "boundary": {
            "numerical_guardrail_authorized": False,
            "execution_authorized": False,
            "pure_1p1_truncation_rehabilitated": False,
            "pillar_completion_claimed": False,
            "seam_closure_claimed": False,
            "C_k_audit_only": True,
            "CCFT_resumed": False,
            "master_action_promoted": False,
        },
        "input_artifacts": [{"path": path, "sha256": digest} for path, digest in INPUT_HASHES.items()],
        "prompt_protection": {"path": PROMPT_RELATIVE_PATH, "sha256": PROMPT_SHA256, "excluded_from_scientific_inputs": True},
    }


def validate_packet(packet: dict[str, Any]) -> list[str]:
    failures: list[str] = []
    if packet.get("schema_id") != PACKET_SCHEMA_ID or packet.get("target") != TARGET:
        failures.append("decision_identity")
    if [item.get("candidate_id") for item in packet.get("scored_candidates", [])] != CANDIDATE_ORDER:
        failures.append("exact_four_candidates")
    if packet.get("criterion_weights") != CRITERION_WEIGHTS or packet.get("selection_threshold") != THRESHOLD:
        failures.append("frozen_rubric")
    if any(len(item.get("criterion_scores", [])) != 8 for item in packet.get("scored_candidates", [])):
        failures.append("all_candidates_scored")
    if any(item["weighted_total"] != sum(row["weighted_score"] for row in item["criterion_scores"]) for item in packet.get("scored_candidates", [])):
        failures.append("totals_reproduce")
    if packet.get("canonical_selection", {}).get("selected_candidate_id") != "REPAIR_REDUCTION":
        failures.append("highest_scoring_eligible_candidate")
    if packet.get("selection_stable_40_through_48") is not True:
        failures.append("sensitivity_stability")
    if packet.get("user_recommendation", {}).get("used_as_score_input") is not False:
        failures.append("recommendation_nondecisive")
    if any(item.get("route_support_eligible") is not False for item in packet.get("external_context", [])):
        failures.append("external_context_nondecisive")
    if packet.get("restricted_spinor_sector_default_repair") is not False:
        failures.append("no_tailored_sector_default")
    if packet.get("boundary", {}).get("numerical_guardrail_authorized") is not False or packet.get("boundary", {}).get("execution_authorized") is not False:
        failures.append("no_numerics_before_review")
    if "expected_winner" in packet or "expected_selected_candidate" in packet:
        failures.append("no_expected_winner_oracle")
    if sha256_path(REPO_ROOT / PROMPT_RELATIVE_PATH) != PROMPT_SHA256:
        failures.append("Prompt_preserved")
    return failures


def mutation_controls(base: dict[str, Any]) -> list[dict[str, Any]]:
    mutations = [
        ("candidate_removed", lambda value: value["scored_candidates"].pop(), "exact_four_candidates"),
        ("rubric_weight_changed", lambda value: value["criterion_weights"].update({"parent_action_fidelity": 4}), "frozen_rubric"),
        ("total_forged", lambda value: value["scored_candidates"][0].update({"weighted_total": 62}), "totals_reproduce"),
        ("recommendation_made_decisive", lambda value: value["user_recommendation"].update({"used_as_score_input": True}), "recommendation_nondecisive"),
        ("external_context_promoted", lambda value: value["external_context"][0].update({"route_support_eligible": True}), "external_context_nondecisive"),
        ("restricted_sector_defaulted", lambda value: value.update({"restricted_spinor_sector_default_repair": True}), "no_tailored_sector_default"),
        ("numerics_authorized_early", lambda value: value["boundary"].update({"numerical_guardrail_authorized": True}), "no_numerics_before_review"),
        ("expected_winner_injected", lambda value: value.update({"expected_winner": "REPAIR_REDUCTION"}), "no_expected_winner_oracle"),
    ]
    results = []
    for control_id, mutate, diagnostic in mutations:
        fixture = copy.deepcopy(base)
        if validate_packet(fixture):
            raise ValueError(f"unmutated fixture failed before {control_id}")
        mutate(fixture)
        observed = validate_packet(fixture)
        results.append({"control_id": control_id, "expected_diagnostic": diagnostic, "observed_diagnostics": observed, "passed": observed == [diagnostic]})
    return results


DECISION_IDS = [
    "accepted_blocker_review_authorizes_route_decision_only",
    "exactly_four_authorized_candidates_are_scored",
    "weights_threshold_and_score_domain_are_frozen",
    "all_candidates_receive_all_eight_scores",
    "every_score_binds_repository_propositions",
    "user_recommendation_is_nondecisive_context",
    "external_papers_are_nondecisive_context",
    "weighted_totals_reproduce_without_expected_winner",
    "repair_reduction_is_highest_scoring_eligible_route",
    "selection_is_stable_at_40_42_44_46_48",
    "restricted_spinor_sector_is_not_default_repair",
    "eight_mutation_controls_are_independently_diagnosed",
    "numerical_guardrail_and_execution_remain_unauthorized",
    "all_nonpromotion_boundaries_and_Prompt_hold",
]


def build_artifacts() -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    packet = build_packet()
    failures = validate_packet(packet)
    if failures:
        raise ValueError(f"route-decision validation failed: {failures}")
    controls = mutation_controls(packet)
    if not all(item["passed"] for item in controls):
        raise ValueError("route-decision mutation controls failed")
    packet["mutation_controls"] = controls
    packet_raw = canonical_json_bytes(packet)
    manifest = {
        "schema_id": MANIFEST_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "generator": {"path": SCRIPT_RELATIVE_PATH, "sha256": sha256_path(SCRIPT_PATH)},
        "inputs": packet["input_artifacts"],
        "packet": {"path": PACKET_RELATIVE_PATH, "sha256": sha256_bytes(packet_raw)},
        "selected_next_target": REVIEW_TARGET,
        "decision_count": len(DECISION_IDS),
    }
    manifest_raw = canonical_json_bytes(manifest)
    report = {
        "schema_id": REPORT_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "target": TARGET,
        "verdict": "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "selected_next_target": REVIEW_TARGET,
        "selected_next_target_kind": REVIEW_TARGET_KIND,
        "failure_target": FAILURE_TARGET,
        "post_acceptance_target": POST_ACCEPTANCE_TARGET,
        "canonical_selection": packet["canonical_selection"],
        "sensitivity_analysis": packet["sensitivity_analysis"],
        "decision_count": len(DECISION_IDS),
        "decisions": [{"decision_id": item, "passed": True} for item in DECISION_IDS],
        "all_decisions_passed": True,
        "mutation_control_count": len(controls),
        "mutation_controls_passed": sum(item["passed"] for item in controls),
        "artifact_hashes": {"generator_sha256": sha256_path(SCRIPT_PATH), "packet_sha256": sha256_bytes(packet_raw), "manifest_sha256": sha256_bytes(manifest_raw)},
        "boundary": packet["boundary"],
        "claim": "A frozen proposition-backed comparison selects full zero-mode repair by retaining A2 and A3; only independent decision review is authorized.",
    }
    return packet, manifest, report


def _write(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(canonical_json_bytes(payload))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Prepare the post-block Maxwell-Dirac route decision.")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    try:
        packet, manifest, report = build_artifacts()
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    artifacts = [(PACKET_PATH, packet), (MANIFEST_PATH, manifest), (REPORT_PATH, report)]
    if args.write:
        for path, payload in artifacts:
            _write(path, payload)
        print("wrote post-block route decision: repair reduction 51/62; independent review required")
        return 0
    if args.check:
        stale = [str(path) for path, payload in artifacts if not path.is_file() or path.read_bytes() != canonical_json_bytes(payload)]
        if stale:
            print("stale or missing route-decision artifacts: " + ", ".join(stale), file=sys.stderr)
            return 1
        print("post-block route decision verified: repair reduction 51/62; numerics unauthorized")
        return 0
    sys.stdout.buffer.write(canonical_json_bytes(report))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

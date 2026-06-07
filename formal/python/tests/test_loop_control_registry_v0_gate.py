from __future__ import annotations

import json
import re
from collections import defaultdict
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
GOVERNANCE_MANIFEST_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "GOVERNANCE_TEST_MANIFEST_v1.json"
)

TOKEN_SOURCE_PATHS = [
    REPO_ROOT / "README.md",
    REPO_ROOT / "State_of_the_Theory.md",
    REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md",
    REPO_ROOT / "formal" / "docs" / "release" / "BOUNDED_SLICE_OPERATIONAL_PROTOCOL_v0.md",
    REPO_ROOT / "formal" / "docs" / "release" / "PHYSICS_FIRST_EXECUTION_RULE_v0.md",
]

CROSS_PILLAR_FRONTIER_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Derivation" / "CrossPillarClosureFrontier.lean"
)
MASTER_ACTION_FRONTIER_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Derivation" / "MasterActionDependencyFrontier.lean"
)
POST_SWEEP_QUEUE_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Derivation" / "PostSweepTheoremQueue.lean"
)
RN_ASSUMP_005_ATTEMPT_LIVE_RESULT_REVIEW_TARGET = (
    "review_qft_gr_renormalization_operator_domain_compatibility_assumption_"
    "reduction_attempt_result"
)
RN_ASSUMP_005_ATTEMPT_SURFACE = (
    "formal/toe_formal/ToeFormal/Bridges/"
    "QFT_GR_RenormalizationOperatorDomainCompatibilityAssumptionReductionAttempt.lean"
)
RN_ASSUMP_005_ATTEMPT_REPORT = (
    "formal/docs/release/"
    "QFT_GR_RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_"
    "REDUCTION_ATTEMPT_20260606_v0.json"
)
RN_ASSUMP_005_ATTEMPT_TOOL = (
    "formal/python/tools/"
    "qft_gr_renormalization_operator_domain_compatibility_assumption_"
    "reduction_attempt_report.py"
)
RN_ASSUMP_005_ATTEMPT_TOKEN = (
    "QFT_GR_RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_"
    "REDUCTION_ATTEMPT_EXECUTED_WITH_NO_CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
)
RN_ASSUMP_005_ATTEMPT_RESULT_REVIEW_TARGET = (
    "review_qft_gr_renormalization_operator_domain_compatibility_assumption_"
    "reduction_attempt_result"
)
RN_ASSUMP_005_CLOSEOUT_PREPARATION_TARGET = (
    "prepare_qft_gr_renormalization_assumption_reduction_closeout_packet"
)
RN_ASSUMP_005_CLOSEOUT_RESULT_REVIEW_TARGET = (
    "review_qft_gr_renormalization_assumption_reduction_closeout_packet_result"
)
STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_TARGET = (
    "prepare_qft_gr_state_domain_assumption_reduction_packet"
)
STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TARGET = (
    "review_qft_gr_state_domain_assumption_reduction_packet_result"
)
RN_ASSUMP_005_ATTEMPT_RESULT_REVIEW_SURFACE = (
    "formal/toe_formal/ToeFormal/Bridges/"
    "QFT_GR_RenormalizationOperatorDomainCompatibilityAssumptionReductionAttemptResultReview.lean"
)
RN_ASSUMP_005_ATTEMPT_RESULT_REVIEW_REPORT = (
    "formal/docs/release/"
    "QFT_GR_RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_"
    "REDUCTION_ATTEMPT_RESULT_REVIEW_20260606_v0.json"
)
RN_ASSUMP_005_ATTEMPT_RESULT_REVIEW_TOOL = (
    "formal/python/tools/"
    "qft_gr_renormalization_operator_domain_compatibility_assumption_"
    "reduction_attempt_result_review_report.py"
)
RN_ASSUMP_005_ATTEMPT_RESULT_REVIEW_TOKEN = (
    "QFT_GR_RENORMALIZATION_OPERATOR_DOMAIN_COMPATIBILITY_ASSUMPTION_"
    "REDUCTION_ATTEMPT_RESULT_REVIEW_ACCEPTS_REDUCED_OPERATOR_DOMAIN_"
    "COMPATIBILITY_AND_AUTHORIZES_RENORMALIZATION_ASSUMPTION_REDUCTION_"
    "CLOSEOUT_PREPARATION_ONLY"
)
RN_ASSUMP_005_ATTEMPT_RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_renormalization_operator_domain_compatibility_assumption_reduction_"
    "attempt_result_review_accepts_reduced_operator_domain_compatibility_and_"
    "authorizes_renormalization_assumption_reduction_closeout_preparation_only"
)
RN_ASSUMP_005_CLOSEOUT_PACKET_SURFACE = (
    "formal/toe_formal/ToeFormal/Bridges/"
    "QFT_GR_RenormalizationAssumptionReductionCloseoutPacket.lean"
)
RN_ASSUMP_005_CLOSEOUT_PACKET_REPORT = (
    "formal/docs/release/"
    "QFT_GR_RENORMALIZATION_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_20260606_v0.json"
)
RN_ASSUMP_005_CLOSEOUT_PACKET_TOOL = (
    "formal/python/tools/"
    "qft_gr_renormalization_assumption_reduction_closeout_packet_report.py"
)
RN_ASSUMP_005_CLOSEOUT_PACKET_TOKEN = (
    "QFT_GR_RENORMALIZATION_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_PREPARED_"
    "WITH_NO_CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
)
RN_ASSUMP_005_CLOSEOUT_PACKET_CLASSIFICATION = (
    "qft_gr_renormalization_assumption_reduction_closeout_packet_prepared_"
    "with_no_conservation_witness_or_seam_closure"
)
RN_ASSUMP_005_CLOSEOUT_RESULT_REVIEW_SURFACE = (
    "formal/toe_formal/ToeFormal/Bridges/"
    "QFT_GR_RenormalizationAssumptionReductionCloseoutPacketResultReview.lean"
)
RN_ASSUMP_005_CLOSEOUT_RESULT_REVIEW_REPORT = (
    "formal/docs/release/"
    "QFT_GR_RENORMALIZATION_ASSUMPTION_REDUCTION_CLOSEOUT_PACKET_RESULT_REVIEW_"
    "20260606_v0.json"
)
RN_ASSUMP_005_CLOSEOUT_RESULT_REVIEW_TOOL = (
    "formal/python/tools/"
    "qft_gr_renormalization_assumption_reduction_closeout_packet_result_review_report.py"
)
RN_ASSUMP_005_CLOSEOUT_RESULT_REVIEW_TOKEN = (
    "QFT_GR_RENORMALIZATION_ASSUMPTION_REDUCTION_CLOSEOUT_RESULT_REVIEW_"
    "ACCEPTS_RENORMALIZATION_ROWS_AND_AUTHORIZES_NEXT_ASSUMPTION_FAMILY_"
    "SELECTION_ONLY"
)
RN_ASSUMP_005_CLOSEOUT_RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_renormalization_assumption_reduction_closeout_result_review_"
    "accepts_renormalization_rows_and_authorizes_next_assumption_family_"
    "selection_only"
)
STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_SURFACE = (
    "formal/toe_formal/ToeFormal/Bridges/"
    "QFT_GR_StateDomainAssumptionReductionPacket.lean"
)
STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_REPORT = (
    "formal/docs/release/"
    "QFT_GR_STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_20260607_v0.json"
)
STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_TOOL = (
    "formal/python/tools/"
    "qft_gr_state_domain_assumption_reduction_packet_report.py"
)
STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_TOKEN = (
    "QFT_GR_STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_PREPARED_WITH_NO_"
    "CONSERVATION_WITNESS_OR_SEAM_CLOSURE"
)
STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_CLASSIFICATION = (
    "qft_gr_state_domain_assumption_reduction_packet_prepared_with_no_"
    "conservation_witness_or_seam_closure"
)

EXPECTED_ALLOWED_STATUSES = [
    "active",
    "retained",
    "paused",
    "deferred",
    "blocked",
    "authorized_reopen",
    "not_authorized",
    "archived",
]

EXPECTED_LEGAL_TRANSITIONS = {
    "active": ["retained", "paused", "blocked", "archived"],
    "retained": ["paused", "authorized_reopen", "archived"],
    "paused": ["authorized_reopen", "archived"],
    "authorized_reopen": ["active", "paused"],
    "blocked": ["paused", "authorized_reopen", "archived"],
}

EXPECTED_FRESH_DELTA_KINDS = {
    "new_theorem",
    "counterexample",
    "dependency_graph_change",
    "stronger_evidence_object",
    "failed_assumption_refutation",
}

REQUIRED_CONTROL_IDS = {
    "scalar_post_capstone_anti_loop",
    "strict_nonclaim_boundary",
    "post_sweep_queue_discipline",
    "cross_pillar_protocol",
    "bounded_slice_stop_conditions",
    "recovery_freeze",
    "generated_first_controls",
    "admissibility_manifest_blocked_by_default",
    "checkpoint_ladder_hygiene",
    "release_gate_truth",
    "fresh_delta_gate",
    "workstream_state_machine",
    "dependency_cycle_detector",
    "attempt_budget",
    "authority_growth_budget",
    "promotion_escrow",
    "existing_one_shot_no_loop_family",
}

PROMOTION_ESCROW_TARGETS = {
    "phase2_authorization",
    "seam_closure",
    "master_action_promotion",
    "governance_manifest_enrollment",
}

LOOP_TOKEN_PATTERN = re.compile(
    r"\b[A-Z0-9_]+_(?:NO_LOOP_RULE|ANTI_LOOP_RULE|FREEZE_RULE)_v0\b"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def _registry() -> dict[str, Any]:
    return _read_json(REGISTRY_PATH)


def _controls(payload: dict[str, Any]) -> list[dict[str, Any]]:
    controls = payload.get("controls", [])
    assert isinstance(controls, list) and controls, "Registry must declare controls."
    return controls


def _source_token_index(payload: dict[str, Any]) -> dict[str, list[str]]:
    token_to_controls: dict[str, list[str]] = defaultdict(list)
    for control in _controls(payload):
        for token in control.get("source_tokens", []):
            token_to_controls[str(token)].append(str(control["control_id"]))
    return token_to_controls


def _covered_by_family(payload: dict[str, Any], token: str) -> bool:
    for family in payload.get("token_family_coverage", []):
        pattern = str(family.get("pattern", ""))
        if pattern and re.fullmatch(pattern, token):
            return True
    return False


def _active_edges(payload: dict[str, Any]) -> list[dict[str, str]]:
    active: list[dict[str, str]] = []
    for edge in payload.get("dependency_edges", []):
        status = str(edge.get("status", "active"))
        if status not in {"archived", "waived"}:
            active.append({key: str(edge[key]) for key in ("from", "to", "status", "evidence")})
    return active


def _find_cycles(edges: list[dict[str, str]]) -> list[list[str]]:
    graph: dict[str, list[str]] = defaultdict(list)
    for edge in edges:
        graph[edge["from"]].append(edge["to"])

    cycles: list[list[str]] = []
    visiting: list[str] = []
    visited: set[str] = set()

    def visit(node: str) -> None:
        if node in visiting:
            cycles.append(visiting[visiting.index(node) :] + [node])
            return
        if node in visited:
            return
        visiting.append(node)
        for target in graph.get(node, []):
            visit(target)
        visiting.pop()
        visited.add(node)

    for source in sorted(graph):
        visit(source)
    return cycles


def test_loop_control_registry_schema_and_core_controls() -> None:
    payload = _registry()

    assert payload["schema_id"] == "LOOP_CONTROL_REGISTRY_v0"
    assert payload["schema_version"] == 0
    assert payload["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert "not enrolled in GOVERNANCE_TEST_MANIFEST_v1.json" in payload["authority_boundary"]
    assert "no Phase 2 authorization" in payload["non_claim_boundary"]

    assert payload["allowed_statuses"] == EXPECTED_ALLOWED_STATUSES
    assert payload["legal_transitions"] == EXPECTED_LEGAL_TRANSITIONS
    assert set(payload["fresh_delta_kinds"]) == EXPECTED_FRESH_DELTA_KINDS
    assert payload["defaults"]["max_consecutive_slices_per_retained_blocker"] == 2
    assert payload["defaults"]["queue_cap"] == 3

    controls = _controls(payload)
    control_ids = {str(control["control_id"]) for control in controls}
    assert REQUIRED_CONTROL_IDS <= control_ids

    allowed_statuses = set(payload["allowed_statuses"])
    for control in controls:
        assert control["status"] in allowed_statuses
        assert isinstance(control.get("max_attempts"), int)
        assert control["max_attempts"] >= 0
        assert "validation_command" in control
        if control.get("fresh_delta_required"):
            assert control.get("allowed_reopen_conditions"), control["control_id"]

    fresh_delta_gate = next(c for c in controls if c["control_id"] == "fresh_delta_gate")
    assert set(fresh_delta_gate["allowed_reopen_conditions"]) == EXPECTED_FRESH_DELTA_KINDS
    assert fresh_delta_gate["no_delta_action"] == "rotate_or_defer"

    attempt_budget = next(c for c in controls if c["control_id"] == "attempt_budget")
    assert attempt_budget["max_attempts"] == 2
    assert attempt_budget["forced_action_on_exhaustion"] == "pause_and_cross_pillar_review"

    authority_growth = next(c for c in controls if c["control_id"] == "authority_growth_budget")
    assert authority_growth["budget"]["max_new_governed_pytests"] == 0
    assert authority_growth["budget"]["max_generated_output_edits"] == 0
    assert authority_growth["budget"]["cannot_become_active_science"] is True

    escrow = payload["promotion_escrow"]
    assert escrow["required_steps"] == ["declaration_commit", "independent_validation_commit"]
    assert set(escrow["targets"]) == PROMOTION_ESCROW_TARGETS
    assert escrow["current_tranche_governance_manifest_enrollment"] == "not_authorized"


def test_loop_and_freeze_tokens_are_covered_without_contradictory_ownership() -> None:
    payload = _registry()
    token_index = _source_token_index(payload)

    duplicated = {token: owners for token, owners in token_index.items() if len(owners) > 1}
    assert not duplicated, "Loop-control source token(s) have multiple owners: " + repr(duplicated)

    extracted_tokens: set[str] = set()
    for path in TOKEN_SOURCE_PATHS:
        extracted_tokens.update(LOOP_TOKEN_PATTERN.findall(_read(path)))

    assert extracted_tokens, "Expected loop/freeze rule tokens on canonical surfaces."
    uncovered = sorted(
        token for token in extracted_tokens if token not in token_index and not _covered_by_family(payload, token)
    )
    assert not uncovered, "Loop/freeze token(s) missing registry coverage: " + ", ".join(uncovered)

    family_ids = {family["family_id"] for family in payload["token_family_coverage"]}
    assert family_ids == {
        "all_no_loop_rule_tokens",
        "all_anti_loop_rule_tokens",
        "all_freeze_rule_tokens",
    }


def test_lean_frontier_blockers_targets_and_citation_boundaries_are_registered() -> None:
    payload = _registry()
    registered_blockers = set(payload["retained_blocker_coverage"])
    registered_targets = set(payload["next_strict_target_coverage"])
    registered_citation_ids = set(payload["citation_boundary_coverage"])

    frontier_text = _read(CROSS_PILLAR_FRONTIER_PATH)
    master_text = _read(MASTER_ACTION_FRONTIER_PATH)
    queue_text = _read(POST_SWEEP_QUEUE_PATH)

    parsed_blockers = set(
        re.findall(r"retained_blocker\s*:=\s*\"([^\"]+)\"", frontier_text + queue_text)
    )
    parsed_citation_ids = set(
        re.findall(r"retained_assumption_id\s*:=\s*\"([^\"]+)\"", master_text)
    )
    parsed_next_targets = set(
        re.findall(r"next_strict_slice\s*:=\s*\"([^\"]+)\"", frontier_text)
    )

    assert parsed_blockers <= registered_blockers
    assert parsed_citation_ids <= registered_citation_ids
    assert parsed_next_targets <= registered_targets

    allowed_scopes = re.findall(r"allowed_citation_scope\s*:=\s*\"([^\"]+)\"", master_text)
    forbidden_scopes = re.findall(r"forbidden_promotion_scope\s*:=\s*\"([^\"]+)\"", master_text)
    assert len(allowed_scopes) == len(parsed_citation_ids)
    assert len(forbidden_scopes) == len(parsed_citation_ids)
    assert all("no" in scope.lower() for scope in forbidden_scopes)


def test_dependency_edges_are_acyclic_unless_archived_or_waived() -> None:
    payload = _registry()
    edges = _active_edges(payload)

    for edge in edges:
        assert edge["from"] != edge["to"], f"Self-cycle dependency edge: {edge}"
        assert (REPO_ROOT / edge["evidence"]).exists(), f"Missing dependency evidence: {edge}"

    cycles = _find_cycles(edges)
    assert not cycles, "Unwaived dependency cycle(s) detected: " + repr(cycles)
    assert payload["cycle_waivers"] == []


def test_post_sweep_queue_cap_and_nonpromotion_boundary_remain_pinned() -> None:
    payload = _registry()
    queue_text = _read(POST_SWEEP_QUEUE_PATH)

    ranks = [int(value) for value in re.findall(r"rank\s*:=\s*(\d+)", queue_text)]
    slice_ids = re.findall(r"slice_id\s*:=\s*\"([^\"]+)\"", queue_text)
    blockers = re.findall(r"retained_blocker\s*:=\s*\"([^\"]+)\"", queue_text)
    validation_targets = re.findall(r"validation_target\s*:=\s*\"([^\"]+)\"", queue_text)

    assert ranks == [1, 2, 3]
    assert len(slice_ids) == payload["defaults"]["queue_cap"] == 3
    assert len(blockers) == len(slice_ids)
    assert len(validation_targets) == len(slice_ids)

    assertions = payload["non_promotion_assertions"]
    assert assertions == {
        "phase2_authorized": False,
        "seam_closure_claimed": False,
        "master_action_promoted": False,
        "empirical_claimed": False,
        "governance_manifest_enrollment_authorized": False,
    }

    state_text = _read(REPO_ROOT / "State_of_the_Theory.md")
    roadmap_text = _read(REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md")
    readme_text = _read(REPO_ROOT / "README.md")
    for text in (state_text, roadmap_text):
        assert "STRICT_PHYSICS_NONCLAIM_BOUNDARY_v0" in text
        assert "NO_PHASE2_AUTHORIZATION_NO_MASTER_ACTION_PROMOTION_NO_SEAM_CLOSURE_NO_EMPIRICAL_CLAIM" in text
    assert "no theorem discharge" in readme_text
    assert "Phase 2 is not authorized" in readme_text


def test_active_result_review_target_is_pending_and_latest_surface_matches_execution_layer() -> None:
    payload = _registry()
    live_target = payload["current_target_state"]["live_next_target"]
    active = [item for item in payload["workstreams"] if item["status"] == "active"]
    assert len(active) == 1
    workstream = active[0]

    if "_result" in live_target and workstream.get("result_review_target") == live_target:
        assert workstream.get("result_review_accepted") != "yes"
        assert workstream.get("result_review_completed") != "yes"
        assert workstream.get("result_review_pending") == "yes"

    if live_target == RN_ASSUMP_005_ATTEMPT_LIVE_RESULT_REVIEW_TARGET:
        assert workstream["latest_surface"] == (
            "qft_gr_renormalization_operator_domain_compatibility_assumption_"
            "reduction_attempt_v0"
        )
        assert workstream["latest_surface_evidence"] == RN_ASSUMP_005_ATTEMPT_SURFACE
        assert workstream["latest_surface_report"] == RN_ASSUMP_005_ATTEMPT_REPORT
        assert workstream["latest_surface_token"] == RN_ASSUMP_005_ATTEMPT_TOKEN
        assert workstream["latest_surface_tool"] == RN_ASSUMP_005_ATTEMPT_TOOL
        assert workstream["result_surface"] == RN_ASSUMP_005_ATTEMPT_SURFACE
        assert workstream["result_report"] == RN_ASSUMP_005_ATTEMPT_REPORT
        assert workstream["result_token"] == RN_ASSUMP_005_ATTEMPT_TOKEN
        assert workstream["selected_next_target"] == live_target
        assert workstream["selected_next_target_kind"] == "result_review"
        assert workstream["selected_next_authorization_token"] == RN_ASSUMP_005_ATTEMPT_TOKEN

    if live_target == RN_ASSUMP_005_CLOSEOUT_PREPARATION_TARGET:
        assert workstream["consumed_target"] == RN_ASSUMP_005_ATTEMPT_RESULT_REVIEW_TARGET
        assert workstream["latest_surface"] == (
            "qft_gr_renormalization_operator_domain_compatibility_assumption_"
            "reduction_attempt_result_review_v0"
        )
        assert workstream["latest_surface_evidence"] == (
            RN_ASSUMP_005_ATTEMPT_RESULT_REVIEW_SURFACE
        )
        assert workstream["latest_surface_report"] == (
            RN_ASSUMP_005_ATTEMPT_RESULT_REVIEW_REPORT
        )
        assert workstream["latest_surface_token"] == (
            RN_ASSUMP_005_ATTEMPT_RESULT_REVIEW_TOKEN
        )
        assert workstream["latest_surface_tool"] == RN_ASSUMP_005_ATTEMPT_RESULT_REVIEW_TOOL
        assert workstream["result_review_accepted"] == "yes"
        assert workstream["result_review_completed"] == "yes"
        assert workstream["result_review_pending"] == "no"
        assert workstream["result_review_target"] == RN_ASSUMP_005_ATTEMPT_RESULT_REVIEW_TARGET
        assert workstream["result_review_surface"] == (
            RN_ASSUMP_005_ATTEMPT_RESULT_REVIEW_SURFACE
        )
        assert workstream["result_review_report"] == (
            RN_ASSUMP_005_ATTEMPT_RESULT_REVIEW_REPORT
        )
        assert workstream["result_review_token"] == (
            RN_ASSUMP_005_ATTEMPT_RESULT_REVIEW_TOKEN
        )
        assert workstream["result_review_classification"] == (
            RN_ASSUMP_005_ATTEMPT_RESULT_REVIEW_CLASSIFICATION
        )
        assert workstream["selected_next_target"] == live_target
        assert workstream["selected_next_target_kind"] == (
            "qft_gr_renormalization_assumption_reduction_closeout_packet_preparation"
        )
        assert workstream["selected_next_authorization_token"] == (
            RN_ASSUMP_005_ATTEMPT_RESULT_REVIEW_TOKEN
        )

    if live_target == RN_ASSUMP_005_CLOSEOUT_RESULT_REVIEW_TARGET:
        assert workstream["consumed_target"] == RN_ASSUMP_005_CLOSEOUT_PREPARATION_TARGET
        assert workstream["latest_surface"] == (
            "qft_gr_renormalization_assumption_reduction_closeout_packet_v0"
        )
        assert workstream["latest_surface_evidence"] == RN_ASSUMP_005_CLOSEOUT_PACKET_SURFACE
        assert workstream["latest_surface_report"] == RN_ASSUMP_005_CLOSEOUT_PACKET_REPORT
        assert workstream["latest_surface_token"] == RN_ASSUMP_005_CLOSEOUT_PACKET_TOKEN
        assert workstream["latest_surface_tool"] == RN_ASSUMP_005_CLOSEOUT_PACKET_TOOL
        assert workstream["result_classification"] == (
            RN_ASSUMP_005_CLOSEOUT_PACKET_CLASSIFICATION
        )
        assert workstream["result_review_accepted"] == "no"
        assert workstream["result_review_completed"] == "no"
        assert workstream["result_review_pending"] == "yes"
        assert workstream["result_review_target"] == RN_ASSUMP_005_CLOSEOUT_RESULT_REVIEW_TARGET
        assert workstream["result_surface"] == RN_ASSUMP_005_CLOSEOUT_PACKET_SURFACE
        assert workstream["result_report"] == RN_ASSUMP_005_CLOSEOUT_PACKET_REPORT
        assert workstream["result_token"] == RN_ASSUMP_005_CLOSEOUT_PACKET_TOKEN
        assert workstream["selected_next_target"] == live_target
        assert workstream["selected_next_target_kind"] == (
            "qft_gr_renormalization_assumption_reduction_closeout_packet_result_review"
        )
        assert workstream["selected_next_authorization_token"] == (
            RN_ASSUMP_005_CLOSEOUT_PACKET_TOKEN
        )

    if live_target == STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_TARGET:
        assert workstream["consumed_target"] == RN_ASSUMP_005_CLOSEOUT_RESULT_REVIEW_TARGET
        assert workstream["latest_surface"] == (
            "qft_gr_renormalization_assumption_reduction_closeout_packet_"
            "result_review_v0"
        )
        assert workstream["latest_surface_evidence"] == (
            RN_ASSUMP_005_CLOSEOUT_RESULT_REVIEW_SURFACE
        )
        assert workstream["latest_surface_report"] == (
            RN_ASSUMP_005_CLOSEOUT_RESULT_REVIEW_REPORT
        )
        assert workstream["latest_surface_token"] == (
            RN_ASSUMP_005_CLOSEOUT_RESULT_REVIEW_TOKEN
        )
        assert workstream["latest_surface_tool"] == (
            RN_ASSUMP_005_CLOSEOUT_RESULT_REVIEW_TOOL
        )
        assert workstream["result_review_accepted"] == "yes"
        assert workstream["result_review_completed"] == "yes"
        assert workstream["result_review_pending"] == "no"
        assert workstream["result_review_target"] == (
            RN_ASSUMP_005_CLOSEOUT_RESULT_REVIEW_TARGET
        )
        assert workstream["result_review_surface"] == (
            RN_ASSUMP_005_CLOSEOUT_RESULT_REVIEW_SURFACE
        )
        assert workstream["result_review_report"] == (
            RN_ASSUMP_005_CLOSEOUT_RESULT_REVIEW_REPORT
        )
        assert workstream["result_review_token"] == (
            RN_ASSUMP_005_CLOSEOUT_RESULT_REVIEW_TOKEN
        )
        assert workstream["result_review_classification"] == (
            RN_ASSUMP_005_CLOSEOUT_RESULT_REVIEW_CLASSIFICATION
        )
        assert workstream[
            "renormalization_assumption_reduction_closeout_packet_selected_next_target"
        ] == RN_ASSUMP_005_CLOSEOUT_RESULT_REVIEW_TARGET
        assert workstream[
            "renormalization_assumption_reduction_closeout_packet_result_review_selected_next_target"
        ] == live_target
        assert workstream[
            "renormalization_assumption_reduction_closeout_packet_selected_next_target"
        ] != workstream[
            "renormalization_assumption_reduction_closeout_packet_result_review_selected_next_target"
        ]
        assert workstream["selected_next_target"] == live_target
        assert workstream["selected_next_target_kind"] == (
            "qft_gr_state_domain_assumption_reduction_packet_preparation"
        )
        assert workstream["selected_next_authorization_token"] == (
            RN_ASSUMP_005_CLOSEOUT_RESULT_REVIEW_TOKEN
        )
        assert workstream["state_domain_assumption_reduction_packet_authorized"] == "yes"

    if live_target == STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TARGET:
        assert workstream["consumed_target"] == STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_TARGET
        assert workstream["latest_surface"] == (
            "qft_gr_state_domain_assumption_reduction_packet_v0"
        )
        assert workstream["latest_surface_evidence"] == (
            STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_SURFACE
        )
        assert workstream["latest_surface_report"] == (
            STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_REPORT
        )
        assert workstream["latest_surface_token"] == (
            STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_TOKEN
        )
        assert workstream["latest_surface_tool"] == (
            STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_TOOL
        )
        assert workstream["result_classification"] == (
            STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_CLASSIFICATION
        )
        assert workstream["result_review_accepted"] == "no"
        assert workstream["result_review_completed"] == "no"
        assert workstream["result_review_pending"] == "yes"
        assert workstream["result_review_target"] == (
            STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_RESULT_REVIEW_TARGET
        )
        assert workstream["result_surface"] == (
            STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_SURFACE
        )
        assert workstream["result_report"] == (
            STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_REPORT
        )
        assert workstream["result_token"] == (
            STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_TOKEN
        )
        assert workstream["selected_next_target"] == live_target
        assert workstream["selected_next_target_kind"] == (
            "qft_gr_state_domain_assumption_reduction_packet_result_review"
        )
        assert workstream["selected_next_authorization_token"] == (
            STATE_DOMAIN_ASSUMPTION_REDUCTION_PACKET_TOKEN
        )
        assert workstream["state_domain_assumption_reduction_packet_prepared"] == "yes"
        assert workstream["state_domain_assumption_reduction_packet_selected_next_target"] == (
            live_target
        )


def test_loop_control_gate_is_focused_not_governance_manifest_enrolled() -> None:
    payload = _registry()
    manifest_text = _read(GOVERNANCE_MANIFEST_PATH)

    assert payload["focused_gate"] == "formal/python/tests/test_loop_control_registry_v0_gate.py"
    assert "test_loop_control_registry_v0_gate.py" not in manifest_text

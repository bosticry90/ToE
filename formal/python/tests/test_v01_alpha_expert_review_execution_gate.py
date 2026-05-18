from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_expert_review_execution_report import (
    DEFAULT_CAPTURED_AT_UTC,
    NEXT_TARGET,
    OUTCOME_ID,
    REPORT_POINTER,
    build_execution,
)


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
RESULT_REVIEW_PATH = (
    RELEASE_DIR / "V01_ALPHA_EXPERT_REVIEW_EXECUTION_PACKET_RESULT_REVIEW_20260515_v0.json"
)
EXECUTION_PATH = RELEASE_DIR / "V01_ALPHA_EXPERT_REVIEW_EXECUTION_20260515_v0.json"
REPORT_PATH = REPO_ROOT / REPORT_POINTER
TOOL_PATH = REPO_ROOT / "formal" / "python" / "tools" / "v01_alpha_expert_review_execution_report.py"
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
LEAN_EXECUTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "V01ExpertReviewExecution.lean"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"

FORBIDDEN_TRUE_KEYS = [
    "release_packet_assembled",
    "v01_alpha_marked_ready",
    "lean_theorem_debt_discharged",
    "axiom_spec_backed_debt_reduced",
    "axiom_spec_backed_debt_reduced_by_documentation",
    "proof_debt_reduced",
    "retained_assumptions_discharged",
    "theorem_discharge_authorized",
    "blocker_movement_authorized",
    "lane_reopen_authorized",
    "phase2_authorized",
    "seam_closure_authorized",
    "empirical_validation_authorized",
    "master_action_promotion_authorized",
    "claim_promotion_authorized",
    "computational_physics_execution_surface_opened",
]

PROHIBITED_POSITIVE_PHRASES = [
    "release packet assembled true",
    "v0.1-alpha marked ready",
    "Lean theorem debt discharged true",
    "proof debt reduced true",
    "retained assumptions discharged true",
    "Phase 2 authorized true",
    "seam closure authorized true",
    "empirical validation authorized true",
    "master action promoted",
    "claim promoted",
    "release packet ready",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_v01_alpha_expert_review_execution_files_exist() -> None:
    assert RESULT_REVIEW_PATH.exists()
    assert EXECUTION_PATH.exists()
    assert REPORT_PATH.exists()
    assert TOOL_PATH.exists()
    assert LEAN_EXECUTION_PATH.exists()
    assert LEAN_INDEX_PATH.exists()


def test_v01_alpha_expert_review_execution_consumes_authorizing_result_review() -> None:
    payload = _json(EXECUTION_PATH)
    assert payload["schema_id"] == "V01_ALPHA_EXPERT_REVIEW_EXECUTION_20260515_v0"
    assert payload["execution_id"] == "V01_ALPHA_EXPERT_REVIEW_EXECUTION_v0"
    assert payload["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert payload["classification"] == "P-POLICY/nonclaim"
    assert payload["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert payload["executed"] is True
    assert payload["outcome_id"] == OUTCOME_ID
    assert payload["consumed_target"] == "execute_v01_alpha_expert_review_packet"
    assert payload["consumes_result_review"] == (
        "V01_ALPHA_EXPERT_REVIEW_EXECUTION_PACKET_RESULT_REVIEW_v0"
    )
    assert payload["consumes_result_review_pointer"] == (
        "formal/docs/release/V01_ALPHA_EXPERT_REVIEW_EXECUTION_PACKET_RESULT_REVIEW_20260515_v0.json"
    )
    assert payload["source_execution_packet"] == "V01_ALPHA_EXPERT_REVIEW_EXECUTION_PACKET_v0"
    assert payload["source_expert_review_packet"] == "V01_ALPHA_EXPERT_REVIEW_PACKET_v0"
    assert payload["execution_report_pointer"] == REPORT_POINTER


def test_v01_alpha_expert_review_execution_is_bounded_to_prepared_scope() -> None:
    payload = _json(EXECUTION_PATH)
    assert payload["execution_scope"] == "BOUNDED_EXPERT_REVIEW_EXECUTION_ONLY_NO_RELEASE_PROMOTION"
    assert payload["review_scope_executed"] is True
    assert payload["expert_review_executed"] is True
    assert payload["expert_review_findings_recorded"] is True
    assert payload["expert_review_result_packet_produced"] is True
    boundary = payload["authorization_boundary"]
    assert boundary["expert_review_execution_completed"] is True
    assert boundary["expert_review_output_is_evidence_only"] is True
    assert boundary["release_readiness_authorized"] is False
    assert boundary["release_packet_assembly_authorized"] is False
    assert boundary["theorem_or_proof_debt_discharge_authorized"] is False
    assert boundary["retained_assumption_discharge_authorized"] is False
    assert boundary["phase2_authorized"] is False
    assert boundary["seam_closure_authorized"] is False
    assert boundary["empirical_validation_authorized"] is False
    assert boundary["master_action_promotion_authorized"] is False


def test_v01_alpha_expert_review_execution_records_required_findings() -> None:
    payload = _json(EXECUTION_PATH)
    findings = payload["review_findings"]
    assert len(findings["release_blocking_dependency_findings"]) == 6
    assert len(findings["documentation_only_dependency_findings"]) == 3
    assert len(findings["expert_review_required_dependency_findings"]) == 6
    assert findings["retained_assumption_findings"]["row_count"] == 22
    assert findings["retained_assumption_findings"]["remain_retained"] is True
    assert findings["retained_assumption_findings"]["discharged_by_this_execution_count"] == 0
    assert findings["proof_debt_findings"]["class_count"] == 3
    assert findings["proof_debt_findings"]["proof_debt_reduced_by_this_execution"] is False
    assert findings["lean_dependency_findings"]["dependency_row_count"] == 6
    assert findings["lean_dependency_findings"]["theorem_debt_discharged_by_this_execution"] is False
    assert (
        findings["axiom_spec_backed_ledger_findings"][
            "axiom_spec_backed_debt_reduced_by_this_execution"
        ]
        is False
    )
    assert len(findings["unresolved_theorem_seam_master_action_blocker_findings"]) == 6

    summary = payload["finding_summary"]
    assert summary["release_blocking_dependency_finding_count"] == 6
    assert summary["documentation_only_dependency_finding_count"] == 3
    assert summary["expert_review_required_dependency_finding_count"] == 6
    assert summary["retained_assumption_finding_count"] == 22
    assert summary["proof_debt_class_count"] == 3
    assert summary["release_promotion_recommended"] is False
    assert summary["release_readiness_adjudication_pending"] is True


def test_v01_alpha_expert_review_execution_forbidden_effects_false() -> None:
    payload = _json(EXECUTION_PATH)
    forbidden = payload["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_TRUE_KEYS)
    for key in FORBIDDEN_TRUE_KEYS:
        assert forbidden[key] is False

    assert payload["release_packet_assembled"] is False
    assert payload["v01_alpha_marked_ready"] is False
    assert payload["lean_theorem_debt_discharged"] is False
    assert payload["axiom_spec_backed_debt_reduced"] is False
    assert payload["axiom_spec_backed_debt_reduced_by_documentation"] is False
    assert payload["proof_debt_reduced"] is False
    assert payload["retained_assumptions_discharged"] is False
    assert payload["validation_claim_authorized"] is False

    combined = (
        json.dumps(payload, sort_keys=True)
        + "\n"
        + _read(RESULT_REVIEW_PATH)
        + "\n"
        + _read(REPORT_PATH)
        + "\n"
        + _read(PHYSICS_ROADMAP_PATH)
    )
    for phrase in PROHIBITED_POSITIVE_PHRASES:
        assert phrase not in combined


def test_v01_alpha_expert_review_execution_selects_result_review_only() -> None:
    payload = _json(EXECUTION_PATH)
    assert payload["selected_next_target"] == NEXT_TARGET
    assert payload["selected_next_target_kind"] == "result_review_only"
    assert payload["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in payload["candidate_next_targets"]} == {
        "review_v01_alpha_expert_review_execution_result": "selected",
        "prepare_v01_alpha_release_readiness_adjudication_packet": "deferred",
        "remediate_v01_alpha_expert_review_execution": "deferred",
    }


def test_v01_alpha_expert_review_execution_acceptance_and_determinism() -> None:
    payload = _json(EXECUTION_PATH)
    for key, value in payload["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_execution(
        result_review_path=RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_execution(
        result_review_path=RESULT_REVIEW_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    assert payload == generated_1


def test_v01_alpha_expert_review_execution_is_pinned() -> None:
    report_text = _read(REPORT_PATH)
    roadmap_text = _read(PHYSICS_ROADMAP_PATH)
    refs = [
        "V01_ALPHA_EXPERT_REVIEW_EXECUTION_v0",
        "formal/docs/release/V01_ALPHA_EXPERT_REVIEW_EXECUTION_20260515_v0.json",
        "formal/docs/paper/V01_ALPHA_EXPERT_REVIEW_EXECUTION_REPORT_v0.md",
        "formal/python/tools/v01_alpha_expert_review_execution_report.py",
        "formal/python/tests/test_v01_alpha_expert_review_execution_gate.py",
        OUTCOME_ID,
        "review_v01_alpha_expert_review_execution_result",
    ]
    for ref in refs:
        assert ref in roadmap_text
    for ref in [OUTCOME_ID, "review_v01_alpha_expert_review_execution_result"]:
        assert ref in report_text

    lean_text = _read(LEAN_EXECUTION_PATH)
    index_text = _read(LEAN_INDEX_PATH)
    assert OUTCOME_ID in lean_text
    assert "V01ExpertReviewExecution" in index_text
    assert "v01_expert_review_execution_does_not_promote_release" in index_text

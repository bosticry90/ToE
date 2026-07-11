from __future__ import annotations

import hashlib
import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_release_packet_gap_review_report import (
    DEFAULT_CAPTURED_AT_UTC,
    EXPECTED_CHECKS,
    NEXT_TARGET,
    OUTCOME_ID,
    build_gap_review,
)


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_DIR = REPO_ROOT / "formal" / "docs" / "release"
SELECTION_PATH = (
    RELEASE_DIR / "MAIN_PHYSICS_TARGET_SELECTION_AFTER_COMPUTATIONAL_PHYSICS_CLOSEOUT_20260515_v0.json"
)
GAP_REVIEW_PATH = RELEASE_DIR / "V01_ALPHA_RELEASE_PACKET_GAP_REVIEW_20260515_v0.json"
TOOL_PATH = REPO_ROOT / "formal" / "python" / "tools" / "v01_alpha_release_packet_gap_review_report.py"
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
FROZEN_GAP_REVIEW_SHA256 = "cf9ea10e8666e1925dc0950e0a9ef2ecb40af7d887810b5bee5002def984ae04"

FORBIDDEN_TRUE_KEYS = [
    "computational_physics_execution_surface_opened",
    "release_packet_assembly_authorized",
    "v01_alpha_completion_authorized",
    "master_action_promotion_authorized",
    "pillar_completion_authorized",
    "seam_closure_authorized",
    "phase2_authorized",
    "empirical_adequacy_claim_authorized",
    "canonical_toe_claim_authorized",
    "qft_gr_source_map_closure_authorized",
    "theorem_discharge_authorized",
    "claim_promotion_authorized",
]

PROHIBITED_POSITIVE_PHRASES = [
    "computational physics execution opened",
    "release packet assembled true",
    "release packet assembly authorized true",
    "v0.1-alpha is complete",
    "master action promoted",
    "seam closure authorized",
    "Phase 2 authorized",
    "empirical adequacy confirmed",
    "theorem discharged by computation",
    "claim promoted",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_v01_alpha_release_packet_gap_review_files_exist() -> None:
    assert SELECTION_PATH.exists()
    assert GAP_REVIEW_PATH.exists()
    assert TOOL_PATH.exists()


def test_v01_alpha_release_packet_gap_review_consumes_return_to_main_selection() -> None:
    payload = _json(GAP_REVIEW_PATH)
    assert payload["schema_id"] == "V01_ALPHA_RELEASE_PACKET_GAP_REVIEW_20260515_v0"
    assert payload["review_id"] == "V01_ALPHA_RELEASE_PACKET_GAP_REVIEW_v0"
    assert payload["status"] == "ACTIVE_NONLIVE_NONCLAIM"
    assert payload["classification"] == "P-POLICY/nonclaim"
    assert payload["captured_at_utc"] == DEFAULT_CAPTURED_AT_UTC
    assert payload["prepared"] is True
    assert payload["outcome_id"] == OUTCOME_ID
    assert payload["consumed_target"] == "prepare_v01_alpha_release_packet_gap_review"
    assert (
        payload["consumes_selection"]
        == "MAIN_PHYSICS_TARGET_SELECTION_AFTER_COMPUTATIONAL_PHYSICS_CLOSEOUT_v0"
    )
    assert payload["consumes_selection_pointer"] == (
        "formal/docs/release/MAIN_PHYSICS_TARGET_SELECTION_AFTER_COMPUTATIONAL_PHYSICS_CLOSEOUT_20260515_v0.json"
    )
    assert payload["computational_physics_stack_status"] == "CLOSED_BOUNDED_NONCLAIM"
    assert payload["release_scope_confirmed"] == "FULL_PILLAR_FULL_SEAM_RELEASE_STANDARD"
    assert payload["gap_review_scope"] == "REVIEW_RELEASE_PACKET_GAPS_ONLY_NO_RELEASE_PACKET_ASSEMBLY"


def test_v01_alpha_release_packet_gap_review_reviews_only_release_packet_gaps() -> None:
    payload = _json(GAP_REVIEW_PATH)
    assert payload["review_summary"] == {
        "gap_row_count": 9,
        "coverage_row_count": 13,
        "claim_evidence_row_count": 5,
        "equation_row_count": 3,
        "blocker_row_count": 4,
        "lean_dependency_audit_row_count": 6,
        "lean_dependency_audit_pending_row_count": 6,
        "lean_release_index_check_count": 8,
        "primary_gap": "LEAN_DEPENDENCY_AUDIT_CAPTURE_AND_EXPERT_REVIEW_PACKET_NOT_READY",
        "release_packet_review_ready": False,
    }
    assert [row["source_check"] for row in payload["gap_rows"]] == EXPECTED_CHECKS
    assert all(row["blocks_release_packet_assembly"] is True for row in payload["gap_rows"])
    assert {
        row["check_id"]: row["status"] for row in payload["gap_rows"]
    } == {
        "pillar_seam_coverage_ledger_completeness": "seeded_structurally_complete",
        "claim_evidence_ledger_completeness": "seeded_with_current_release_labels",
        "equation_ledger_completeness": "seeded_minimal_equation_surface",
        "blocker_ledger_completeness": "seeded_active_blockers_visible",
        "lean_release_index_audit_rows": "index_present_audit_rows_pending",
        "public_summary_readiness": "partial_manifest_enrolled_not_complete_language_present",
        "expert_review_packet_readiness": "not_prepared_v0",
        "remaining_unmigrated_release_facing_labels": "requires_scoped_exception_audit_v0",
        "remaining_draft_deferred_rows": "deferred_release_assembly_and_review_packet_gaps_remain",
    }


def test_v01_alpha_release_packet_gap_review_artifact_pointers_exist() -> None:
    payload = _json(GAP_REVIEW_PATH)
    for pointer in payload["reviewed_release_artifacts"].values():
        assert (REPO_ROOT / pointer).exists(), f"Missing reviewed artifact pointer: {pointer}"


def test_v01_alpha_release_packet_gap_review_preserves_nonclaim_boundaries() -> None:
    payload = _json(GAP_REVIEW_PATH)
    assert payload["release_packet_assembled"] is False
    assert payload["release_packet_assembly_authorized"] is False
    assert payload["v01_alpha_public_release_completion_authorized"] is False
    forbidden = payload["forbidden_effect_status"]
    assert sorted(forbidden) == sorted(FORBIDDEN_TRUE_KEYS)
    for key in FORBIDDEN_TRUE_KEYS:
        assert forbidden[key] is False

    combined = json.dumps(payload, sort_keys=True) + "\n" + _read(PHYSICS_ROADMAP_PATH)
    for phrase in PROHIBITED_POSITIVE_PHRASES:
        assert phrase not in combined


def test_v01_alpha_release_packet_gap_review_selects_exactly_one_next_target() -> None:
    payload = _json(GAP_REVIEW_PATH)
    assert payload["selected_next_target"] == NEXT_TARGET
    assert payload["selected_next_target_kind"] == "lean_dependency_audit_capture_preparation_only"
    assert payload["selection_count"] == 1
    assert {row["target"]: row["decision"] for row in payload["candidate_next_targets"]} == {
        "prepare_v01_alpha_lean_dependency_audit_capture_packet": "selected",
        "prepare_v01_alpha_expert_review_packet_readiness_audit": "deferred",
        "assemble_v01_alpha_public_release_packet": "blocked",
    }


def test_v01_alpha_release_packet_gap_review_acceptance_criteria_and_determinism() -> None:
    payload = _json(GAP_REVIEW_PATH)
    assert hashlib.sha256(GAP_REVIEW_PATH.read_bytes()).hexdigest() == FROZEN_GAP_REVIEW_SHA256
    for key, value in payload["acceptance_criteria"].items():
        assert value is True, f"Acceptance criterion failed: {key}"

    generated_1 = build_gap_review(
        selection_path=SELECTION_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    generated_2 = build_gap_review(
        selection_path=SELECTION_PATH,
        captured_at_utc=DEFAULT_CAPTURED_AT_UTC,
    )
    assert generated_1 == generated_2
    # The dated artifact is hash-frozen above. The builder intentionally reads
    # mutable public surfaces, so its current output is a separate live
    # diagnostic and must not be mistaken for historical byte regeneration.
    for key in (
        "schema_id",
        "review_id",
        "captured_at_utc",
        "outcome_id",
        "consumed_target",
        "selected_next_target",
        "forbidden_effect_status",
        "acceptance_criteria",
    ):
        assert payload[key] == generated_1[key]
    assert [row["check_id"] for row in payload["gap_rows"]] == [
        row["check_id"] for row in generated_1["gap_rows"]
    ]
    current_rows = {row["check_id"]: row for row in generated_1["gap_rows"]}
    assert generated_1["release_packet_assembled"] is False
    assert generated_1["release_packet_assembly_authorized"] is False
    assert generated_1["v01_alpha_public_release_completion_authorized"] is False
    assert all(value is False for value in generated_1["forbidden_effect_status"].values())
    assert current_rows["public_summary_readiness"]["observed"][
        "not_complete_signal_count"
    ] > 0
    live_legacy_counts = current_rows["remaining_unmigrated_release_facing_labels"][
        "observed"
    ]["legacy_label_signal_counts_on_public_surfaces"]
    assert set(live_legacy_counts) == {"T-PROVED", "T-CONDITIONAL", "DISCHARGED_v0", "LOCKED"}
    assert all(isinstance(count, int) and count >= 0 for count in live_legacy_counts.values())


def test_v01_alpha_release_packet_gap_review_is_pinned_in_physics_roadmap() -> None:
    roadmap_text = _read(PHYSICS_ROADMAP_PATH)
    refs = [
        "V01_ALPHA_RELEASE_PACKET_GAP_REVIEW_v0",
        "formal/docs/release/V01_ALPHA_RELEASE_PACKET_GAP_REVIEW_20260515_v0.json",
        "formal/python/tools/v01_alpha_release_packet_gap_review_report.py",
        "formal/python/tests/test_v01_alpha_release_packet_gap_review_gate.py",
        "V01_ALPHA_RELEASE_PACKET_GAP_REVIEW_PREPARED_AFTER_COMPUTATIONAL_PHYSICS_STACK_CLOSEOUT_WITH_NO_RELEASE_PROMOTION",
        "prepare_v01_alpha_lean_dependency_audit_capture_packet",
    ]
    for ref in refs:
        assert ref in roadmap_text

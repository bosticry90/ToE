from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.strict_physics_state_helpers import (
    assert_current_target_consistent,
    assert_focused_gate_not_manifest_enrolled,
    assert_forbidden_promotions_closed,
    assert_public_surfaces_match_registry,
    workstream,
)


REPO_ROOT = find_repo_root(Path(__file__))
LEAN_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "FullPillarTargetMapRebase.lean"
)
DOC_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "FULL_PILLAR_TARGET_MAP_REBASE_v0.md"
RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRStressEnergyOperatorDomainResultReview.lean"
)
TARGET_MAP_RESULT_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "FullPillarTargetMapRebaseResultReview.lean"
)
TARGET_MAP_RESULT_REVIEW_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "FULL_PILLAR_TARGET_MAP_REBASE_RESULT_REVIEW_20260503_v0.json"
)
REGISTRY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
README_PATH = REPO_ROOT / "README.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STRICT_MAP_PATH = (
    REPO_ROOT / "formal" / "docs" / "lanes" / "STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md"
)

SURFACE_ID = "FULL_PILLAR_TARGET_MAP_REBASE_v0"
NEXT_TARGET = "prepare_full_pillar_target_map_rebase"
RESULT_REVIEW_TARGET = "review_full_pillar_target_map_rebase_result"
SELECTION_TARGET = "select_next_post_rebase_bounded_attack"
SELECTED_POST_REBASE_TARGET = (
    "prepare_qft_gr_state_expectation_functional_semantics_bounded_attack"
)
STATE_EXPECTATION_RESULT_REVIEW_TARGET = (
    "review_qft_gr_state_expectation_functional_semantics_result"
)
CURRENT_LIVE_TARGET = "prepare_qft_gr_renormalized_expectation_value_semantics_bounded_attack"
RESULT_REVIEW_EVIDENCE = str(RESULT_REVIEW_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
LEAN_EVIDENCE = str(LEAN_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
DOC_EVIDENCE = str(DOC_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
TARGET_MAP_RESULT_REVIEW_EVIDENCE = str(
    TARGET_MAP_RESULT_REVIEW_PATH.relative_to(REPO_ROOT)
).replace("\\", "/")
TARGET_MAP_RESULT_REVIEW_REPORT = str(
    TARGET_MAP_RESULT_REVIEW_REPORT_PATH.relative_to(REPO_ROOT)
).replace("\\", "/")

REQUIRED_SCHEMA = [
    "row_id",
    "domain",
    "target_type",
    "current_local_result",
    "full_target",
    "route_source",
    "completion_scale",
    "claim_posture",
    "retained_blocker",
    "semantic_status",
    "next_admissible_action",
    "not_authorized",
]
ROUTE_SOURCE_VALUES = {
    "derived",
    "conditional",
    "supplied",
    "residual_only",
    "refuted",
    "retained",
    "not_authorized",
}
COMPLETION_SCALE_VALUES = {"local", "pillar", "seam", "master_action"}
CLAIM_POSTURE_VALUES = {
    "T-PROVED",
    "T-CONDITIONAL",
    "E-REPRO",
    "P-POLICY/nonclaim",
    "P-POLICY/planning_only",
    "P-POLICY/speculative",
    "B-BLOCKED/not_authorized",
}
EXPECTED_ROWS = {
    "FULL_GR_TARGET_MAP_v0",
    "FULL_QM_TARGET_MAP_v0",
    "FULL_EM_TARGET_MAP_v0",
    "FULL_SR_TARGET_MAP_v0",
    "FULL_SCALAR_QFT_TARGET_MAP_v0",
    "FULL_STAT_TARGET_MAP_v0",
    "FULL_COSMO_TARGET_MAP_v0",
    "FULL_SEAM_QFT_GR_TARGET_MAP_v0",
    "FULL_SEAM_QM_STAT_TARGET_MAP_v0",
    "FULL_SEAM_EM_QFT_TARGET_MAP_v0",
    "FULL_SEAM_SR_COSMO_TARGET_MAP_v0",
    "FULL_SEAM_GR_QM_TARGET_MAP_v0",
    "MASTER_ACTION_FULL_DEPENDENCY_MAP_v0",
}
EXPECTED_SECTION_IDS = {
    "FULL_GR_TARGET_MAP_v0",
    "FULL_QM_TARGET_MAP_v0",
    "FULL_EM_TARGET_MAP_v0",
    "FULL_SR_TARGET_MAP_v0",
    "FULL_SCALAR_QFT_TARGET_MAP_v0",
    "FULL_STAT_TARGET_MAP_v0",
    "FULL_COSMO_TARGET_MAP_v0",
    "FULL_SEAM_COMPLETION_MAP_v0",
    "MASTER_ACTION_FULL_DEPENDENCY_MAP_v0",
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _registry() -> dict[str, Any]:
    return json.loads(_read(REGISTRY_PATH))


def _unquote_cell(cell: str) -> str:
    value = cell.strip()
    if value.startswith("`") and value.endswith("`"):
        return value[1:-1]
    return value


def _target_rows() -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    in_table = False
    headers: list[str] = []
    for line in _read(DOC_PATH).splitlines():
        if line.startswith("| row_id |"):
            in_table = True
            headers = [part.strip() for part in line.strip("|").split("|")]
            continue
        if not in_table:
            continue
        if line.startswith("| ---"):
            continue
        if not line.startswith("|"):
            break
        cells = [_unquote_cell(part) for part in line.strip("|").split("|")]
        assert len(cells) == len(headers), line
        rows.append(dict(zip(headers, cells, strict=True)))
    assert rows, "Target-map rows table was not parsed."
    return rows


def test_target_map_lean_surface_records_schema_and_vocabularies() -> None:
    text = _read(LEAN_PATH)

    for token in {
        SURFACE_ID,
        NEXT_TARGET,
        RESULT_REVIEW_TARGET,
        "FullPillarTargetMapRow",
        "FullPillarTargetDomain",
        "RouteSource",
        "CompletionScale",
        "ClaimPosture",
        "SemanticStatus",
        "fullPillarTargetMapRowsV0",
        "full_pillar_target_map_row_count_v0",
        "full_pillar_target_map_rebase_consumes_selected_target_v0",
        "full_pillar_target_map_rebase_master_action_citation_bound_v0",
        "full_pillar_target_map_rebase_gr_is_local_not_pillar_done_v0",
        "full_pillar_target_map_rebase_qft_gr_route_source_supplied_v0",
        "full_pillar_target_map_rebase_no_full_pillar_completion_claim_v0",
        "full_pillar_target_map_rebase_master_action_not_promoted_v0",
        "full_pillar_target_map_rebase_selected_next_target_v0",
    }:
        assert token in text

    for field in REQUIRED_SCHEMA:
        assert field in text
    for value in ROUTE_SOURCE_VALUES | COMPLETION_SCALE_VALUES | CLAIM_POSTURE_VALUES:
        assert value in text
    for row_id in EXPECTED_ROWS:
        assert row_id in text


def test_consolidated_document_contains_required_sections_and_rows() -> None:
    text = _read(DOC_PATH)

    for field in REQUIRED_SCHEMA:
        assert field in text
    for value in ROUTE_SOURCE_VALUES | COMPLETION_SCALE_VALUES | CLAIM_POSTURE_VALUES:
        assert value in text
    for section_id in EXPECTED_SECTION_IDS:
        assert section_id in text

    rows = _target_rows()
    assert {row["row_id"] for row in rows} == EXPECTED_ROWS
    assert len(rows) == 13


def test_target_rows_satisfy_acceptance_constraints() -> None:
    rows = _target_rows()

    for row in rows:
        assert row["route_source"], row["row_id"]
        assert row["route_source"] in ROUTE_SOURCE_VALUES, row
        assert row["completion_scale"] in COMPLETION_SCALE_VALUES, row
        assert row["claim_posture"] in CLAIM_POSTURE_VALUES, row
        assert row["retained_blocker"], row["row_id"]
        assert row["next_admissible_action"], row["row_id"]
        assert row["not_authorized"], row["row_id"]

        if row["completion_scale"] == "local":
            assert row["target_type"] == "pillar", row
        if row["target_type"] == "pillar":
            assert row["completion_scale"] != "pillar", row
        if "PILLAR_TARGET_OPEN" in row["semantic_status"]:
            assert row["full_target"].strip(), row["row_id"]
        if row["route_source"] == "supplied":
            supplied_text = " ".join(
                [
                    row["current_local_result"],
                    row["full_target"],
                    row["semantic_status"],
                ]
            ).lower()
            assert "supplied" in supplied_text, row["row_id"]

    master = next(row for row in rows if row["row_id"] == "MASTER_ACTION_FULL_DEPENDENCY_MAP_v0")
    assert master["completion_scale"] == "master_action"
    assert master["claim_posture"] == "P-POLICY/nonclaim"
    assert master["semantic_status"] == "MASTER_ACTION_CITATION_BOUND"
    assert master["route_source"] == "not_authorized"
    assert "MASTER_ACTION_CITATION_BOUND" in master["not_authorized"]
    assert "promotion" in master["not_authorized"].lower()


def test_registry_and_public_surfaces_track_target_map_rebase() -> None:
    assert_current_target_consistent()
    assert_forbidden_promotions_closed()
    assert_public_surfaces_match_registry()
    payload = _registry()

    target_map = workstream("full_pillar_target_map_rebase", payload)
    assert target_map["status"] == "paused"
    assert target_map["authorized_next_strict_target"] == RESULT_REVIEW_TARGET
    assert target_map["authorization_evidence"] == RESULT_REVIEW_EVIDENCE
    assert target_map["latest_surface"] == SURFACE_ID
    assert target_map["target_map_evidence"] == LEAN_EVIDENCE
    assert target_map["target_map_document"] == DOC_EVIDENCE
    assert target_map["route_source_required"] == "yes"
    assert target_map["completion_scale_required"] == "yes"
    assert target_map["claim_posture_taxonomy_bound"] == "yes"
    assert target_map["master_action_status"] == "MASTER_ACTION_CITATION_BOUND"
    assert target_map["full_pillar_completion_claim"] == "no"
    assert target_map["seam_closure_claim"] == "no"
    assert target_map["phase2_authorized"] == "no"
    assert target_map["empirical_claim"] == "no"
    assert target_map["master_action_promotion_authorized"] == "no"
    assert target_map["theorem_work_authorized"] == (
        "result_review_only_after_target_map_rebase"
    )
    assert target_map["target_map_result_review_target"] == RESULT_REVIEW_TARGET
    assert target_map["target_map_result_review_surface"] == TARGET_MAP_RESULT_REVIEW_EVIDENCE
    assert target_map["target_map_result_review_report"] == TARGET_MAP_RESULT_REVIEW_REPORT
    assert target_map["target_map_result_review_status"] == "prepared_for_live_result_review"

    review = workstream("full_pillar_target_map_rebase_result_review", payload)
    assert review["status"] == "paused"
    assert review["authorized_next_strict_target"] == SELECTION_TARGET
    assert review["consumed_target"] == NEXT_TARGET
    assert review["review_surface"] == TARGET_MAP_RESULT_REVIEW_EVIDENCE
    assert review["release_report"] == TARGET_MAP_RESULT_REVIEW_REPORT
    assert review["target_map_authority_only"] == "yes"
    assert review["next_physics_attack_selected"] == "no"
    assert review["theorem_work_authorized"] == (
        "selection_only_no_physics_attack"
    )

    active = workstream("post_rebase_next_bounded_attack_selection", payload)
    assert active["status"] == "paused"
    assert active["authorized_next_strict_target"] == SELECTED_POST_REBASE_TARGET
    assert active["selected_next_target"] == SELECTED_POST_REBASE_TARGET
    assert active["selection_executes_attack"] == "no"
    assert (
        active["state_expectation_functional_result_review_target"]
        == STATE_EXPECTATION_RESULT_REVIEW_TARGET
    )

    for path in [README_PATH, STATE_PATH, ROADMAP_PATH, STRICT_MAP_PATH]:
        text = _read(path)
        assert SURFACE_ID in text
        if path in {ROADMAP_PATH, STRICT_MAP_PATH}:
            assert NEXT_TARGET in text
            assert RESULT_REVIEW_TARGET in text
            assert SELECTION_TARGET in text
        assert STATE_EXPECTATION_RESULT_REVIEW_TARGET in text
        assert CURRENT_LIVE_TARGET in text

    assert_focused_gate_not_manifest_enrolled("test_full_pillar_target_map_rebase_gate.py")

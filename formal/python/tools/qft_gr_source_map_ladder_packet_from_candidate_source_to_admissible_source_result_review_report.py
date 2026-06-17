from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_source_map_ladder_packet_from_candidate_source_to_admissible_source_report import (
    CANDIDATE_SOURCE_ID,
    DEFAULT_OUT as DEFAULT_PACKET_PATH,
    FIRST_LADDER_BREAK_ROW_ID,
    OUTCOME_ID as EXPECTED_PACKET_OUTCOME,
    PACKET_CLASSIFICATION as EXPECTED_PACKET_CLASSIFICATION,
    PACKET_ID as EXPECTED_PACKET_ID,
    SCHEMA_ID as EXPECTED_PACKET_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-16T00:00:00Z"
REVIEWED_COMMIT = "e482398a07bc5eb458af1356ff6d7e1283c00f1c"
SCHEMA_ID = (
    "QFT_GR_SOURCE_MAP_LADDER_PACKET_FROM_CANDIDATE_SOURCE_TO_ADMISSIBLE_"
    "SOURCE_RESULT_REVIEW_20260616_v0"
)
REVIEW_ID = (
    "QFT_GR_SOURCE_MAP_LADDER_PACKET_FROM_CANDIDATE_SOURCE_TO_ADMISSIBLE_"
    "SOURCE_RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "QFT_GR_SOURCE_MAP_LADDER_PACKET_RESULT_REVIEW_ACCEPTS_CANDIDATE_ONLY_"
    "FIRST_BREAK_AND_AUTHORIZES_MINIMAL_GLOBAL_MATHEMATICAL_OBLIGATION_"
    "INDEX_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "qft_gr_source_map_ladder_packet_result_review_accepts_candidate_only_"
    "first_break_and_authorizes_minimal_global_mathematical_obligation_index_only"
)
CONSUMED_TARGET = (
    "review_qft_gr_source_map_ladder_packet_from_candidate_source_to_"
    "admissible_source_result"
)
NEXT_TARGET = "prepare_minimal_global_toe_mathematical_obligation_index"
NEXT_TARGET_KIND = "minimal_global_toe_mathematical_obligation_index_preparation"
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "QFT_GR_SOURCE_MAP_LADDER_PACKET_FROM_CANDIDATE_SOURCE_TO_"
        "ADMISSIBLE_SOURCE_RESULT_REVIEW_20260616_v0.json"
    )
)
LEAN_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRSourceMapLadderPacketFromCandidateSourceToAdmissibleSourceResultReview.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The ladder result is accepted as candidate-only with a first "
                "mathematical break, so the next step is a small calculation "
                "obligation index."
            ),
        },
        {
            "target": CONSUMED_TARGET,
            "decision": "completed_consumed_live_target",
            "reason": "The ladder result-review target is consumed here.",
        },
        {
            "target": "prepare_global_toe_pillar_seam_candidate_maturity_matrix",
            "decision": "deferred_not_selected",
            "reason": (
                "A broad maturity matrix is intentionally deferred so the "
                "project pivots toward calculation obligations."
            ),
        },
        {
            "target": "repair_qft_gr_source_action_test_action_and_weak_pairing_domain",
            "decision": "not_authorized",
            "reason": (
                "Repair is not authorized until the obligation index and "
                "selection packet choose a calculation target."
            ),
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": "routine_qft_gr_source_map_ladder_result_review",
        "bounded_focused_validation_only": True,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_aggregate_lean_required": False,
        "full_ci_parity_required": False,
        "full_security_scan_required": False,
        "aggregate_lean_not_run": True,
        "release_index_path_not_freshly_lean_validated": True,
        "aggregate_lean_health_claimed": False,
    }


def build_qft_gr_source_map_ladder_packet_from_candidate_source_to_admissible_source_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    reviewed_commit: str = REVIEWED_COMMIT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(packet_path)
    candidate_next_targets = _candidate_next_targets()
    acceptance_criteria = {
        "review_binds_preserved_packet_artifact": (
            packet.get("schema_id") == EXPECTED_PACKET_SCHEMA_ID
            and packet.get("packet_id") == EXPECTED_PACKET_ID
            and packet.get("outcome_id") == EXPECTED_PACKET_OUTCOME
            and packet.get("packet_classification") == EXPECTED_PACKET_CLASSIFICATION
            and reviewed_commit == REVIEWED_COMMIT
        ),
        "reviewed_live_target_before_review_recorded": CONSUMED_TARGET
        == packet.get("selected_next_target"),
        "candidate_source_remains_candidate_only": (
            packet.get("candidate_source_object_id") == CANDIDATE_SOURCE_ID
            and packet.get("candidate_source_is_admissible_source") is False
            and packet.get("source_admissibility_claimed") is False
        ),
        "first_break_recorded_exactly": (
            packet.get("first_ladder_break_row_id") == FIRST_LADDER_BREAK_ROW_ID
            and packet.get("first_ladder_break_status") == "blocked"
            and packet.get("admissibility_ladder_row_count") == 12
        ),
        "no_later_row_reached": all(
            row.get("status") != "derivable"
            for row in packet.get("admissibility_ladder", [])[3:]
        ),
        "minimal_obligation_index_selected_only": [
            row["target"]
            for row in candidate_next_targets
            if row.get("decision") == "selected"
        ]
        == [NEXT_TARGET],
        "non_promotion_boundary_preserved": all(
            packet.get(key) is False
            for key in [
                "countermodel_result_claimed",
                "no_go_result_claimed",
                "not_found_under_pinned_scope_claimed",
                "source_admissibility_claimed",
                "Bianchi_compatibility_claimed",
                "semiclassical_einstein_equation_derived",
                "qft_gr_seam_closed",
                "qft_gr_source_map_closure_claimed",
                "empirical_validation_claimed",
                "public_submission_authorized",
                "master_action_promoted",
            ]
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = NEXT_TARGET if accepted else "REMEDIATE_QFT_GR_SOURCE_MAP_LADDER_RESULT_REVIEW"

    return {
        "schema_id": SCHEMA_ID,
        "review_id": REVIEW_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "reviewed_artifact_id": packet.get("schema_id"),
        "reviewed_packet_id": packet.get("packet_id"),
        "reviewed_commit": reviewed_commit,
        "reviewed_live_target_before_review": CONSUMED_TARGET,
        "review_outcome": OUTCOME_ID if accepted else "REQUIRES_REMEDIATION",
        "accepted": accepted,
        "result_review_accepted": accepted,
        "outcome_id": OUTCOME_ID if accepted else "QFT_GR_SOURCE_MAP_LADDER_PACKET_RESULT_REVIEW_REQUIRES_REMEDIATION",
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "candidate_source_object_id": CANDIDATE_SOURCE_ID,
        "candidate_source_status": "candidate_only_not_source_admissible",
        "first_ladder_break_row_id": FIRST_LADDER_BREAK_ROW_ID,
        "first_ladder_break_status": "blocked",
        "admissibility_ladder_row_count": packet.get("admissibility_ladder_row_count"),
        "supplied_condition_count": packet.get("supplied_condition_count"),
        "derivable_condition_count": packet.get("derivable_condition_count"),
        "blocked_condition_count": packet.get("blocked_condition_count"),
        "absent_condition_count": packet.get("absent_condition_count"),
        "countermodel_sensitive_condition_count": packet.get(
            "countermodel_sensitive_condition_count"
        ),
        "countermodel_hook_count": packet.get("countermodel_hook_count"),
        "minimal_obligation_index_authorized": accepted,
        "global_maturity_matrix_deferred": True,
        "repair_loop_authorized": False,
        "source_admissibility_claimed": False,
        "conservation_claimed": False,
        "Bianchi_compatibility_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "qft_gr_seam_closed": False,
        "qft_gr_source_map_closure_claimed": False,
        "empirical_validation_claimed": False,
        "public_submission_authorized": False,
        "master_action_promoted": False,
        "candidate_next_targets": candidate_next_targets,
        "validation_policy": _validation_policy(),
        "lean_review_file": _ptr(LEAN_REVIEW_PATH),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This review accepts the preserved QFT-GR source-map ladder as a "
            "candidate-only bounded obstruction result. It authorizes only a "
            "minimal mathematical obligation index, not source admissibility, "
            "countermodel/no-go/not-found claims, Bianchi compatibility, a "
            "semiclassical Einstein equation, QFT-GR closure, public release, "
            "or master-action promotion."
        ),
    }


def write_qft_gr_source_map_ladder_packet_from_candidate_source_to_admissible_source_result_review(
    *,
    packet_path: Path = DEFAULT_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    reviewed_commit: str = REVIEWED_COMMIT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_source_map_ladder_packet_from_candidate_source_to_admissible_source_result_review(
        packet_path=packet_path,
        reviewed_commit=reviewed_commit,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate QFT-GR source-map ladder result review JSON.")
    parser.add_argument("--packet", type=Path, default=DEFAULT_PACKET_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--reviewed-commit", default=REVIEWED_COMMIT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    packet_path = ns.packet if ns.packet.is_absolute() else (REPO_ROOT / ns.packet)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_source_map_ladder_packet_from_candidate_source_to_admissible_source_result_review(
        packet_path=packet_path,
        out=out,
        reviewed_commit=str(ns.reviewed_commit),
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        json.dumps(
            {
                "out": _ptr(out),
                "review_id": payload["review_id"],
                "outcome_id": payload["outcome_id"],
                "accepted": payload["accepted"],
                "selected_next_target": payload["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

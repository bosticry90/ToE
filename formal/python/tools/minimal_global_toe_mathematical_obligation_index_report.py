from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_source_map_ladder_packet_from_candidate_source_to_admissible_source_result_review_report import (
    DEFAULT_OUT as DEFAULT_LADDER_REVIEW_PATH,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as EXPECTED_LADDER_REVIEW_OUTCOME,
    REVIEW_ID as EXPECTED_LADDER_REVIEW_ID,
    SCHEMA_ID as EXPECTED_LADDER_REVIEW_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-16T00:00:00Z"
SCHEMA_ID = "MINIMAL_GLOBAL_TOE_MATHEMATICAL_OBLIGATION_INDEX_20260616_v0"
INDEX_ID = "MINIMAL_GLOBAL_TOE_MATHEMATICAL_OBLIGATION_INDEX_v0"
OUTCOME_ID = (
    "MINIMAL_GLOBAL_TOE_MATHEMATICAL_OBLIGATION_INDEX_PREPARED_WITH_NO_"
    "DERIVATION_EXECUTION_OR_THEORY_CLOSURE"
)
INDEX_CLASSIFICATION = (
    "minimal_global_toe_mathematical_obligation_index_prepared_as_calculation_"
    "stoplight_not_maturity_matrix"
)
NEXT_TARGET = "review_minimal_global_toe_mathematical_obligation_index_result"
NEXT_TARGET_KIND = "minimal_global_toe_mathematical_obligation_index_result_review"
QFT_GR_CALCULATION_TARGET = (
    "prepare_qft_gr_source_action_test_action_weak_pairing_domain_calculation_packet"
)
QFT_GR_FIRST_REQUIRED_CALCULATION = (
    "construct_source_action_test_action_weak_pairing_domain"
)
QFT_GR_FIRST_BREAK_ROW_ID = "source_action_test_action_and_weak_pairing_domain"
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "MINIMAL_GLOBAL_TOE_MATHEMATICAL_OBLIGATION_INDEX_20260616_v0.json"
)
LEAN_INDEX_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "MinimalGlobalToeMathematicalObligationIndex.lean"
)
ALLOWED_MATURITY_STATES = [
    "UNKNOWN_OR_UNASSESSED",
    "NOT_STARTED",
    "INVENTORIED_ONLY",
    "CANDIDATE_ONLY",
    "COMPATIBILITY_SURFACE",
    "PARTIAL_DERIVATION",
    "BOUNDED_OBSTRUCTION",
    "COUNTERMODEL_FOUND",
    "KNOWN_LIMIT_RECOVERY",
    "EMPIRICAL_REFERENT_REGISTERED",
    "PREDICTION_OR_FALSIFIER_REGISTERED",
    "REVIEWED_NONPROMOTIONAL_RESULT",
    "PUBLIC_HYPOTHESIS_READY",
]


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _math_evidence(first_required_calculation: str) -> dict[str, Any]:
    return {
        "calculation_performed": False,
        "derivation_performed": False,
        "known_limit_recovered": False,
        "symbolic_identity_verified": False,
        "numerical_experiment_performed": False,
        "first_required_calculation": first_required_calculation,
    }


def _row(
    *,
    unit_id: str,
    unit_type: str,
    maturity_state: str,
    artifact_maturity: str,
    formal_maturity: str,
    scientific_maturity: str,
    mathematical_obligation: str,
    first_required_calculation: str,
    next_calculation_target: str,
    evidence_source: str,
    first_unresolved_blocker: str,
) -> dict[str, Any]:
    return {
        "unit_id": unit_id,
        "unit_type": unit_type,
        "maturity_state": maturity_state,
        "artifact_maturity": artifact_maturity,
        "formal_maturity": formal_maturity,
        "scientific_maturity": scientific_maturity,
        "mathematical_obligation": mathematical_obligation,
        "calculation_status": "BLOCKED_NOT_EXECUTED",
        "calculation_artifact": "none",
        "derivation_status": "not_executed",
        "symbolic_check_status": "not_executed",
        "numerical_check_status": "not_executed",
        "known_limit_check_status": "not_executed",
        "first_required_calculation": first_required_calculation,
        "first_unresolved_blocker": first_unresolved_blocker,
        "evidence_source": evidence_source,
        "mathematical_evidence": _math_evidence(first_required_calculation),
        "forbidden_claims": [
            "complete_unified_theory",
            "pillar_completion",
            "seam_closure",
            "source_admissibility",
            "empirical_validation",
            "public_hypothesis_ready",
            "master_action_promotion",
        ],
        "next_calculation_target": next_calculation_target,
    }


def _obligation_rows(ladder_review: dict[str, Any]) -> list[dict[str, Any]]:
    qft_gr_evidence = ladder_review.get(
        "lean_review_file",
        "formal/toe_formal/ToeFormal/Derivation/"
        "QFTGRSourceMapLadderPacketFromCandidateSourceToAdmissibleSourceResultReview.lean",
    )
    return [
        _row(
            unit_id="QFT_GR",
            unit_type="seam",
            maturity_state="BOUNDED_OBSTRUCTION",
            artifact_maturity="preserved_packet_plus_review",
            formal_maturity="first_break_recorded",
            scientific_maturity="source_admissibility_blocked",
            mathematical_obligation=(
                "Supply or refute the source action, allowed test action, "
                "and weak-pairing domain for the current candidate source."
            ),
            first_required_calculation=QFT_GR_FIRST_REQUIRED_CALCULATION,
            next_calculation_target=QFT_GR_CALCULATION_TARGET,
            evidence_source=qft_gr_evidence,
            first_unresolved_blocker=QFT_GR_FIRST_BREAK_ROW_ID,
        ),
        _row(
            unit_id="GR",
            unit_type="pillar",
            maturity_state="UNKNOWN_OR_UNASSESSED",
            artifact_maturity="not_assessed_by_this_index",
            formal_maturity="not_assessed_by_this_index",
            scientific_maturity="not_assessed_by_this_index",
            mathematical_obligation="Identify the next GR-specific derivation or known-limit calculation.",
            first_required_calculation="unknown_or_unassessed",
            next_calculation_target="defer_until_selection",
            evidence_source="not_assessed_by_minimal_index",
            first_unresolved_blocker="unknown_or_unassessed",
        ),
        _row(
            unit_id="STAT",
            unit_type="pillar",
            maturity_state="UNKNOWN_OR_UNASSESSED",
            artifact_maturity="not_assessed_by_this_index",
            formal_maturity="not_assessed_by_this_index",
            scientific_maturity="not_assessed_by_this_index",
            mathematical_obligation="Identify the next emergence or coarse-graining calculation.",
            first_required_calculation="unknown_or_unassessed",
            next_calculation_target="defer_until_selection",
            evidence_source="not_assessed_by_minimal_index",
            first_unresolved_blocker="unknown_or_unassessed",
        ),
        _row(
            unit_id="GR_QM",
            unit_type="seam",
            maturity_state="UNKNOWN_OR_UNASSESSED",
            artifact_maturity="not_assessed_by_this_index",
            formal_maturity="not_assessed_by_this_index",
            scientific_maturity="not_assessed_by_this_index",
            mathematical_obligation="Identify the next derivation-grade bridge calculation.",
            first_required_calculation="unknown_or_unassessed",
            next_calculation_target="defer_until_selection",
            evidence_source="not_assessed_by_minimal_index",
            first_unresolved_blocker="unknown_or_unassessed",
        ),
        _row(
            unit_id="master_action_family",
            unit_type="candidate_family",
            maturity_state="UNKNOWN_OR_UNASSESSED",
            artifact_maturity="not_assessed_by_this_index",
            formal_maturity="architecture_not_derivation_assessed_here",
            scientific_maturity="derivation_power_not_assessed_here",
            mathematical_obligation="Separate organizing grammar from derivation or constraint generation.",
            first_required_calculation="unknown_or_unassessed",
            next_calculation_target="defer_until_selection",
            evidence_source="not_assessed_by_minimal_index",
            first_unresolved_blocker="unknown_or_unassessed",
        ),
        _row(
            unit_id="computational_physics_vvuq_layer",
            unit_type="computational_layer",
            maturity_state="UNKNOWN_OR_UNASSESSED",
            artifact_maturity="not_assessed_by_this_index",
            formal_maturity="designed_vvuq_not_executed_vvuq_assessed_here",
            scientific_maturity="validation_not_claimed",
            mathematical_obligation="Identify any executed numerical verification, validation, or robustness calculation.",
            first_required_calculation="unknown_or_unassessed",
            next_calculation_target="defer_until_selection",
            evidence_source="not_assessed_by_minimal_index",
            first_unresolved_blocker="unknown_or_unassessed",
        ),
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": "minimal_global_toe_mathematical_obligation_index",
        "support_artifact_not_scientific_progress_by_itself": True,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_aggregate_lean_required": False,
        "full_ci_parity_required": False,
        "full_security_scan_required": False,
        "aggregate_lean_not_run": True,
        "release_index_path_not_freshly_lean_validated": True,
    }


def build_minimal_global_toe_mathematical_obligation_index(
    *,
    ladder_review_path: Path = DEFAULT_LADDER_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    ladder_review = _read_json(ladder_review_path)
    rows = _obligation_rows(ladder_review)
    acceptance_criteria = {
        "consumes_ladder_result_review": (
            ladder_review.get("schema_id") == EXPECTED_LADDER_REVIEW_SCHEMA_ID
            and ladder_review.get("review_id") == EXPECTED_LADDER_REVIEW_ID
            and ladder_review.get("outcome_id") == EXPECTED_LADDER_REVIEW_OUTCOME
            and ladder_review.get("selected_next_target") == CONSUMED_TARGET
        ),
        "index_is_small_and_calculation_oriented": len(rows) <= 8
        and all("first_required_calculation" in row for row in rows),
        "qft_gr_obstruction_carried_forward_exactly": any(
            row["unit_id"] == "QFT_GR"
            and row["maturity_state"] == "BOUNDED_OBSTRUCTION"
            and row["first_unresolved_blocker"] == QFT_GR_FIRST_BREAK_ROW_ID
            and row["first_required_calculation"] == QFT_GR_FIRST_REQUIRED_CALCULATION
            and row["next_calculation_target"] == QFT_GR_CALCULATION_TARGET
            for row in rows
        ),
        "unknown_state_allowed": "UNKNOWN_OR_UNASSESSED" in ALLOWED_MATURITY_STATES,
        "all_rows_have_separate_maturity_fields": all(
            all(
                key in row
                for key in [
                    "artifact_maturity",
                    "formal_maturity",
                    "scientific_maturity",
                    "mathematical_evidence",
                    "forbidden_claims",
                ]
            )
            for row in rows
        ),
        "row_groups_exist": {row["unit_type"] for row in rows}
        >= {"pillar", "seam", "candidate_family", "computational_layer"},
    }
    prepared = all(acceptance_criteria.values())
    selected_next_target = NEXT_TARGET if prepared else "REMEDIATE_MINIMAL_GLOBAL_TOE_MATHEMATICAL_OBLIGATION_INDEX"

    return {
        "schema_id": SCHEMA_ID,
        "index_id": INDEX_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "accepted": prepared,
        "outcome_id": OUTCOME_ID if prepared else "MINIMAL_GLOBAL_TOE_MATHEMATICAL_OBLIGATION_INDEX_REQUIRES_REMEDIATION",
        "index_classification": INDEX_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "global_maturity_matrix_deferred": True,
        "index_scope": "small_calculation_obligation_stoplight_only",
        "central_field": "first_required_calculation",
        "allowed_maturity_states": ALLOWED_MATURITY_STATES,
        "obligation_rows": rows,
        "obligation_row_count": len(rows),
        "required_row_groups": ["pillar", "seam", "candidate_family", "computational_layer"],
        "qft_gr_first_required_calculation": QFT_GR_FIRST_REQUIRED_CALCULATION,
        "qft_gr_next_calculation_target": QFT_GR_CALCULATION_TARGET,
        "calculation_executed_by_this_index": False,
        "derivation_executed_by_this_index": False,
        "theory_closure_claimed": False,
        "public_hypothesis_ready_claimed": False,
        "source_admissibility_claimed": False,
        "qft_gr_closure_claimed": False,
        "empirical_validation_claimed": False,
        "master_action_promoted": False,
        "validation_policy": _validation_policy(),
        "lean_index_file": _ptr(LEAN_INDEX_PATH),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The minimal obligation index is a support artifact. It records "
            "the next required calculation and does not claim source "
            "admissibility, derivation execution, known-limit recovery, "
            "empirical validation, public readiness, or theory closure."
        ),
    }


def write_minimal_global_toe_mathematical_obligation_index(
    *,
    ladder_review_path: Path = DEFAULT_LADDER_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_minimal_global_toe_mathematical_obligation_index(
        ladder_review_path=ladder_review_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the minimal ToE mathematical obligation index.")
    parser.add_argument("--ladder-review", type=Path, default=DEFAULT_LADDER_REVIEW_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    ladder_review_path = ns.ladder_review if ns.ladder_review.is_absolute() else (REPO_ROOT / ns.ladder_review)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_minimal_global_toe_mathematical_obligation_index(
        ladder_review_path=ladder_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        json.dumps(
            {
                "out": _ptr(out),
                "index_id": payload["index_id"],
                "outcome_id": payload["outcome_id"],
                "prepared": payload["prepared"],
                "selected_next_target": payload["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

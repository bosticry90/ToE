from __future__ import annotations

"""Execute Stage-3 CCFT contract completeness/conflict adjudication.

The tool consumes only the immutable Stage-2 ledger.  A temporary decision
spec supplies the seven exact-candidate judgments and may not add evidence.
"""

if __name__ == "__main__" and (__package__ is None or __package__ == ""):
    from pathlib import Path as _Path
    raise SystemExit(
        "Run this tool as a module:\n\n"
        f"  .\\py.ps1 -m formal.python.tools.{_Path(__file__).stem} --help"
    )

import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_ROOT = REPO_ROOT / "formal/docs/release"
PROGRAM_ID = "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0"
STAGE_ID = "TARGETED_CCFT_CONTRACT_COMPLETENESS_AND_CONFLICT_ADJUDICATION"
TARGET = "adjudicate_toe_targeted_ccft_contract_completeness_and_conflicts_v0"
OUTCOME = "ONE_OR_MORE_EXACT_CCFT_CLOSURE_CONTRACTS_RECOVERED"
NEXT_TARGET = "select_toe_post_targeted_ccft_recovery_construction_handoff_v0"
STAGE2_RESULT = RELEASE_ROOT / "TOE_TARGETED_CCFT_CLOSURE_CONTRACT_EXTRACTION_RESULT_v0.json"
AUTHORITY = RELEASE_ROOT / (
    "TOE_TARGETED_CCFT_CONTRACT_COMPLETENESS_AND_CONFLICT_ADJUDICATION_"
    "STAGE_3_OPEN_AUTHORITY_v0.json"
)
MANIFEST = RELEASE_ROOT / "bounded_program_manifests/TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0_MANIFEST_v1.json"
OPEN_EVENT = RELEASE_ROOT / "bounded_program_events/TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0_ATTEMPT_03_OPEN_v0.json"
RESULT_PATH = RELEASE_ROOT / "TOE_TARGETED_CCFT_CONTRACT_COMPLETENESS_AND_CONFLICT_ADJUDICATION_RESULT_v0.json"

EXACT_STATUSES = {
    "RECOVERED_EXACT_CLOSURE_CONTRACT",
    "EXACT_EVIDENCE_APPLICATION_BLOCKED_BY_CONFLICT",
    "EXACT_EVIDENCE_CONFIGURATION_BOUND_NOT_GENERAL_CONTRACT",
    "EXACT_EVIDENCE_INCOMPLETE_PARAMETER_RANGE",
}
NONEXACT_STATUSES = {
    "CONFLICT_PRESERVED_NO_CONTRACT_RECOVERED",
    "ONLY_NONEXACT_EVIDENCE_NO_CONTRACT_RECOVERED",
    "NO_RELEVANT_EVIDENCE_NO_CONTRACT_RECOVERED",
}
CRITERIA = (
    "explicit_and_portable",
    "materially_complete_for_declared_role",
    "conflict_free",
    "general_enough_for_model_contract",
    "source_recovered_not_numerical_default",
    "reduces_named_future_postulate",
)


def _load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _write(path: Path, value: dict[str, Any]) -> None:
    if path.exists():
        raise ValueError(f"immutable result already exists: {path}")
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n",
        encoding="ascii", newline="\n",
    )


def _stage() -> dict[str, Any]:
    stage = _load(MANIFEST)["stages"][2]
    if stage["stage_number"] != 3 or stage["semantic_stage_id"] != STAGE_ID:
        raise ValueError("manifest Stage 3 mismatch")
    return stage


def _validate_decision(decision: dict[str, Any], record: dict[str, Any]) -> None:
    if decision["record_id"] != record["contract_record_id"]:
        raise ValueError("exact-candidate decision record mismatch")
    if decision["adjudication_status"] not in EXACT_STATUSES:
        raise ValueError(f"invalid exact-candidate status: {decision['adjudication_status']}")
    criteria = decision["criteria"]
    if set(criteria) != set(CRITERIA) or not all(isinstance(criteria[item], bool) for item in CRITERIA):
        raise ValueError("exact-candidate criteria are incomplete")
    recovered = decision["adjudication_status"] == "RECOVERED_EXACT_CLOSURE_CONTRACT"
    if recovered != all(criteria.values()):
        raise ValueError("recovered status must equal passage of all six criteria")
    if decision["future_postulate_reduction"] is None and recovered:
        raise ValueError("a recovered contract must reduce a named future postulate")


def execute(*, decision_spec_path: Path, captured_at_utc: str) -> dict[str, Any]:
    if RESULT_PATH.exists():
        raise ValueError(f"immutable result already exists: {RESULT_PATH}")
    stage2 = _load(STAGE2_RESULT)
    authority = _load(AUTHORITY)
    spec = _load(decision_spec_path)
    records = {row["contract_record_id"]: row for row in stage2["source_bound_contract_record_ledger"]}
    exact_ids = {
        record_id for record_id, row in records.items()
        if row["evidence_strength_classification"] == "EXACT_SOURCE_BOUND_CONTRACT_RECOVERED"
    }
    if exact_ids != set(authority["exact_candidate_record_ids"]) or len(exact_ids) != 7:
        raise ValueError("frozen exact-candidate set mismatch")
    decisions = {row["record_id"]: row for row in spec["exact_candidate_decisions"]}
    if set(decisions) != exact_ids:
        raise ValueError("decision spec must adjudicate exactly the seven candidates")
    exact_matrix = []
    for record_id in sorted(exact_ids):
        decision = decisions[record_id]
        record = records[record_id]
        _validate_decision(decision, record)
        exact_matrix.append({
            "record_id": record_id,
            "ccft_branch": record["ccft_branch"],
            "missing_contract_id": record["missing_contract_id"],
            "source_path": record["source_record_id_path_hash_lineage_and_custody"]["custody_relative_path"],
            "source_sha256": record["source_record_id_path_hash_lineage_and_custody"]["verified_sha256"],
            "portability": record["portability_limitation"],
            "criteria": decision["criteria"],
            "adjudication_status": decision["adjudication_status"],
            "rationale": decision["rationale"],
            "future_postulate_reduction": decision["future_postulate_reduction"],
            "physical_or_mathematical_validity_established": False,
        })

    matrix = []
    by_contract = {(row["ccft_branch"], row["missing_contract_id"]): row for row in stage2["missing_contract_checklist_ledger"]}
    exact_by_contract = {(row["ccft_branch"], row["missing_contract_id"]): row for row in exact_matrix}
    for key, extracted in sorted(by_contract.items()):
        if key in exact_by_contract:
            status = exact_by_contract[key]["adjudication_status"]
            recovered_ids = [exact_by_contract[key]["record_id"]] if status == "RECOVERED_EXACT_CLOSURE_CONTRACT" else []
        elif extracted["extraction_status"] == "CONFLICTING_EVIDENCE_EXTRACTED":
            status = "CONFLICT_PRESERVED_NO_CONTRACT_RECOVERED"
            recovered_ids = []
        elif extracted["extraction_status"] == "NO_RELEVANT_EVIDENCE_IN_SELECTED_SET":
            status = "NO_RELEVANT_EVIDENCE_NO_CONTRACT_RECOVERED"
            recovered_ids = []
        else:
            status = "ONLY_NONEXACT_EVIDENCE_NO_CONTRACT_RECOVERED"
            recovered_ids = []
        matrix.append({
            "ccft_branch": key[0],
            "missing_contract_id": key[1],
            "source_record_ids": extracted["record_ids"],
            "stage_2_extraction_status": extracted["extraction_status"],
            "stage_3_adjudication_status": status,
            "recovered_contract_record_ids": recovered_ids,
        })

    conflicts = []
    for row in spec["conflict_adjudications"]:
        if row["adjudication_status"] != "CONFLICT_PRESERVED_NO_CONTRACT_RECOVERED":
            raise ValueError("Stage 3 may only preserve, not select, conflict records")
        if not set(row["record_ids"]).issubset(records):
            raise ValueError("conflict adjudication references a nonfrozen record")
        conflicts.append(row)
    if len(conflicts) != 3:
        raise ValueError("all three conflicted checklist items must be preserved")

    recovered = [row for row in exact_matrix if row["adjudication_status"] == "RECOVERED_EXACT_CLOSURE_CONTRACT"]
    recovered_by_branch = Counter(row["ccft_branch"] for row in recovered)
    status_counts = Counter(row["stage_3_adjudication_status"] for row in matrix)
    open_event = _load(OPEN_EVENT)
    result = {
        "artifact_id": "TOE_TARGETED_CCFT_CONTRACT_COMPLETENESS_AND_CONFLICT_ADJUDICATION_RESULT_v0",
        "schema_id": "toe.targeted_ccft.contract_completeness_and_conflict_adjudication.result.v0",
        "captured_at_utc": captured_at_utc,
        "program_id": PROGRAM_ID,
        "semantic_stage_id": STAGE_ID,
        "scientific_target": TARGET,
        "scope_hash": _stage()["canonical_scope_hash"],
        "attempt_sequence_number": 3,
        "open_event_binding": {
            "path": OPEN_EVENT.relative_to(REPO_ROOT).as_posix(),
            "sha256": _sha(OPEN_EVENT),
            "event_hash": open_event["event_hash"],
        },
        "stage_2_input_binding": {
            "path": STAGE2_RESULT.relative_to(REPO_ROOT).as_posix(),
            "sha256": _sha(STAGE2_RESULT),
            "frozen_source_count": 96,
            "contract_record_count": 23,
            "checklist_count": 18,
            "exact_candidate_count": 7,
            "new_source_search_performed": False,
            "overflow_sources_used": 0,
        },
        "exact_candidate_adjudication_matrix": exact_matrix,
        "contract_by_contract_completeness_matrix": matrix,
        "primary_source_conflict_supersession_and_portability_adjudication": {
            "conflicts": conflicts,
            "supersession_established_for_any_conflict": False,
            "chronology_used_to_select_a_contract": False,
            "all_evidence_sources_git_portable": True,
            "custody_or_provenance_block": False,
        },
        "exact_recovered_contract_count_by_branch": {
            "CP_NLSE": recovered_by_branch.get("CP_NLSE", 0),
            "LCRD_V3": recovered_by_branch.get("LCRD_V3", 0),
            "TOTAL": len(recovered),
        },
        "future_new_postulate_reduction_ledger": [
            {
                "record_id": row["record_id"],
                "ccft_branch": row["ccft_branch"],
                "missing_contract_id": row["missing_contract_id"],
                "future_postulate_no_longer_required_if_branch_is_selected": row["future_postulate_reduction"],
                "branch_selection_or_model_validation_implied": False,
            }
            for row in recovered
        ],
        "adjudication_summary": {
            "exact_candidates_adjudicated": 7,
            "exact_contracts_recovered": len(recovered),
            "checklist_status_counts": dict(sorted(status_counts.items())),
            "conflicts_preserved": 3,
            "contracts_not_recovered": 18 - len(recovered),
        },
        "nonclaim_boundary": {
            "cp_nlse_equation_selected_or_repaired": False,
            "cp_nlse_dispersion_selected_derived_or_repaired": False,
            "numerical_default_promoted": False,
            "new_ccft_postulate_inserted": False,
            "ccft_v0_selected_constructed_or_validated": False,
            "theorem_discovery_lane_opened": False,
            "new_proof_counterexample_or_calculation_attempted": False,
            "evidence_promoted": False,
            "physical_operationalization_established": False,
            "repository_claim_exhaustion_established": False,
        },
        "stage_4_handoff": {
            "selected_target": NEXT_TARGET,
            "stage_4_authorized": False,
            "required_decision": "SEPARATE_STAGE_4_SCIENTIFIC_AUTHORITY_DECISION",
            "purpose": "select the program-level targeted recovery result and mandatory construction-preparation handoff",
        },
        "terminal_outcome": OUTCOME,
        "lifecycle_result": "PASSED",
        "status": "STAGE_3_CLOSED_RESULT_READY_FOR_INDEPENDENT_REVIEW",
    }
    _write(RESULT_PATH, result)
    return result


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--decision-spec", type=Path, required=True)
    parser.add_argument("--captured-at-utc", required=True)
    args = parser.parse_args(argv)
    result = execute(decision_spec_path=args.decision_spec, captured_at_utc=args.captured_at_utc)
    print(json.dumps(result["adjudication_summary"], indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

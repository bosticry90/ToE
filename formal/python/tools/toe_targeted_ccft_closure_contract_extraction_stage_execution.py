from __future__ import annotations

"""Extract Stage-2 CCFT closure evidence from the frozen Stage-1 captures.

This tool never reopens a repository or archive source.  It verifies and reads
only the 96 passive-text captures embedded in the immutable Stage-1 result.
Scientific record choices are supplied in an ephemeral, reviewable spec; the
result itself retains the complete 96-source disposition ledger.
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
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
RELEASE_ROOT = REPO_ROOT / "formal/docs/release"
PROGRAM_ID = "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0"
STAGE_ID = "TARGETED_CCFT_CLOSURE_CONTRACT_EXTRACTION"
TARGET = "extract_toe_targeted_ccft_closure_contracts_v0"
OUTCOME = "TARGETED_CCFT_CONTRACT_EXTRACTION_COMPLETE"
NEXT_TARGET = "adjudicate_toe_targeted_ccft_contract_completeness_and_conflicts_v0"
STAGE1_RESULT = RELEASE_ROOT / "TOE_TARGETED_CCFT_CLOSURE_SOURCE_DISCOVERY_AND_CUSTODY_RESULT_v0.json"
MANIFEST = RELEASE_ROOT / "bounded_program_manifests/TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0_MANIFEST_v1.json"
OPEN_EVENT = RELEASE_ROOT / "bounded_program_events/TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0_ATTEMPT_02_OPEN_v0.json"
RESULT_PATH = RELEASE_ROOT / "TOE_TARGETED_CCFT_CLOSURE_CONTRACT_EXTRACTION_RESULT_v0.json"

EVIDENCE_CLASSES = {
    "EXACT_SOURCE_BOUND_CONTRACT_RECOVERED",
    "PARTIAL_CONTRACT_RECOVERED",
    "CONFLICTING_SOURCE_CONTRACTS",
    "DERIVED_SUMMARY_WITH_PRIMARY_SOURCE_MISSING",
    "NUMERICAL_DEFAULT_ONLY",
    "HEURISTIC_NOT_A_CONTRACT",
    "NO_RELEVANT_EVIDENCE",
}

CHECKLISTS = {
    "CP_NLSE": (
        "FINAL_INTENDED_NONLINEAR_EQUATION",
        "COEFFICIENT_DEFINITIONS_AND_ADMISSIBLE_RANGES",
        "INITIAL_DATA_RULES",
        "BOUNDARY_CONDITIONS",
        "NONDIMENSIONALIZATION_OR_NORMALIZATION",
        "CONSERVED_OR_MONITORED_QUANTITIES",
        "FAILURE_AND_INSTABILITY_CRITERIA",
        "NUMERICAL_IMPLEMENTATION_PROVENANCE",
        "CORRECT_INTERACTION_MODIFIED_DISPERSION_RELATION",
        "ADDITIVE_FREQUENCY_CONFLICT_RESOLUTION",
    ),
    "LCRD_V3": (
        "COMPLETE_STATE_VARIABLE_DEFINITIONS",
        "INITIAL_AND_BOUNDARY_DATA",
        "PARAMETER_RANGES",
        "NORMALIZATION_CONVENTIONS",
        "CONSTITUTIVE_OR_CLOSURE_RELATIONS",
        "REPRODUCIBLE_IMPLEMENTATION",
        "ROTOR_CURVATURE_COUPLING_DEFINITIONS",
        "LSDA_COARSE_GRAINING_MAP_OR_VARIATIONAL_EFFECTIVE_DERIVATION",
    ),
}

OPTIONAL_RECORD_FIELDS = (
    "mathematical_transcription",
    "definitions_of_all_symbols",
    "parameter_values_or_ranges",
    "initial_and_boundary_conditions",
    "normalization_or_nondimensionalization",
    "conservation_invariant_or_monitoring_rule",
    "failure_or_instability_criterion",
    "implementation_provenance",
    "conflicting_source_records",
    "extraction_note",
)


def _load(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _sha(path: Path) -> str:
    return _sha_bytes(path.read_bytes())


def _manifest_stage() -> dict[str, Any]:
    manifest = _load(MANIFEST)
    return next(stage for stage in manifest["stages"] if stage["stage_number"] == 2)


def _verify_frozen_inputs(stage1: dict[str, Any]) -> dict[str, dict[str, Any]]:
    selected = stage1["selected_source_ledger"]
    if len(selected) != 96:
        raise ValueError("Stage 1 must bind exactly 96 sources")
    if Counter(row["allocation_branch"] for row in selected) != {"CP_NLSE": 48, "LCRD_V3": 48}:
        raise ValueError("Stage-1 branch allocation is not the frozen 48/48 split")
    if stage1["single_content_pass"]["passes_consumed"] != 1:
        raise ValueError("the single discovery pass is not recorded as consumed")
    if any(not row["portable_in_normal_git_history"] for row in selected):
        raise ValueError("Stage 2 is restricted to the frozen Git-portable set")
    by_path: dict[str, dict[str, Any]] = {}
    for row in selected:
        text = row["passive_text_capture"]
        if _sha_bytes(text.encode("utf-8")) != row["passive_text_capture_sha256"]:
            raise ValueError(f"captured-text hash mismatch: {row['custody_relative_path']}")
        path = row["custody_relative_path"]
        if path in by_path:
            raise ValueError(f"duplicate selected path: {path}")
        by_path[path] = row
    return by_path


def _extract_excerpt(text: str, selector: dict[str, Any]) -> tuple[int, int, str]:
    anchor = selector["anchor"]
    occurrence = selector.get("occurrence", 1)
    if not isinstance(anchor, str) or not anchor:
        raise ValueError("record selector anchor must be nonempty text")
    if not isinstance(occurrence, int) or occurrence < 1:
        raise ValueError("selector occurrence must be a positive integer")
    lines = text.splitlines()
    hits = [index for index, line in enumerate(lines) if anchor in line]
    if len(hits) < occurrence:
        raise ValueError(f"anchor not found at occurrence {occurrence}: {anchor!r}")
    hit = hits[occurrence - 1]
    before = selector.get("before", 0)
    after = selector.get("after", 0)
    if not all(isinstance(value, int) and 0 <= value <= 24 for value in (before, after)):
        raise ValueError("excerpt context must be between 0 and 24 lines")
    start = max(0, hit - before)
    end = min(len(lines), hit + after + 1)
    excerpt = "\n".join(lines[start:end])
    if len(excerpt.encode("utf-8")) > 8192:
        raise ValueError("bounded excerpt exceeds 8192 bytes")
    return start + 1, end, excerpt


def _record(spec: dict[str, Any], source: dict[str, Any]) -> dict[str, Any]:
    branch = spec["ccft_branch"]
    checklist_id = spec["missing_contract_id"]
    evidence_class = spec["evidence_strength_classification"]
    if branch not in CHECKLISTS or checklist_id not in CHECKLISTS[branch]:
        raise ValueError(f"invalid branch/checklist pair: {branch}/{checklist_id}")
    if source["allocation_branch"] != branch:
        raise ValueError(f"source allocation does not match record branch: {source['custody_relative_path']}")
    if evidence_class not in EVIDENCE_CLASSES or evidence_class == "NO_RELEVANT_EVIDENCE":
        raise ValueError("material records require one of the six nonempty evidence classes")
    line_start, line_end, excerpt = _extract_excerpt(source["passive_text_capture"], spec["selector"])
    result = {
        "contract_record_id": spec["contract_record_id"],
        "ccft_branch": branch,
        "missing_contract_id": checklist_id,
        "source_record_id_path_hash_lineage_and_custody": {
            "record_id": source["record_id"],
            "custody_relative_path": source["custody_relative_path"],
            "verified_sha256": source["verified_sha256"],
            "passive_text_capture_sha256": source["passive_text_capture_sha256"],
            "lineage_id": source["lineage_id"],
            "source_root_id": source["source_root_id"],
            "custody_class": source["custody_class"],
            "portable_in_normal_git_history": source["portable_in_normal_git_history"],
        },
        "bounded_supporting_excerpt_and_location": {
            "line_start": line_start,
            "line_end": line_end,
            "text": excerpt,
            "excerpt_sha256": _sha_bytes(excerpt.encode("utf-8")),
        },
        "evidence_strength_classification": evidence_class,
        "portability_limitation": "NONE_GIT_PORTABLE_CAPTURE_BOUND",
        "stage_3_eligibility": "ELIGIBLE_FOR_COMPLETENESS_AND_CONFLICT_ADJUDICATION",
    }
    for field in OPTIONAL_RECORD_FIELDS:
        result[field] = spec.get(field, [] if field in {"definitions_of_all_symbols", "conflicting_source_records"} else None)
    return result


def _checklist_status(records: list[dict[str, Any]]) -> str:
    classes = {row["evidence_strength_classification"] for row in records}
    if "CONFLICTING_SOURCE_CONTRACTS" in classes:
        return "CONFLICTING_EVIDENCE_EXTRACTED"
    if "EXACT_SOURCE_BOUND_CONTRACT_RECOVERED" in classes:
        return "EXACT_EVIDENCE_EXTRACTED_PENDING_STAGE_3_ADJUDICATION"
    if records:
        return "ONLY_NONEXACT_EVIDENCE_EXTRACTED"
    return "NO_RELEVANT_EVIDENCE_IN_SELECTED_SET"


def execute(*, evidence_spec_path: Path, captured_at_utc: str) -> dict[str, Any]:
    if RESULT_PATH.exists():
        raise ValueError(f"immutable result already exists: {RESULT_PATH}")
    stage1 = _load(STAGE1_RESULT)
    sources = _verify_frozen_inputs(stage1)
    spec = _load(evidence_spec_path)
    spec_records = spec["records"]
    if len(spec_records) > 192:
        raise ValueError("contract record cap exceeded")
    ids = [row["contract_record_id"] for row in spec_records]
    if len(ids) != len(set(ids)):
        raise ValueError("contract record IDs must be unique")
    records: list[dict[str, Any]] = []
    for row in spec_records:
        path = row["custody_relative_path"]
        if path not in sources:
            raise ValueError(f"spec attempts to use a nonfrozen or overflow source: {path}")
        records.append(_record(row, sources[path]))
    per_contract = Counter((row["ccft_branch"], row["missing_contract_id"]) for row in records)
    if any(count > 12 for count in per_contract.values()):
        raise ValueError("per-contract record cap exceeded")
    conflict_count = sum(
        row["evidence_strength_classification"] == "CONFLICTING_SOURCE_CONTRACTS"
        for row in records
    )
    if conflict_count > 32:
        raise ValueError("conflicting-record cap exceeded")

    linked_by_path: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for row in records:
        linked_by_path[row["source_record_id_path_hash_lineage_and_custody"]["custody_relative_path"]].append(row)
    source_ledger = []
    for path, source in sorted(sources.items()):
        linked = linked_by_path.get(path, [])
        source_ledger.append(
            {
                "record_id": source["record_id"],
                "custody_relative_path": path,
                "allocation_branch": source["allocation_branch"],
                "verified_sha256": source["verified_sha256"],
                "passive_text_capture_sha256": source["passive_text_capture_sha256"],
                "contract_record_ids": [row["contract_record_id"] for row in linked],
                "evidence_strength_classifications": sorted(
                    {row["evidence_strength_classification"] for row in linked}
                ) or ["NO_RELEVANT_EVIDENCE"],
                "disposition": "MATERIAL_EVIDENCE_EXTRACTED" if linked else "NO_RELEVANT_EVIDENCE",
                "new_root_traversal_performed": False,
            }
        )

    checklist_ledger = []
    for branch, checklist in CHECKLISTS.items():
        for checklist_id in checklist:
            linked = [
                row for row in records
                if row["ccft_branch"] == branch and row["missing_contract_id"] == checklist_id
            ]
            checklist_ledger.append(
                {
                    "ccft_branch": branch,
                    "missing_contract_id": checklist_id,
                    "record_ids": [row["contract_record_id"] for row in linked],
                    "evidence_class_counts": dict(sorted(Counter(
                        row["evidence_strength_classification"] for row in linked
                    ).items())),
                    "extraction_status": _checklist_status(linked),
                    "contract_completeness_adjudicated": False,
                }
            )

    class_counts = Counter(row["evidence_strength_classification"] for row in records)
    branch_counts = Counter(row["ccft_branch"] for row in records)
    open_event = _load(OPEN_EVENT)
    stage = _manifest_stage()
    result = {
        "artifact_id": "TOE_TARGETED_CCFT_CLOSURE_CONTRACT_EXTRACTION_RESULT_v0",
        "schema_id": "toe.targeted_ccft_closure.contract_extraction.result.v0",
        "captured_at_utc": captured_at_utc,
        "program_id": PROGRAM_ID,
        "semantic_stage_id": STAGE_ID,
        "scientific_target": TARGET,
        "scope_hash": stage["canonical_scope_hash"],
        "attempt_sequence_number": 2,
        "open_event_binding": {
            "path": OPEN_EVENT.relative_to(REPO_ROOT).as_posix(),
            "sha256": _sha(OPEN_EVENT),
            "event_hash": open_event["event_hash"],
        },
        "frozen_stage_1_input": {
            "path": STAGE1_RESULT.relative_to(REPO_ROOT).as_posix(),
            "sha256": _sha(STAGE1_RESULT),
            "selected_source_count": 96,
            "selected_by_branch": {"CP_NLSE": 48, "LCRD_V3": 48},
            "overflow_source_count": 137,
            "overflow_sources_used": 0,
            "new_source_search_or_root_traversal_performed": False,
            "content_discovery_passes_consumed": 1,
            "content_discovery_passes_remaining": 0,
        },
        "workload_cap_accounting": {
            "contract_record_cap": 192,
            "contract_records_extracted": len(records),
            "maximum_records_per_missing_contract": 12,
            "largest_records_for_one_missing_contract": max(per_contract.values(), default=0),
            "conflicting_record_cap": 32,
            "conflicting_records_extracted": conflict_count,
            "parser_failure_cap": 8,
            "parser_failures": 0,
            "frozen_capture_text_bytes": sum(row["passive_text_capture_bytes"] for row in sources.values()),
            "maximum_total_extracted_text_bytes": 33554432,
        },
        "source_bound_contract_record_ledger": records,
        "source_review_ledger": source_ledger,
        "missing_contract_checklist_ledger": checklist_ledger,
        "extraction_summary": {
            "record_count": len(records),
            "records_by_branch": dict(sorted(branch_counts.items())),
            "records_by_evidence_class": dict(sorted(class_counts.items())),
            "sources_with_material_evidence": sum(row["disposition"] == "MATERIAL_EVIDENCE_EXTRACTED" for row in source_ledger),
            "sources_with_no_relevant_evidence": sum(row["disposition"] == "NO_RELEVANT_EVIDENCE" for row in source_ledger),
            "checklists_with_exact_candidates": sum(row["extraction_status"].startswith("EXACT_") for row in checklist_ledger),
            "checklists_with_conflicts": sum(row["extraction_status"] == "CONFLICTING_EVIDENCE_EXTRACTED" for row in checklist_ledger),
            "checklists_with_only_nonexact_evidence": sum(row["extraction_status"] == "ONLY_NONEXACT_EVIDENCE_EXTRACTED" for row in checklist_ledger),
            "checklists_with_no_relevant_evidence": sum(row["extraction_status"] == "NO_RELEVANT_EVIDENCE_IN_SELECTED_SET" for row in checklist_ledger),
        },
        "adjudication_boundary": {
            "contract_recovery_or_rejection_established": False,
            "conflicting_contract_selected_or_repaired": False,
            "numerical_default_promoted_to_theory_contract": False,
            "new_postulate_inserted": False,
            "cp_nlse_or_lcrd_v3_selected_for_ccft_v0": False,
            "ccft_v0_constructed": False,
            "physical_operationalization_claimed": False,
            "canonical_evidence_promoted": False,
            "repository_claim_exhaustion_established": False,
        },
        "stage_3_handoff": {
            "selected_target": NEXT_TARGET,
            "stage_3_authorized": False,
            "required_decision": "SEPARATE_STAGE_3_SCIENTIFIC_AUTHORITY_DECISION",
            "purpose": "adjudicate completeness and compatibility of extracted contract evidence without equation repair or model construction",
        },
        "terminal_outcome": OUTCOME,
        "lifecycle_result": "PASSED",
        "status": "STAGE_2_CLOSED_RESULT_READY_FOR_INDEPENDENT_REVIEW",
    }
    RESULT_PATH.write_text(
        json.dumps(result, indent=2, sort_keys=True, ensure_ascii=True) + "\n",
        encoding="ascii",
        newline="\n",
    )
    return result


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--evidence-spec", type=Path, required=True)
    parser.add_argument("--captured-at-utc", required=True)
    args = parser.parse_args(argv)
    result = execute(evidence_spec_path=args.evidence_spec, captured_at_utc=args.captured_at_utc)
    print(json.dumps(result["extraction_summary"], indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

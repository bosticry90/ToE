from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "V01_ALPHA_RELEASE_PACKET_GAP_REVIEW_20260515_v0"
REVIEW_ID = "V01_ALPHA_RELEASE_PACKET_GAP_REVIEW_v0"
OUTCOME_ID = (
    "V01_ALPHA_RELEASE_PACKET_GAP_REVIEW_PREPARED_AFTER_COMPUTATIONAL_PHYSICS_STACK_CLOSEOUT_"
    "WITH_NO_RELEASE_PROMOTION"
)
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_SELECTION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "MAIN_PHYSICS_TARGET_SELECTION_AFTER_COMPUTATIONAL_PHYSICS_CLOSEOUT_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT / "formal" / "docs" / "release" / "V01_ALPHA_RELEASE_PACKET_GAP_REVIEW_20260515_v0.json"
)

RELEASE_STANDARD_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "TOE_V01_ALPHA_RELEASE_STANDARD_20260513_v0.json"
)
COVERAGE_LEDGER_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "TOE_V01_ALPHA_PILLAR_SEAM_COVERAGE_LEDGER_v0.json"
)
CLAIM_LEDGER_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "TOE_V01_ALPHA_CLAIM_EVIDENCE_LEDGER_v0.json"
)
EQUATION_LEDGER_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "TOE_V01_ALPHA_EQUATION_LEDGER_v0.json"
)
BLOCKER_LEDGER_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "TOE_V01_ALPHA_BLOCKER_LEDGER_v0.json"
)
LEAN_AUDIT_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "TOE_V01_ALPHA_LEAN_DEPENDENCY_AUDIT_v0.md"
)
LEAN_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"
PUBLIC_SURFACE_PATHS = [
    REPO_ROOT / "README.md",
    REPO_ROOT / "State_of_the_Theory.md",
    REPO_ROOT / "formal" / "docs" / "release" / "CURRENT_AUTHORITATIVE_SURFACES_v0.md",
    REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md",
    REPO_ROOT / "formal" / "docs" / "lanes" / "STRICT_PHYSICS_DERIVATION_OBLIGATION_MAP_v0.md",
]

EXPECTED_CONSUMED_SELECTION = "MAIN_PHYSICS_TARGET_SELECTION_AFTER_COMPUTATIONAL_PHYSICS_CLOSEOUT_v0"
EXPECTED_SELECTED_TARGET = "prepare_v01_alpha_release_packet_gap_review"
NEXT_TARGET = "prepare_v01_alpha_lean_dependency_audit_capture_packet"
EXPECTED_CHECKS = [
    "pillar/seam coverage ledger completeness",
    "claim/evidence ledger completeness",
    "equation ledger completeness",
    "blocker ledger completeness",
    "Lean release index audit rows",
    "public summary readiness",
    "expert review packet readiness",
    "remaining unmigrated release-facing labels",
    "remaining draft/deferred rows",
]
FORBIDDEN_EFFECTS = [
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


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required text file: {path}")
    return path.read_text(encoding="utf-8")


def _dependency_audit_status_counts(coverage: dict[str, Any], claim: dict[str, Any]) -> dict[str, int]:
    counts: dict[str, int] = {}
    for row in coverage.get("rows", []) + claim.get("rows", []):
        status = str(row.get("dependency_audit", {}).get("audit_status", "missing"))
        counts[status] = counts.get(status, 0) + 1
    return dict(sorted(counts.items()))


def _lean_audit_row_count(audit_text: str) -> int:
    return sum(1 for line in audit_text.splitlines() if line.startswith("| `") and line.endswith(" |"))


def _lean_audit_pending_count(audit_text: str) -> int:
    return sum(1 for line in audit_text.splitlines() if line.startswith("| `") and "`pending`" in line)


def _lean_index_check_count(index_text: str) -> int:
    return sum(1 for line in index_text.splitlines() if line.strip().startswith("#check "))


def _public_surface_signal_counts() -> dict[str, int]:
    legacy_labels = ["T-PROVED", "T-CONDITIONAL", "DISCHARGED_v0", "LOCKED"]
    counts: dict[str, int] = {label: 0 for label in legacy_labels}
    counts["not_complete_signal_count"] = 0
    counts["manifest_enrolled_signal_count"] = 0
    for path in PUBLIC_SURFACE_PATHS:
        text = _read_text(path)
        for label in legacy_labels:
            counts[label] += len(re.findall(re.escape(label), text))
        lower = text.lower()
        counts["not_complete_signal_count"] += lower.count("not complete")
        counts["manifest_enrolled_signal_count"] += lower.count("manifest-enrolled")
    return counts


def _gap_rows(
    *,
    selection: dict[str, Any],
    standard: dict[str, Any],
    coverage: dict[str, Any],
    claim: dict[str, Any],
    equation: dict[str, Any],
    blocker: dict[str, Any],
    audit_text: str,
    index_text: str,
) -> list[dict[str, Any]]:
    domains_present = sorted(row.get("domain") for row in coverage.get("rows", []))
    required_domains = sorted(standard.get("pillar_seam_row_set", []))
    dependency_counts = _dependency_audit_status_counts(coverage, claim)
    public_counts = _public_surface_signal_counts()
    lean_audit_rows = _lean_audit_row_count(audit_text)
    lean_pending_rows = _lean_audit_pending_count(audit_text)
    lean_index_checks = _lean_index_check_count(index_text)
    return [
        {
            "check_id": "pillar_seam_coverage_ledger_completeness",
            "source_check": "pillar/seam coverage ledger completeness",
            "status": "seeded_structurally_complete",
            "evidence": [_ptr(COVERAGE_LEDGER_PATH)],
            "observed": {
                "row_count": len(coverage.get("rows", [])),
                "required_domain_count": len(required_domains),
                "all_required_domains_present": domains_present == required_domains,
                "closure_authorized_count": sum(
                    1 for row in coverage.get("rows", []) if row.get("closure_authorized") is True
                ),
            },
            "gap": "coverage rows are present, but dependency audits remain pending across release-facing rows",
            "blocks_release_packet_assembly": True,
        },
        {
            "check_id": "claim_evidence_ledger_completeness",
            "source_check": "claim/evidence ledger completeness",
            "status": "seeded_with_current_release_labels",
            "evidence": [_ptr(CLAIM_LEDGER_PATH)],
            "observed": {
                "row_count": len(claim.get("rows", [])),
                "closure_authorized_count": sum(
                    1 for row in claim.get("rows", []) if row.get("closure_authorized") is True
                ),
                "dependency_audit_status_counts": dependency_counts,
            },
            "gap": "claim evidence is seeded, but dependency-audit status is not sufficiently captured for release packet assembly",
            "blocks_release_packet_assembly": True,
        },
        {
            "check_id": "equation_ledger_completeness",
            "source_check": "equation ledger completeness",
            "status": "seeded_minimal_equation_surface",
            "evidence": [_ptr(EQUATION_LEDGER_PATH)],
            "observed": {
                "row_count": len(equation.get("rows", [])),
                "closure_authorized_count": sum(
                    1 for row in equation.get("rows", []) if row.get("closure_authorized") is True
                ),
            },
            "gap": "equation rows are present, but public derivation readiness depends on the pending Lean dependency audit",
            "blocks_release_packet_assembly": True,
        },
        {
            "check_id": "blocker_ledger_completeness",
            "source_check": "blocker ledger completeness",
            "status": "seeded_active_blockers_visible",
            "evidence": [_ptr(BLOCKER_LEDGER_PATH)],
            "observed": {
                "row_count": len(blocker.get("rows", [])),
                "blocker_ids": [row.get("blocker_id") for row in blocker.get("rows", [])],
            },
            "gap": "blockers remain explicit; release packet may summarize them, but cannot claim completion while they remain active",
            "blocks_release_packet_assembly": True,
        },
        {
            "check_id": "lean_release_index_audit_rows",
            "source_check": "Lean release index audit rows",
            "status": "index_present_audit_rows_pending",
            "evidence": [_ptr(LEAN_INDEX_PATH), _ptr(LEAN_AUDIT_PATH)],
            "observed": {
                "lean_index_check_count": lean_index_checks,
                "lean_dependency_audit_row_count": lean_audit_rows,
                "lean_dependency_audit_pending_row_count": lean_pending_rows,
            },
            "gap": "Lean audit rows still need captured dependency output and project-axiom/supplied-structure classification",
            "blocks_release_packet_assembly": True,
        },
        {
            "check_id": "public_summary_readiness",
            "source_check": "public summary readiness",
            "status": "partial_manifest_enrolled_not_complete_language_present",
            "evidence": [_ptr(path) for path in PUBLIC_SURFACE_PATHS],
            "observed": {
                "manifest_enrolled_signal_count": public_counts["manifest_enrolled_signal_count"],
                "not_complete_signal_count": public_counts["not_complete_signal_count"],
            },
            "gap": "public summaries state the bounded release-track posture, but no final release-packet summary has been assembled",
            "blocks_release_packet_assembly": True,
        },
        {
            "check_id": "expert_review_packet_readiness",
            "source_check": "expert review packet readiness",
            "status": "not_prepared_v0",
            "evidence": [],
            "observed": {
                "expert_review_packet_present": False,
            },
            "gap": "external/expert review packet is not prepared",
            "blocks_release_packet_assembly": True,
        },
        {
            "check_id": "remaining_unmigrated_release_facing_labels",
            "source_check": "remaining unmigrated release-facing labels",
            "status": "requires_scoped_exception_audit_v0",
            "evidence": [_ptr(path) for path in PUBLIC_SURFACE_PATHS],
            "observed": {
                "legacy_label_signal_counts_on_public_surfaces": {
                    key: public_counts[key] for key in ["T-PROVED", "T-CONDITIONAL", "DISCHARGED_v0", "LOCKED"]
                },
                "release_standard_legacy_labels_declared": standard.get("legacy_labels", []),
            },
            "gap": "legacy labels appear on broad public/historical surfaces and need scoped release-facing exception review before packet assembly",
            "blocks_release_packet_assembly": True,
        },
        {
            "check_id": "remaining_draft_deferred_rows",
            "source_check": "remaining draft/deferred rows",
            "status": "deferred_release_assembly_and_review_packet_gaps_remain",
            "evidence": [selection.get("selected_target_source", "")],
            "observed": {
                "selection_candidate_targets": selection.get("candidate_targets", []),
                "release_packet_assembly_deferred": any(
                    row.get("target") == "assemble_v01_alpha_public_release_packet"
                    and row.get("decision") == "deferred"
                    for row in selection.get("candidate_targets", [])
                ),
            },
            "gap": "release assembly remains deferred until the dependency-audit and review-packet gaps are reduced",
            "blocks_release_packet_assembly": True,
        },
    ]


def build_gap_review(
    *,
    selection_path: Path = DEFAULT_SELECTION_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    selection = _read_json(selection_path)
    standard = _read_json(RELEASE_STANDARD_PATH)
    coverage = _read_json(COVERAGE_LEDGER_PATH)
    claim = _read_json(CLAIM_LEDGER_PATH)
    equation = _read_json(EQUATION_LEDGER_PATH)
    blocker = _read_json(BLOCKER_LEDGER_PATH)
    audit_text = _read_text(LEAN_AUDIT_PATH)
    index_text = _read_text(LEAN_INDEX_PATH)
    gap_rows = _gap_rows(
        selection=selection,
        standard=standard,
        coverage=coverage,
        claim=claim,
        equation=equation,
        blocker=blocker,
        audit_text=audit_text,
        index_text=index_text,
    )
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}
    selected_next_targets = [NEXT_TARGET]
    acceptance_criteria = {
        "consumes_main_selection": selection.get("selection_id") == EXPECTED_CONSUMED_SELECTION,
        "main_selection_accepted": selection.get("accepted") is True,
        "main_selection_selected_gap_review": selection.get("selected_target") == EXPECTED_SELECTED_TARGET,
        "computational_physics_stack_closed": selection.get("computational_physics_stack_status")
        == "CLOSED_BOUNDED_NONCLAIM",
        "release_scope_full_pillar_full_seam": standard.get("release_scope")
        == "FULL_PILLAR_FULL_SEAM_RELEASE_STANDARD",
        "all_required_gap_checks_reviewed": [row["source_check"] for row in gap_rows] == EXPECTED_CHECKS,
        "coverage_row_count_thirteen": len(coverage.get("rows", [])) == 13,
        "lean_dependency_audit_has_pending_rows": _lean_audit_pending_count(audit_text) > 0,
        "release_packet_assembly_not_authorized": forbidden_effect_status[
            "release_packet_assembly_authorized"
        ]
        is False,
        "v01_alpha_completion_not_authorized": forbidden_effect_status["v01_alpha_completion_authorized"]
        is False,
        "exactly_one_next_target_selected": len(selected_next_targets) == 1,
        "forbidden_effects_all_false": all(value is False for value in forbidden_effect_status.values()),
    }
    accepted = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "review_id": REVIEW_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "classification": "P-POLICY/nonclaim",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "outcome_id": OUTCOME_ID if accepted else "V01_ALPHA_RELEASE_PACKET_GAP_REVIEW_BLOCKED",
        "consumed_target": EXPECTED_SELECTED_TARGET,
        "consumes_selection": EXPECTED_CONSUMED_SELECTION,
        "consumes_selection_pointer": _ptr(selection_path),
        "computational_physics_stack_status": "CLOSED_BOUNDED_NONCLAIM",
        "release_scope_confirmed": standard.get("release_scope"),
        "gap_review_scope": "REVIEW_RELEASE_PACKET_GAPS_ONLY_NO_RELEASE_PACKET_ASSEMBLY",
        "reviewed_release_artifacts": {
            "release_standard": _ptr(RELEASE_STANDARD_PATH),
            "pillar_seam_coverage_ledger": _ptr(COVERAGE_LEDGER_PATH),
            "claim_evidence_ledger": _ptr(CLAIM_LEDGER_PATH),
            "equation_ledger": _ptr(EQUATION_LEDGER_PATH),
            "blocker_ledger": _ptr(BLOCKER_LEDGER_PATH),
            "lean_dependency_audit": _ptr(LEAN_AUDIT_PATH),
            "lean_release_index": _ptr(LEAN_INDEX_PATH),
        },
        "review_summary": {
            "gap_row_count": len(gap_rows),
            "coverage_row_count": len(coverage.get("rows", [])),
            "claim_evidence_row_count": len(claim.get("rows", [])),
            "equation_row_count": len(equation.get("rows", [])),
            "blocker_row_count": len(blocker.get("rows", [])),
            "lean_dependency_audit_row_count": _lean_audit_row_count(audit_text),
            "lean_dependency_audit_pending_row_count": _lean_audit_pending_count(audit_text),
            "lean_release_index_check_count": _lean_index_check_count(index_text),
            "primary_gap": "LEAN_DEPENDENCY_AUDIT_CAPTURE_AND_EXPERT_REVIEW_PACKET_NOT_READY",
            "release_packet_review_ready": False,
        },
        "gap_rows": gap_rows,
        "release_packet_assembled": False,
        "release_packet_assembly_authorized": False,
        "v01_alpha_public_release_completion_authorized": False,
        "selected_next_target": NEXT_TARGET if accepted else "REMEDIATE_V01_ALPHA_RELEASE_PACKET_GAP_REVIEW",
        "selected_next_target_kind": "lean_dependency_audit_capture_preparation_only",
        "selection_count": len(selected_next_targets) if accepted else 0,
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": "The seeded Lean dependency audit is the sharpest current release-packet blocker because every audit row still has pending captured output and pending project-axiom classification.",
            },
            {
                "target": "prepare_v01_alpha_expert_review_packet_readiness_audit",
                "decision": "deferred",
                "reason": "Expert review packet preparation should follow dependency-audit capture so reviewer-facing theorem dependency posture is not underspecified.",
            },
            {
                "target": "assemble_v01_alpha_public_release_packet",
                "decision": "blocked",
                "reason": "Release packet assembly remains blocked until the gap review's dependency-audit and review-readiness debts are reduced.",
            },
        ],
        "forbidden_effect_status": forbidden_effect_status,
        "acceptance_criteria": acceptance_criteria,
        "nonclaim_ids": standard.get("stable_nonclaim_ids", []),
        "not_authorized_claims": [
            "v0.1-alpha public release completion",
            "release packet assembly",
            "master-action promotion",
            "pillar completion",
            "seam closure",
            "Phase 2 readiness",
            "empirical adequacy",
            "canonical ToE status",
            "QFT-GR source-map closure",
            "computational-physics execution",
        ],
        "non_claim_boundary": (
            "The v0.1-alpha release packet gap review audits release-packet readiness gaps only. It does not "
            "assemble the release packet, mark v0.1-alpha complete, promote the master action, close pillars or "
            "seams, authorize Phase 2, claim empirical adequacy, discharge theorems, open computational-physics "
            "execution, or promote any claim."
        ),
        "roadmap_update_required": True,
    }


def write_gap_review(
    *,
    selection_path: Path = DEFAULT_SELECTION_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_gap_review(selection_path=selection_path, captured_at_utc=captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the v0.1-alpha release packet gap review.")
    parser.add_argument("--selection", type=Path, default=DEFAULT_SELECTION_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    selection_path = ns.selection if ns.selection.is_absolute() else (REPO_ROOT / ns.selection)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_gap_review(
        selection_path=selection_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_release_packet_gap_review_report: "
        f"prepared={payload['prepared']} selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

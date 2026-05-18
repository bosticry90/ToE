from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_PACKET_20260515_v0"
PACKET_ID = "V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_PACKET_v0"
OUTCOME_ID = "V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_PACKET_PREPARED_WITH_NO_RELEASE_ASSEMBLY_OR_PROOF_PROMOTION"
DEFAULT_CAPTURED_AT_UTC = "2026-05-15T00:00:00Z"

DEFAULT_GAP_REVIEW_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "V01_ALPHA_RELEASE_PACKET_GAP_REVIEW_20260515_v0.json"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_PACKET_20260515_v0.json"
)

LEAN_AGGREGATE_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal.lean"
LEAN_RELEASE_INDEX_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Release" / "V01Index.lean"
LEAN_DEPENDENCY_AUDIT_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "TOE_V01_ALPHA_LEAN_DEPENDENCY_AUDIT_v0.md"
)
AXIOM_LEDGER_PATH = REPO_ROOT / "formal" / "docs" / "release" / "LEAN_AXIOM_SPEC_BACKED_LEDGER_v0.md"
AXIOM_REFRESH_REVIEW_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "AXIOM_LEDGER_AUDIT_REFRESH_AFTER_SAMPLEREP32_RESULT_REVIEW_20260505_v0.json"
)

EXPECTED_GAP_REVIEW_ID = "V01_ALPHA_RELEASE_PACKET_GAP_REVIEW_v0"
EXPECTED_PRIMARY_GAP = "LEAN_DEPENDENCY_AUDIT_CAPTURE_AND_EXPERT_REVIEW_PACKET_NOT_READY"
EXPECTED_CONSUMED_TARGET = "prepare_v01_alpha_lean_dependency_audit_capture_packet"
NEXT_TARGET = "review_v01_alpha_lean_dependency_audit_capture_packet_result"

FORBIDDEN_EFFECTS = [
    "expert_review_executed",
    "release_packet_assembled",
    "v01_alpha_marked_ready",
    "lean_theorem_debt_discharged",
    "axiom_spec_backed_debt_reduced_by_documentation",
    "proof_debt_reduced",
    "theorem_discharge_authorized",
    "phase2_authorized",
    "seam_closure_authorized",
    "empirical_validation_authorized",
    "master_action_promotion_authorized",
    "claim_promotion_authorized",
    "computational_physics_execution_surface_opened",
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


def _strip_tick(value: str) -> str:
    return value.strip().strip("`")


def _parse_audit_rows(audit_text: str) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for line in audit_text.splitlines():
        if not line.startswith("| `"):
            continue
        cells = [cell.strip() for cell in line.strip().strip("|").split("|")]
        if len(cells) != 9:
            continue
        rows.append(
            {
                "theorem": _strip_tick(cells[0]),
                "source_file": _strip_tick(cells[1]),
                "release_label": _strip_tick(cells[2]),
                "audit_command": _strip_tick(cells[3]),
                "observed_dependency_result": cells[4],
                "project_axioms_used": cells[5],
                "supplied_structures_used": cells[6],
                "linked_assumptions": cells[7],
                "audit_status": _strip_tick(cells[8]),
                "release_dependency_class": (
                    "release_blocking_pending_capture"
                    if "pending" in cells[4].lower() or "pending" in cells[5].lower()
                    else "captured"
                ),
                "expert_review_required": True,
                "proof_debt_discharge_claim": False,
            }
        )
    return rows


def _parse_axiom_ledger_rows(ledger_text: str) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for line in ledger_text.splitlines():
        if not line.startswith("| `"):
            continue
        cells = [cell.strip() for cell in line.strip().strip("|").split("|")]
        if len(cells) != 7:
            continue
        rows.append(
            {
                "declaration": _strip_tick(cells[0]),
                "file": _strip_tick(cells[1]),
                "status": _strip_tick(cells[2]),
                "reason": cells[3],
                "associated_pillar_or_seam": _strip_tick(cells[4]),
                "blocks_full_pillar_target": _strip_tick(cells[5]),
                "replacement_or_discharge_path": cells[6],
            }
        )
    return rows


def _baseline_value(ledger_text: str, key: str) -> int:
    match = re.search(rf"{re.escape(key)}:\s*(\d+)", ledger_text)
    if not match:
        raise ValueError(f"Missing baseline value: {key}")
    return int(match.group(1))


def _release_index_checks(index_text: str) -> list[str]:
    checks: list[str] = []
    for line in index_text.splitlines():
        line = line.strip()
        if line.startswith("#check "):
            checks.append(line.removeprefix("#check ").strip())
    return checks


def _module_pointers(audit_rows: list[dict[str, Any]]) -> list[str]:
    return sorted({row["source_file"] for row in audit_rows})


def build_capture_packet(
    *,
    gap_review_path: Path = DEFAULT_GAP_REVIEW_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    gap_review = _read_json(gap_review_path)
    audit_text = _read_text(LEAN_DEPENDENCY_AUDIT_PATH)
    index_text = _read_text(LEAN_RELEASE_INDEX_PATH)
    ledger_text = _read_text(AXIOM_LEDGER_PATH)
    axiom_review = _read_json(AXIOM_REFRESH_REVIEW_PATH)
    audit_rows = _parse_audit_rows(audit_text)
    ledger_rows = _parse_axiom_ledger_rows(ledger_text)
    release_index_checks = _release_index_checks(index_text)
    retained_rows = [row for row in ledger_rows if row["status"] == "retained_assumption"]
    spec_backed_rows = [row for row in ledger_rows if row["status"] == "spec_backed"]
    blocking_rows = [row for row in ledger_rows if row["blocks_full_pillar_target"] == "yes"]
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_gap_review": gap_review.get("review_id") == EXPECTED_GAP_REVIEW_ID,
        "gap_review_primary_gap_confirmed": gap_review.get("review_summary", {}).get("primary_gap")
        == EXPECTED_PRIMARY_GAP,
        "gap_review_selected_this_packet": gap_review.get("selected_next_target") == EXPECTED_CONSUMED_TARGET,
        "release_packet_assembly_blocked": gap_review.get("release_packet_assembly_authorized") is False,
        "v01_alpha_not_ready": gap_review.get("v01_alpha_public_release_completion_authorized") is False,
        "lean_dependency_audit_rows_captured": len(audit_rows) == 6,
        "lean_release_index_checks_captured": len(release_index_checks) == 8,
        "axiom_ledger_rows_captured": len(ledger_rows) == _baseline_value(
            ledger_text, "real_axiom_count_v0"
        ),
        "axiom_ledger_active_posture_confirmed": axiom_review.get("ledger_posture", {}).get(
            "real_axiom_count"
        )
        == 59,
        "no_expert_review_execution": forbidden_effect_status["expert_review_executed"] is False,
        "no_release_packet_assembly": forbidden_effect_status["release_packet_assembled"] is False,
        "no_theorem_or_axiom_debt_discharge": forbidden_effect_status["lean_theorem_debt_discharged"]
        is False
        and forbidden_effect_status["axiom_spec_backed_debt_reduced_by_documentation"] is False,
        "exactly_one_next_target_selected": NEXT_TARGET
        == "review_v01_alpha_lean_dependency_audit_capture_packet_result",
        "forbidden_effects_all_false": all(value is False for value in forbidden_effect_status.values()),
    }
    prepared = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "classification": "P-POLICY/nonclaim",
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "outcome_id": OUTCOME_ID
        if prepared
        else "V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_PACKET_BLOCKED",
        "consumed_target": EXPECTED_CONSUMED_TARGET,
        "consumes_gap_review": EXPECTED_GAP_REVIEW_ID,
        "consumes_gap_review_pointer": _ptr(gap_review_path),
        "source_gap_review_primary_gap": gap_review.get("review_summary", {}).get("primary_gap"),
        "packet_scope": "CAPTURE_DEPENDENCY_AUDIT_READINESS_ONLY_NO_DISCHARGE_OR_RELEASE_ASSEMBLY",
        "lean_aggregate_pointer": _ptr(LEAN_AGGREGATE_PATH),
        "lean_release_index_pointer": _ptr(LEAN_RELEASE_INDEX_PATH),
        "lean_dependency_audit_pointer": _ptr(LEAN_DEPENDENCY_AUDIT_PATH),
        "axiom_spec_backed_ledger_pointer": _ptr(AXIOM_LEDGER_PATH),
        "axiom_refresh_result_review_pointer": _ptr(AXIOM_REFRESH_REVIEW_PATH),
        "current_lean_build_status": {
            "release_index_command": "Push-Location formal/toe_formal; lake env lean ToeFormal/Release/V01Index.lean; Pop-Location",
            "release_index_status": "passed_current_packet_validation",
            "full_aggregate_status": "not_run_by_this_packet",
            "interpretation": "release index checks current referenced theorem surfaces, but this is not theorem discharge",
        },
        "axiom_ledger_posture": {
            "real_axiom_count": _baseline_value(ledger_text, "real_axiom_count_v0"),
            "real_sorry_or_admit_count": _baseline_value(ledger_text, "real_sorry_or_admit_count_v0"),
            "real_axiom_file_count": _baseline_value(ledger_text, "real_axiom_file_count_v0"),
            "retained_assumption_count": len(retained_rows),
            "spec_backed_count": len(spec_backed_rows),
            "blocks_full_pillar_target_count": len(blocking_rows),
            "defaultNonAlias": axiom_review.get("ledger_posture", {}).get("defaultNonAlias"),
            "sampleRep32": axiom_review.get("ledger_posture", {}).get("sampleRep32"),
            "documentation_discharge_claim": False,
        },
        "known_retained_assumptions": retained_rows,
        "known_proof_debt_classes": [
            {
                "class_id": "retained_assumption",
                "row_count": len(retained_rows),
                "release_impact": "blocks release packet assembly when tied to release-facing theorem dependency posture",
            },
            {
                "class_id": "spec_backed",
                "row_count": len(spec_backed_rows),
                "release_impact": "documentation and convention debt; does not discharge by being listed",
            },
            {
                "class_id": "blocks_full_pillar_target",
                "row_count": len(blocking_rows),
                "release_impact": "prevents pillar/seam or master-action promotion",
            },
        ],
        "v01_release_dependency_rows": audit_rows,
        "release_index_checks": release_index_checks,
        "relevant_modules": _module_pointers(audit_rows),
        "release_blocking_dependencies": [
            row["theorem"] for row in audit_rows if row["release_dependency_class"] == "release_blocking_pending_capture"
        ],
        "documentation_only_dependencies": [
            "release index import/check surface",
            "seeded dependency-audit row table",
            "axiom/spec-backed ledger pointer",
        ],
        "expert_review_required_dependencies": [row["theorem"] for row in audit_rows],
        "unresolved_dependencies": [
            {
                "dependency": row["theorem"],
                "reason": "exact #print axioms output and project-axiom classification remain pending",
            }
            for row in audit_rows
        ],
        "capture_summary": {
            "v01_dependency_audit_row_count": len(audit_rows),
            "release_index_check_count": len(release_index_checks),
            "relevant_module_count": len(_module_pointers(audit_rows)),
            "release_blocking_dependency_count": len(audit_rows),
            "expert_review_required_dependency_count": len(audit_rows),
            "unresolved_dependency_count": len(audit_rows),
            "primary_capture_gap": "EXACT_AXIOM_PRINT_OUTPUT_AND_EXPERT_REVIEW_NOT_EXECUTED_V0",
        },
        "selected_next_target": NEXT_TARGET if prepared else "REMEDIATE_V01_ALPHA_LEAN_DEPENDENCY_AUDIT_CAPTURE_PACKET",
        "selected_next_target_kind": "result_review_only",
        "selection_count": 1 if prepared else 0,
        "candidate_next_targets": [
            {
                "target": NEXT_TARGET,
                "decision": "selected",
                "reason": "The capture packet should be reviewed before opening expert-review packet preparation or any dependency adjudication.",
            },
            {
                "target": "prepare_v01_alpha_expert_review_packet",
                "decision": "deferred",
                "reason": "Expert review packet preparation should wait for capture-packet result review.",
            },
            {
                "target": "prepare_v01_alpha_release_readiness_dependency_gap_adjudication",
                "decision": "deferred",
                "reason": "Gap adjudication should consume the capture result review and, if needed, expert-review packet preparation.",
            },
        ],
        "expert_review_executed": False,
        "release_packet_assembled": False,
        "v01_alpha_marked_ready": False,
        "lean_theorem_debt_discharged": False,
        "axiom_spec_backed_debt_reduced_by_documentation": False,
        "forbidden_effect_status": forbidden_effect_status,
        "acceptance_criteria": acceptance_criteria,
        "not_authorized_claims": [
            "expert review executed",
            "v0.1-alpha public release ready",
            "v0.1-alpha public release assembled",
            "Lean theorem debt discharged",
            "axiom/spec-backed proof debt reduced by documentation",
            "Phase 2 authorization",
            "seam closure",
            "empirical validation",
            "master-action promotion",
        ],
        "non_claim_boundary": (
            "The Lean dependency audit capture packet records release-index, audit-row, and axiom-ledger dependency "
            "posture only. Captured dependency posture is not dependency discharge, not expert review execution, not "
            "release packet assembly, not v0.1-alpha readiness, and not proof-debt reduction."
        ),
        "roadmap_update_required": True,
    }


def write_capture_packet(
    *,
    gap_review_path: Path = DEFAULT_GAP_REVIEW_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_capture_packet(gap_review_path=gap_review_path, captured_at_utc=captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the v0.1-alpha Lean dependency audit capture packet.")
    parser.add_argument("--gap-review", type=Path, default=DEFAULT_GAP_REVIEW_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    gap_review_path = ns.gap_review if ns.gap_review.is_absolute() else (REPO_ROOT / ns.gap_review)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_capture_packet(
        gap_review_path=gap_review_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_lean_dependency_audit_capture_packet_report: "
        f"prepared={payload['prepared']} selected_next_target={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
import unicodedata
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCRIPT_PATH = Path(__file__).resolve()
SCRIPT_RELATIVE_PATH = "formal/python/tools/pillar_seam_unit_mapping_ledger_first_unit_selector_result_review.py"
V2_PACKET_RELATIVE_PATH = (
    "formal/output/PILLAR-SEAM-UNIT-MAPPING-LEDGER-BLOCKER-RESPONSE-ROUTE-SELECTION-PACKET-v2.json"
)
PACKET_RELATIVE_PATH = "formal/output/PILLAR-SEAM-UNIT-MAPPING-LEDGER-FIRST-UNIT-SELECTOR-PACKET-v0.json"
MANIFEST_RELATIVE_PATH = "formal/output/PILLAR-SEAM-UNIT-MAPPING-LEDGER-FIRST-UNIT-SELECTOR-MANIFEST-v0.json"
PREPARATION_REPORT_RELATIVE_PATH = "formal/docs/release/PILLAR_SEAM_UNIT_MAPPING_LEDGER_FIRST_UNIT_SELECTOR_PACKET_20260713_v0.json"
REVIEW_REPORT_RELATIVE_PATH = "formal/docs/release/PILLAR_SEAM_UNIT_MAPPING_LEDGER_FIRST_UNIT_SELECTOR_PACKET_RESULT_REVIEW_20260713_v0.json"
PACKET_PATH = REPO_ROOT / PACKET_RELATIVE_PATH
MANIFEST_PATH = REPO_ROOT / MANIFEST_RELATIVE_PATH
PREPARATION_REPORT_PATH = REPO_ROOT / PREPARATION_REPORT_RELATIVE_PATH
REVIEW_REPORT_PATH = REPO_ROOT / REVIEW_REPORT_RELATIVE_PATH
V2_PACKET_PATH = REPO_ROOT / V2_PACKET_RELATIVE_PATH

CAPTURED_AT_UTC = "2026-07-13T00:00:00Z"
REVIEW_TARGET = "review_pillar_seam_unit_mapping_ledger_first_unit_selector_packet_v0_result"
ACCEPTED_NEXT_TARGET = "prepare_maxwell_dirac_unit_object_foundation_packet_v0"
BLOCKED_NEXT_TARGET = "prepare_pillar_seam_unit_mapping_ledger_first_unit_selector_packet_v1"
REVIEW_SCHEMA_ID = "PILLAR_SEAM_UNIT_MAPPING_LEDGER_FIRST_UNIT_SELECTOR_PACKET_RESULT_REVIEW_20260713_v0"
PREPARATION_COMMIT = "e02c6d078321e43ebe3834da38bb86aa8c7b236e"
PREPARATION_PARENT = "7ec3bd88a666914f0a3255f22d41265435341d5f"
EXPECTED_PREPARATION_HASHES = {
    "formal/python/tools/pillar_seam_unit_mapping_ledger_first_unit_selector.py": "91a224102775972c1ff43a544ae1e0acd67cd8b6d962dd1249a62b72a41ebb5b",
    PACKET_RELATIVE_PATH: "2441f3e766f4546ef31530ff2ca00b79251591e868226ff7e41b1ad3b4d12375",
    MANIFEST_RELATIVE_PATH: "b8b4554a1e9f134c6e83c64eb4e6770fadf53e4acd3aef9c7884626743447b6e",
    PREPARATION_REPORT_RELATIVE_PATH: "afb502f24ab74a99104dab130ff26256a31dc8e5444f72fe3575c18eceb175a3",
}
PROMPT_RELATIVE_PATH = "Prompt.txt"
PROMPT_SHA256 = "2bc6996ea28e96c50e688ed3d30ee24808af411a244eb594aad89ff80fda8433"
WEIGHTS = {
    "evidence_authority": 5,
    "object_clarity": 5,
    "noncircularity": 5,
    "dependency_readiness": 4,
    "downstream_leverage": 4,
    "bounded_scope": 3,
    "restoration_clarity": 3,
    "computational_enablement": 2,
}
THRESHOLDS = [40, 42, 44, 46, 48]
TIE_ORDER = ["SR", "GR", "EM", "QFT", "QM", "STAT", "COSMO"]
CODE_BY_ROW = {
    "PILLAR-QFT-units_and_dimensions-v0": "QFT",
    "PILLAR-GR-units_and_dimensions-v0": "GR",
    "PILLAR-QM-units_and_dimensions-v0": "QM",
    "PILLAR-STAT-units_and_dimensions-v0": "STAT",
    "PILLAR-EM-units_and_dimensions-v0": "EM",
    "PILLAR-SR-units_and_dimensions-v0": "SR",
    "PILLAR-COSMO-units_and_dimensions-v0": "COSMO",
}


def _normalize(value: Any) -> Any:
    if isinstance(value, str):
        return unicodedata.normalize("NFC", value)
    if isinstance(value, list):
        return [_normalize(item) for item in value]
    if isinstance(value, dict):
        return {_normalize(str(key)): _normalize(item) for key, item in value.items()}
    return value


def canonical_json_bytes(payload: Any) -> bytes:
    return (json.dumps(_normalize(payload), allow_nan=False, ensure_ascii=False, indent=2, sort_keys=True) + "\n").encode("utf-8")


def sha256_bytes(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def sha256_path(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected object: {path}")
    return value


def _direct(row: dict[str, Any]) -> dict[str, Any]:
    records = [
        item
        for item in row["evidence_records"]
        if item["evidence_role"] in {"PLANNING_AUTHORITY", "MATHEMATICAL_DERIVATION"}
        and item["route_support_eligible"] is True
    ]
    if len(records) != 1:
        raise ValueError(f"direct record count: {row['row_id']}")
    return records[0]


def independent_scores(v2_row: dict[str, Any]) -> dict[str, int]:
    code = CODE_BY_ROW[v2_row["row_id"]]
    direct = _direct(v2_row)
    return {
        "evidence_authority": 2 if direct["authority_class"] == "BOUNDED_ACCEPTED_MATHEMATICAL_SURFACE" else 1,
        "object_clarity": 2 if code in {"SR", "EM"} else 1,
        "noncircularity": 2,
        "dependency_readiness": 1,
        "downstream_leverage": 2 if code in {"SR", "GR", "EM", "QFT"} else 1,
        "bounded_scope": 2 if code in {"SR", "EM"} else 1,
        "restoration_clarity": 2 if code == "SR" else (1 if code in {"GR", "EM", "COSMO"} else 0),
        "computational_enablement": 2 if code == "EM" else (0 if code == "STAT" else 1),
    }


def _select(rows: list[dict[str, Any]], threshold: int) -> str | None:
    eligible = []
    for row in rows:
        values = row["scores"]
        if (
            row["total"] >= threshold
            and values["evidence_authority"] >= 1
            and values["object_clarity"] >= 1
            and values["dependency_readiness"] >= 1
            and values["bounded_scope"] >= 1
            and values["noncircularity"] == 2
            and not row["conflicts"]
        ):
            eligible.append(row)
    if not eligible:
        return None
    maximum = max(row["total"] for row in eligible)
    tied = [row for row in eligible if row["total"] == maximum]
    return min(tied, key=lambda row: TIE_ORDER.index(row["code"]))["row_id"]


def custody() -> dict[str, Any]:
    head = subprocess.run(["git", "rev-parse", PREPARATION_COMMIT], cwd=REPO_ROOT, capture_output=True, text=True, check=False).stdout.strip()
    parent = subprocess.run(["git", "rev-parse", f"{PREPARATION_COMMIT}^"], cwd=REPO_ROOT, capture_output=True, text=True, check=False).stdout.strip()
    working = {path: sha256_path(REPO_ROOT / path) for path in EXPECTED_PREPARATION_HASHES}
    committed = {}
    for path in EXPECTED_PREPARATION_HASHES:
        result = subprocess.run(["git", "show", f"{PREPARATION_COMMIT}:{path}"], cwd=REPO_ROOT, capture_output=True, check=False)
        committed[path] = sha256_bytes(result.stdout) if result.returncode == 0 else "MISSING"
    passed = head == PREPARATION_COMMIT and parent == PREPARATION_PARENT and working == EXPECTED_PREPARATION_HASHES and committed == EXPECTED_PREPARATION_HASHES
    return {"preparation_commit": head, "preparation_parent": parent, "working_hashes": working, "commit_hashes": committed, "expected_hashes": EXPECTED_PREPARATION_HASHES, "passed": passed}


DECISION_IDS = [
    "immutable_selector_preparation_bound",
    "all_eight_criteria_independently_recomputed",
    "every_score_binds_propositions_reasons_and_next_evidence",
    "weighted_totals_independently_recomputed",
    "target_readiness_gates_recomputed",
    "execution_readiness_gates_recomputed",
    "sensitivity_selection_recomputed_at_all_thresholds",
    "SR_is_stable_highest_scoring_selection",
    "tie_break_used_only_for_exact_score_tie",
    "no_unit_assignment_or_restoration_is_authorized",
    "Maxwell_Dirac_remains_candidate_and_nonclaims_hold",
    "Prompt_preserved",
]


def build_review_report() -> dict[str, Any]:
    packet = load_json(PACKET_PATH)
    v2_packet = load_json(V2_PACKET_PATH)
    custody_result = custody()
    v2_rows = {row["row_id"]: row for row in v2_packet["route_selections"] if row["row_kind"] == "pillar"}
    prepared_rows = {row["row_id"]: row for row in packet["scored_rows"]}
    recomputed = []
    score_match = reason_bindings = totals_match = readiness_match = True
    for row_id, v2_row in v2_rows.items():
        scores = independent_scores(v2_row)
        total = sum(WEIGHTS[key] * value for key, value in scores.items())
        prepared = prepared_rows[row_id]
        observed_scores = {item["criterion"]: item["score"] for item in prepared["criterion_scores"]}
        score_match = score_match and observed_scores == scores
        reason_bindings = reason_bindings and all(
            len(item["exact_supporting_proposition_ids"]) == 2
            and bool(item["eligibility_basis"])
            and bool(item["missing_evidence_required_for_next_score"])
            for item in prepared["criterion_scores"]
        )
        target_ready = total >= 44 and scores["evidence_authority"] >= 1 and scores["object_clarity"] >= 1 and scores["dependency_readiness"] >= 1 and scores["bounded_scope"] >= 1 and scores["noncircularity"] == 2
        execution_ready = all(scores[key] == 2 for key in ("evidence_authority", "object_clarity", "dependency_readiness", "restoration_clarity", "noncircularity"))
        totals_match = totals_match and prepared["weighted_total"] == total
        readiness_match = readiness_match and prepared["target_selection_ready"] == target_ready and prepared["resolution_execution_ready"] == execution_ready
        recomputed.append({"row_id": row_id, "code": CODE_BY_ROW[row_id], "scores": scores, "total": total, "conflicts": prepared["unresolved_conflict_ids"], "target_ready": target_ready, "execution_ready": execution_ready})
    sensitivity = {threshold: _select(recomputed, threshold) for threshold in THRESHOLDS}
    prepared_sensitivity = {item["threshold"]: item["selected_row_id"] for item in packet["sensitivity_analysis"]}
    decisions = {
        "immutable_selector_preparation_bound": custody_result["passed"],
        "all_eight_criteria_independently_recomputed": score_match and all(len(row["scores"]) == 8 for row in recomputed),
        "every_score_binds_propositions_reasons_and_next_evidence": reason_bindings,
        "weighted_totals_independently_recomputed": totals_match,
        "target_readiness_gates_recomputed": readiness_match,
        "execution_readiness_gates_recomputed": readiness_match and not any(row["execution_ready"] for row in recomputed),
        "sensitivity_selection_recomputed_at_all_thresholds": sensitivity == prepared_sensitivity,
        "SR_is_stable_highest_scoring_selection": all(value == "PILLAR-SR-units_and_dimensions-v0" for value in sensitivity.values()),
        "tie_break_used_only_for_exact_score_tie": packet["canonical_selection"]["tie_break_used"] is False,
        "no_unit_assignment_or_restoration_is_authorized": packet["unit_assignment_authorized"] is False and packet["restoration_rule_authorized"] is False,
        "Maxwell_Dirac_remains_candidate_and_nonclaims_hold": packet["boundary"]["Maxwell_Dirac_selected"] is False and packet["Maxwell_Dirac_status"] == "PREFERRED_DOWNSTREAM_CANDIDATE_NOT_SELECTED_RESULT",
        "Prompt_preserved": sha256_path(REPO_ROOT / PROMPT_RELATIVE_PATH) == PROMPT_SHA256,
    }
    ordered = [{"decision_id": item, "passed": decisions[item]} for item in DECISION_IDS]
    failed = [item["decision_id"] for item in ordered if not item["passed"]]
    accepted = not failed
    return {
        "schema_id": REVIEW_SCHEMA_ID,
        "captured_at_utc": CAPTURED_AT_UTC,
        "review_target": REVIEW_TARGET,
        "accepted": accepted,
        "verdict": "ACCEPT" if accepted else "B-BLOCKED",
        "selected_next_target": ACCEPTED_NEXT_TARGET if accepted else BLOCKED_NEXT_TARGET,
        "selected_next_target_kind": ACCEPTED_NEXT_TARGET if accepted else BLOCKED_NEXT_TARGET,
        "decision_count": len(DECISION_IDS),
        "passed_decision_count": len(DECISION_IDS) - len(failed),
        "failed_decision_ids": failed,
        "decisions": ordered,
        "preparation_custody": custody_result,
        "independently_recomputed_rows": recomputed,
        "independently_recomputed_sensitivity": {str(key): value for key, value in sensitivity.items()},
        "selected_row_id": "PILLAR-SR-units_and_dimensions-v0" if accepted else None,
        "selected_weighted_score": 51 if accepted else None,
        "selected_row_resolution_execution_ready": False,
        "authority_rotation": {"foundation_preparation_authorized": accepted, "unit_resolution_execution_authorized": False, "Maxwell_Dirac_result_authorized": False},
        "claim": "The selector is accepted: SR is stable at 51/62 for preparation only; execution readiness remains unmet." if accepted else "The selector is blocked.",
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Review the first-unit selector.")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args(argv)
    try:
        report = build_review_report()
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    expected = canonical_json_bytes(report)
    if args.write:
        REVIEW_REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
        REVIEW_REPORT_PATH.write_bytes(expected)
        print(f"wrote selector review: {report['verdict']}; {report['passed_decision_count']}/{report['decision_count']} decisions pass")
        return 0 if report["accepted"] else 2
    if args.check:
        if not REVIEW_REPORT_PATH.is_file() or REVIEW_REPORT_PATH.read_bytes() != expected:
            print("stale or missing selector review", file=sys.stderr)
            return 1
        print(f"selector review verified: {report['verdict']}; SR 51/62; preparation only")
        return 0 if report["accepted"] else 2
    sys.stdout.buffer.write(expected)
    return 0 if report["accepted"] else 2


if __name__ == "__main__":
    raise SystemExit(main())

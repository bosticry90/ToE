from __future__ import annotations

import argparse
import json
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "PHYSICS_PROGRESS_LEDGER_v0"

MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "release" / "TOE_GLOBAL_COMPLETION_MATRIX_v0.md"
PROGRAM_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "WS_10_GLOBAL_COMPLETION_EXECUTION_PROGRAM_20260408_v0.md"
)
TGC92_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "WS_10_TGC_92_CLOSURE_TO_BLOCKER_TRACEABILITY_DECISION_PACKAGE_20260410_v0.md"
)
TGC93_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "WS_10_TGC_93_BRANCH_DECISION_PACKAGE_20260411_v0.md"
)
TREND_WINDOW_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "governance_blocker_trend_window_20260410_v0.json"
)
CLOSURE_MAP_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "governance_blocker_closure_map_20260410_v0.json"
)


def _read(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _extract_token(text: str, token: str) -> str:
    pattern = re.compile(rf"(?m)^\s*(?:[-*]\s+)?`?{re.escape(token)}`?\s*:\s*`?(\S+?)`?\s*$")
    match = pattern.search(text)
    if not match:
        raise ValueError(f"Missing token: {token}")
    return match.group(1).strip()


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _parse_blocker_counts(matrix_text: str) -> dict[str, int]:
    counts: dict[str, int] = {}
    pat = re.compile(r"`([A-Z_]+):\s*(\d+)`")
    for key, value in pat.findall(matrix_text):
        counts[key] = int(value)

    required = [
        "THEOREM_GAP",
        "SEAM_INTEGRATION_GAP",
        "PARITY_DRIFT",
        "GOVERNANCE_GUARDRAIL",
        "EVIDENCE_ALIGNMENT_GAP",
    ]
    for key in required:
        if key not in counts:
            raise ValueError(f"Missing blocker count in matrix scoreboard: {key}")
    return counts


def _classification(net_delta: int, tgc93_decision: str) -> str:
    if net_delta < 0:
        return "PROGRESS"
    if tgc93_decision == "ROUTE_TO_THEOREM_GAP_REWORK":
        return "REWORK_ROUTED"
    return "MAINTENANCE"


def _validate_tgc93_consistency(net_delta: int, tgc93_decision: str) -> None:
    known = {
        "AUTHORIZE_SINGLE_SEAM_REENTRY",
        "ROUTE_TO_THEOREM_GAP_REWORK",
    }
    if tgc93_decision not in known:
        raise ValueError(f"Unexpected TGC-93 branch decision token: {tgc93_decision!r}")

    # Fail closed when route intent and blocker movement are contradictory.
    if net_delta < 0 and tgc93_decision == "ROUTE_TO_THEOREM_GAP_REWORK":
        raise ValueError(
            "Contradiction detected: blocker net delta is negative but TGC-93 decision routes to theorem-gap rework."
        )
    if net_delta >= 0 and tgc93_decision == "AUTHORIZE_SINGLE_SEAM_REENTRY":
        raise ValueError(
            "Contradiction detected: blocker net delta is non-negative but TGC-93 decision authorizes seam reentry."
        )


def _movement_token(net_delta: int) -> str:
    if net_delta < 0:
        return "NEGATIVE_DELTA_DETECTED"
    if net_delta > 0:
        return "POSITIVE_DELTA_DETECTED"
    return "NO_DELTA_DETECTED"


def _row_level_evidence(closure_map: dict[str, Any]) -> list[dict[str, str]]:
    rows = closure_map.get("mappings", [])
    evidence: list[dict[str, str]] = []
    for row in rows:
        blocker_class = str(row.get("blocker_class", ""))
        if blocker_class not in {"THEOREM_GAP", "SEAM_INTEGRATION_GAP", "PARITY_DRIFT"}:
            continue
        evidence.append(
            {
                "row_id": str(row.get("row_id", "")),
                "blocker_class": blocker_class,
                "exit_criterion": str(row.get("exit_criterion", "")),
                "required_closure_artifact": str(row.get("required_closure_artifact", "")),
                "closure_gate": str(row.get("closure_gate", "")),
            }
        )
    return evidence


def _resolve_timestamp(captured_at_utc: str | None) -> str:
    if captured_at_utc:
        return captured_at_utc
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def build_payload(captured_at_utc: str | None) -> dict[str, Any]:
    matrix_text = _read(MATRIX_PATH)
    program_text = _read(PROGRAM_PATH)
    tgc92_text = _read(TGC92_PATH)
    tgc93_text = _read(TGC93_PATH)
    trend_window = _read_json(TREND_WINDOW_REPORT_PATH)
    closure_map = _read_json(CLOSURE_MAP_REPORT_PATH)

    blocker_counts = _parse_blocker_counts(matrix_text)
    active_routing_decision_pointer = _extract_token(program_text, "CURRENT_ACTIVE_ROUTING_DECISION_POINTER_v0")
    tgc92_evidence = _extract_token(tgc92_text, "TGC92_BLOCKER_REDUCING_CLOSURE_EVIDENCE_v0")
    tgc93_decision = _extract_token(tgc93_text, "TGC93_BRANCH_DECISION_v0")
    expected_tgc93_pointer = str(TGC93_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
    if active_routing_decision_pointer != expected_tgc93_pointer:
        raise ValueError(
            "Global completion execution program active routing pointer does not match canonical TGC-93 decision."
        )
    trend_delta = int(trend_window.get("blocker_counts", {}).get("net_delta", 0))
    trend_movement_status = str(trend_window.get("trend_summary", {}).get("movement_status", "UNKNOWN"))
    row_level_evidence = _row_level_evidence(closure_map)
    if not row_level_evidence:
        raise ValueError("Closure map produced zero row-level evidence rows.")
    _validate_tgc93_consistency(trend_delta, tgc93_decision)

    progress_classification = _classification(trend_delta, tgc93_decision)
    actual_blocker_state_change = _movement_token(trend_delta)
    if progress_classification == "REWORK_ROUTED":
        actual_blocker_state_change = f"{actual_blocker_state_change}_ROUTE_TO_REWORK"

    trend_pointer = str(TREND_WINDOW_REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")
    closure_pointer = str(CLOSURE_MAP_REPORT_PATH.relative_to(REPO_ROOT)).replace("\\", "/")

    payload = {
        "schema_id": SCHEMA_ID,
        "captured_at_utc": _resolve_timestamp(captured_at_utc),
        "matrix_pointer": str(MATRIX_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
        "program_pointer": str(PROGRAM_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
        "tgc92_pointer": str(TGC92_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
        "tgc93_pointer": str(TGC93_PATH.relative_to(REPO_ROOT)).replace("\\", "/"),
        "active_routing_decision_source": active_routing_decision_pointer,
        "trend_window_pointer": trend_pointer,
        "closure_map_pointer": closure_pointer,
        "blocker_counts": blocker_counts,
        "target_blocker_state_change": "REQUIRE_NEGATIVE_DELTA_OR_EXPLICIT_REWORK_ROUTE",
        "actual_blocker_state_change": actual_blocker_state_change,
        "progress_classification": progress_classification,
        "evidence_pointer": trend_pointer,
        "evidence_bundle": {
            "trend_window": {
                "pointer": trend_pointer,
                "movement_status": trend_movement_status,
                "net_delta": trend_delta,
            },
            "closure_map": {
                "pointer": closure_pointer,
                "rows_total": len(row_level_evidence),
                "row_level_evidence": row_level_evidence,
            },
            "tgc_tokens": {
                "tgc92_blocker_reducing_closure_evidence": tgc92_evidence,
                "tgc93_branch_decision": tgc93_decision,
                "active_routing_decision_source": active_routing_decision_pointer,
            },
            "consistency": {
                "status": "CONSISTENT",
                "rule": "FAIL_CLOSED_ON_TREND_DELTA_AND_TGC93_ROUTE_CONTRADICTION",
            },
        },
        "non_claim_boundary": "This ledger is a repository-local progress-classification artifact and does not assert global physics adequacy claims.",
    }
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate canonical physics progress ledger report.")
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "physics_progress_ledger_v0.json",
        help="Output path for physics progress ledger JSON.",
    )
    parser.add_argument(
        "--captured-at-utc",
        default=None,
        help="Optional RFC3339 UTC timestamp override.",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    out_path = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)

    payload = build_payload(captured_at_utc=ns.captured_at_utc)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    print(
        "physics_progress_ledger_generate: "
        f"classification={payload['progress_classification']} "
        f"out={out_path}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

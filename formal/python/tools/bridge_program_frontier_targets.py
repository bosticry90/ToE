from __future__ import annotations

"""Deterministic frontier-target extractor for bridge-program mismatch regions."""

if __name__ == "__main__" and (__package__ is None or __package__ == ""):
    from pathlib import Path as _Path

    _tool = _Path(__file__).stem
    raise SystemExit(
        "Do not run this tool as a script.\n"
        "Run it as a module so package imports resolve.\n\n"
        f"  .\\py.ps1 -m formal.python.tools.{_tool} --help\n"
    )

import argparse
import hashlib
import json
from pathlib import Path
from typing import Optional


SOURCE_MISMATCH_REPORT = "formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_MISMATCH_REPORT.json"
SOURCE_SUMMARY_REPORT = "formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_MISMATCH_REASON_SUMMARY.json"
DEFAULT_TARGET_REASONS = (
    "mismatch_toyh_current_only",
    "mismatch_toyh_pair_vs_toyg_bridge",
)


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    if p.is_file():
        p = p.parent
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def _sha256_path(p: Path) -> str:
    h = hashlib.sha256()
    with p.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _sha256_bytes(data: bytes) -> str:
    h = hashlib.sha256()
    h.update(data)
    return h.hexdigest()


def _ticket_for_reason(reason: str) -> str:
    if reason == "mismatch_toyh_current_only":
        return "BRIDGE_TICKET_TOYH_0004"
    if reason == "mismatch_toyh_pair_vs_toyg_bridge":
        return "BRIDGE_TICKET_TOYHG_0001"
    return "BRIDGE_TICKET_PROGRAM_TBD"


def _resolved_counter_key_for_reason(reason: str) -> str:
    if reason == "mismatch_toyh_current_only":
        return "n_current_control_fail_resolved_by_current_anchor"
    if reason == "mismatch_toyh_pair_vs_toyg_bridge":
        return "n_pair_vs_bridge_resolved_by_pair_channel"
    return ""


def _numeric_margin(ch: dict) -> Optional[float]:
    raw = dict(ch).get("signed_margin", None)
    try:
        if raw is None:
            return None
        return float(raw)
    except (TypeError, ValueError):
        return None


def _item_failure_score(item: dict) -> float:
    channels = dict(item.get("channels", {}))
    failing: list[float] = []
    for _, ch in sorted(channels.items()):
        p = bool(dict(ch).get("pass", True))
        if p:
            continue
        m = _numeric_margin(dict(ch))
        if m is not None:
            failing.append(float(m))
    if not failing:
        return 0.0
    return float(min(failing))


def _candidate_probe_ids(items: list[dict]) -> list[str]:
    out = sorted({str(it.get("probe_id", "")) for it in items if str(it.get("probe_id", ""))})
    return out


def build_bridge_program_frontier_targets(
    *,
    repo_root: Path,
    source_mismatch_report: str = SOURCE_MISMATCH_REPORT,
    source_summary_report: str = SOURCE_SUMMARY_REPORT,
    target_reasons: tuple[str, ...] = DEFAULT_TARGET_REASONS,
    top_k: int = 1,
) -> dict:
    top_k = int(top_k)
    if top_k < 1:
        raise ValueError("top_k must be >= 1")

    mismatch_path = repo_root / str(source_mismatch_report)
    summary_path = repo_root / str(source_summary_report)

    mismatch_payload = json.loads(mismatch_path.read_text(encoding="utf-8"))
    summary_payload = json.loads(summary_path.read_text(encoding="utf-8"))

    mismatch_items = [dict(it) for it in mismatch_payload.get("items", [])]
    summary = dict(summary_payload.get("summary", {}))
    reason_counts = {str(k): int(v) for k, v in dict(summary.get("reason_code_counts", {})).items()}
    target_resolution = dict(summary.get("targeted_resolution", {}))

    targets: list[dict] = []
    for reason in tuple(str(r) for r in target_reasons):
        items = [it for it in mismatch_items if str(it.get("reason_code")) == reason]
        items_sorted = sorted(
            items,
            key=lambda it: (
                float(_item_failure_score(it)),
                str(it.get("probe_id", "")),
            ),
        )

        selected = items_sorted[:top_k]
        selected_probe_ids = [str(it.get("probe_id", "")) for it in selected if str(it.get("probe_id", ""))]
        selected_details = [
            {
                "probe_id": str(it.get("probe_id", "")),
                "probe_kind": str(it.get("probe_kind", "")),
                "signature": str(it.get("signature", "")),
                "localization_note": str(it.get("localization_note", "")),
                "failure_score": float(_item_failure_score(it)),
            }
            for it in selected
        ]
        selected_details = sorted(selected_details, key=lambda d: (float(d["failure_score"]), str(d["probe_id"])))

        resolved_counter_key = _resolved_counter_key_for_reason(reason)
        resolved_by_count = int(target_resolution.get(resolved_counter_key, 0)) if resolved_counter_key else 0

        if items_sorted:
            status = "open"
        else:
            status = "resolved"

        targets.append(
            {
                "reason_code": reason,
                "status": status,
                "count": int(reason_counts.get(reason, 0)),
                "resolved_by_count": int(resolved_by_count),
                "ticket": _ticket_for_reason(reason),
                "selection_policy": "min_failure_score_then_probe_id",
                "top_k": int(top_k),
                "candidate_probe_ids": _candidate_probe_ids(items_sorted),
                "selected_probe_ids": selected_probe_ids,
                "selected": selected_details,
            }
        )

    open_targets = [t for t in targets if str(t.get("status")) == "open"]
    frontier_complete = len(open_targets) == 0

    payload = {
        "schema_version": 1,
        "report_id": "BRIDGE_PROGRAM_FRONTIER_TARGETS",
        "source_artifacts": {
            "mismatch_report": {
                "path": str(source_mismatch_report),
                "sha256": _sha256_path(mismatch_path),
            },
            "mismatch_reason_summary": {
                "path": str(source_summary_report),
                "sha256": _sha256_path(summary_path),
            },
        },
        "summary": {
            "n_mismatch_total": int(summary.get("n_mismatch", 0)),
            "target_reason_codes": [str(r) for r in target_reasons],
            "open_targets_count": int(len(open_targets)),
            "resolved_targets_count": int(len(targets) - len(open_targets)),
            "frontier_complete": bool(frontier_complete),
            "reason_code_counts": {k: int(reason_counts[k]) for k in sorted(reason_counts.keys())},
        },
        "targets": targets,
        "recommended_next_ticket": (
            "BRIDGE_TICKET_PROGRAM_COMPLETE" if frontier_complete else str(open_targets[0].get("ticket", "BRIDGE_TICKET_PROGRAM_TBD"))
        ),
        "evidence": {
            "pytest_nodes": [
                "formal/python/tests/test_bridge_program_frontier_targets_determinism.py::test_bridge_program_frontier_targets_is_deterministic",
                "formal/python/tests/test_bridge_program_frontier_targets_semantics.py::test_bridge_program_frontier_targets_track_historical_frontier_reasons",
                "formal/python/tests/test_bridge_program_frontier_targets_pointers_exist.py::test_bridge_program_frontier_targets_artifact_pointers_exist",
            ]
        },
    }

    out_text = json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    payload["artifact_sha256"] = _sha256_bytes(out_text.encode("utf-8"))
    return payload


def main(argv: Optional[list[str]] = None) -> int:
    p = argparse.ArgumentParser(description="Generate deterministic bridge-program frontier targets artifact.")
    p.add_argument(
        "--out",
        default="formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_FRONTIER_TARGETS.json",
        help=(
            "Repo-relative output JSON path (default: "
            "formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_FRONTIER_TARGETS.json)"
        ),
    )
    p.add_argument("--no-write", action="store_true", help="Do not write the file; just validate generation")
    p.add_argument(
        "--source-mismatch-report",
        default=SOURCE_MISMATCH_REPORT,
        help="Repo-relative mismatch report JSON path (default: baseline mismatch report).",
    )
    p.add_argument(
        "--source-summary-report",
        default=SOURCE_SUMMARY_REPORT,
        help="Repo-relative mismatch reason summary JSON path (default: baseline summary).",
    )
    p.add_argument(
        "--target-reason",
        action="append",
        default=[],
        help="Target reason code to track (repeatable). Defaults to the two historical frontier reasons.",
    )
    p.add_argument(
        "--top-k",
        type=int,
        default=1,
        help="Number of selected probes to keep per open target (default: 1).",
    )
    args = p.parse_args(argv)

    target_reasons = tuple(args.target_reason) if args.target_reason else DEFAULT_TARGET_REASONS
    repo_root = _find_repo_root(Path(__file__))
    payload = build_bridge_program_frontier_targets(
        repo_root=repo_root,
        source_mismatch_report=str(args.source_mismatch_report),
        source_summary_report=str(args.source_summary_report),
        target_reasons=target_reasons,
        top_k=int(args.top_k),
    )
    out_text = json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"

    if not args.no_write:
        out_path = repo_root / str(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(out_text, encoding="utf-8")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())

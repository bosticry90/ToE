from __future__ import annotations

"""Deterministic extractor for program-level bridge mismatch reason summary."""

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
SOURCE_ORTHOGONALITY_REPORT = "formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_ORTHOGONALITY_REPORT.json"

_REASON_PRIORITY = {
    "mismatch_toyhg_pair_only": 0,
    "mismatch_toyh_phase_only": 1,
    "mismatch_toyh_current_only": 2,
    "mismatch_toyh_pair_only": 3,
    "mismatch_phase_and_pair": 4,
    "mismatch_current_and_pair": 5,
}


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
    if reason == "mismatch_toyhg_pair_only":
        return "BRIDGE_TICKET_TOYHG_0001"
    if reason == "mismatch_toyh_pair_only":
        return "BRIDGE_TICKET_TOYHG_0001"
    if reason in {"mismatch_phase_and_pair", "mismatch_current_and_pair"}:
        return "BRIDGE_TICKET_TOYHG_0001"
    if reason == "mismatch_toyg_bridge_only":
        return "BRIDGE_TICKET_TOYG_0003"
    if reason == "mismatch_toyh_phase_only":
        return "BRIDGE_TICKET_TOYH_0003"
    if reason == "mismatch_toyh_current_only":
        return "BRIDGE_TICKET_TOYH_0004"
    if reason == "none":
        return "BRIDGE_TICKET_PROGRAM_COMPLETE"
    return "BRIDGE_TICKET_PROGRAM_TBD"


def build_bridge_program_mismatch_reason_summary(
    *,
    repo_root: Path,
    source_mismatch_report: str = SOURCE_MISMATCH_REPORT,
    source_orthogonality_report: str = SOURCE_ORTHOGONALITY_REPORT,
) -> dict:
    mismatch_path = repo_root / str(source_mismatch_report)
    orth_path = repo_root / str(source_orthogonality_report)

    mismatch_payload = json.loads(mismatch_path.read_text(encoding="utf-8"))
    orth_payload = json.loads(orth_path.read_text(encoding="utf-8"))

    reason_counts = {
        str(k): int(v)
        for k, v in dict(mismatch_payload.get("summary", {}).get("reason_code_counts", {})).items()
    }
    items = list(mismatch_payload.get("items", []))

    channel_reason_counts = {
        "toyh_phase_bridge": {},
        "toyh_current_bridge": {},
        "toyg_bridge": {},
        "toyhg_pair_bridge": {},
        "toyg_winding": {},
        "toyg_mode": {},
        "toyg_unwrap": {},
        "toyh_phase": {},
        "toyh_phase_anchor": {},
        "toyh_current_anchor": {},
        "toyh_current": {},
    }
    reason_probe_ids: dict[str, list[str]] = {}
    for it in items:
        reason = str(it.get("reason_code", "UNKNOWN"))
        reason_probe_ids.setdefault(reason, []).append(str(it.get("probe_id", "")))

        channels = dict(it.get("channels", {}))
        for ch in channel_reason_counts.keys():
            ch_payload = dict(channels.get(ch, {}))
            ch_reason = str(ch_payload.get("reason_code", "UNKNOWN"))
            counts = channel_reason_counts[ch]
            counts[ch_reason] = int(counts.get(ch_reason, 0)) + 1

    ranked = sorted(
        reason_counts.items(),
        key=lambda kv: (-int(kv[1]), int(_REASON_PRIORITY.get(str(kv[0]), 99)), str(kv[0])),
    )
    recommended_reason = str(ranked[0][0]) if ranked else "none"
    recommended_count = int(ranked[0][1]) if ranked else 0

    orth_summary = dict(orth_payload.get("summary", {}))
    targeted_resolution = dict(orth_summary.get("targeted_resolution", {}))

    payload = {
        "schema_version": 1,
        "report_id": "BRIDGE_PROGRAM_MISMATCH_REASON_SUMMARY",
        "source_artifacts": {
            "orthogonality_report": {
                "path": str(source_orthogonality_report),
                "sha256": _sha256_path(orth_path),
            },
            "mismatch_report": {
                "path": str(source_mismatch_report),
                "sha256": _sha256_path(mismatch_path),
            },
        },
        "summary": {
            "n_mismatch": int(mismatch_payload.get("summary", {}).get("n_mismatch", 0)),
            "reason_code_counts": {k: reason_counts[k] for k in sorted(reason_counts.keys())},
            "targeted_resolution": {
                "n_winding_not_integer_close_resolved_by_mode": int(
                    targeted_resolution.get("n_winding_not_integer_close_resolved_by_mode", 0)
                ),
                "n_winding_unwrap_guard_resolved_by_unwrap": int(
                    targeted_resolution.get("n_winding_unwrap_guard_resolved_by_unwrap", 0)
                ),
                "n_phase_control_fail_resolved_by_phase_anchor": int(
                    targeted_resolution.get("n_phase_control_fail_resolved_by_phase_anchor", 0)
                ),
                "n_current_control_fail_resolved_by_current_anchor": int(
                    targeted_resolution.get("n_current_control_fail_resolved_by_current_anchor", 0)
                ),
                "n_pair_vs_bridge_resolved_by_pair_channel": int(
                    targeted_resolution.get("n_pair_vs_bridge_resolved_by_pair_channel", 0)
                ),
            },
        },
        "ranking_policy": {
            "primary": "descending_reason_count",
            "tie_break_1": "reason_priority_map",
            "tie_break_2": "lexicographic_reason_code",
            "reason_priority_map": dict(_REASON_PRIORITY),
        },
        "ranked_targets": [
            {
                "reason_code": str(reason),
                "count": int(count),
                "priority_rank": int(_REASON_PRIORITY.get(str(reason), 99)),
                "probe_ids": sorted(reason_probe_ids.get(str(reason), [])),
                "suggested_design_ticket": _ticket_for_reason(str(reason)),
            }
            for reason, count in ranked
        ],
        "channel_reason_counts": {
            channel: {k: channel_reason_counts[channel][k] for k in sorted(channel_reason_counts[channel].keys())}
            for channel in sorted(channel_reason_counts.keys())
        },
        "recommended_next_target": {
            "reason_code": recommended_reason,
            "count": int(recommended_count),
            "suggested_design_ticket": _ticket_for_reason(recommended_reason),
        },
    }

    out_text = json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    payload["artifact_sha256"] = _sha256_bytes(out_text.encode("utf-8"))
    return payload


def main(argv: Optional[list[str]] = None) -> int:
    p = argparse.ArgumentParser(description="Generate deterministic bridge-program mismatch reason summary.")
    p.add_argument(
        "--out",
        default="formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_MISMATCH_REASON_SUMMARY.json",
        help=(
            "Repo-relative output JSON path (default: "
            "formal/quarantine/bridge_tickets/BRIDGE_PROGRAM_MISMATCH_REASON_SUMMARY.json)"
        ),
    )
    p.add_argument("--no-write", action="store_true", help="Do not write the file; just validate generation")
    p.add_argument(
        "--source-orthogonality-report",
        default=SOURCE_ORTHOGONALITY_REPORT,
        help="Repo-relative orthogonality report JSON path (default: baseline orthogonality report).",
    )
    p.add_argument(
        "--source-mismatch-report",
        default=SOURCE_MISMATCH_REPORT,
        help="Repo-relative mismatch report JSON path (default: baseline mismatch report).",
    )
    args = p.parse_args(argv)

    repo_root = _find_repo_root(Path(__file__))
    payload = build_bridge_program_mismatch_reason_summary(
        repo_root=repo_root,
        source_orthogonality_report=str(args.source_orthogonality_report),
        source_mismatch_report=str(args.source_mismatch_report),
    )
    out_text = json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False) + "\n"

    if not args.no_write:
        out_path = repo_root / str(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(out_text, encoding="utf-8")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())

from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


def _resolve_repo_root(start: Path) -> Path:
    p = start.resolve()
    if p.is_file():
        p = p.parent
    while p != p.parent:
        if (p / "formal" / "python").exists() and (p / "State_of_the_Theory.md").exists():
            return p
        p = p.parent
    return find_repo_root(start)


REPO_ROOT = _resolve_repo_root(Path(__file__))
SCHEMA_ID = "DISCOVERY_PRIORITY_QUEUE_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "DISCOVERY_PRIORITY_QUEUE_20260411_v0.json"
DEFAULT_TREND_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_blocker_trend_window_20260410_v0.json"
DEFAULT_CLOSURE_MAP_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_blocker_closure_map_20260410_v0.json"
DEFAULT_LEDGER_PATH = REPO_ROOT / "formal" / "output" / "reports" / "physics_progress_ledger_v0.json"
DEFAULT_OUT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "discovery_priority_queue_report_20260411_v0.json"

BOOSTS: dict[str, dict[str, int]] = {
    "ROW-SEAM-QM-STAT-001": {
        "discriminator_potential": 5,
        "falsification_value": 4,
        "blocker_leverage": 5,
        "empirical_proximity": 3,
    },
    "ROW-SEAM-QFT-GR-001": {
        "discriminator_potential": 4,
        "falsification_value": 5,
        "blocker_leverage": 4,
        "empirical_proximity": 2,
    },
    "ROW-PILLAR-GR-001": {
        "discriminator_potential": 4,
        "falsification_value": 4,
        "blocker_leverage": 4,
        "empirical_proximity": 3,
    },
    "ROW-PILLAR-QFT-001": {
        "discriminator_potential": 4,
        "falsification_value": 4,
        "blocker_leverage": 3,
        "empirical_proximity": 2,
    },
    "ROW-PILLAR-STAT-001": {
        "discriminator_potential": 3,
        "falsification_value": 4,
        "blocker_leverage": 3,
        "empirical_proximity": 3,
    },
}


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _score(parts: dict[str, int]) -> int:
    return 4 * parts["discriminator_potential"] + 3 * parts["falsification_value"] + 2 * parts["blocker_leverage"] + parts["empirical_proximity"]


def _defaults_for_row(row_id: str, blocker_class: str, domain: str) -> dict[str, int]:
    if blocker_class == "SEAM_INTEGRATION_GAP":
        return {
            "discriminator_potential": 4,
            "falsification_value": 4,
            "blocker_leverage": 4,
            "empirical_proximity": 2,
        }
    if blocker_class == "PARITY_DRIFT":
        return {
            "discriminator_potential": 3,
            "falsification_value": 3,
            "blocker_leverage": 3,
            "empirical_proximity": 2,
        }
    _ = row_id, domain
    return {
        "discriminator_potential": 3,
        "falsification_value": 3,
        "blocker_leverage": 3,
        "empirical_proximity": 3,
    }


def build_report(*, declaration_path: Path, trend_path: Path, closure_map_path: Path, ledger_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    trend = _read_json(trend_path)
    closure_map = _read_json(closure_map_path)
    ledger = _read_json(ledger_path)

    ranking_policy = dict(declaration.get("ranking_policy", {}))
    queue_size = int(ranking_policy.get("queue_size", 5))

    candidates: list[dict[str, Any]] = []
    for mapping in closure_map.get("mappings", []):
        row_id = str(mapping.get("row_id", "")).strip()
        blocker_class = str(mapping.get("blocker_class", "")).strip()
        domain = str(mapping.get("domain", "")).strip()
        lane = str(mapping.get("owning_lane", "")).strip()

        if not row_id or not blocker_class:
            continue

        dimensions = dict(_defaults_for_row(row_id, blocker_class, domain))
        if row_id in BOOSTS:
            dimensions = dict(BOOSTS[row_id])

        score = _score(dimensions)
        candidates.append(
            {
                "row_id": row_id,
                "lane": lane,
                "blocker_class": blocker_class,
                "domain": domain,
                **dimensions,
                "score": score,
                "closure_gate": mapping.get("closure_gate"),
                "required_closure_artifact": mapping.get("required_closure_artifact"),
            }
        )

    candidates.sort(
        key=lambda c: (
            int(c["score"]),
            int(c["falsification_value"]),
            int(c["blocker_leverage"]),
        ),
        reverse=True,
    )

    top = candidates[:queue_size]
    ranked = []
    for idx, item in enumerate(top, start=1):
        ranked.append({"rank": idx, **item})

    current_counts = dict(trend.get("blocker_counts", {}).get("current", {}))
    net_delta = trend.get("blocker_counts", {}).get("net_delta")
    progress_classification = str(ledger.get("progress_classification", "")).strip()

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "summary": {
            "queue_size": len(ranked),
            "configured_queue_size": queue_size,
            "top_rank_row": ranked[0]["row_id"] if ranked else "",
            "blocker_net_delta": net_delta,
            "progress_classification": progress_classification,
        },
        "ranking_policy": {
            "score_formula": ranking_policy.get(
                "score_formula",
                "4x_DISCRIMINATOR_POTENTIAL_PLUS3x_FALSIFICATION_VALUE_PLUS2x_BLOCKER_LEVERAGE_PLUS1x_EMPIRICAL_PROXIMITY",
            ),
            "tie_breaker": ranking_policy.get("tie_breaker", "HIGHER_FALSIFICATION_VALUE_THEN_HIGHER_BLOCKER_LEVERAGE"),
            "queue_size": queue_size,
        },
        "blocker_context": {
            "current_counts": current_counts,
            "net_delta": net_delta,
            "movement_status": trend.get("trend_summary", {}).get("movement_status"),
            "ledger_progress_classification": progress_classification,
        },
        "ranked_candidates": ranked,
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "trend": _ptr(trend_path),
            "closure_map": _ptr(closure_map_path),
            "ledger": _ptr(ledger_path),
        },
        "non_claim_boundary": "Repository-local discovery priority queue report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate ranked discovery priority queue report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument("--trend", type=Path, default=DEFAULT_TREND_PATH)
    parser.add_argument("--closure-map", type=Path, default=DEFAULT_CLOSURE_MAP_PATH)
    parser.add_argument("--ledger", type=Path, default=DEFAULT_LEDGER_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT_PATH)
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    declaration_path = ns.declaration if ns.declaration.is_absolute() else (REPO_ROOT / ns.declaration)
    trend_path = ns.trend if ns.trend.is_absolute() else (REPO_ROOT / ns.trend)
    closure_map_path = ns.closure_map if ns.closure_map.is_absolute() else (REPO_ROOT / ns.closure_map)
    ledger_path = ns.ledger if ns.ledger.is_absolute() else (REPO_ROOT / ns.ledger)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)

    payload = build_report(
        declaration_path=declaration_path,
        trend_path=trend_path,
        closure_map_path=closure_map_path,
        ledger_path=ledger_path,
        captured_at_utc=ns.captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "discovery_priority_queue_report: "
        f"top_rank_row={payload['summary']['top_rank_row']} queue_size={payload['summary']['queue_size']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

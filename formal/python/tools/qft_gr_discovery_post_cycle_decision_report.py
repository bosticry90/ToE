from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_discovery_interpretation_report import build_report as build_interpretation_report
from formal.python.tools.qft_gr_discovery_ruling_report import build_report as build_ruling_report


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QFT_GR_DISCOVERY_POST_CYCLE_DECISION_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_DISCOVERY_POST_CYCLE_DECISION_20260411_v0.json"
)


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


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    decision_policy = dict(declaration.get("decision_policy", {}))

    interpretation_path = REPO_ROOT / str(required_inputs.get("discovery_interpretation_report", "")).strip()
    ruling_path = REPO_ROOT / str(required_inputs.get("discovery_ruling_report", "")).strip()

    if not interpretation_path.exists():
        interpretation_declaration = REPO_ROOT / "formal" / "docs" / "release" / "QFT_GR_DISCOVERY_INTERPRETATION_20260411_v0.json"
        generated = build_interpretation_report(
            declaration_path=interpretation_declaration,
            captured_at_utc=captured_at_utc,
        )
        interpretation_path.parent.mkdir(parents=True, exist_ok=True)
        interpretation_path.write_text(json.dumps(generated, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    if not ruling_path.exists():
        ruling_declaration = REPO_ROOT / "formal" / "docs" / "release" / "QFT_GR_DISCOVERY_RULING_20260411_v0.json"
        generated = build_ruling_report(
            declaration_path=ruling_declaration,
            captured_at_utc=captured_at_utc,
        )
        ruling_path.parent.mkdir(parents=True, exist_ok=True)
        ruling_path.write_text(json.dumps(generated, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    interpretation = _read_json(interpretation_path)
    ruling = _read_json(ruling_path)

    interpretation_summary = dict(interpretation.get("summary", {}))
    ruling_summary = dict(ruling.get("summary", {}))

    interpretation_class = str(interpretation_summary.get("interpretation", "")).strip()
    ruling_value = str(ruling_summary.get("ruling", "")).strip()

    stronger_comparator_identified = bool(decision_policy.get("stronger_comparator_identified", False))
    bounded_comparator_refinement_packet = decision_policy.get("bounded_comparator_refinement_packet")
    bounded_comparator_defined = isinstance(bounded_comparator_refinement_packet, str) and bool(
        bounded_comparator_refinement_packet.strip()
    )

    if interpretation_class == "PATH_FALSIFIED":
        decision = "RETIRE_THIS_QFT_GR_DISCOVERY_PATH_NONPRODUCTIVE"
        disposition = "RETIRE_PATH"
        probe_lane_allowed = False
        next_action = "ADVANCE_DISCOVERY_QUEUE_TO_NEXT_SEAM"
    elif interpretation_class == "PROBE_READY":
        if stronger_comparator_identified and bounded_comparator_defined:
            decision = "REFINE_QFT_GR_COMPARATOR_ONCE_BOUNDED"
            disposition = "REFINE_COMPARATOR_ONCE"
            probe_lane_allowed = False
            next_action = "MATERIALIZE_ONE_QFT_GR_STRONGER_COMPARATOR_PACKET"
        else:
            decision = "KEEP_QFT_GR_AS_INTERNAL_DISCRIMINATOR_LANE"
            disposition = "KEEP_INTERNAL_LANE"
            probe_lane_allowed = False
            next_action = "HOLD_QFT_GR_INTERNAL_AND_BLOCK_PROBE_EXPANSION"
    elif interpretation_class == "EXTERNALLY_COMPARABLE_CANDIDATE":
        if stronger_comparator_identified and bounded_comparator_defined:
            decision = "REFINE_QFT_GR_COMPARATOR_ONCE_BOUNDED"
            disposition = "REFINE_COMPARATOR_ONCE"
            probe_lane_allowed = False
            next_action = "MATERIALIZE_ONE_QFT_GR_STRONGER_COMPARATOR_PACKET"
        else:
            decision = "KEEP_QFT_GR_AS_INTERNAL_DISCRIMINATOR_LANE"
            disposition = "KEEP_INTERNAL_LANE"
            probe_lane_allowed = False
            next_action = "HOLD_QFT_GR_INTERNAL_AND_BLOCK_PROBE_EXPANSION"
    else:
        decision = "KEEP_QFT_GR_AS_INTERNAL_DISCRIMINATOR_LANE"
        disposition = "KEEP_INTERNAL_LANE"
        probe_lane_allowed = False
        next_action = "HOLD_QFT_GR_INTERNAL_AND_BLOCK_PROBE_EXPANSION"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "summary": {
            "post_cycle_decision": decision,
            "decision_disposition": disposition,
            "interpretation": interpretation_class,
            "ruling": ruling_value,
            "probe_lane_allowed": probe_lane_allowed,
            "no_probe_expansion_without_interpretation_rule": str(
                decision_policy.get("no_probe_expansion_without_interpretation_rule", "")
            ).strip(),
            "no_loop_rule": str(decision_policy.get("no_loop_rule", "")).strip(),
            "next_action": next_action,
        },
        "criteria": {
            "decision_materialized": decision
            in {
                "KEEP_QFT_GR_AS_INTERNAL_DISCRIMINATOR_LANE",
                "REFINE_QFT_GR_COMPARATOR_ONCE_BOUNDED",
                "RETIRE_THIS_QFT_GR_DISCOVERY_PATH_NONPRODUCTIVE",
            },
            "probe_lane_remains_blocked": probe_lane_allowed is False,
            "bounded_decision_only": str(decision_policy.get("no_loop_rule", "")).strip()
            == "ONE_POST_QFT_GR_CYCLE_DECISION_ONLY",
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "discovery_interpretation_report": _ptr(interpretation_path),
            "discovery_ruling_report": _ptr(ruling_path),
        },
        "non_claim_boundary": "Repository-local QFT-GR post-cycle decision report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate QFT-GR post-cycle decision report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "qft_gr_discovery_post_cycle_decision_report_20260411_v0.json",
    )
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    declaration_path = ns.declaration if ns.declaration.is_absolute() else (REPO_ROOT / ns.declaration)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)

    payload = build_report(declaration_path=declaration_path, captured_at_utc=ns.captured_at_utc)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "qft_gr_discovery_post_cycle_decision_report: "
        f"post_cycle_decision={payload['summary']['post_cycle_decision']} "
        f"probe_lane_allowed={payload['summary']['probe_lane_allowed']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

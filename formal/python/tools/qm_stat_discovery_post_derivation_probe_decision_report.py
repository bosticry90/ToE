from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qm_stat_discovery_derivation_probe_ruling_report import build_report as build_paired_ruling_report
from formal.python.tools.qm_stat_discovery_interpretation_report import build_report as build_interpretation_report
from formal.python.tools.qm_stat_discovery_numerical_probe_execution_report import build_report as build_probe_execution_report


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_DISCOVERY_POST_DERIVATION_PROBE_DECISION_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_DISCOVERY_POST_DERIVATION_PROBE_DECISION_20260411_v0.json"
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

    paired_ruling_path = REPO_ROOT / str(required_inputs.get("derivation_probe_ruling_report", "")).strip()
    probe_execution_path = REPO_ROOT / str(required_inputs.get("numerical_probe_execution_report", "")).strip()
    interpretation_path = REPO_ROOT / str(required_inputs.get("discovery_interpretation_report", "")).strip()

    if not interpretation_path.exists():
        interpretation_declaration = REPO_ROOT / "formal" / "docs" / "release" / "QM_STAT_DISCOVERY_INTERPRETATION_20260411_v0.json"
        generated = build_interpretation_report(
            declaration_path=interpretation_declaration,
            captured_at_utc=captured_at_utc,
        )
        interpretation_path.parent.mkdir(parents=True, exist_ok=True)
        interpretation_path.write_text(json.dumps(generated, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    if not probe_execution_path.exists():
        probe_exec_declaration = REPO_ROOT / "formal" / "docs" / "release" / "QM_STAT_DISCOVERY_NUMERICAL_PROBE_EXECUTION_20260411_v0.json"
        generated = build_probe_execution_report(
            declaration_path=probe_exec_declaration,
            captured_at_utc=captured_at_utc,
        )
        probe_execution_path.parent.mkdir(parents=True, exist_ok=True)
        probe_execution_path.write_text(json.dumps(generated, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    if not paired_ruling_path.exists():
        paired_ruling_declaration = REPO_ROOT / "formal" / "docs" / "release" / "QM_STAT_DISCOVERY_DERIVATION_PROBE_RULING_20260411_v0.json"
        generated = build_paired_ruling_report(
            declaration_path=paired_ruling_declaration,
            captured_at_utc=captured_at_utc,
        )
        paired_ruling_path.parent.mkdir(parents=True, exist_ok=True)
        paired_ruling_path.write_text(json.dumps(generated, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    paired_ruling = _read_json(paired_ruling_path)
    probe_execution = _read_json(probe_execution_path)
    interpretation = _read_json(interpretation_path)

    paired_summary = dict(paired_ruling.get("summary", {}))
    probe_summary = dict(probe_execution.get("summary", {}))
    interpretation_summary = dict(interpretation.get("summary", {}))

    paired_outcome = str(paired_summary.get("paired_outcome", "")).strip()
    probe_signal = str(probe_summary.get("probe_signal", "")).strip()
    interpretation_class = str(interpretation_summary.get("interpretation", "")).strip()

    stronger_comparator_identified = bool(decision_policy.get("stronger_comparator_identified", False))
    bounded_comparator_refinement_packet = decision_policy.get("bounded_comparator_refinement_packet")
    bounded_comparator_defined = isinstance(bounded_comparator_refinement_packet, str) and bool(
        bounded_comparator_refinement_packet.strip()
    )

    if paired_outcome == "PROBE_REVEALS_PATH_FALSIFICATION":
        decision = "RETIRE_THIS_QM_STAT_PROBE_PATH_NONPRODUCTIVE"
        disposition = "RETIRE_PROBE_PATH"
        auto_rerun_allowed = False
        next_action = "RESELECT_NEXT_DISCOVERY_TARGET_OR_PROBE_SHAPE"
    elif paired_outcome == "DERIVATION_AND_PROBE_AGREE" and stronger_comparator_identified and bounded_comparator_defined:
        decision = "REFINE_PROBE_COMPARATOR_ONCE_BOUNDED"
        disposition = "REFINE_COMPARATOR_ONCE"
        auto_rerun_allowed = False
        next_action = "MATERIALIZE_ONE_STRONGER_COMPARATOR_PACKET"
    elif paired_outcome == "DERIVATION_INTERNAL_ONLY_PROBE_NONDISCRIMINATIVE":
        if stronger_comparator_identified and bounded_comparator_defined:
            decision = "REFINE_PROBE_COMPARATOR_ONCE_BOUNDED"
            disposition = "REFINE_COMPARATOR_ONCE"
            auto_rerun_allowed = False
            next_action = "MATERIALIZE_ONE_STRONGER_COMPARATOR_PACKET"
        else:
            decision = "KEEP_QM_STAT_AS_INTERNAL_DISCRIMINATOR_LANE"
            disposition = "KEEP_INTERNAL_LANE"
            auto_rerun_allowed = False
            next_action = "HOLD_QM_STAT_INTERNAL_AND_BLOCK_AUTO_RERUN"
    else:
        decision = "RETIRE_THIS_QM_STAT_PROBE_PATH_NONPRODUCTIVE"
        disposition = "RETIRE_PROBE_PATH"
        auto_rerun_allowed = False
        next_action = "RESELECT_NEXT_DISCOVERY_TARGET_OR_PROBE_SHAPE"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "summary": {
            "post_cycle_decision": decision,
            "decision_disposition": disposition,
            "paired_outcome": paired_outcome,
            "interpretation": interpretation_class,
            "probe_signal": probe_signal,
            "auto_rerun_allowed": auto_rerun_allowed,
            "no_auto_rerun_rule": str(decision_policy.get("no_auto_rerun_rule", "")).strip(),
            "no_loop_rule": str(decision_policy.get("no_loop_rule", "")).strip(),
            "next_action": next_action,
        },
        "criteria": {
            "decision_materialized": decision
            in {
                "KEEP_QM_STAT_AS_INTERNAL_DISCRIMINATOR_LANE",
                "REFINE_PROBE_COMPARATOR_ONCE_BOUNDED",
                "RETIRE_THIS_QM_STAT_PROBE_PATH_NONPRODUCTIVE",
            },
            "auto_rerun_block_enforced": auto_rerun_allowed is False,
            "bounded_decision_only": str(decision_policy.get("no_loop_rule", "")).strip()
            == "ONE_POST_DERIVATION_PROBE_DECISION_ONLY",
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "derivation_probe_ruling_report": _ptr(paired_ruling_path),
            "numerical_probe_execution_report": _ptr(probe_execution_path),
            "discovery_interpretation_report": _ptr(interpretation_path),
        },
        "non_claim_boundary": "Repository-local QM-STAT post-derivation/probe decision report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate QM-STAT post-derivation/probe decision report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "qm_stat_discovery_post_derivation_probe_decision_report_20260411_v0.json",
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
        "qm_stat_discovery_post_derivation_probe_decision_report: "
        f"post_cycle_decision={payload['summary']['post_cycle_decision']} "
        f"auto_rerun_allowed={payload['summary']['auto_rerun_allowed']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

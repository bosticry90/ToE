from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qm_stat_discovery_interpretation_report import build_report as build_interpretation_report
from formal.python.tools.qm_stat_discovery_numerical_probe_report import build_report as build_probe_report
from formal.python.tools.qm_stat_discovery_ruling_report import build_report as build_derivation_ruling_report


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_DISCOVERY_NUMERICAL_PROBE_EXECUTION_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_DISCOVERY_NUMERICAL_PROBE_EXECUTION_20260411_v0.json"
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


def _probe_signal(*, interpretation: str, probe_executed: bool) -> str:
    if not probe_executed:
        return "PROBE_NOT_EXECUTED"
    if interpretation in {"EXTERNALLY_COMPARABLE", "NUMERICAL_PROBE_READY"}:
        return "PROBE_DISCRIMINATIVE"
    return "PROBE_NONDISCRIMINATIVE"


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    execution_policy = dict(declaration.get("execution_policy", {}))

    probe_path = REPO_ROOT / str(required_inputs.get("numerical_probe_report", "")).strip()
    interpretation_path = REPO_ROOT / str(required_inputs.get("discovery_interpretation_report", "")).strip()
    derivation_ruling_path = REPO_ROOT / str(required_inputs.get("discovery_ruling_report", "")).strip()

    if not derivation_ruling_path.exists():
        derivation_ruling_declaration = REPO_ROOT / "formal" / "docs" / "release" / "QM_STAT_DISCOVERY_RULING_20260411_v0.json"
        generated = build_derivation_ruling_report(
            declaration_path=derivation_ruling_declaration,
            captured_at_utc=captured_at_utc,
        )
        derivation_ruling_path.parent.mkdir(parents=True, exist_ok=True)
        derivation_ruling_path.write_text(json.dumps(generated, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    if not interpretation_path.exists():
        interpretation_declaration = REPO_ROOT / "formal" / "docs" / "release" / "QM_STAT_DISCOVERY_INTERPRETATION_20260411_v0.json"
        generated = build_interpretation_report(
            declaration_path=interpretation_declaration,
            captured_at_utc=captured_at_utc,
        )
        interpretation_path.parent.mkdir(parents=True, exist_ok=True)
        interpretation_path.write_text(json.dumps(generated, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    if not probe_path.exists():
        probe_declaration = REPO_ROOT / "formal" / "docs" / "release" / "QM_STAT_DISCOVERY_NUMERICAL_PROBE_20260411_v0.json"
        generated = build_probe_report(
            declaration_path=probe_declaration,
            captured_at_utc=captured_at_utc,
        )
        probe_path.parent.mkdir(parents=True, exist_ok=True)
        probe_path.write_text(json.dumps(generated, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    probe = _read_json(probe_path)
    interpretation = _read_json(interpretation_path)
    derivation_ruling = _read_json(derivation_ruling_path)

    probe_summary = dict(probe.get("summary", {}))
    interpretation_summary = dict(interpretation.get("summary", {}))
    derivation_summary = dict(derivation_ruling.get("summary", {}))

    target_row = str(execution_policy.get("target_row", "")).strip()
    max_probe_cycles = int(execution_policy.get("max_probe_cycles", 1))

    seam_alignment = bool(probe_summary.get("seam_alignment", False))
    probe_runnable = bool(probe_summary.get("probe_runnable", False))
    derivation_outcome = str(derivation_summary.get("ruling", "")).strip()
    interpretation_class = str(interpretation_summary.get("interpretation", "")).strip()

    probe_executed = seam_alignment and probe_runnable and max_probe_cycles == 1
    path_falsification_observed = False
    probe_signal = _probe_signal(interpretation=interpretation_class, probe_executed=probe_executed)

    probe_execution_status = "BOUNDED_PROBE_EXECUTED" if probe_executed else "BOUNDED_PROBE_BLOCKED"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "summary": {
            "target_row": target_row,
            "derivation_outcome": derivation_outcome,
            "interpretation": interpretation_class,
            "seam_alignment": seam_alignment,
            "probe_executed": probe_executed,
            "probe_signal": probe_signal,
            "path_falsification_observed": path_falsification_observed,
            "probe_execution_status": probe_execution_status,
            "max_probe_cycles": max_probe_cycles,
            "shadow_mode_required": bool(execution_policy.get("shadow_mode_required", True)),
            "next_action": "EMIT_DERIVATION_PROBE_PAIRED_RULING" if probe_executed else "RECONCILE_PROBE_EXECUTION_PRECONDITIONS",
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "numerical_probe_report": _ptr(probe_path),
            "discovery_interpretation_report": _ptr(interpretation_path),
            "discovery_ruling_report": _ptr(derivation_ruling_path),
        },
        "non_claim_boundary": "Repository-local QM-STAT bounded numerical probe execution report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate QM-STAT bounded numerical probe execution report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "qm_stat_discovery_numerical_probe_execution_report_20260411_v0.json",
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
        "qm_stat_discovery_numerical_probe_execution_report: "
        f"probe_execution_status={payload['summary']['probe_execution_status']} "
        f"probe_signal={payload['summary']['probe_signal']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

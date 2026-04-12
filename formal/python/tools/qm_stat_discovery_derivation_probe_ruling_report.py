from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qm_stat_discovery_numerical_probe_execution_report import build_report as build_probe_execution_report
from formal.python.tools.qm_stat_discovery_ruling_report import build_report as build_derivation_ruling_report


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_DISCOVERY_DERIVATION_PROBE_RULING_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_DISCOVERY_DERIVATION_PROBE_RULING_20260411_v0.json"
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
    allowed_outcomes = [str(item) for item in declaration.get("allowed_outcomes", [])]

    derivation_ruling_path = REPO_ROOT / str(required_inputs.get("derivation_ruling_report", "")).strip()
    probe_execution_path = REPO_ROOT / str(required_inputs.get("numerical_probe_execution_report", "")).strip()

    if not derivation_ruling_path.exists():
        derivation_declaration = REPO_ROOT / "formal" / "docs" / "release" / "QM_STAT_DISCOVERY_RULING_20260411_v0.json"
        generated = build_derivation_ruling_report(
            declaration_path=derivation_declaration,
            captured_at_utc=captured_at_utc,
        )
        derivation_ruling_path.parent.mkdir(parents=True, exist_ok=True)
        derivation_ruling_path.write_text(json.dumps(generated, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    if not probe_execution_path.exists():
        probe_execution_declaration = (
            REPO_ROOT
            / "formal"
            / "docs"
            / "release"
            / "QM_STAT_DISCOVERY_NUMERICAL_PROBE_EXECUTION_20260411_v0.json"
        )
        generated = build_probe_execution_report(
            declaration_path=probe_execution_declaration,
            captured_at_utc=captured_at_utc,
        )
        probe_execution_path.parent.mkdir(parents=True, exist_ok=True)
        probe_execution_path.write_text(json.dumps(generated, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    derivation_ruling = _read_json(derivation_ruling_path)
    probe_execution = _read_json(probe_execution_path)

    derivation_summary = dict(derivation_ruling.get("summary", {}))
    probe_summary = dict(probe_execution.get("summary", {}))

    derivation_outcome = str(derivation_summary.get("ruling", "")).strip()
    probe_signal = str(probe_summary.get("probe_signal", "")).strip()
    path_falsification_observed = bool(probe_summary.get("path_falsification_observed", False))

    if path_falsification_observed:
        paired_outcome = "PROBE_REVEALS_PATH_FALSIFICATION"
    elif derivation_outcome == "DISCRIMINATOR_PRODUCED" and probe_signal == "PROBE_DISCRIMINATIVE":
        paired_outcome = "DERIVATION_AND_PROBE_AGREE"
    elif derivation_outcome == "DISCRIMINATOR_PRODUCED" and probe_signal == "PROBE_NONDISCRIMINATIVE":
        paired_outcome = "DERIVATION_INTERNAL_ONLY_PROBE_NONDISCRIMINATIVE"
    else:
        paired_outcome = "NONPRODUCTIVE_RETIRED"

    if paired_outcome not in allowed_outcomes:
        paired_outcome = "NONPRODUCTIVE_RETIRED"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "summary": {
            "paired_outcome": paired_outcome,
            "derivation_outcome": derivation_outcome,
            "probe_signal": probe_signal,
            "path_falsification_observed": path_falsification_observed,
            "shadow_mode_required": bool(declaration.get("shadow_mode_required", True)),
            "allowed_outcomes": allowed_outcomes,
            "next_action": "QUEUE_RECOMPUTE_OR_NEXT_DISCOVERY_TRANCHE_SELECTION" if paired_outcome != "NONPRODUCTIVE_RETIRED" else "RETIRE_PROBE_PATH_AND_RESELECT",
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "derivation_ruling_report": _ptr(derivation_ruling_path),
            "numerical_probe_execution_report": _ptr(probe_execution_path),
        },
        "non_claim_boundary": "Repository-local QM-STAT derivation/probe paired ruling report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate QM-STAT derivation/probe paired ruling report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "qm_stat_discovery_derivation_probe_ruling_report_20260411_v0.json",
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
        "qm_stat_discovery_derivation_probe_ruling_report: "
        f"paired_outcome={payload['summary']['paired_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

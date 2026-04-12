from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qm_stat_discovery_discriminator_tranche_report import build_report as build_execution_report


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_DISCOVERY_RULING_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_DISCOVERY_RULING_20260411_v0.json"
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

    execution_path = REPO_ROOT / str(required_inputs.get("execution_report", "")).strip()
    contract_path = REPO_ROOT / str(required_inputs.get("discovery_tranche_ruling_contract", "")).strip()

    # Keep ruling deterministic in both CLI and tests by materializing execution payload on demand.
    if not execution_path.exists():
        execution_declaration = (
            REPO_ROOT
            / "formal"
            / "docs"
            / "release"
            / "QM_STAT_DISCOVERY_DISCRIMINATOR_TRANCHE_EXECUTION_20260411_v0.json"
        )
        generated_execution = build_execution_report(
            declaration_path=execution_declaration,
            captured_at_utc=captured_at_utc,
        )
        execution_path.parent.mkdir(parents=True, exist_ok=True)
        execution_path.write_text(json.dumps(generated_execution, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    execution = _read_json(execution_path)
    contract = _read_json(contract_path)

    execution_summary = dict(execution.get("summary", {}))
    terminal_outcome = str(execution_summary.get("terminal_outcome", "")).strip()
    execution_classification = str(execution_summary.get("execution_classification", "")).strip()
    top_rank_alignment = bool(execution_summary.get("top_rank_alignment", False))
    required_fields_present = bool(execution_summary.get("required_fields_present", False))

    allowed_terminal_outcomes = [str(item) for item in contract.get("allowed_terminal_outcomes", [])]
    terminal_outcome_allowed = terminal_outcome in allowed_terminal_outcomes

    if (
        execution_classification == "DISCRIMINATOR_TRANCHE_EXECUTABLE"
        and terminal_outcome_allowed
        and top_rank_alignment
        and required_fields_present
    ):
        ruling_status = "TERMINAL_OUTCOME_CONFIRMED"
        ruling = terminal_outcome
        next_action = "QUEUE_RECOMPUTE_OR_NEXT_TRANCHE_SELECTION"
    else:
        ruling_status = "TERMINAL_OUTCOME_BLOCKED"
        ruling = "NONPRODUCTIVE_RETIRED"
        next_action = "FIX_DISCOVERY_EXECUTION_PRECONDITIONS"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "summary": {
            "ruling_status": ruling_status,
            "ruling": ruling,
            "terminal_outcome": terminal_outcome,
            "terminal_outcome_allowed": terminal_outcome_allowed,
            "allowed_terminal_outcomes": allowed_terminal_outcomes,
            "single_terminal_outcome_enforced": True,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "execution_report": _ptr(execution_path),
            "discovery_tranche_ruling_contract": _ptr(contract_path),
        },
        "non_claim_boundary": "Repository-local QM-STAT discovery ruling report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate QM-STAT discovery ruling report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "qm_stat_discovery_ruling_report_20260411_v0.json",
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
        "qm_stat_discovery_ruling_report: "
        f"ruling_status={payload['summary']['ruling_status']} ruling={payload['summary']['ruling']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

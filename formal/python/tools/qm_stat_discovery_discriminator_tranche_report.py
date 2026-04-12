from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_DISCOVERY_DISCRIMINATOR_TRANCHE_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_DISCOVERY_DISCRIMINATOR_TRANCHE_EXECUTION_20260411_v0.json"
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
    execution_policy = dict(declaration.get("execution_policy", {}))

    tranche_path = REPO_ROOT / str(required_inputs.get("tranche_declaration", "")).strip()
    queue_path = REPO_ROOT / str(required_inputs.get("discovery_priority_queue_report", "")).strip()
    contract_path = REPO_ROOT / str(required_inputs.get("discovery_tranche_ruling_contract", "")).strip()

    tranche = _read_json(tranche_path)
    queue = _read_json(queue_path)
    contract = _read_json(contract_path)

    top_rank_required = str(execution_policy.get("top_rank_required", "")).strip()
    top_rank_row = str(queue.get("summary", {}).get("top_rank_row", "")).strip()

    target_row = str(tranche.get("target_row", "")).strip()
    blocker_class = str(tranche.get("blocker_class", "")).strip()
    terminal_outcome = str(tranche.get("terminal_outcome", "")).strip()
    evidence_pointer = str(tranche.get("evidence_pointer", "")).strip()
    next_action = str(tranche.get("next_action", "")).strip()

    allowed_terminal_outcomes = [str(item) for item in contract.get("allowed_terminal_outcomes", [])]
    required_fields = dict(contract.get("required_fields", {}))

    required_fields_present = all(bool(tranche.get(field)) for field in required_fields)
    top_rank_alignment = (top_rank_row == top_rank_required == target_row)
    terminal_outcome_allowed = terminal_outcome in allowed_terminal_outcomes

    execution_classification = (
        "DISCRIMINATOR_TRANCHE_EXECUTABLE"
        if top_rank_alignment and terminal_outcome_allowed and required_fields_present
        else "DISCRIMINATOR_TRANCHE_BLOCKED"
    )

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "summary": {
            "tranche_id": tranche.get("tranche_id"),
            "target_row": target_row,
            "blocker_class": blocker_class,
            "top_rank_row": top_rank_row,
            "top_rank_alignment": top_rank_alignment,
            "terminal_outcome": terminal_outcome,
            "terminal_outcome_allowed": terminal_outcome_allowed,
            "required_fields_present": required_fields_present,
            "execution_classification": execution_classification,
            "evidence_pointer": evidence_pointer,
            "next_action": next_action,
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "tranche_declaration": _ptr(tranche_path),
            "discovery_priority_queue_report": _ptr(queue_path),
            "discovery_tranche_ruling_contract": _ptr(contract_path),
        },
        "non_claim_boundary": "Repository-local QM-STAT discovery tranche execution report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate QM-STAT discovery discriminator tranche execution report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "qm_stat_discovery_discriminator_tranche_report_20260411_v0.json",
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
        "qm_stat_discovery_discriminator_tranche_report: "
        f"execution_classification={payload['summary']['execution_classification']} "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

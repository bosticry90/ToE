from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qm_stat_discovery_discriminator_tranche_report import build_report as build_execution_report
from formal.python.tools.qm_stat_discovery_ruling_report import build_report as build_ruling_report


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "QM_STAT_DISCOVERY_INTERPRETATION_REPORT_20260411_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QM_STAT_DISCOVERY_INTERPRETATION_20260411_v0.json"
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


def _classify(*, ruling: str, execution_classification: str, evidence_pointer: str) -> str:
    if ruling == "DISCRIMINATOR_PRODUCED" and execution_classification == "DISCRIMINATOR_TRANCHE_EXECUTABLE":
        # Interpretation is intentionally conservative in shadow mode until external comparators are attached.
        if evidence_pointer.startswith("formal/output/reports/"):
            return "INTERNAL_DISCRIMINATIVE_ONLY"
        return "EXTERNALLY_COMPARABLE"
    return "INTERNAL_DISCRIMINATIVE_ONLY"


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    interpretation_policy = dict(declaration.get("interpretation_policy", {}))

    ruling_path = REPO_ROOT / str(required_inputs.get("discovery_ruling_report", "")).strip()
    execution_path = REPO_ROOT / str(required_inputs.get("discovery_execution_report", "")).strip()

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

    if not ruling_path.exists():
        ruling_declaration = REPO_ROOT / "formal" / "docs" / "release" / "QM_STAT_DISCOVERY_RULING_20260411_v0.json"
        generated_ruling = build_ruling_report(
            declaration_path=ruling_declaration,
            captured_at_utc=captured_at_utc,
        )
        ruling_path.parent.mkdir(parents=True, exist_ok=True)
        ruling_path.write_text(json.dumps(generated_ruling, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    ruling = _read_json(ruling_path)
    execution = _read_json(execution_path)

    execution_summary = dict(execution.get("summary", {}))
    ruling_summary = dict(ruling.get("summary", {}))

    categories = [str(item) for item in interpretation_policy.get("categories", [])]
    default_category = str(interpretation_policy.get("default_category", "INTERNAL_DISCRIMINATIVE_ONLY")).strip()

    target_row = str(execution_summary.get("target_row", "")).strip()
    ruling_value = str(ruling_summary.get("ruling", "")).strip()
    execution_classification = str(execution_summary.get("execution_classification", "")).strip()
    evidence_pointer = str(execution_summary.get("evidence_pointer", "")).strip()

    interpretation = _classify(
        ruling=ruling_value,
        execution_classification=execution_classification,
        evidence_pointer=evidence_pointer,
    )
    if interpretation not in categories:
        interpretation = default_category

    externally_comparable = interpretation in {"EXTERNALLY_COMPARABLE", "NUMERICAL_PROBE_READY"}
    numerical_probe_ready = interpretation == "NUMERICAL_PROBE_READY"

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "summary": {
            "target_row": target_row,
            "ruling": ruling_value,
            "execution_classification": execution_classification,
            "interpretation": interpretation,
            "externally_comparable": externally_comparable,
            "numerical_probe_ready": numerical_probe_ready,
            "shadow_mode_required": bool(interpretation_policy.get("shadow_mode_required", True)),
            "next_action": "PREPARE_SINGLE_BOUNDED_NUMERICAL_PROBE" if externally_comparable else "MAINTAIN_INTERNAL_DISCRIMINATOR_TRACK",
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "discovery_ruling_report": _ptr(ruling_path),
            "discovery_execution_report": _ptr(execution_path),
        },
        "non_claim_boundary": "Repository-local QM-STAT discovery interpretation report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate QM-STAT discovery interpretation report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "qm_stat_discovery_interpretation_report_20260411_v0.json",
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
        "qm_stat_discovery_interpretation_report: "
        f"interpretation={payload['summary']['interpretation']} "
        f"probe_ready={payload['summary']['numerical_probe_ready']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

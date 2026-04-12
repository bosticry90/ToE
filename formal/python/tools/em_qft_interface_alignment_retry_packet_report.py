from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "EM_QFT_INTERFACE_ALIGNMENT_RETRY_PACKET_REPORT_20260412_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "EM_QFT_INTERFACE_ALIGNMENT_RETRY_PACKET_20260412_v0.json"
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
    retry_binding = dict(declaration.get("retry_binding", {}))
    ruling_contract = dict(declaration.get("ruling_contract", {}))

    prior_decl_path = REPO_ROOT / str(
        required_inputs.get("em_qft_interface_alignment_packet_declaration", "")
    ).strip()
    prior_report_path = REPO_ROOT / str(
        required_inputs.get("em_qft_interface_alignment_packet_report", "")
    ).strip()
    obligation_report_path = REPO_ROOT / str(
        required_inputs.get("em_qft_interface_alignment_obligation_declaration_report", "")
    ).strip()
    selection_report_path = REPO_ROOT / str(
        required_inputs.get("em_qft_next_attack_class_selection_report", "")
    ).strip()

    prior_decl = _read_json(prior_decl_path)
    prior_report = _read_json(prior_report_path)
    obligation_report = _read_json(obligation_report_path)
    selection_report = _read_json(selection_report_path)

    target_seam = str(declaration.get("target_seam", "")).strip()

    prior_attack_class = str(prior_decl.get("attack_class", "")).strip()
    prior_summary = dict(prior_report.get("summary", {}))
    prior_packet_outcome = str(prior_summary.get("terminal_outcome", "")).strip()
    prior_target_seam = str(prior_summary.get("target_seam", "")).strip()

    obligation_summary = dict(obligation_report.get("summary", {}))
    obligation_outcome = str(obligation_summary.get("terminal_outcome", "")).strip()
    obligation_id = str(obligation_summary.get("missing_obligation_id", "")).strip()
    retry_justified = bool(obligation_summary.get("retry_justified", False))

    selection_summary = dict(selection_report.get("summary", {}))
    selected_attack_class = str(selection_summary.get("selected_attack_class", "")).strip()
    selected_target_seam = str(selection_summary.get("target_seam", "")).strip()

    required_prior_packet_outcome = str(retry_binding.get("required_prior_packet_outcome", "")).strip()
    required_obligation_outcome = str(retry_binding.get("required_obligation_outcome", "")).strip()
    required_obligation_id = str(retry_binding.get("required_obligation_id", "")).strip()
    required_attack_class = str(retry_binding.get("required_attack_class", "")).strip()
    required_target_seam = str(retry_binding.get("required_target_seam", "")).strip()
    em_qft_signal_observed = bool(retry_binding.get("em_qft_signal_observed", False))

    preconditions_ok = (
        target_seam == required_target_seam == prior_target_seam == selected_target_seam
        and prior_attack_class == required_attack_class == selected_attack_class
        and prior_packet_outcome == required_prior_packet_outcome
        and obligation_outcome == required_obligation_outcome
        and obligation_id == required_obligation_id
        and retry_justified
    )

    allowed_outcomes = set(ruling_contract.get("allowed_outcomes", []))
    default_outcome = str(ruling_contract.get("default_outcome", "EM_QFT_PATH_FALSIFIED")).strip()

    if not preconditions_ok:
        terminal_outcome = "EM_QFT_PATH_FALSIFIED"
        next_action = "RESTORE_EM_QFT_INTERFACE_ALIGNMENT_RETRY_BINDING_INTEGRITY"
    elif em_qft_signal_observed:
        terminal_outcome = "EM_QFT_SEAM_SIGNAL_PRODUCED"
        next_action = "PROMOTE_EM_QFT_INTERFACE_ALIGNMENT_AFTER_RETRY_SIGNAL"
    else:
        terminal_outcome = "EM_QFT_INTERFACE_ALIGNMENT_OBLIGATION_DECLARED_BUT_STILL_INSUFFICIENT"
        next_action = "ESCALATE_EM_QFT_STRUCTURE_BEYOND_DECLARED_INTERFACE_ALIGNMENT_OBLIGATION"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "target_seam_scope_match": target_seam == required_target_seam == prior_target_seam == selected_target_seam,
            "attack_class_binding_match": prior_attack_class == required_attack_class == selected_attack_class,
            "prior_packet_outcome_match": prior_packet_outcome == required_prior_packet_outcome,
            "obligation_outcome_match": obligation_outcome == required_obligation_outcome,
            "obligation_id_match": obligation_id == required_obligation_id,
            "retry_justified": retry_justified,
            "single_terminal_outcome_rule_declared": str(
                ruling_contract.get("single_terminal_outcome_rule", "")
            ).strip()
            == "EXACTLY_ONE_ALLOWED_EM_QFT_INTERFACE_ALIGNMENT_RETRY_OUTCOME",
            "no_loop_rule_declared": str(ruling_contract.get("no_loop_rule", "")).strip()
            == "ONE_EM_QFT_INTERFACE_ALIGNMENT_RETRY_PACKET_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "retry_binding_preconditions_ok": preconditions_ok,
            },
            "inputs": {
                "target_seam": target_seam,
                "prior_target_seam": prior_target_seam,
                "selected_target_seam": selected_target_seam,
                "prior_attack_class": prior_attack_class,
                "selected_attack_class": selected_attack_class,
                "required_attack_class": required_attack_class,
                "prior_packet_outcome": prior_packet_outcome,
                "required_prior_packet_outcome": required_prior_packet_outcome,
                "obligation_outcome": obligation_outcome,
                "required_obligation_outcome": required_obligation_outcome,
                "obligation_id": obligation_id,
                "required_obligation_id": required_obligation_id,
                "retry_justified": retry_justified,
                "em_qft_signal_observed": em_qft_signal_observed,
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "target_seam": target_seam,
            "attack_class": required_attack_class,
            "bound_obligation_id": required_obligation_id,
            "next_action": next_action,
            "single_retry_only": bool(retry_binding.get("single_retry_only", True)),
            "single_ruling_only": bool(retry_binding.get("single_ruling_only", True)),
        },
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "em_qft_interface_alignment_packet_declaration": _ptr(prior_decl_path),
            "em_qft_interface_alignment_packet_report": _ptr(prior_report_path),
            "em_qft_interface_alignment_obligation_declaration_report": _ptr(obligation_report_path),
            "em_qft_next_attack_class_selection_report": _ptr(selection_report_path),
        },
        "non_claim_boundary": "Repository-local EM-QFT interface-alignment retry packet report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate EM-QFT interface-alignment retry packet report."
    )
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT
        / "formal"
        / "output"
        / "reports"
        / "em_qft_interface_alignment_retry_packet_20260412_v0.json",
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
        "em_qft_interface_alignment_retry_packet_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

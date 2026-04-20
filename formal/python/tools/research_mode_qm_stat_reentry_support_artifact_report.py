from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "RESEARCH_MODE_QM_STAT_REENTRY_SUPPORT_ARTIFACT_REPORT_20260419_v0"
DEFAULT_DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "RESEARCH_MODE_QM_STAT_REENTRY_SUPPORT_ARTIFACT_20260419_v0.json"
)
DEFAULT_ARTIFACT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "support"
    / "qm_stat_reentry_support_artifact_20260419_v0.json"
)
DEFAULT_OUT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "research_mode_qm_stat_reentry_support_artifact_20260419_v0.json"
)


def _read_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(_read_text(path))


def _text(value: Any) -> str:
    return str(value).strip() if value is not None else ""


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _latest_active_definition(entries: list[dict[str, Any]], row_id: str) -> dict[str, Any]:
    active_entries = [
        entry
        for entry in entries
        if entry.get("target_row_id") == row_id and entry.get("status") == "ACTIVE"
    ]
    return dict(active_entries[-1]) if active_entries else {}


def build_payload(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    contract = dict(declaration.get("support_artifact_contract", {}))

    adjudication_path = REPO_ROOT / _text(required_inputs.get("post_review_adjudication_report"))
    evidence_path = REPO_ROOT / _text(required_inputs.get("live_authority_evidence_report"))
    eligibility_path = REPO_ROOT / _text(required_inputs.get("reentry_eligibility_review_report"))
    bridge_object_path = REPO_ROOT / _text(required_inputs.get("bridge_object"))
    witness_binding_path = REPO_ROOT / _text(required_inputs.get("witness_binding"))
    blocker_definitions_path = REPO_ROOT / _text(required_inputs.get("blocker_definitions"))

    adjudication_report = _read_json(adjudication_path)
    evidence_report = _read_json(evidence_path)
    eligibility_report = _read_json(eligibility_path)
    bridge_object = _read_json(bridge_object_path)
    witness_binding = _read_json(witness_binding_path)
    blocker_definitions = _read_json(blocker_definitions_path)

    adjudication_summary = dict(adjudication_report.get("summary", {}))
    evidence_summary = dict(evidence_report.get("summary", {}))
    evidence_inputs = dict(evidence_report.get("objective_quality", {}).get("inputs", {}))
    eligibility_summary = dict(eligibility_report.get("summary", {}))
    eligibility_criteria = dict(eligibility_report.get("criteria", {}))
    latest_definition = _latest_active_definition(
        list(blocker_definitions.get("entries", [])), _text(contract.get("required_target_row"))
    )

    retained_candidate_ok = all(
        [
            adjudication_summary.get("post_review_adjudication") == _text(contract.get("required_post_review_adjudication")),
            adjudication_summary.get("candidate_disposition") == _text(contract.get("required_candidate_disposition")),
            adjudication_summary.get("canonical_mutation_emitted") is False,
        ]
    )
    evidence_chain_ok = all(
        [
            evidence_summary.get("terminal_outcome") == _text(contract.get("required_evidence_terminal_outcome")),
            evidence_summary.get("target_row_id") == _text(contract.get("required_target_row")),
            evidence_summary.get("target_seam_id") == _text(contract.get("required_target_seam")),
            evidence_summary.get("target_package_id") == _text(contract.get("required_target_package_id")),
            evidence_summary.get("authoritative_blocker_definition_id") == _text(contract.get("required_blocker_definition_id")),
            evidence_summary.get("canonical_mutation_emitted") is False,
        ]
    )
    eligibility_gap_targeted = any(
        [
            all(
                [
                    eligibility_summary.get("terminal_outcome")
                    == _text(contract.get("required_partial_eligibility_outcome")),
                    eligibility_summary.get("next_action") == _text(contract.get("required_partial_next_action")),
                    eligibility_criteria.get("direct_reentry_queue_authorized") is False,
                ]
            ),
            all(
                [
                    eligibility_summary.get("terminal_outcome") == "QM_STAT_REENTRY_ELIGIBILITY_MET_FOR_BOUNDED_REENTRY",
                    eligibility_summary.get("next_action") == _text(contract.get("next_action_on_ready")),
                    eligibility_criteria.get("direct_reentry_queue_authorized") is True,
                ]
            ),
        ]
    )
    live_binding_ok = all(
        [
            bridge_object.get("row_id") == _text(contract.get("required_target_row")),
            bridge_object.get("target_package_id") == _text(contract.get("required_target_package_id")),
            witness_binding.get("row_id") == _text(contract.get("required_target_row")),
            witness_binding.get("target_package_id") == _text(contract.get("required_target_package_id")),
            witness_binding.get("bridge_object_id") == bridge_object.get("object_id"),
            evidence_inputs.get("bridge_object_id") == bridge_object.get("object_id"),
            evidence_inputs.get("witness_id") == witness_binding.get("witness_id"),
        ]
    )
    authority_binding_ok = all(
        [
            latest_definition.get("definition_id") == _text(contract.get("required_blocker_definition_id")),
            latest_definition.get("coupling_state") == _text(contract.get("required_coupling_state")),
            latest_definition.get("promotion_ruling") == _text(contract.get("required_promotion_ruling")),
        ]
    )
    queue_authorization_ready = all(
        [retained_candidate_ok, evidence_chain_ok, eligibility_gap_targeted, live_binding_ok, authority_binding_ok]
    )

    authorization_status = (
        _text(contract.get("authorization_status_on_ready")) if queue_authorization_ready else "NOT_AUTHORIZED"
    )
    next_action = (
        _text(contract.get("next_action_on_ready"))
        if queue_authorization_ready
        else _text(contract.get("next_action_on_incomplete"))
    )
    terminal_outcome = (
        "QM_STAT_REENTRY_SUPPORT_ARTIFACT_MATERIALIZED_AND_QUEUE_AUTHORIZED"
        if queue_authorization_ready
        else "QM_STAT_REENTRY_SUPPORT_ARTIFACT_INCOMPLETE"
    )

    artifact = {
        "artifact_id": "qm_stat_reentry_support_artifact_20260419_v0",
        "artifact_class": "BOUNDED_REENTRY_SUPPORT_ARTIFACT",
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "target_binding": {
            "row_id": _text(contract.get("required_target_row")),
            "seam_id": _text(contract.get("required_target_seam")),
            "target_package_id": _text(contract.get("required_target_package_id")),
            "authorized_candidate_target": _text(contract.get("authorized_candidate_target")),
        },
        "support_scope": {
            "gap_token": _text(contract.get("required_gap_token")),
            "authorization_scope_token": _text(contract.get("authorization_scope_token")),
            "support_role": "NARROW_QUEUE_AUTHORIZATION_SUPPORT_ONLY",
        },
        "authority_chain": {
            "bridge_object_id": bridge_object.get("object_id"),
            "witness_id": witness_binding.get("witness_id"),
            "authoritative_blocker_definition_id": latest_definition.get("definition_id"),
            "coupling_state": latest_definition.get("coupling_state"),
            "promotion_ruling": latest_definition.get("promotion_ruling"),
        },
        "authorization": {
            "authorization_status": authorization_status,
            "authorized_candidate_target": _text(contract.get("authorized_candidate_target")),
            "next_action": next_action,
        },
        "source_bundle": {
            "post_review_adjudication_report": _ptr(adjudication_path),
            "live_authority_evidence_report": _ptr(evidence_path),
            "reentry_eligibility_review_report": _ptr(eligibility_path),
            "bridge_object": _ptr(bridge_object_path),
            "witness_binding": _ptr(witness_binding_path),
            "blocker_definitions": _ptr(blocker_definitions_path),
        },
        "non_claim_boundary": "Repository-local QM-STAT re-entry support artifact only; no canonical promotion, canonical mutation, or seam-closure claim.",
    }

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": artifact["captured_at_utc"],
        "criteria": {
            "retained_reviewed_candidate_present": retained_candidate_ok,
            "stronger_evidence_chain_bound": evidence_chain_ok,
            "eligibility_gap_targeted": eligibility_gap_targeted,
            "live_binding_preserved": live_binding_ok,
            "authority_binding_preserved": authority_binding_ok,
            "queue_authorization_ready": queue_authorization_ready,
        },
        "objective_quality": {
            "criteria": {
                "single_outcome_materialized": True,
                "gap_target_is_direct_queue_authorization_only": eligibility_gap_targeted,
                "noncanonical_boundary_preserved": True,
                "queue_authorization_requires_live_authority_chain": (
                    not queue_authorization_ready
                )
                or (live_binding_ok and authority_binding_ok),
            },
            "inputs": {
                "post_review_adjudication": adjudication_summary.get("post_review_adjudication"),
                "evidence_terminal_outcome": evidence_summary.get("terminal_outcome"),
                "eligibility_terminal_outcome": eligibility_summary.get("terminal_outcome"),
                "authorized_candidate_target": _text(contract.get("authorized_candidate_target")),
                "authoritative_blocker_definition_id": latest_definition.get("definition_id"),
            },
            "summary": {
                "all_criteria_satisfied": queue_authorization_ready,
                "phase_status": "COMPLETE" if queue_authorization_ready else "INCOMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "authorization_status": authorization_status,
            "authorized_candidate_target": _text(contract.get("authorized_candidate_target")),
            "target_row_id": _text(contract.get("required_target_row")),
            "target_seam_id": _text(contract.get("required_target_seam")),
            "target_package_id": _text(contract.get("required_target_package_id")),
            "canonical_mutation_emitted": False,
            "next_action": next_action,
        },
        "artifact": artifact,
        "source_bundle": artifact["source_bundle"],
        "non_claim_boundary": artifact["non_claim_boundary"],
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the QM-STAT re-entry support artifact report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument("--artifact-out", type=Path, default=DEFAULT_ARTIFACT_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT_PATH)
    parser.add_argument("--captured-at-utc", default=None)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    declaration_path = ns.declaration if ns.declaration.is_absolute() else (REPO_ROOT / ns.declaration)
    artifact_out = ns.artifact_out if ns.artifact_out.is_absolute() else (REPO_ROOT / ns.artifact_out)
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = build_payload(declaration_path=declaration_path, captured_at_utc=ns.captured_at_utc)
    artifact_out.parent.mkdir(parents=True, exist_ok=True)
    out.parent.mkdir(parents=True, exist_ok=True)
    artifact_out.write_text(json.dumps(payload["artifact"], indent=2, sort_keys=True) + "\n", encoding="utf-8")
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "research_mode_qm_stat_reentry_support_artifact_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
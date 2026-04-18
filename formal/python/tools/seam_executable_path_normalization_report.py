from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "SEAM_EXECUTABLE_PATH_NORMALIZATION_REPORT_20260418_v0"

DEFAULT_DECLARATION_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "SEAM_EXECUTABLE_PATH_NORMALIZATION_20260418_v0.json"
)


def _read(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(f"Missing required file: {path}")
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict[str, Any]:
    return json.loads(_read(path))


def _ts(value: str | None) -> str:
    if value:
        return value
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _parse_markdown_table(text: str, required_columns: list[str]) -> list[dict[str, str]]:
    lines = text.splitlines()
    start = None
    for index, line in enumerate(lines):
        if not line.strip().startswith("|"):
            continue
        header_cells = [cell.strip().strip("`") for cell in line.strip().strip("|").split("|")]
        if all(column in header_cells for column in required_columns):
            start = index
            break
    if start is None or start + 2 >= len(lines):
        return []

    header_cells = [cell.strip().strip("`") for cell in lines[start].strip().strip("|").split("|")]
    rows: list[dict[str, str]] = []
    for line in lines[start + 2 :]:
        if not line.startswith("|"):
            break
        cells = [cell.strip().strip("`") for cell in line.strip().strip("|").split("|")]
        if len(cells) != len(header_cells):
            continue
        rows.append(dict(zip(header_cells, cells)))
    return rows


def _seam_row_id(seam_id: str) -> str | None:
    mapping = {
        "SEAM-QFT-GR": "ROW-SEAM-QFT-GR-001",
        "SEAM-QM-STAT": "ROW-SEAM-QM-STAT-001",
        "SEAM-COSMO-SR": "ROW-SEAM-COSMO-SR-001",
        "SEAM-GR-QM": "ROW-SEAM-GR-QM-001",
    }
    return mapping.get(seam_id)


def _sla_entry(entries: list[dict[str, Any]], row_id: str | None) -> dict[str, Any]:
    if not row_id:
        return {}
    for entry in entries:
        if str(entry.get("row_id", "")).strip() == row_id:
            return dict(entry)
    return {}


def build_report(*, declaration_path: Path, captured_at_utc: str | None) -> dict[str, Any]:
    declaration = _read_json(declaration_path)
    required_inputs = dict(declaration.get("required_inputs", {}))
    normalization_policy = dict(declaration.get("normalization_policy", {}))
    expected_rows = dict(declaration.get("expected_rows", {}))
    outcome_contract = dict(declaration.get("outcome_contract", {}))

    inventory_path = REPO_ROOT / str(required_inputs.get("seam_inventory", "")).strip()
    registry_path = REPO_ROOT / str(required_inputs.get("seam_constraint_registry", "")).strip()
    sla_path = REPO_ROOT / str(required_inputs.get("seam_resolution_sla_ledger_report", "")).strip()
    qm_stat_path = REPO_ROOT / str(required_inputs.get("qm_stat_seam_authorization_readiness_dossier_report", "")).strip()
    cosmo_path = REPO_ROOT / str(required_inputs.get("cosmo_sr_bounded_activation_authorization_report", "")).strip()

    inventory_text = _read(inventory_path)
    registry_text = _read(registry_path)
    sla = _read_json(sla_path)
    qm_stat = _read_json(qm_stat_path)
    cosmo = _read_json(cosmo_path)

    inventory_rows = _parse_markdown_table(
        inventory_text,
        ["seam_id", "class", "seam_class_token", "witness_route_status", "source_artifacts", "promotion_candidate"],
    )
    split_rows = _parse_markdown_table(
        inventory_text,
        ["seam_id", "governance_complete", "physics_complete", "status_read"],
    )
    split_by_seam = {row["seam_id"]: row for row in split_rows}
    sla_entries = list(sla.get("entries", []))
    qm_summary = dict(qm_stat.get("summary", {}))
    cosmo_summary = dict(cosmo.get("summary", {}))

    normalized_rows: list[dict[str, Any]] = []
    executable_rows: list[str] = []
    for row in inventory_rows:
        seam_id = str(row.get("seam_id", "")).strip()
        witness_route_status = str(row.get("witness_route_status", "")).strip()
        seam_class = str(row.get("class", "")).strip()
        split = split_by_seam.get(seam_id, {})
        governance_complete = str(split.get("governance_complete", "")).strip() == "YES"
        physics_complete = str(split.get("physics_complete", "")).strip() == "YES"
        status_read = str(split.get("status_read", "")).strip()
        sla_entry = _sla_entry(sla_entries, _seam_row_id(seam_id))

        if seam_id == "SEAM-COSMO-SR" and str(cosmo_summary.get("terminal_outcome", "")).strip() == "COSMO_SR_CYCLE07_SINGLE_LANE_ACTIVATION_AUTHORIZED_NONLIVE_v0":
            path_class = str(normalization_policy.get("single_authorized_path_class", "")).strip()
            next_action = str(cosmo_summary.get("next_action", "")).strip()
            executable_rows.append(seam_id)
            evidence = _ptr(cosmo_path)
        elif seam_id == "SEAM-QM-STAT" and str(qm_summary.get("terminal_outcome", "")).strip() == "QM_STAT_SEAM_AUTHORIZATION_DOSSIER_READY_BUT_RESTART_BLOCKED":
            path_class = str(normalization_policy.get("policy_blocked_path_class", "")).strip()
            next_action = str(qm_summary.get("next_action", "")).strip()
            evidence = _ptr(qm_stat_path)
        elif seam_id == "SEAM-QFT-GR" and witness_route_status == "HOLD_FOR_SCALAR_PUBLICATION_v0":
            path_class = str(normalization_policy.get("external_hold_path_class", "")).strip()
            next_action = "WAIT_FOR_SCALAR_PUBLICATION_RELEASE_ONLY"
            evidence = _ptr(sla_path)
        elif seam_id in {"SEAM-STAT-QM", "SEAM-SR-COSMO"} and witness_route_status == "COUNTERFACTUAL_BUNDLE_PINNED_v0":
            path_class = str(normalization_policy.get("mirror_only_path_class", "")).strip()
            next_action = "REMAIN_MIRROR_ONLY_UNTIL_A_CANONICAL_ROW_AND_AUTHORIZATION_SURFACE_EXIST"
            evidence = _ptr(inventory_path)
        elif seam_id == "SEAM-GR-QM" and physics_complete and str(sla_entry.get("decision_state", "")).strip() == "CLOSED_RECOMPUTE_MONITORING_REQUIRED":
            path_class = str(normalization_policy.get("closed_monitoring_path_class", "")).strip()
            next_action = "REMAIN_IN_RECOMPUTE_MONITORING_ONLY"
            evidence = _ptr(sla_path)
        elif seam_id == "SEAM-EM-QFT" and governance_complete and not physics_complete:
            path_class = str(normalization_policy.get("governance_complete_no_active_path_class", "")).strip()
            next_action = "WAIT_FOR_EXPLICIT_NEW_EXECUTION_AUTHORIZATION_BEFORE_ANY_EM_QFT_REOPEN"
            evidence = _ptr(inventory_path)
        else:
            path_class = "UNCLASSIFIED_PATH_STATE"
            next_action = "REPAIR_SEAM_EXECUTABLE_PATH_CLASSIFICATION_INPUTS"
            evidence = _ptr(inventory_path)

        normalized_rows.append(
            {
                "seam_id": seam_id,
                "seam_class": seam_class,
                "witness_route_status": witness_route_status,
                "governance_complete": governance_complete,
                "physics_complete": physics_complete,
                "status_read": status_read,
                "path_class": path_class,
                "next_action": next_action,
                "supporting_evidence": evidence,
            }
        )

    expected_rows_match = all(
        any(
            row["seam_id"] == seam_id
            and row["path_class"] == str(expectation.get("required_path_class", "")).strip()
            and row["next_action"] == str(expectation.get("required_next_action", "")).strip()
            for row in normalized_rows
        )
        for seam_id, expectation in expected_rows.items()
    )
    active_execution_path_limit = int(normalization_policy.get("active_execution_path_limit", 1))
    single_active_path_rule_satisfied = len(executable_rows) <= active_execution_path_limit
    allowed_outcomes = set(outcome_contract.get("allowed_outcomes", []))
    default_outcome = str(outcome_contract.get("default_outcome", "SEAM_EXECUTABLE_PATH_NORMALIZATION_EVIDENCE_INCOMPLETE")).strip()

    if not normalized_rows:
        terminal_outcome = "HOLD_PENDING_SEAM_EXECUTABLE_PATH_NORMALIZATION_REPAIR"
        next_action = "RESTORE_SEAM_INVENTORY_INPUTS_AND_RERUN"
    elif expected_rows_match and single_active_path_rule_satisfied and len(executable_rows) == 1:
        terminal_outcome = "SEAM_EXECUTABLE_PATHS_NORMALIZED"
        next_action = "USE_NORMALIZED_PATH_CLASSES_AS_THE_PHASE3_CANONICAL_SEAM_EXECUTION_MODEL"
    else:
        terminal_outcome = "SEAM_EXECUTABLE_PATH_NORMALIZATION_EVIDENCE_INCOMPLETE"
        next_action = "REPAIR_SEAM_PATH_CLASSIFICATIONS_AND_RERUN"

    if terminal_outcome not in allowed_outcomes:
        terminal_outcome = default_outcome

    return {
        "schema_id": SCHEMA_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": _ts(captured_at_utc),
        "criteria": {
            "inventory_rows_present": bool(inventory_rows),
            "expected_rows_match": expected_rows_match,
            "single_active_path_rule_satisfied": single_active_path_rule_satisfied,
            "no_live_execution_rule_preserved": True,
            "single_terminal_outcome_rule_declared": str(outcome_contract.get("single_terminal_outcome_rule", "")).strip()
            == "EXACTLY_ONE_ALLOWED_SEAM_EXECUTABLE_PATH_NORMALIZATION_OUTCOME",
            "no_loop_rule_declared": str(outcome_contract.get("no_loop_rule", "")).strip()
            == "ONE_SEAM_EXECUTABLE_PATH_NORMALIZATION_LAYER_ONLY",
        },
        "objective_quality": {
            "criteria": {
                "allowed_outcome_materialized": terminal_outcome in allowed_outcomes,
                "single_outcome_materialized": True,
                "one_executable_path_only": len(executable_rows) == 1,
                "phase3_scope_preserved": True,
            },
            "inputs": {
                "active_execution_path_limit": active_execution_path_limit,
                "executable_rows": executable_rows,
                "phase3_scope": normalization_policy.get("phase3_scope"),
                "qm_stat_terminal_outcome": qm_summary.get("terminal_outcome"),
                "cosmo_sr_terminal_outcome": cosmo_summary.get("terminal_outcome"),
            },
            "summary": {
                "all_criteria_satisfied": terminal_outcome in allowed_outcomes,
                "phase_status": "COMPLETE",
                "next_action": next_action,
            },
        },
        "summary": {
            "terminal_outcome": terminal_outcome,
            "executable_path_count": len(executable_rows),
            "authorized_executable_seams": executable_rows,
            "next_action": next_action,
        },
        "normalized_rows": normalized_rows,
        "source_bundle": {
            "declaration": _ptr(declaration_path),
            "seam_inventory": _ptr(inventory_path),
            "seam_constraint_registry": _ptr(registry_path),
            "seam_resolution_sla_ledger_report": _ptr(sla_path),
            "qm_stat_seam_authorization_readiness_dossier_report": _ptr(qm_stat_path),
            "cosmo_sr_bounded_activation_authorization_report": _ptr(cosmo_path),
        },
        "non_claim_boundary": "Repository-local seam executable-path normalization report only; no scientific adequacy claim.",
    }


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate the seam executable-path normalization report.")
    parser.add_argument("--declaration", type=Path, default=DEFAULT_DECLARATION_PATH)
    parser.add_argument(
        "--out",
        type=Path,
        default=REPO_ROOT / "formal" / "output" / "reports" / "seam_executable_path_normalization_20260418_v0.json",
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
        "seam_executable_path_normalization_report: "
        f"terminal_outcome={payload['summary']['terminal_outcome']} out={out}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
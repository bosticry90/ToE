from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
CAPTURED_AT_UTC = "2026-07-09T00:00:00Z"
READINESS_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0.json"
)
PREPARE_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCIENCE_FIRST_PILLAR_SEAM_DEPENDENCY_REBASE_PACKET_20260709_v0.json"
)
REVIEW_REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "SCIENCE_FIRST_PILLAR_SEAM_DEPENDENCY_REBASE_PACKET_RESULT_REVIEW_20260709_v0.json"
)

PREPARE_TARGET = "prepare_science_first_pillar_seam_dependency_rebase_packet"
REVIEW_TARGET = "review_science_first_pillar_seam_dependency_rebase_packet_result"
FIRST_SPRINT_GUARDRAIL_TARGET = (
    "prepare_scalar_qft_gr_source_contract_flat_limit_pretest_guardrail_packet"
)
PREPARE_OUTCOME = (
    "SCIENCE_FIRST_PILLAR_SEAM_DEPENDENCY_REBASE_PACKET_PREPARED_COMPACT_"
    "READINESS_AUTHORITY_PENDING_REVIEW_NO_PILLAR_OR_SEAM_CLOSURE"
)
PREPARE_STRICT_OUTCOME = (
    "SCIENCE_FIRST_PILLAR_SEAM_DEPENDENCY_REBASE_PACKET_PREPARED_ENTRY_"
    "MATURITY_AND_SEAM_GATES_ONLY_NO_MASTER_ACTION_PROMOTION_OR_CCFT_RESUMPTION"
)
REVIEW_OUTCOME = (
    "SCIENCE_FIRST_PILLAR_SEAM_DEPENDENCY_REBASE_PACKET_RESULT_REVIEW_ACCEPTS_"
    "COMPACT_SCIENCE_SPRINT_READINESS_AUTHORITY_AND_SELECTS_FLAT_LIMIT_"
    "PRETEST_ONLY"
)
REVIEW_STRICT_OUTCOME = (
    "SCIENCE_FIRST_PILLAR_SEAM_DEPENDENCY_REBASE_PACKET_RESULT_REVIEW_ACCEPTS_"
    "READINESS_CLASSIFICATION_ONLY_NO_QFT_GR_SEAM_ADMISSIBILITY_NO_MASTER_"
    "ACTION_PROMOTION"
)

ALLOWED_READINESS_STATUSES = (
    "met",
    "partial",
    "missing",
    "blocked",
    "not_assessed",
    "not_applicable",
)
PILLAR_ENTRY_CRITERIA = (
    ("physical_objects", "Clearly defined physical objects"),
    ("governing_equation_or_action", "Governing equation or action"),
    ("assumptions_and_domain", "Explicit assumptions and domain"),
    ("units_and_dimensions", "Units and dimensions"),
    ("neighboring_interface_variables", "Neighboring interface variables"),
)
PILLAR_MATURITY_CRITERIA = (
    ("symmetry_or_conservation_witness", "Symmetry or conservation witness"),
    ("known_limit_recovery", "Known-limit recovery"),
    ("formal_witness", "Analytic or Lean-backed witness"),
    ("reproducible_calculation", "Reproducible numerical calculation"),
    ("negative_control", "Known failure case or negative control"),
)
SEAM_CRITERIA = (
    ("object_map", "Object map"),
    ("unit_map", "Unit map"),
    ("source_balance", "Source balance"),
    ("conservation_compatibility", "Conservation compatibility"),
    ("shared_limit", "Shared limiting regime"),
    ("residual", "Defined seam residual"),
    ("positive_witness", "Positive witness"),
    ("negative_obstruction", "Negative example or obstruction"),
)
SPRINT_INTERFACE_FIELDS = (
    "question",
    "inputs",
    "equation_surfaces",
    "assumptions",
    "units",
    "allowed_operations",
    "forbidden_claims",
    "success_criteria",
    "failure_criteria",
    "outputs",
    "claim_ceiling",
    "reproduction_command",
)

PILLARS = {
    "PILLAR-QFT": {
        "plain_name": "Scalar/QFT reference pillar",
        "scope": "bounded real-scalar reference route",
        "evidence_pointer": (
            "formal/docs/paper/DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md"
        ),
        "statuses": (
            "met",
            "met",
            "partial",
            "missing",
            "partial",
            "partial",
            "partial",
            "partial",
            "missing",
            "missing",
        ),
    },
    "PILLAR-GR": {
        "plain_name": "General relativity pillar",
        "scope": "classical metric and source-response route",
        "evidence_pointer": (
            "formal/docs/paper/DERIVATION_TARGET_GR01_FULL_DERIVATION_DISCHARGE_v0.md"
        ),
        "statuses": (
            "met",
            "met",
            "partial",
            "partial",
            "partial",
            "partial",
            "partial",
            "partial",
            "missing",
            "missing",
        ),
    },
    "PILLAR-QM": {
        "plain_name": "Quantum mechanics pillar",
        "scope": "state, observable, measurement, and open-system objects",
        "evidence_pointer": (
            "formal/docs/paper/DERIVATION_TARGET_QM_FULL_DERIVATION_DISCHARGE_v0.md"
        ),
        "statuses": (
            "partial",
            "partial",
            "partial",
            "missing",
            "missing",
            "partial",
            "partial",
            "partial",
            "not_assessed",
            "missing",
        ),
    },
    "PILLAR-STAT": {
        "plain_name": "Statistical mechanics pillar",
        "scope": "entropy, ensemble, coarse-graining, and transport objects",
        "evidence_pointer": (
            "formal/docs/paper/DERIVATION_TARGET_STAT_ENTROPY_PLAN_v0.md"
        ),
        "statuses": (
            "partial",
            "partial",
            "partial",
            "missing",
            "missing",
            "partial",
            "partial",
            "partial",
            "not_assessed",
            "missing",
        ),
    },
    "PILLAR-EM": {
        "plain_name": "Electromagnetism pillar",
        "scope": "U(1) gauge field, current, and stress-energy route",
        "evidence_pointer": (
            "formal/docs/paper/DERIVATION_TARGET_EM_U1_MAXWELL_OBJECT_v0.md"
        ),
        "statuses": (
            "met",
            "partial",
            "partial",
            "partial",
            "partial",
            "partial",
            "partial",
            "partial",
            "not_assessed",
            "missing",
        ),
    },
    "PILLAR-SR": {
        "plain_name": "Special relativity pillar",
        "scope": "Lorentz covariance and causal compatibility layer",
        "evidence_pointer": (
            "formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md"
        ),
        "statuses": (
            "partial",
            "partial",
            "partial",
            "partial",
            "partial",
            "partial",
            "partial",
            "partial",
            "not_assessed",
            "missing",
        ),
    },
    "PILLAR-COSMO": {
        "plain_name": "Cosmology pillar",
        "scope": "GR/SR/STAT-dependent background route",
        "evidence_pointer": (
            "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md"
        ),
        "statuses": (
            "partial",
            "partial",
            "partial",
            "partial",
            "missing",
            "partial",
            "blocked",
            "partial",
            "not_assessed",
            "missing",
        ),
    },
}

SEAMS = {
    "SEAM-QFT-GR": {
        "plain_name": "Scalar/QFT-GR",
        "pillar_ids": ["PILLAR-QFT", "PILLAR-GR"],
        "statuses": (
            "partial",
            "missing",
            "partial",
            "blocked",
            "partial",
            "partial",
            "partial",
            "met",
        ),
    },
    "SEAM-QM-STAT": {
        "plain_name": "QM-STAT",
        "pillar_ids": ["PILLAR-QM", "PILLAR-STAT"],
        "statuses": (
            "partial",
            "missing",
            "missing",
            "partial",
            "partial",
            "partial",
            "missing",
            "partial",
        ),
    },
    "SEAM-EM-QFT": {
        "plain_name": "EM-QFT",
        "pillar_ids": ["PILLAR-EM", "PILLAR-QFT"],
        "statuses": (
            "partial",
            "partial",
            "partial",
            "partial",
            "partial",
            "partial",
            "partial",
            "partial",
        ),
    },
    "SEAM-SR-COSMO": {
        "plain_name": "SR-COSMO",
        "pillar_ids": ["PILLAR-SR", "PILLAR-COSMO"],
        "statuses": (
            "partial",
            "partial",
            "partial",
            "partial",
            "partial",
            "missing",
            "missing",
            "partial",
        ),
    },
    "SEAM-GR-QM": {
        "plain_name": "GR-QM",
        "pillar_ids": ["PILLAR-GR", "PILLAR-QM"],
        "statuses": (
            "partial",
            "missing",
            "blocked",
            "blocked",
            "missing",
            "missing",
            "missing",
            "partial",
        ),
    },
}


def canonical_json_bytes(payload: Any) -> bytes:
    return (
        json.dumps(
            payload,
            indent=2,
            sort_keys=True,
            ensure_ascii=True,
            allow_nan=False,
        )
        + "\n"
    ).encode("utf-8")


def sha256_bytes(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def _pillar_rows() -> list[dict[str, Any]]:
    criteria = [
        (*criterion, "entry_gating", True) for criterion in PILLAR_ENTRY_CRITERIA
    ] + [
        (*criterion, "maturity", False) for criterion in PILLAR_MATURITY_CRITERIA
    ]
    rows: list[dict[str, Any]] = []
    for pillar_id, pillar in PILLARS.items():
        for index, (criterion_id, description, criterion_class, mandatory) in enumerate(
            criteria
        ):
            status = pillar["statuses"][index]
            rows.append(
                {
                    "row_id": f"{pillar_id}-{criterion_id}-v0",
                    "pillar_id": pillar_id,
                    "pillar_plain_name": pillar["plain_name"],
                    "pillar_scope": pillar["scope"],
                    "criterion_id": criterion_id,
                    "criterion_description": description,
                    "criterion_class": criterion_class,
                    "mandatory_for_exploratory_seam_entry": mandatory,
                    "status": status,
                    "assessment_reason": (
                        "Conservative science-readiness classification from the "
                        "evidence inventory; legacy closure labels are not imported."
                    ),
                    "evidence_pointer": pillar["evidence_pointer"],
                }
            )
    return rows


def _seam_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    inventory = "formal/docs/paper/FULL_PILLAR_TARGET_MAP_REBASE_v0.md"
    for seam_id, seam in SEAMS.items():
        for index, (criterion_id, description) in enumerate(SEAM_CRITERIA):
            rows.append(
                {
                    "row_id": f"{seam_id}-{criterion_id}-v0",
                    "seam_id": seam_id,
                    "seam_plain_name": seam["plain_name"],
                    "pillar_ids": seam["pillar_ids"],
                    "criterion_id": criterion_id,
                    "criterion_description": description,
                    "required_for_level_5_admissibility": True,
                    "status": seam["statuses"][index],
                    "assessment_reason": (
                        "Conservative seam-readiness classification; partial route "
                        "records do not establish seam admissibility."
                    ),
                    "evidence_pointer": inventory,
                }
            )
    return rows


def _status_counts(rows: list[dict[str, Any]]) -> dict[str, int]:
    observed = Counter(row["status"] for row in rows)
    return {status: observed.get(status, 0) for status in ALLOWED_READINESS_STATUSES}


def _pillar_entry_met(pillar_id: str, rows: list[dict[str, Any]]) -> bool:
    entry_rows = [
        row
        for row in rows
        if row["pillar_id"] == pillar_id and row["criterion_class"] == "entry_gating"
    ]
    return len(entry_rows) == 5 and all(row["status"] == "met" for row in entry_rows)


def build_readiness_artifact(*, reviewed: bool) -> dict[str, Any]:
    pillar_rows = _pillar_rows()
    seam_rows = _seam_rows()
    exploratory_eligible: list[str] = []
    level_5_eligible: list[str] = []
    for seam_id, seam in SEAMS.items():
        rows = [row for row in seam_rows if row["seam_id"] == seam_id]
        by_criterion = {row["criterion_id"]: row["status"] for row in rows}
        pillar_ready = all(
            _pillar_entry_met(pillar_id, pillar_rows)
            for pillar_id in seam["pillar_ids"]
        )
        if (
            pillar_ready
            and by_criterion["object_map"] == "met"
            and by_criterion["unit_map"] == "met"
            and by_criterion["residual"] == "met"
        ):
            exploratory_eligible.append(seam_id)
        if all(row["status"] == "met" for row in rows):
            level_5_eligible.append(seam_id)

    status = (
        "accepted_current_science_sprint_readiness_authority"
        if reviewed
        else "prepared_pending_result_review"
    )
    selection_status = "selected_after_review" if reviewed else "candidate_pending_review"
    return {
        "schema_id": "SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0",
        "artifact_id": "SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0",
        "status": status,
        "captured_at_utc": CAPTURED_AT_UTC,
        "authority_roles": {
            "formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json": (
                "legacy operational/governance authority"
            ),
            "formal/docs/release/SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0.json": (
                "current science-sprint readiness authority"
            ),
            "formal/docs/paper/FULL_PILLAR_TARGET_MAP_REBASE_v0.md": (
                "evidence inventory and input surface"
            ),
        },
        "status_vocabulary": list(ALLOWED_READINESS_STATUSES),
        "not_applicable_policy": {
            "required_fields": ["justification", "reviewed_by", "evidence_pointer"],
            "prohibited_for_mandatory_entry_gating_criteria": True,
        },
        "pillar_entry_gating_criteria": [
            {"criterion_id": key, "description": description}
            for key, description in PILLAR_ENTRY_CRITERIA
        ],
        "pillar_maturity_criteria": [
            {"criterion_id": key, "description": description}
            for key, description in PILLAR_MATURITY_CRITERIA
        ],
        "seam_level_5_admissibility_criteria": [
            {"criterion_id": key, "description": description}
            for key, description in SEAM_CRITERIA
        ],
        "exploratory_seam_entry_contract": {
            "both_pillars_five_entry_criteria_must_be_met": True,
            "required_seam_fields": [
                "object_map",
                "unit_map",
                "residual",
                "success_condition",
                "failure_condition",
            ],
        },
        "pillar_readiness_rows": pillar_rows,
        "seam_readiness_rows": seam_rows,
        "summary_counts": {
            "pillar_count": len(PILLARS),
            "pillar_criterion_count": 10,
            "pillar_row_count": len(pillar_rows),
            "pillar_entry_row_count": len(PILLARS) * 5,
            "pillar_maturity_row_count": len(PILLARS) * 5,
            "pillar_status_counts": _status_counts(pillar_rows),
            "seam_count": len(SEAMS),
            "seam_criterion_count": 8,
            "seam_row_count": len(seam_rows),
            "seam_status_counts": _status_counts(seam_rows),
            "exploratory_seam_entry_eligible_count": len(exploratory_eligible),
            "level_5_seam_admissible_count": len(level_5_eligible),
        },
        "exploratory_seam_entry_eligible_ids": exploratory_eligible,
        "level_5_seam_admissible_ids": level_5_eligible,
        "required_sprint_interface": list(SPRINT_INTERFACE_FIELDS),
        "first_science_sprint": {
            "selection_status": selection_status,
            "target": FIRST_SPRINT_GUARDRAIL_TARGET,
            "execution_target": (
                "execute_calc_scalar_stress_energy_divergence_identity_minkowski_v0"
            ),
            "claim_ceiling": "Level 3 toy-model demonstration",
            "scope": (
                "Minkowski scalar stress-energy divergence identity flat-limit pretest"
            ),
            "not_a_qft_gr_seam_admissibility_claim": True,
        },
        "ccft_resume_gates": [
            {"gate_id": "open_system_qm_object", "status": "missing"},
            {"gate_id": "qm_stat_decoherence_bridge", "status": "missing"},
            {"gate_id": "scqed_em_qm_mapping", "status": "missing"},
            {"gate_id": "validated_variable_map", "status": "missing"},
            {"gate_id": "validated_unit_map", "status": "missing"},
            {"gate_id": "validated_assumption_map", "status": "missing"},
            {"gate_id": "source_validation_criteria", "status": "partial"},
            {"gate_id": "adopted_baseline_equation_family", "status": "missing"},
        ],
        "ccft_lane_status": "paused_upstream_prerequisites",
        "master_action_policy": {
            "exploratory_sandboxing_allowed_labels": ["H-HYP", "S-SUPPLIED"],
            "canonicalization_allowed": False,
            "promotion_allowed": False,
            "closure_claim_allowed": False,
        },
        "dependency_driven_program": [
            "flat scalar pretest then bounded curved-space QFT-GR source-contract retest",
            "QM, STAT, EM, and SR maturation where prerequisites do not overlap",
            "QM-STAT and EM-QFT stress tests alongside independent QFT-GR repairs",
            "COSMO construction from GR, SR, and STAT inputs then SR-COSMO test",
            "GR-QM after QM-STAT and QFT-GR source semantics mature",
            "earned integration and later CCFT resumption",
        ],
        "effort_guidance": {
            "pillar_and_seam_science_percent": 60,
            "empirical_forcing_function_percent_ceiling_while_paused": "10-15",
            "governance_and_integration_percent": 15,
            "acceptance_gate": False,
        },
        "claim_boundary": {
            "pillar_completion_claimed": False,
            "seam_admissibility_claimed": False,
            "seam_closure_claimed": False,
            "ccft_resumed": False,
            "ccft_validated": False,
            "master_action_promoted": False,
        },
    }


def validate_readiness_artifact(payload: dict[str, Any]) -> None:
    if payload.get("status_vocabulary") != list(ALLOWED_READINESS_STATUSES):
        raise ValueError("readiness status vocabulary differs")
    pillar_rows = payload.get("pillar_readiness_rows")
    seam_rows = payload.get("seam_readiness_rows")
    if not isinstance(pillar_rows, list) or len(pillar_rows) != 70:
        raise ValueError("expected 70 pillar readiness rows")
    if not isinstance(seam_rows, list) or len(seam_rows) != 40:
        raise ValueError("expected 40 seam readiness rows")
    for row in [*pillar_rows, *seam_rows]:
        status = row.get("status")
        if status not in ALLOWED_READINESS_STATUSES:
            raise ValueError(f"unsupported readiness status: {status}")
        if status == "not_applicable":
            if row.get("mandatory_for_exploratory_seam_entry") is True:
                raise ValueError("not_applicable forbidden for entry-gating criteria")
            for field in ("justification", "reviewed_by", "evidence_pointer"):
                if not row.get(field):
                    raise ValueError(f"not_applicable row missing {field}")
    summary = payload.get("summary_counts", {})
    if summary.get("pillar_status_counts") != _status_counts(pillar_rows):
        raise ValueError("pillar status counts differ from rows")
    if summary.get("seam_status_counts") != _status_counts(seam_rows):
        raise ValueError("seam status counts differ from rows")
    if payload.get("required_sprint_interface") != list(SPRINT_INTERFACE_FIELDS):
        raise ValueError("required sprint interface differs")


def build_prepare_report(readiness: dict[str, Any]) -> dict[str, Any]:
    validate_readiness_artifact(readiness)
    readiness_bytes = canonical_json_bytes(readiness)
    return {
        "schema_id": "SCIENCE_FIRST_PILLAR_SEAM_DEPENDENCY_REBASE_PACKET_20260709_v0",
        "packet_id": "SCIENCE_FIRST_PILLAR_SEAM_DEPENDENCY_REBASE_PACKET_v0",
        "status": "prepared_pending_result_review",
        "captured_at_utc": CAPTURED_AT_UTC,
        "consumed_target": PREPARE_TARGET,
        "consumed_target_kind": "science_first_pillar_seam_dependency_rebase_packet",
        "selected_next_target": REVIEW_TARGET,
        "selected_next_target_kind": (
            "science_first_pillar_seam_dependency_rebase_packet_result_review"
        ),
        "packet_result": PREPARE_OUTCOME,
        "strict_packet_result": PREPARE_STRICT_OUTCOME,
        "readiness_artifact_id": readiness["artifact_id"],
        "readiness_artifact_path": (
            "formal/docs/release/SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0.json"
        ),
        "readiness_artifact_sha256": sha256_bytes(readiness_bytes),
        "readiness_summary_counts": readiness["summary_counts"],
        "readiness_rows_embedded_in_loop_registry": False,
        "authority_roles": readiness["authority_roles"],
        "first_science_sprint_candidate": readiness["first_science_sprint"],
        "required_sprint_interface": readiness["required_sprint_interface"],
        "ccft_resume_gates": readiness["ccft_resume_gates"],
        "ccft_lane_status": "paused_upstream_prerequisites",
        "claim_boundary": readiness["claim_boundary"],
        "equation_compendium_row_added": False,
        "lean_status_wording": (
            "scoped Lean passed; full ToeFormal aggregate not run / not upgraded"
        ),
    }


def build_review_report(readiness: dict[str, Any]) -> dict[str, Any]:
    validate_readiness_artifact(readiness)
    readiness_bytes = canonical_json_bytes(readiness)
    return {
        "schema_id": (
            "SCIENCE_FIRST_PILLAR_SEAM_DEPENDENCY_REBASE_PACKET_RESULT_REVIEW_"
            "20260709_v0"
        ),
        "packet_id": (
            "SCIENCE_FIRST_PILLAR_SEAM_DEPENDENCY_REBASE_PACKET_RESULT_REVIEW_v0"
        ),
        "status": "accepted_current_science_sprint_readiness_authority",
        "captured_at_utc": CAPTURED_AT_UTC,
        "consumed_target": REVIEW_TARGET,
        "consumed_target_kind": (
            "science_first_pillar_seam_dependency_rebase_packet_result_review"
        ),
        "selected_next_target": FIRST_SPRINT_GUARDRAIL_TARGET,
        "selected_next_target_kind": (
            "scalar_qft_gr_source_contract_flat_limit_pretest_guardrail_packet"
        ),
        "packet_result": REVIEW_OUTCOME,
        "strict_packet_result": REVIEW_STRICT_OUTCOME,
        "review_result": REVIEW_OUTCOME,
        "strict_review_result": REVIEW_STRICT_OUTCOME,
        "readiness_artifact_id": readiness["artifact_id"],
        "readiness_artifact_path": (
            "formal/docs/release/SCIENCE_FIRST_PILLAR_SEAM_READINESS_v0.json"
        ),
        "readiness_artifact_sha256": sha256_bytes(readiness_bytes),
        "readiness_summary_counts": readiness["summary_counts"],
        "readiness_rows_embedded_in_loop_registry": False,
        "authority_roles": readiness["authority_roles"],
        "first_science_sprint": readiness["first_science_sprint"],
        "ccft_resume_gates": readiness["ccft_resume_gates"],
        "ccft_lane_status": "paused_upstream_prerequisites",
        "claim_boundary": readiness["claim_boundary"],
        "equation_compendium_row_added": False,
        "lean_status_wording": (
            "scoped Lean passed; full ToeFormal aggregate not run / not upgraded"
        ),
    }


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(canonical_json_bytes(payload))


def prepare_main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Prepare the science-first rebase.")
    parser.add_argument("--readiness-out", type=Path, default=READINESS_PATH)
    parser.add_argument("--report-out", type=Path, default=PREPARE_REPORT_PATH)
    args = parser.parse_args(argv)
    readiness = build_readiness_artifact(reviewed=False)
    report = build_prepare_report(readiness)
    write_json(args.readiness_out, readiness)
    write_json(args.report_out, report)
    print(json.dumps({"outcome": PREPARE_OUTCOME, "selected_next_target": REVIEW_TARGET}))
    return 0


def review_main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Review the science-first rebase.")
    parser.add_argument("--readiness-out", type=Path, default=READINESS_PATH)
    parser.add_argument("--report-out", type=Path, default=REVIEW_REPORT_PATH)
    args = parser.parse_args(argv)
    readiness = build_readiness_artifact(reviewed=True)
    report = build_review_report(readiness)
    write_json(args.readiness_out, readiness)
    write_json(args.report_out, report)
    print(
        json.dumps(
            {"outcome": REVIEW_OUTCOME, "selected_next_target": FIRST_SPRINT_GUARDRAIL_TARGET}
        )
    )
    return 0

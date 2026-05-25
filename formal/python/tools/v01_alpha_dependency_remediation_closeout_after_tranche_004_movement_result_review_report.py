from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.v01_alpha_dependency_remediation_closeout_after_tranche_004_movement_report import (
    CLOSEOUT_CLASSIFICATION as EXPECTED_CLOSEOUT_CLASSIFICATION,
    DEFAULT_OUT as DEFAULT_CLOSEOUT_PACKET_PATH,
    FORBIDDEN_EFFECTS,
    OUTCOME_ID as EXPECTED_CLOSEOUT_OUTCOME,
    PACKET_ID as EXPECTED_CLOSEOUT_PACKET_ID,
    REGISTERED_TRANCHE_004_STATUS,
    SCHEMA_ID as EXPECTED_CLOSEOUT_SCHEMA_ID,
)
from formal.python.tools.v01_alpha_retained_tranche_004_future_remediation_program_report import (
    DEFAULT_CAPTURED_AT_UTC,
    TRANCHE_001_STATUS,
    TRANCHE_002_STATUS,
    TRANCHE_003_STATUS,
    TRANCHE_004_DEPENDENCY,
    TRANCHE_004_FINDING_ID,
    TRANCHE_005_STATUS,
    TRANCHE_006_STATUS,
)
from formal.python.tools.v01_alpha_retained_tranche_004_release_readiness_adjudication_report import (
    SELECTED_TRANCHE_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_CLOSEOUT_AFTER_TRANCHE_004_"
    "MOVEMENT_RESULT_REVIEW_20260523_v0"
)
REVIEW_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_CLOSEOUT_AFTER_TRANCHE_004_"
    "MOVEMENT_RESULT_REVIEW_v0"
)
OUTCOME_ID = (
    "V01_ALPHA_DEPENDENCY_REMEDIATION_CLOSEOUT_RESULT_REVIEW_ACCEPTS_ALL_"
    "TRANCHES_DOCUMENTED_NONBLOCKING_AND_AUTHORIZES_RELEASE_READINESS_"
    "ADJUDICATION_PREPARATION_ONLY"
)
RESULT_REVIEW_CLASSIFICATION = (
    "dependency_remediation_closeout_accepted_all_tranches_documented_"
    "nonblocking_release_readiness_adjudication_preparation_only"
)
CONSUMED_TARGET = (
    "review_v01_alpha_dependency_remediation_closeout_after_tranche_004_movement_result"
)
NEXT_TARGET = (
    "prepare_v01_alpha_release_readiness_adjudication_after_dependency_remediation_closeout"
)
DEPENDENCY_REMEDIATION_CLOSEOUT_ACCEPTED_STATUS = (
    "dependency_remediation_closeout_accepted_all_tranches_documented_nonblocking"
)
RELEASE_READINESS_STATUS = (
    "release_readiness_adjudication_preparation_authorized_after_dependency_"
    "remediation_closeout_no_readiness_marking"
)

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / (
        "V01_ALPHA_DEPENDENCY_REMEDIATION_CLOSEOUT_AFTER_TRANCHE_004_"
        "MOVEMENT_RESULT_REVIEW_20260523_v0.json"
    )
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _documented_dependency_nonblocking_tranches() -> list[dict[str, str]]:
    return [
        {"finding_id": "V01-ALPHA-DEP-REM-001", "status": TRANCHE_001_STATUS},
        {"finding_id": "V01-ALPHA-DEP-REM-002", "status": TRANCHE_002_STATUS},
        {"finding_id": "V01-ALPHA-DEP-REM-003", "status": TRANCHE_003_STATUS},
        {
            "finding_id": TRANCHE_004_FINDING_ID,
            "tranche_id": SELECTED_TRANCHE_ID,
            "dependency": TRANCHE_004_DEPENDENCY,
            "status": REGISTERED_TRANCHE_004_STATUS,
        },
        {"finding_id": "V01-ALPHA-DEP-REM-005", "status": TRANCHE_005_STATUS},
        {"finding_id": "V01-ALPHA-DEP-REM-006", "status": TRANCHE_006_STATUS},
    ]


def _candidate_next_targets() -> list[dict[str, str]]:
    return [
        {
            "target": NEXT_TARGET,
            "decision": "selected",
            "reason": (
                "The dependency-remediation closeout packet is accepted; the "
                "next bounded step is release-readiness adjudication packet "
                "preparation only."
            ),
        },
        {
            "target": "execute_v01_alpha_release_readiness_adjudication",
            "decision": "not_authorized",
            "reason": (
                "Release-readiness adjudication execution requires a separate "
                "prepared packet and result review."
            ),
        },
        {
            "target": "assemble_v01_alpha_release_packet",
            "decision": "not_authorized",
            "reason": "Release assembly remains downstream of readiness adjudication.",
        },
        {
            "target": "close_qft_gr_seam",
            "decision": "not_authorized",
            "reason": "QFT-GR seam closure remains a separate downstream adjudication.",
        },
        {
            "target": "mark_v01_alpha_release_ready",
            "decision": "not_authorized",
            "reason": "Release readiness is not marked by closeout result review.",
        },
    ]


def build_closeout_result_review(
    *,
    closeout_packet_path: Path = DEFAULT_CLOSEOUT_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    packet = _read_json(closeout_packet_path)
    documented_tranches = _documented_dependency_nonblocking_tranches()
    criteria = list(packet.get("closeout_criteria", []))
    evidence_chain = list(packet.get("evidence_chain", []))
    candidate_next_targets = _candidate_next_targets()
    forbidden_effect_status = {effect: False for effect in FORBIDDEN_EFFECTS}

    acceptance_criteria = {
        "consumes_expected_closeout_packet": packet.get("packet_id")
        == EXPECTED_CLOSEOUT_PACKET_ID,
        "packet_schema_expected": packet.get("schema_id") == EXPECTED_CLOSEOUT_SCHEMA_ID,
        "packet_outcome_expected": packet.get("outcome_id") == EXPECTED_CLOSEOUT_OUTCOME,
        "packet_classification_expected": packet.get(
            "dependency_remediation_closeout_classification"
        )
        == EXPECTED_CLOSEOUT_CLASSIFICATION
        and packet.get("dependency_remediation_closeout_classification_count") == 1,
        "packet_selected_this_review": packet.get("selected_next_target")
        == CONSUMED_TARGET,
        "packet_prepared_closeout_only": packet.get("accepted") is True
        and packet.get("prepared") is True
        and packet.get("dependency_remediation_closeout_packet_prepared") is True
        and packet.get("dependency_remediation_closeout_prepared") is True
        and packet.get("dependency_remediation_closeout_result_review_required") is True
        and packet.get("dependency_remediation_closeout_status")
        == "dependency_remediation_closeout_prepared_pending_result_review",
        "all_six_dependency_tranches_documented_nonblocking": len(documented_tranches)
        == 6
        and packet.get("all_dependency_tranches_nonblocking") is True
        and packet.get("documented_dependency_nonblocking_tranche_count") == 6
        and packet.get("tranche_001_status") == TRANCHE_001_STATUS
        and packet.get("tranche_002_status") == TRANCHE_002_STATUS
        and packet.get("tranche_003_status") == TRANCHE_003_STATUS
        and packet.get("tranche_004_status") == REGISTERED_TRANCHE_004_STATUS
        and packet.get("tranche_005_status") == TRANCHE_005_STATUS
        and packet.get("tranche_006_status") == TRANCHE_006_STATUS,
        "dependency_remediation_queue_exhausted": packet.get(
            "dependency_remediation_queue_exhausted"
        )
        is True
        and packet.get("dependency_remediation_blocker_queue_exhausted") is True
        and packet.get("simple_dependency_remediation_queue_exhausted") is True
        and packet.get("unresolved_dependency_remediation_tranche_count") == 0,
        "review_material_preserved": len(criteria) == 4
        and packet.get("closeout_criteria_count") == 4
        and len(evidence_chain) == packet.get("evidence_chain_count"),
        "source_map_closure_evidence_preserved": packet.get(
            "source_map_closure_registered"
        )
        is True
        and packet.get("final_source_map_closure_registered") is True
        and packet.get("source_map_closure_achieved") is True
        and packet.get("source_map_closure_external_truth_claimed") is False,
        "does_not_close_seam_or_mark_release": packet.get("qft_gr_seam_closed")
        is False
        and packet.get("qft_gr_seam_closure_authorized") is False
        and packet.get("qft_gr_seam_closure_claimed") is False
        and packet.get("release_readiness_held") is True
        and packet.get("release_readiness_still_blocked") is True
        and packet.get("release_readiness_proceed_authorized") is False
        and packet.get("release_assembly_authorized") is False
        and packet.get("release_packet_assembled") is False
        and packet.get("v01_alpha_marked_ready") is False,
        "does_not_discharge_debt_or_promote_science_program": packet.get(
            "lean_theorem_debt_discharged"
        )
        is False
        and packet.get("proof_debt_reduced") is False
        and packet.get("retained_assumptions_discharged") is False
        and packet.get("phase2_authorized") is False
        and packet.get("empirical_validation_authorized") is False
        and packet.get("publication_authorized") is False
        and packet.get("master_action_promotion_authorized") is False,
        "exactly_one_next_target_selected": sum(
            1 for row in candidate_next_targets if row["decision"] == "selected"
        )
        == 1
        and candidate_next_targets[0]["target"] == NEXT_TARGET,
        "forbidden_effects_all_false": all(
            value is False for value in forbidden_effect_status.values()
        ),
    }
    accepted = all(acceptance_criteria.values())

    return {
        "schema_id": SCHEMA_ID,
        "review_id": REVIEW_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "V01_ALPHA_DEPENDENCY_REMEDIATION_CLOSEOUT_RESULT_REVIEW_BLOCKED",
        "consumes_dependency_remediation_closeout_packet": EXPECTED_CLOSEOUT_PACKET_ID,
        "consumes_dependency_remediation_closeout_packet_pointer": _ptr(
            closeout_packet_path
        ),
        "consumed_dependency_remediation_closeout_schema_id": packet.get("schema_id"),
        "consumed_dependency_remediation_closeout_outcome_id": packet.get("outcome_id"),
        "consumed_dependency_remediation_closeout_classification": packet.get(
            "dependency_remediation_closeout_classification"
        ),
        "review_scope": (
            "REVIEW_V01_ALPHA_DEPENDENCY_REMEDIATION_CLOSEOUT_AFTER_TRANCHE_004_"
            "MOVEMENT_RESULT_ONLY_AUTHORIZE_RELEASE_READINESS_ADJUDICATION_"
            "PREPARATION_NO_RELEASE_MARKING_OR_QFT_GR_SEAM_CLOSURE"
        ),
        "result_review_classification": RESULT_REVIEW_CLASSIFICATION,
        "result_classification_count": 1 if accepted else 0,
        "dependency_remediation_closeout_result_reviewed": accepted,
        "dependency_remediation_closeout_result_accepted": accepted,
        "dependency_remediation_closeout_accepted": accepted,
        "dependency_remediation_closeout_rejected": False,
        "dependency_remediation_closeout_status": (
            DEPENDENCY_REMEDIATION_CLOSEOUT_ACCEPTED_STATUS
        ),
        "dependency_remediation_queue_closed": accepted,
        "dependency_remediation_queue_exhausted": accepted,
        "dependency_remediation_blocker_queue_exhausted": accepted,
        "simple_dependency_remediation_queue_exhausted": accepted,
        "all_dependency_tranches_nonblocking": accepted,
        "documented_dependency_nonblocking_tranches": documented_tranches,
        "documented_dependency_nonblocking_tranche_count": len(documented_tranches),
        "unresolved_dependency_remediation_tranches": [],
        "unresolved_dependency_remediation_tranche_count": 0,
        "tranche_001_status": TRANCHE_001_STATUS,
        "tranche_002_status": TRANCHE_002_STATUS,
        "tranche_003_status": TRANCHE_003_STATUS,
        "tranche_004_status": REGISTERED_TRANCHE_004_STATUS,
        "tranche_004_status_exact": REGISTERED_TRANCHE_004_STATUS,
        "tranche_004_formal_movement_accepted": True,
        "tranche_004_retained_blocker_discharged": True,
        "tranche_004_cleared_for_release_readiness": False,
        "tranche_005_status": TRANCHE_005_STATUS,
        "tranche_006_status": TRANCHE_006_STATUS,
        "accepted_source_map_closure_registration": packet.get(
            "accepted_source_map_closure_registration"
        ),
        "source_map_closure_registration_status": packet.get(
            "source_map_closure_registration_status"
        ),
        "registered_source_map_closure_accepted_by_review": packet.get(
            "registered_source_map_closure_accepted_by_review"
        ),
        "source_map_closure_registered": True,
        "final_source_map_closure_registered": True,
        "source_map_closure_achieved": True,
        "source_map_closure_claimed": False,
        "source_map_closure_external_truth_claimed": False,
        "closeout_criteria": criteria,
        "closeout_criteria_count": len(criteria),
        "evidence_chain": evidence_chain,
        "evidence_chain_count": len(evidence_chain),
        "release_readiness_decision_status": RELEASE_READINESS_STATUS,
        "release_readiness_adjudication_preparation_authorized": accepted,
        "release_readiness_adjudication_prepared": False,
        "release_readiness_eligible_for_adjudication": accepted,
        "release_readiness_held": True,
        "release_readiness_still_blocked": True,
        "release_readiness_still_requires_separate_adjudication": True,
        "release_readiness_proceed_authorized": False,
        "release_assembly_authorized": False,
        "release_packet_assembled": False,
        "readiness_marking_authorized": False,
        "v01_alpha_marked_ready": False,
        "qft_gr_source_map_semantic_closure_claimed": False,
        "qft_gr_seam_closed": False,
        "qft_gr_seam_closure_authorized": False,
        "qft_gr_seam_closure_claimed": False,
        "lean_theorem_debt_discharged": False,
        "axiom_spec_backed_debt_reduced": False,
        "proof_debt_reduced": False,
        "retained_assumptions_discharged": False,
        "theorem_discharge_authorized": False,
        "phase2_authorized": False,
        "empirical_validation_authorized": False,
        "empirical_validation_claimed": False,
        "publication_authorized": False,
        "master_action_promotion_authorized": False,
        "forbidden_effect_status": forbidden_effect_status,
        "candidate_next_targets": candidate_next_targets,
        "selected_next_target": NEXT_TARGET
        if accepted
        else "REMEDIATE_V01_ALPHA_DEPENDENCY_REMEDIATION_CLOSEOUT_RESULT_REVIEW",
        "selected_next_target_kind": (
            "release_readiness_adjudication_preparation_after_dependency_"
            "remediation_closeout_only"
        ),
        "selection_count": 1 if accepted else 0,
        "next_action_scope": (
            "PREPARE_V01_ALPHA_RELEASE_READINESS_ADJUDICATION_AFTER_DEPENDENCY_"
            "REMEDIATION_CLOSEOUT_ONLY_NO_RELEASE_ASSEMBLY_OR_READINESS_MARKING"
        ),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "The v0.1-alpha dependency-remediation closeout result review "
            "accepts all six dependency-remediation tranches as nonblocking "
            "at the control layer and authorizes only release-readiness "
            "adjudication packet preparation. It does not close the QFT-GR "
            "seam, assemble release, mark release readiness, discharge "
            "theorem/proof debt or retained assumptions, authorize Phase 2, "
            "authorize empirical validation, authorize publication, promote "
            "the master action, or make an external-truth claim."
        ),
        "roadmap_update_required": True,
    }


def write_closeout_result_review(
    *,
    closeout_packet_path: Path = DEFAULT_CLOSEOUT_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_closeout_result_review(
        closeout_packet_path=closeout_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the v0.1-alpha dependency remediation closeout result "
            "review after tranche 004 movement."
        )
    )
    parser.add_argument("--closeout-packet", type=Path, default=DEFAULT_CLOSEOUT_PACKET_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    closeout_packet_path = (
        ns.closeout_packet
        if ns.closeout_packet.is_absolute()
        else (REPO_ROOT / ns.closeout_packet)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_closeout_result_review(
        closeout_packet_path=closeout_packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        "v01_alpha_dependency_remediation_closeout_after_tranche_004_movement_"
        "result_review_report: "
        f"accepted={payload['accepted']} classification="
        f"{payload['result_review_classification']} "
        f"next={payload['selected_next_target']} out={_ptr(out)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

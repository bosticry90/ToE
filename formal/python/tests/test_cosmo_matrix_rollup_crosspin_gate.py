from __future__ import annotations

import json
import re
from pathlib import Path

from formal.python.tests._archived_history_sentinel import split_active_and_archived


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
MATRIX_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PILLAR_STATUS_MATRIX_v1.json"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
COSMO_TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md"

# Literal cross-pin token residency block for nonflip micro21-29 rollup gates.
COSMO_NONFLIP_MICRO21_29_ROLLUP_TOKENS = {
    "dryrun_nonflip_execution_boundary_status_doc",
    "dryrun_nonflip_execution_boundary_status_gate",
    "dryrun_nonflip_execution_boundary_status_policy",
    "COSMO_DRYRUN_NONFLIP_EXECUTION_BOUNDARY_STATUS_POLICY_v0",
    "dryrun_nonflip_execution_custody_parity_packet_doc",
    "dryrun_nonflip_execution_custody_parity_packet_gate",
    "dryrun_nonflip_execution_custody_parity_packet_policy",
    "COSMO_DRYRUN_NONFLIP_EXECUTION_CUSTODY_PARITY_PACKET_POLICY_v0",
    "dryrun_nonflip_bounded_scope_audit_doc",
    "dryrun_nonflip_bounded_scope_audit_gate",
    "dryrun_nonflip_bounded_scope_audit_policy",
    "COSMO_DRYRUN_NONFLIP_BOUNDED_SCOPE_AUDIT_POLICY_v0",
    "dryrun_nonflip_custody_chain_parity_audit_doc",
    "dryrun_nonflip_custody_chain_parity_audit_gate",
    "dryrun_nonflip_custody_chain_parity_audit_policy",
    "COSMO_DRYRUN_NONFLIP_CUSTODY_CHAIN_PARITY_AUDIT_POLICY_v0",
    "dryrun_nonflip_execution_boundary_recertification_packet_doc",
    "dryrun_nonflip_execution_boundary_recertification_packet_gate",
    "dryrun_nonflip_execution_boundary_recertification_packet_policy",
    "COSMO_DRYRUN_NONFLIP_EXECUTION_BOUNDARY_RECERTIFICATION_PACKET_POLICY_v0",
    "dryrun_nonflip_execution_custody_continuity_audit_doc",
    "dryrun_nonflip_execution_custody_continuity_audit_gate",
    "dryrun_nonflip_execution_custody_continuity_audit_policy",
    "COSMO_DRYRUN_NONFLIP_EXECUTION_CUSTODY_CONTINUITY_AUDIT_POLICY_v0",
    "dryrun_nonflip_custody_boundary_recertification_audit_doc",
    "dryrun_nonflip_custody_boundary_recertification_audit_gate",
    "dryrun_nonflip_custody_boundary_recertification_audit_policy",
    "COSMO_DRYRUN_NONFLIP_CUSTODY_BOUNDARY_RECERTIFICATION_AUDIT_POLICY_v0",
    "dryrun_nonflip_execution_boundary_continuity_recertification_audit_doc",
    "dryrun_nonflip_execution_boundary_continuity_recertification_audit_gate",
    "dryrun_nonflip_execution_boundary_continuity_recertification_audit_policy",
    "COSMO_DRYRUN_NONFLIP_EXECUTION_BOUNDARY_CONTINUITY_RECERTIFICATION_AUDIT_POLICY_v0",
    "dryrun_nonflip_execution_custody_recertification_continuity_audit_doc",
    "dryrun_nonflip_execution_custody_recertification_continuity_audit_gate",
    "dryrun_nonflip_execution_custody_recertification_continuity_audit_policy",
    "COSMO_DRYRUN_NONFLIP_EXECUTION_CUSTODY_RECERTIFICATION_CONTINUITY_AUDIT_POLICY_v0",
}


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def _cosmo_roadmap_row(roadmap_text: str) -> tuple[str, str, str, str]:
    active_text, _ = split_active_and_archived(roadmap_text, ROADMAP_PATH)
    match = re.search(
        r"^\|\s*`PILLAR-COSMO`\s*\|\s*`([^`]+)`\s*\|\s*`([^`]+)`\s*\|\s*`([^`]+)`\s*\|\s*`([^`]*)`\s*\|",
        active_text,
        flags=re.MULTILINE,
    )
    assert match is not None, "Missing active roadmap row for PILLAR-COSMO."
    return match.groups()


def test_cosmo_matrix_row_is_present_and_locked() -> None:
    matrix = _read_json(MATRIX_PATH)
    cosmo = matrix.get("pillars", {}).get("PILLAR-COSMO")
    assert isinstance(cosmo, dict), "PILLAR-COSMO matrix row must exist."

    expected_pairs = {
        "discharge_doc": "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md",
        "full_derivation_token": "COSMO_BACKGROUND_ADJUDICATION",
        "inevitability_token": "COSMO_BACKGROUND_ADJUDICATION",
            "full_derivation": "DISCHARGED_v0_BOUNDED",
            "inevitability": "DISCHARGED_v0_BOUNDED",
            "matrix_status": "CLOSED",
        "target_id": "TARGET-COSMO-BG-PLAN",
        "target_doc": "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_OBJECT_v0.md",
        "prereq_targets": "TARGET-GR01-DERIV-CHECKLIST-PLAN;TARGET-SR-COV-PLAN",
        "rollup_summary_doc": "formal/docs/paper/TOE_COSMO_BACKGROUND_PILLAR_SUMMARY_v0.md",
        "rollup_package_doc": "formal/markdown/locks/policy/COSMO_BACKGROUND_PILLAR_PACKAGE_v0.md",
        "rollup_gate": "formal/python/tests/test_cosmo_background_pillar_package_rollup_gate.py",
        "state_checkpoint_gate": "formal/python/tests/test_cosmo_state_rollup_checkpoint_gate.py",
        "lane_drift_alarm_gate": "formal/python/tests/test_cosmo_bg_micro07_matrix_lane_drift_alarm_gate.py",
        "lane_transition_policy": "LOCKED_QUEUE_ENFORCED_CROSS_SURFACE",
        "unlock_transition_packet_doc": "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_08_LOCKED_QUEUE_UNLOCK_TRANSITION_PACKET_v0.md",
        "unlock_transition_packet_gate": "formal/python/tests/test_cosmo_bg_micro08_locked_queue_unlock_transition_packet_gate.py",
        "unlock_transition_packet_policy": "PREAUTHORIZED_CONDITIONS_REQUIRED_NO_STATUS_FLIP",
        "authorized_unlock_checklist_doc": "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_09_AUTHORIZED_UNLOCK_CONDITIONS_CHECKLIST_PACKET_v0.md",
        "authorized_unlock_checklist_gate": "formal/python/tests/test_cosmo_bg_micro09_authorized_unlock_conditions_checklist_packet_gate.py",
        "authorized_unlock_checklist_policy": "CHECKLIST_PACKET_COMPLETE_BEFORE_ANY_STATUS_CHANGE",
        "lock_transition_dryrun_attestation_doc": "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_10_LOCK_TRANSITION_DRYRUN_ATTESTATION_PACKET_v0.md",
        "lock_transition_dryrun_attestation_gate": "formal/python/tests/test_cosmo_bg_micro10_lock_transition_dryrun_attestation_packet_gate.py",
        "lock_transition_dryrun_attestation_policy": "DRYRUN_ATTESTATION_REQUIRED_NO_STATUS_FLIP",
        "dryrun_reconciliation_doc": "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_11_DRYRUN_RECONCILIATION_PACKET_v0.md",
        "dryrun_reconciliation_gate": "formal/python/tests/test_cosmo_bg_micro11_dryrun_reconciliation_packet_gate.py",
        "dryrun_reconciliation_policy": "CYCLE08_09_10_POLICY_COHERENCE_REQUIRED_NO_STATUS_FLIP",
        "dryrun_closure_doc": "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_12_DRYRUN_CLOSURE_PACKET_v0.md",
        "dryrun_closure_gate": "formal/python/tests/test_cosmo_bg_micro12_dryrun_closure_packet_gate.py",
        "dryrun_closure_policy": "CYCLE08_09_10_11_BUNDLE_HASH_POINTER_LOCK_REQUIRED_NO_STATUS_FLIP",
        "dryrun_custody_doc": "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_13_DRYRUN_CUSTODY_PACKET_v0.md",
        "dryrun_custody_gate": "formal/python/tests/test_cosmo_bg_micro13_dryrun_custody_packet_gate.py",
        "dryrun_custody_policy": "CYCLE08_09_10_11_12_CUSTODY_ATTESTATION_LOCK_REQUIRED_NO_STATUS_FLIP",
        "dryrun_custody_confirmation_doc": "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_14_DRYRUN_CUSTODY_CONFIRMATION_PACKET_v0.md",
        "dryrun_custody_confirmation_gate": "formal/python/tests/test_cosmo_bg_micro14_dryrun_custody_confirmation_packet_gate.py",
        "dryrun_custody_confirmation_policy": "CYCLE08_09_10_11_12_13_CUSTODY_CONFIRMATION_LOCK_REQUIRED_NO_STATUS_FLIP",
        "dryrun_custody_confirmation_attestation_doc": "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_15_DRYRUN_CUSTODY_CONFIRMATION_ATTESTATION_PACKET_v0.md",
        "dryrun_custody_confirmation_attestation_gate": "formal/python/tests/test_cosmo_bg_micro15_dryrun_custody_confirmation_attestation_packet_gate.py",
        "dryrun_custody_confirmation_attestation_policy": "CYCLE08_09_10_11_12_13_14_CUSTODY_CONFIRMATION_ATTESTATION_LOCK_REQUIRED_NO_STATUS_FLIP",
        "dryrun_custody_confirmation_attestation_confirmation_doc": "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_16_DRYRUN_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_v0.md",
        "dryrun_custody_confirmation_attestation_confirmation_gate": "formal/python/tests/test_cosmo_bg_micro16_dryrun_custody_confirmation_attestation_confirmation_packet_gate.py",
        "dryrun_custody_confirmation_attestation_confirmation_policy": "CYCLE08_09_10_11_12_13_14_15_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_LOCK_REQUIRED_NO_STATUS_FLIP",
        "dryrun_custody_confirmation_attestation_confirmation_attestation_doc": "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_17_DRYRUN_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_v0.md",
        "dryrun_custody_confirmation_attestation_confirmation_attestation_gate": "formal/python/tests/test_cosmo_bg_micro17_dryrun_custody_confirmation_attestation_confirmation_attestation_packet_gate.py",
        "dryrun_custody_confirmation_attestation_confirmation_attestation_policy": "CYCLE08_09_10_11_12_13_14_15_16_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_LOCK_REQUIRED_NO_STATUS_FLIP",
        "dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_doc": "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_18_DRYRUN_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_v0.md",
        "dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_gate": "formal/python/tests/test_cosmo_bg_micro18_dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_packet_gate.py",
        "dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_policy": "CYCLE08_09_10_11_12_13_14_15_16_17_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_LOCK_REQUIRED_NO_STATUS_FLIP",
        "dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_doc": "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_19_DRYRUN_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_v0.md",
        "dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_gate": "formal/python/tests/test_cosmo_bg_micro19_dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_packet_gate.py",
        "dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_policy": "CYCLE08_09_10_11_12_13_14_15_16_17_18_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_LOCK_REQUIRED_NO_STATUS_FLIP",
        "dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_doc": "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_20_DRYRUN_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_v0.md",
        "dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_gate": "formal/python/tests/test_cosmo_bg_micro20_dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_packet_gate.py",
        "dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_policy": "CYCLE08_09_10_11_12_13_14_15_16_17_18_19_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_LOCK_REQUIRED_NO_STATUS_FLIP",
        "dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_doc": "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_21_DRYRUN_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_v0.md",
        "dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_gate": "formal/python/tests/test_cosmo_bg_micro21_dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_packet_gate.py",
        "dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_policy": "CYCLE08_09_10_11_12_13_14_15_16_17_18_19_20_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_LOCK_REQUIRED_NO_STATUS_FLIP",
        "dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_doc": "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_22_DRYRUN_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_v0.md",
        "dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_gate": "formal/python/tests/test_cosmo_bg_micro22_dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_packet_gate.py",
        "dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_policy": "CYCLE08_09_10_11_12_13_14_15_16_17_18_19_20_21_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_LOCK_REQUIRED_NO_STATUS_FLIP",
        "dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_doc": "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_23_DRYRUN_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_v0.md",
        "dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_gate": "formal/python/tests/test_cosmo_bg_micro23_dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_packet_gate.py",
        "dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_policy": "CYCLE08_09_10_11_12_13_14_15_16_17_18_19_20_21_22_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_LOCK_REQUIRED_NO_STATUS_FLIP",
        "dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_doc": "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_24_DRYRUN_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_v0.md",
        "dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_gate": "formal/python/tests/test_cosmo_bg_micro24_dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_packet_gate.py",
        "dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_policy": "CYCLE08_09_10_11_12_13_14_15_16_17_18_19_20_21_22_23_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_LOCK_REQUIRED_NO_STATUS_FLIP",
        "dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_doc": "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_25_DRYRUN_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_v0.md",
        "dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_gate": "formal/python/tests/test_cosmo_bg_micro25_dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_packet_gate.py",
        "dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_policy": "CYCLE08_09_10_11_12_13_14_15_16_17_18_19_20_21_22_23_24_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_LOCK_REQUIRED_NO_STATUS_FLIP",
        "dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_doc": "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_26_DRYRUN_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_v0.md",
        "dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_gate": "formal/python/tests/test_cosmo_bg_micro26_dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_packet_gate.py",
        "dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_policy": "CYCLE08_09_10_11_12_13_14_15_16_17_18_19_20_21_22_23_24_25_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_LOCK_REQUIRED_NO_STATUS_FLIP",
        "dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_doc": "formal/docs/paper/DERIVATION_TARGET_COSMOLOGY_BACKGROUND_MICRO_27_DRYRUN_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_v0.md",
        "dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_gate": "formal/python/tests/test_cosmo_bg_micro27_dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_packet_gate.py",
        "dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_policy": "CYCLE08_09_10_11_12_13_14_15_16_17_18_19_20_21_22_23_24_25_26_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_LOCK_REQUIRED_NO_STATUS_FLIP",
        "consistency_gate": "formal/python/tests/test_cosmo_matrix_rollup_crosspin_gate.py",
    }

    for key, expected in expected_pairs.items():
        assert cosmo.get(key) == expected, f"PILLAR-COSMO matrix field drift: `{key}` must equal `{expected}`."


def test_cosmo_matrix_crosspins_roadmap_state_and_target() -> None:
    matrix = _read_json(MATRIX_PATH)
    cosmo = matrix.get("pillars", {}).get("PILLAR-COSMO", {})

    status, target_id, target_path, prereqs = _cosmo_roadmap_row(_read(ROADMAP_PATH))
    assert status == cosmo.get("matrix_status")
    assert target_id == cosmo.get("target_id")
    assert target_path == cosmo.get("target_doc")
    assert prereqs == cosmo.get("prereq_targets")

    state_text = _read(STATE_PATH)
    state_required = [
        "NEXT_PILLAR_FOCUS_v0: PILLAR-COSMO",
        "NEXT_PILLAR_PRIMARY_LANE_v0: TARGET-COSMO-BG-PLAN",
        cosmo["rollup_summary_doc"],
        cosmo["rollup_package_doc"],
        cosmo["rollup_gate"],
        cosmo["state_checkpoint_gate"],
        "COSMO_LOCKED_QUEUE_UNLOCK_TRANSITION_PACKET_POLICY_v0: PREAUTHORIZED_CONDITIONS_REQUIRED_NO_STATUS_FLIP",
        cosmo["unlock_transition_packet_gate"],
        "COSMO_AUTHORIZED_UNLOCK_CHECKLIST_PACKET_POLICY_v0: CHECKLIST_PACKET_COMPLETE_BEFORE_ANY_STATUS_CHANGE",
        cosmo["authorized_unlock_checklist_gate"],
        "COSMO_LOCK_TRANSITION_DRYRUN_ATTESTATION_PACKET_POLICY_v0: DRYRUN_ATTESTATION_REQUIRED_NO_STATUS_FLIP",
        cosmo["lock_transition_dryrun_attestation_gate"],
        "COSMO_DRYRUN_RECONCILIATION_PACKET_POLICY_v0: CYCLE08_09_10_POLICY_COHERENCE_REQUIRED_NO_STATUS_FLIP",
        cosmo["dryrun_reconciliation_gate"],
        "COSMO_DRYRUN_CLOSURE_PACKET_POLICY_v0: CYCLE08_09_10_11_BUNDLE_HASH_POINTER_LOCK_REQUIRED_NO_STATUS_FLIP",
        cosmo["dryrun_closure_gate"],
        "COSMO_DRYRUN_CUSTODY_PACKET_POLICY_v0: CYCLE08_09_10_11_12_CUSTODY_ATTESTATION_LOCK_REQUIRED_NO_STATUS_FLIP",
        cosmo["dryrun_custody_gate"],
        "COSMO_DRYRUN_CUSTODY_CONFIRMATION_PACKET_POLICY_v0: CYCLE08_09_10_11_12_13_CUSTODY_CONFIRMATION_LOCK_REQUIRED_NO_STATUS_FLIP",
        cosmo["dryrun_custody_confirmation_gate"],
        "COSMO_DRYRUN_CUSTODY_CONFIRMATION_ATTESTATION_PACKET_POLICY_v0: CYCLE08_09_10_11_12_13_14_CUSTODY_CONFIRMATION_ATTESTATION_LOCK_REQUIRED_NO_STATUS_FLIP",
        cosmo["dryrun_custody_confirmation_attestation_gate"],
        "COSMO_DRYRUN_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_POLICY_v0: CYCLE08_09_10_11_12_13_14_15_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_LOCK_REQUIRED_NO_STATUS_FLIP",
        cosmo["dryrun_custody_confirmation_attestation_confirmation_gate"],
        "COSMO_DRYRUN_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_POLICY_v0: CYCLE08_09_10_11_12_13_14_15_16_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_LOCK_REQUIRED_NO_STATUS_FLIP",
        cosmo["dryrun_custody_confirmation_attestation_confirmation_attestation_gate"],
        "COSMO_DRYRUN_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_POLICY_v0: CYCLE08_09_10_11_12_13_14_15_16_17_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_LOCK_REQUIRED_NO_STATUS_FLIP",
        cosmo["dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_gate"],
        "COSMO_DRYRUN_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_POLICY_v0: CYCLE08_09_10_11_12_13_14_15_16_17_18_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_LOCK_REQUIRED_NO_STATUS_FLIP",
        cosmo["dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_gate"],
        "COSMO_DRYRUN_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_POLICY_v0: CYCLE08_09_10_11_12_13_14_15_16_17_18_19_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_LOCK_REQUIRED_NO_STATUS_FLIP",
        cosmo["dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_gate"],
        "COSMO_DRYRUN_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_POLICY_v0: CYCLE08_09_10_11_12_13_14_15_16_17_18_19_20_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_LOCK_REQUIRED_NO_STATUS_FLIP",
        cosmo["dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_gate"],
        "COSMO_DRYRUN_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_POLICY_v0: CYCLE08_09_10_11_12_13_14_15_16_17_18_19_20_21_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_LOCK_REQUIRED_NO_STATUS_FLIP",
        cosmo["dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_gate"],
        "COSMO_DRYRUN_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_POLICY_v0: CYCLE08_09_10_11_12_13_14_15_16_17_18_19_20_21_22_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_LOCK_REQUIRED_NO_STATUS_FLIP",
        cosmo["dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_gate"],
        "COSMO_DRYRUN_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_POLICY_v0: CYCLE08_09_10_11_12_13_14_15_16_17_18_19_20_21_22_23_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_LOCK_REQUIRED_NO_STATUS_FLIP",
        cosmo["dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_gate"],
        "COSMO_DRYRUN_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_POLICY_v0: CYCLE08_09_10_11_12_13_14_15_16_17_18_19_20_21_22_23_24_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_LOCK_REQUIRED_NO_STATUS_FLIP",
        cosmo["dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_gate"],
        "COSMO_DRYRUN_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_PACKET_POLICY_v0: CYCLE08_09_10_11_12_13_14_15_16_17_18_19_20_21_22_23_24_25_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_LOCK_REQUIRED_NO_STATUS_FLIP",
        cosmo["dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_gate"],
        "COSMO_DRYRUN_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_PACKET_POLICY_v0: CYCLE08_09_10_11_12_13_14_15_16_17_18_19_20_21_22_23_24_25_26_CUSTODY_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_CONFIRMATION_ATTESTATION_LOCK_REQUIRED_NO_STATUS_FLIP",
        cosmo["dryrun_custody_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_confirmation_attestation_gate"],
    ]
    missing_state = [token for token in state_required if token not in state_text]
    assert not missing_state, "State COSMO matrix cross-pin token drift: " + ", ".join(missing_state)

    target_text = _read(COSMO_TARGET_PATH)
    target_required = [
        "formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json",
        cosmo["target_id"],
        cosmo["rollup_summary_doc"],
        cosmo["rollup_package_doc"],
        cosmo["rollup_gate"],
        "formal/python/tests/test_pillar_matrix_roadmap_coverage_gate.py",
    ]
    missing_target = [token for token in target_required if token not in target_text]
    assert not missing_target, "COSMO target matrix cross-pin token drift: " + ", ".join(missing_target)

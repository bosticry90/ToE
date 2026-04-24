from __future__ import annotations

import json
from pathlib import Path

from formal.python.tests._archived_history_sentinel import split_active_and_archived
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md"
DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_IMPLEMENTATION_TRANCHE_28_DECLARATION_20260406_v0.md"
CHECKPOINT_DOC_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_T28_GR_QM_BOUNDED_EXECUTION_CHECKPOINT_20260406_v0.md"
CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "ws10_t28_gr_qm_bounded_execution_checkpoint_20260406_v0.json"
GATE_PATH = REPO_ROOT / "formal" / "python" / "tests" / "test_ws10_t28_gr_qm_bounded_execution_checkpoint_gate.py"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _active_text(path: Path) -> str:
    active, _ = split_active_and_archived(_read(path), path)
    return active


def test_ws10_t28_files_exist() -> None:
    assert PROGRAM_PATH.exists(), "Missing remediation execution program doc."
    assert DECLARATION_PATH.exists(), "Missing Tranche 28 declaration."
    assert CHECKPOINT_DOC_PATH.exists(), "Missing T28 execution checkpoint artifact."
    assert CHECKPOINT_PATH.exists(), "Missing T28 checkpoint json artifact."
    assert GATE_PATH.exists(), "Missing T28 gate file."


def test_ws10_t28_tokens_parity() -> None:
    state_text = _active_text(STATE_PATH)
    roadmap_text = _active_text(ROADMAP_PATH)
    parity_tokens = [
        "THEORY_RESTART_T28_REMEDIATION_PHASE_B_STATUS_v0: ACTIVE_BOUNDED_GR_QM_EXECUTION_CHECKPOINT_NONLIVE",
        "THEORY_RESTART_T28_REMEDIATION_PHASE_B_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_28_DECLARATION_20260406_v0.md",
        "THEORY_RESTART_T28_REMEDIATION_PHASE_B_PROGRAM_DOC_v0: formal/docs/release/WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md",
        "THEORY_RESTART_T28_REMEDIATION_PHASE_B_CHECKPOINT_ARTIFACT_v0: formal/docs/release/WS_10_T28_GR_QM_BOUNDED_EXECUTION_CHECKPOINT_20260406_v0.md",
        "THEORY_RESTART_T28_REMEDIATION_PHASE_B_CHECKPOINT_JSON_v0: formal/output/ws10_t28_gr_qm_bounded_execution_checkpoint_20260406_v0.json",
        "THEORY_RESTART_T28_REMEDIATION_PHASE_B_GATE_v0: formal/python/tests/test_ws10_t28_gr_qm_bounded_execution_checkpoint_gate.py",
        "THEORY_RESTART_T28_REMEDIATION_PHASE_B_ENTRY_CRITERIA_v0: REQUIRES_T27_ACCEPTANCE_PLUS_SINGLE_LANE_SCOPE_LOCK_NONLIVE",
        "THEORY_RESTART_T28_REMEDIATION_PHASE_B_EXECUTION_LIVE_TOKEN_COUNT_v0: 0",
        "THEORY_RESTART_T28_REMEDIATION_PHASE_B_SCOPE_TOKEN_v0: CONTROL_SURFACE_BOUNDED_GR_QM_EXECUTION_CHECKPOINT_NONLIVE",
        "THEORY_RESTART_T28_REMEDIATION_PHASE_B_ACTIVE_LANE_v0: A1_GR_QM_SEAM_PROMOTION",
        "THEORY_RESTART_T28_REMEDIATION_PHASE_B_PAUSED_LANE_v0: A1_BR01_DISPERSION_TO_METRIC",
        "THEORY_RESTART_T28_REMEDIATION_PHASE_B_CHECKPOINT_STATUS_v0: READY_FOR_NEXT_BOUNDED_INCREMENT_NONLIVE",
        "THEORY_RESTART_T28_REMEDIATION_PHASE_B_STOP_CONDITION_v0: HALT_ON_SCOPE_DRIFT_OR_LIVE_TOKEN_OR_BR01_REACTIVATION",
        "THEORY_RESTART_T28_REMEDIATION_PHASE_B_ROLLBACK_ANCHOR_v0: 522eedb",
        "THEORY_RESTART_T28_REMEDIATION_PACKET42_POLICY_INVARIANCE_v0: ENFORCED",
    ]
    for token in parity_tokens:
        assert token in state_text, f"Missing state token: {token}"
        assert token in roadmap_text, f"Missing roadmap token: {token}"


def test_ws10_t28_program_tokens_present() -> None:
    text = _read(PROGRAM_PATH)
    required = [
        "WS10_REMEDIATION_PHASE_B_T28_STATUS_v0: ACTIVE_BOUNDED_GR_QM_EXECUTION_CHECKPOINT_NONLIVE",
        "WS10_REMEDIATION_PHASE_B_T28_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_28_DECLARATION_20260406_v0.md",
        "WS10_REMEDIATION_PHASE_B_T28_CHECKPOINT_ARTIFACT_v0: formal/docs/release/WS_10_T28_GR_QM_BOUNDED_EXECUTION_CHECKPOINT_20260406_v0.md",
        "WS10_REMEDIATION_PHASE_B_T28_CHECKPOINT_JSON_v0: formal/output/ws10_t28_gr_qm_bounded_execution_checkpoint_20260406_v0.json",
        "WS10_REMEDIATION_PHASE_B_T28_GATE_v0: formal/python/tests/test_ws10_t28_gr_qm_bounded_execution_checkpoint_gate.py",
        "WS10_REMEDIATION_PHASE_B_T28_ENTRY_CRITERIA_v0: REQUIRES_T27_ACCEPTANCE_PLUS_SINGLE_LANE_SCOPE_LOCK_NONLIVE",
        "WS10_REMEDIATION_PHASE_B_T28_EXECUTION_LIVE_TOKEN_COUNT_v0: 0",
        "WS10_REMEDIATION_PHASE_B_T28_SCOPE_TOKEN_v0: CONTROL_SURFACE_BOUNDED_GR_QM_EXECUTION_CHECKPOINT_NONLIVE",
        "WS10_REMEDIATION_PHASE_B_T28_ACTIVE_LANE_v0: A1_GR_QM_SEAM_PROMOTION",
        "WS10_REMEDIATION_PHASE_B_T28_PAUSED_LANE_v0: A1_BR01_DISPERSION_TO_METRIC",
        "WS10_REMEDIATION_PHASE_B_T28_CHECKPOINT_STATUS_v0: READY_FOR_NEXT_BOUNDED_INCREMENT_NONLIVE",
        "WS10_REMEDIATION_PHASE_B_T28_STOP_CONDITION_v0: HALT_ON_SCOPE_DRIFT_OR_LIVE_TOKEN_OR_BR01_REACTIVATION",
        "WS10_REMEDIATION_PHASE_B_T28_ROLLBACK_ANCHOR_v0: 522eedb",
        "WS10_REMEDIATION_PHASE_B_T28_ADJUDICATION_v0: FIRST_BOUNDED_EXECUTION_CHECKPOINT_PINNED_NONLIVE",
    ]
    missing = [token for token in required if token not in text]
    assert not missing, "Missing remediation program Phase B T28 token(s): " + ", ".join(missing)


def test_ws10_t28_checkpoint_binding() -> None:
    checkpoint_text = _read(CHECKPOINT_DOC_PATH)
    payload = _json(CHECKPOINT_PATH)

    assert "scope_token: CONTROL_SURFACE_BOUNDED_GR_QM_EXECUTION_CHECKPOINT_NONLIVE" in checkpoint_text
    assert "checkpoint_type: BOUNDED_CLASS_FLIP_READINESS_PACKAGE" in checkpoint_text
    assert "checkpoint_status_token: READY_FOR_NEXT_BOUNDED_INCREMENT_NONLIVE" in checkpoint_text
    assert "theorem_surface_target: formal/toe_formal/ToeFormal/Bridges/GR_QM_SeamPromotion.lean" in checkpoint_text

    assert payload.get("status") == "ACTIVE_BOUNDED_GR_QM_EXECUTION_CHECKPOINT_NONLIVE"
    assert payload.get("execution_live_token_count") == 0
    assert payload.get("active_lane") == "A1_GR_QM_SEAM_PROMOTION"
    assert payload.get("paused_lane") == "A1_BR01_DISPERSION_TO_METRIC"
    assert payload.get("scope_token") == "CONTROL_SURFACE_BOUNDED_GR_QM_EXECUTION_CHECKPOINT_NONLIVE"
    assert payload.get("checkpoint_type") == "BOUNDED_CLASS_FLIP_READINESS_PACKAGE"
    assert payload.get("checkpoint_status") == "READY_FOR_NEXT_BOUNDED_INCREMENT_NONLIVE"


def test_ws10_t28_status_vocabulary_is_closed() -> None:
    surfaces = [
        _active_text(STATE_PATH),
        _active_text(ROADMAP_PATH),
        _read(PROGRAM_PATH),
        _read(CHECKPOINT_DOC_PATH),
    ]

    required_values = {
        "A1_GR_QM_SEAM_PROMOTION",
        "A1_BR01_DISPERSION_TO_METRIC",
        "CONTROL_SURFACE_BOUNDED_GR_QM_EXECUTION_CHECKPOINT_NONLIVE",
        "READY_FOR_NEXT_BOUNDED_INCREMENT_NONLIVE",
    }
    for value in required_values:
        assert any(value in text for text in surfaces), f"Missing required execution-checkpoint value: {value}"

    forbidden_values = [
        "AUTHORIZED_SINGLE_LANE_LIVE",
        "DUAL_LANE_LIVE",
        "BR01_REACTIVATED",
    ]
    for forbidden in forbidden_values:
        assert all(forbidden not in text for text in surfaces), (
            f"Forbidden live-status vocabulary present: {forbidden}"
        )

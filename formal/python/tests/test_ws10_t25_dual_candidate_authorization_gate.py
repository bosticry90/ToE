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
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
PROGRAM_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md"
DECLARATION_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_IMPLEMENTATION_TRANCHE_25_DECLARATION_20260405_v0.md"
CANDIDATE_A_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_T25_A1_GR_QM_SEAM_PROMOTION_MICRO_CANDIDATE_v0.md"
CANDIDATE_B_PATH = REPO_ROOT / "formal" / "docs" / "release" / "WS_10_T25_A1_BR01_DISPERSION_TO_METRIC_MICRO_CANDIDATE_v0.md"
CHECKPOINT_PATH = REPO_ROOT / "formal" / "output" / "ws10_t25_dual_candidate_preauthorization_checkpoint_20260405_v0.json"
GATE_PATH = REPO_ROOT / "formal" / "python" / "tests" / "test_ws10_t25_dual_candidate_authorization_gate.py"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def _active_text(path: Path) -> str:
    active, _ = split_active_and_archived(_read(path), path)
    return active


def test_ws10_t25_files_exist() -> None:
    assert PROGRAM_PATH.exists(), "Missing remediation execution program doc."
    assert DECLARATION_PATH.exists(), "Missing Tranche 25 declaration."
    assert CANDIDATE_A_PATH.exists(), "Missing T25 candidate A artifact."
    assert CANDIDATE_B_PATH.exists(), "Missing T25 candidate B artifact."
    assert CHECKPOINT_PATH.exists(), "Missing Tranche 25 checkpoint artifact."
    assert GATE_PATH.exists(), "Missing Tranche 25 gate file."


def test_ws10_t25_tokens_parity() -> None:
    state_text = _active_text(STATE_PATH)
    roadmap_text = _active_text(ROADMAP_PATH)
    parity_tokens = [
        "THEORY_RESTART_T25_REMEDIATION_PHASE_E_STATUS_v0: ACTIVE_DUAL_CANDIDATE_PREDECISION_NONCLAIM",
        "THEORY_RESTART_T25_REMEDIATION_PHASE_E_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_25_DECLARATION_20260405_v0.md",
        "THEORY_RESTART_T25_REMEDIATION_PHASE_E_PROGRAM_DOC_v0: formal/docs/release/WS_10_REMEDIATION_EXECUTION_PROGRAM_20260404_v0.md",
        "THEORY_RESTART_T25_REMEDIATION_PHASE_E_CANDIDATE_A_ARTIFACT_v0: formal/docs/release/WS_10_T25_A1_GR_QM_SEAM_PROMOTION_MICRO_CANDIDATE_v0.md",
        "THEORY_RESTART_T25_REMEDIATION_PHASE_E_CANDIDATE_B_ARTIFACT_v0: formal/docs/release/WS_10_T25_A1_BR01_DISPERSION_TO_METRIC_MICRO_CANDIDATE_v0.md",
        "THEORY_RESTART_T25_REMEDIATION_PHASE_E_CHECKPOINT_ARTIFACT_v0: formal/output/ws10_t25_dual_candidate_preauthorization_checkpoint_20260405_v0.json",
        "THEORY_RESTART_T25_REMEDIATION_PHASE_E_GATE_v0: formal/python/tests/test_ws10_t25_dual_candidate_authorization_gate.py",
        "THEORY_RESTART_T25_REMEDIATION_PHASE_E_ENTRY_CRITERIA_v0: REQUIRES_T24_ACCEPTANCE_PLUS_TWO_STRUCTURALLY_MATCHED_CANDIDATES_PLUS_NO_EXECUTION_LIVE_TOKENS",
        "THEORY_RESTART_T25_REMEDIATION_PHASE_E_CANDIDATE_COUNT_v0: 2",
        "THEORY_RESTART_T25_REMEDIATION_PHASE_E_EXECUTION_LIVE_TOKEN_COUNT_v0: 0",
        "THEORY_RESTART_T25_REMEDIATION_PHASE_E_AUTHORIZATION_STATE_v0: BOTH_LANES_PREDECISION_NOT_AUTHORIZED_NONLIVE",
        "THEORY_RESTART_T25_REMEDIATION_PHASE_E_ROLLBACK_ANCHOR_v0: 28f228f",
        "THEORY_RESTART_T25_REMEDIATION_PACKET42_POLICY_INVARIANCE_v0: ENFORCED",
    ]
    for token in parity_tokens:
        assert token in state_text, f"Missing state token: {token}"
        assert token in roadmap_text, f"Missing roadmap token: {token}"


def test_ws10_t25_program_tokens_present() -> None:
    text = _read(PROGRAM_PATH)
    required = [
        "WS10_REMEDIATION_PHASE_E_T25_STATUS_v0: ACTIVE_DUAL_CANDIDATE_PREDECISION_NONCLAIM",
        "WS10_REMEDIATION_PHASE_E_T25_DECLARATION_v0: formal/docs/release/WS_10_IMPLEMENTATION_TRANCHE_25_DECLARATION_20260405_v0.md",
        "WS10_REMEDIATION_PHASE_E_T25_CANDIDATE_A_ARTIFACT_v0: formal/docs/release/WS_10_T25_A1_GR_QM_SEAM_PROMOTION_MICRO_CANDIDATE_v0.md",
        "WS10_REMEDIATION_PHASE_E_T25_CANDIDATE_B_ARTIFACT_v0: formal/docs/release/WS_10_T25_A1_BR01_DISPERSION_TO_METRIC_MICRO_CANDIDATE_v0.md",
        "WS10_REMEDIATION_PHASE_E_T25_CHECKPOINT_ARTIFACT_v0: formal/output/ws10_t25_dual_candidate_preauthorization_checkpoint_20260405_v0.json",
        "WS10_REMEDIATION_PHASE_E_T25_GATE_v0: formal/python/tests/test_ws10_t25_dual_candidate_authorization_gate.py",
        "WS10_REMEDIATION_PHASE_E_T25_ENTRY_CRITERIA_v0: REQUIRES_T24_ACCEPTANCE_PLUS_TWO_STRUCTURALLY_MATCHED_CANDIDATES_PLUS_NO_EXECUTION_LIVE_TOKENS",
        "WS10_REMEDIATION_PHASE_E_T25_CANDIDATE_COUNT_v0: 2",
        "WS10_REMEDIATION_PHASE_E_T25_EXECUTION_LIVE_TOKEN_COUNT_v0: 0",
        "WS10_REMEDIATION_PHASE_E_T25_AUTHORIZATION_STATE_v0: BOTH_LANES_PREDECISION_NOT_AUTHORIZED_NONLIVE",
        "WS10_REMEDIATION_PHASE_E_T25_ROLLBACK_ANCHOR_v0: 28f228f",
        "WS10_REMEDIATION_PHASE_E_T25_ADJUDICATION_v0: CANDIDATE_ARTIFACTS_PINNED_NONLIVE_PREDECISION",
    ]
    missing = [token for token in required if token not in text]
    assert not missing, "Missing remediation program Phase E T25 token(s): " + ", ".join(missing)


def test_ws10_t25_candidate_structure_and_nonlive_semantics() -> None:
    candidate_texts = [_read(CANDIDATE_A_PATH), _read(CANDIDATE_B_PATH)]
    required_sections = [
        "## Candidate identity",
        "## Objective class",
        "## Bounded scope",
        "## Candidate payload",
        "## Non-authorization status",
        "## Comparative evaluation hooks",
        "## Pointer contract",
    ]
    for text in candidate_texts:
        for section in required_sections:
            assert section in text, f"Missing required section '{section}' in candidate artifact."
        assert "WS10_T25_CANDIDATE_AUTHORIZATION_STATE_v0: PREDECISION_NOT_AUTHORIZED_NONLIVE" in text
        assert "WS10_T25_CANDIDATE_EXECUTION_STATUS_v0: PREDECISION_NONLIVE" in text

    live_execution_tokens = 0
    live_patterns = [
        re.compile(r"WS10_T25_.*_EXECUTION_LIVE_v0:"),
        re.compile(r"WS10_T25_.*AUTHORIZED_FOR_EXECUTION"),
    ]
    for text in candidate_texts:
        for pattern in live_patterns:
            live_execution_tokens += len(pattern.findall(text))
    assert live_execution_tokens == 0, "Execution-live tokens must be absent for both T25 candidates."


def test_ws10_t25_checkpoint_schema() -> None:
    payload = _json(CHECKPOINT_PATH)
    assert payload.get("artifact_id") == "ws10_t25_dual_candidate_preauthorization_checkpoint_20260405_v0"
    assert payload.get("status") == "ACTIVE_DUAL_CANDIDATE_PREDECISION_NONCLAIM"
    assert payload.get("anchored_commit") == "28f228f"
    assert payload.get("phase") == "E"
    assert (
        payload.get("entry_criteria")
        == "REQUIRES_T24_ACCEPTANCE_PLUS_TWO_STRUCTURALLY_MATCHED_CANDIDATES_PLUS_NO_EXECUTION_LIVE_TOKENS"
    )
    assert payload.get("candidate_count") == 2
    assert payload.get("execution_live_token_count") == 0
    assert payload.get("authorization_state") == "BOTH_LANES_PREDECISION_NOT_AUTHORIZED_NONLIVE"

    required_sections = payload.get("required_sections", [])
    expected_sections = [
        "Candidate identity",
        "Objective class",
        "Bounded scope",
        "Candidate payload",
        "Non-authorization status",
        "Comparative evaluation hooks",
        "Pointer contract",
    ]
    assert required_sections == expected_sections

    artifacts = payload.get("candidate_artifacts", {})
    assert artifacts.get("candidate_a") == "formal/docs/release/WS_10_T25_A1_GR_QM_SEAM_PROMOTION_MICRO_CANDIDATE_v0.md"
    assert artifacts.get("candidate_b") == "formal/docs/release/WS_10_T25_A1_BR01_DISPERSION_TO_METRIC_MICRO_CANDIDATE_v0.md"

    invariance = payload.get("invariance", {})
    assert invariance.get("release_gate_truth_invariance") == "ENFORCED"
    assert invariance.get("packet42_policy_invariance") == "ENFORCED"
    assert invariance.get("nonclaim_boundary_invariance") == "ENFORCED"
    assert invariance.get("scalar_freeze_policy_invariance") == "ENFORCED"

from __future__ import annotations

import json
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
CHECKLIST_PATH = REPO_ROOT / "Canonical Verification Checklist.md"
GOVERNANCE_SUITE_PATH = REPO_ROOT / "governance_suite.ps1"
DECLARATION_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "CONVERGENCE_PROMOTION_SIGNIFICANCE_DECLARATION_20260409_v0.md"
)
CHECKPOINT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "convergence_promotion_significance_checkpoint_20260409_v0.json"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _active_text(path: Path) -> str:
    active, _ = split_active_and_archived(_read(path), path)
    return active


def _json(path: Path) -> dict:
    return json.loads(_read(path))


def test_convergence_promotion_significance_files_exist() -> None:
    assert DECLARATION_PATH.exists(), "Missing promotion-significance declaration."
    assert CHECKPOINT_PATH.exists(), "Missing promotion-significance checkpoint JSON."


def test_convergence_promotion_significance_checkpoint_shape() -> None:
    payload = _json(CHECKPOINT_PATH)

    assert payload.get("schema_id") == "CONVERGENCE_PROMOTION_SIGNIFICANCE_CHECKPOINT_20260409_v0"
    assert payload.get("status") == "ACTIVE_NONLIVE_NONCLAIM"
    assert payload.get("baseline_pack_pointer") == (
        "formal/output/reports/convergence_baseline_pack_20260409_v0.json"
    )

    ps = payload.get("promotion_significance", {})
    assert isinstance(ps, dict)

    threshold = ps.get("discriminator_threshold", {})
    assert threshold.get("metric") == "CONVERGENCE_SCORE"
    assert threshold.get("operator") == ">="
    assert isinstance(threshold.get("value"), (int, float))

    score = ps.get("discriminator_score", {})
    assert isinstance(score.get("value"), (int, float))
    assert isinstance(score.get("measurement_window"), str) and score["measurement_window"]

    blocker = ps.get("blocker_reduction_claim", {})
    assert isinstance(blocker.get("baseline_total"), int)
    assert isinstance(blocker.get("current_total"), int)
    assert isinstance(blocker.get("delta"), int)
    assert isinstance(blocker.get("required_for_promotion"), str)

    proof_debt = ps.get("proof_debt_movement", {})
    assert isinstance(proof_debt.get("baseline_open_items"), int)
    assert isinstance(proof_debt.get("current_open_items"), int)
    assert isinstance(proof_debt.get("delta"), int)
    assert isinstance(proof_debt.get("required_for_promotion"), str)


def test_convergence_promotion_significance_state_and_checklist_tokens_present() -> None:
    state_text = _active_text(STATE_PATH)
    checklist_text = _read(CHECKLIST_PATH)

    state_required = [
        "CONVERGENCE_PROMOTION_SIGNIFICANCE_STATUS_v0: ACTIVE_NONLIVE_NONCLAIM",
        "CONVERGENCE_PROMOTION_SIGNIFICANCE_DECLARATION_v0: formal/docs/release/CONVERGENCE_PROMOTION_SIGNIFICANCE_DECLARATION_20260409_v0.md",
        "CONVERGENCE_PROMOTION_SIGNIFICANCE_CHECKPOINT_v0: formal/output/reports/convergence_promotion_significance_checkpoint_20260409_v0.json",
        "CONVERGENCE_PROMOTION_SIGNIFICANCE_RULE_v0: MISSING_DISCRIMINATOR_OR_BLOCKER_OR_PROOF_DEBT_FIELDS_IS_HARD_FAIL",
        "CONVERGENCE_PROMOTION_SIGNIFICANCE_GATE_v0: formal/python/tests/test_convergence_promotion_significance_gate.py",
    ]
    for token in state_required:
        assert token in state_text, f"Missing state token: {token}"

    checklist_required = [
        "Promotion-significance checkpoint pointer declared? YES / NO",
        "Discriminator score measured? YES / NO",
        "Blocker-count delta measured? YES / NO",
        "Proof-debt delta measured? YES / NO",
    ]
    for token in checklist_required:
        assert token in checklist_text, f"Missing checklist token: {token}"


def test_convergence_hardening_bundle_is_wired_in_governance_suite() -> None:
    suite_text = _read(GOVERNANCE_SUITE_PATH)
    required = [
        "formal/python/tests/test_convergence_baseline_pack_gate.py",
        "formal/python/tests/test_convergence_promotion_significance_gate.py",
        "formal/python/tests/test_convergence_promotion_authorization_block_gate.py",
        "formal/python/tests/test_redundancy_control_registry_family_index_gate.py",
        "formal/python/tests/test_redundancy_control_seam_family_index_gate.py",
    ]
    for token in required:
        assert token in suite_text, f"Missing governance-suite integration token: {token}"

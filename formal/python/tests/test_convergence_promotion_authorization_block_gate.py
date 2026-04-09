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


def test_convergence_promotion_authorization_status_semantics() -> None:
    payload = _json(CHECKPOINT_PATH)
    ps = payload.get("promotion_significance", {})

    threshold = ps.get("discriminator_threshold", {})
    score = ps.get("discriminator_score", {})
    blocker = ps.get("blocker_reduction_claim", {})
    proof_debt = ps.get("proof_debt_movement", {})
    auth = ps.get("promotion_authorization", {})

    threshold_value = float(threshold.get("value"))
    score_value = float(score.get("value"))
    blocker_delta = int(blocker.get("delta"))
    proof_debt_delta = int(proof_debt.get("delta"))

    status = auth.get("status")
    assert isinstance(status, str) and status

    exception = auth.get("exception", {})
    exception_declared = bool(exception.get("declared"))
    exception_pointer = str(exception.get("rationale_pointer", ""))

    if score_value >= threshold_value and blocker_delta < 0 and proof_debt_delta < 0:
        assert status == "PROMOTION_ELIGIBLE"
    elif exception_declared:
        assert status == "EXCEPTION_REVIEW_REQUIRED"
        assert exception_pointer
    else:
        assert status == "BLOCKED_PENDING_BLOCKER_AND_PROOF_DEBT_MOVEMENT"
        block_reasons = auth.get("block_reasons", [])
        assert isinstance(block_reasons, list) and block_reasons



def test_convergence_promotion_authorization_tokens_present() -> None:
    state_text = _active_text(STATE_PATH)
    checklist_text = _read(CHECKLIST_PATH)

    state_required = [
        "CONVERGENCE_PROMOTION_AUTHORIZATION_STATUS_v0: BLOCKED_PENDING_BLOCKER_AND_PROOF_DEBT_MOVEMENT",
        "CONVERGENCE_PROMOTION_AUTHORIZATION_RULE_v0: PROMOTION_ELIGIBLE_REQUIRES_THRESHOLD_PLUS_NEGATIVE_BLOCKER_DELTA_PLUS_NEGATIVE_PROOF_DEBT_DELTA_OR_EXPLICIT_EXCEPTION_REVIEW",
        "CONVERGENCE_PROMOTION_AUTHORIZATION_GATE_v0: formal/python/tests/test_convergence_promotion_authorization_block_gate.py",
    ]
    for token in state_required:
        assert token in state_text, f"Missing state token: {token}"

    checklist_required = [
        "Promotion authorization status recorded? YES / NO",
        "Exception declaration recorded if used? YES / NO",
    ]
    for token in checklist_required:
        assert token in checklist_text, f"Missing checklist token: {token}"

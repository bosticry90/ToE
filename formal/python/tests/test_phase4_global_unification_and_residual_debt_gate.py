from __future__ import annotations

import re
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
PLAN_PATH = REPO_ROOT / "formal" / "docs" / "release" / "PILLAR_FULL_COMPLETION_ACTION_PLAN_v0.md"
DEBT_PATH = REPO_ROOT / "formal" / "docs" / "release" / "RESIDUAL_GLOBAL_DEBT_REGISTER_v0.md"
UNIFICATION_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_TOE_GLOBAL_UNIFICATION_CLOSURE_v0.md"
COMPOSITION_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_TOE_GLOBAL_UNIFICATION_COMPOSITION_v0.md"
NECESSITY_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_TOE_GLOBAL_UNIFICATION_NECESSITY_v0.md"
COUNTERFACTUAL_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_TOE_GLOBAL_UNIFICATION_COUNTERFACTUAL_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
RESULTS_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "RESULTS_TABLE_v0.md"
SUITE_PATH = REPO_ROOT / "governance_suite.ps1"

GATE_REL = "formal/python/tests/test_phase4_global_unification_and_residual_debt_gate.py"
DEBT_REL = "formal/docs/release/RESIDUAL_GLOBAL_DEBT_REGISTER_v0.md"
UNIFICATION_REL = "formal/docs/paper/DERIVATION_TARGET_TOE_GLOBAL_UNIFICATION_CLOSURE_v0.md"
COMPOSITION_REL = "formal/docs/paper/DERIVATION_TARGET_TOE_GLOBAL_UNIFICATION_COMPOSITION_v0.md"
NECESSITY_REL = "formal/docs/paper/DERIVATION_TARGET_TOE_GLOBAL_UNIFICATION_NECESSITY_v0.md"
COUNTERFACTUAL_REL = "formal/docs/paper/DERIVATION_TARGET_TOE_GLOBAL_UNIFICATION_COUNTERFACTUAL_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _extract_token(text: str, token_name: str) -> str:
    m = re.search(rf"\b{re.escape(token_name)}\s*:\s*([A-Za-z0-9_\-]+)", text)
    assert m is not None, f"Missing token `{token_name}`."
    return m.group(1)


def _result_row_status(row_id: str, results_text: str) -> str:
    m = re.search(rf"^\|\s*{re.escape(row_id)}\s*\|\s*`([^`]+)`\s*\|", results_text, flags=re.MULTILINE)
    assert m is not None, f"Missing `{row_id}` row in RESULTS_TABLE_v0.md."
    return m.group(1)


def _pillar_derivation_rows(results_text: str) -> list[tuple[str, str]]:
    pattern = re.compile(r"^\|\s*(TOE-(?:GR|QM|EM|SR|QFT|STAT|COSMO)-DER-[0-9]+)\s*\|\s*`([^`]+)`\s*\|", flags=re.MULTILINE)
    return pattern.findall(results_text)


def _classification(doc_text: str) -> str:
    m = re.search(r"Classification:\s*\n-\s*`([^`]+)`", doc_text)
    assert m is not None, "Missing Classification line."
    return m.group(1)


def test_phase4_artifacts_are_pinned_and_wired() -> None:
    plan_text = _read(PLAN_PATH)
    debt_text = _read(DEBT_PATH)
    unification_text = _read(UNIFICATION_PATH)
    composition_text = _read(COMPOSITION_PATH)
    necessity_text = _read(NECESSITY_PATH)
    counterfactual_text = _read(COUNTERFACTUAL_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    suite_text = _read(SUITE_PATH)

    for token in (
        "### Phase 4: Cross-Pillar Unification and Residual-Risk Closure",
        DEBT_REL,
        UNIFICATION_REL,
        COMPOSITION_REL,
        NECESSITY_REL,
        COUNTERFACTUAL_REL,
        GATE_REL,
    ):
        assert token in plan_text, f"Action plan missing Phase-4 token `{token}`."

    assert GATE_REL in debt_text, "Residual debt register must pin phase-4 enforcement gate."
    assert DEBT_REL in unification_text, "Global unification target must depend on residual debt register."
    assert GATE_REL in unification_text, "Global unification target must pin phase-4 enforcement gate."
    assert COMPOSITION_REL in unification_text, "Global unification target must pin composition package."
    assert NECESSITY_REL in unification_text, "Global unification target must pin necessity package."
    assert COUNTERFACTUAL_REL in unification_text, "Global unification target must pin counterfactual package."

    assert "TOE_GLOBAL_UNIFICATION_COMPOSITION_ADJUDICATION_v0: DISCHARGED_v0" in composition_text
    assert "TOE_GLOBAL_UNIFICATION_NECESSITY_ADJUDICATION_v0: DISCHARGED_v0" in necessity_text
    assert "TOE_GLOBAL_UNIFICATION_COUNTERFACTUAL_ADJUDICATION_v0: DISCHARGED_v0" in counterfactual_text

    for doc_text, label in ((state_text, "state"), (roadmap_text, "roadmap")):
        assert DEBT_REL in doc_text, f"{label} must pin residual debt register path."
        assert UNIFICATION_REL in doc_text, f"{label} must pin global unification target path."
        assert COMPOSITION_REL in doc_text, f"{label} must pin global composition package path."
        assert NECESSITY_REL in doc_text, f"{label} must pin global necessity package path."
        assert COUNTERFACTUAL_REL in doc_text, f"{label} must pin global counterfactual package path."
        assert GATE_REL in doc_text, f"{label} must pin phase-4 enforcement gate path."

    assert GATE_REL in suite_text, "governance_suite.ps1 must include phase-4 global debt/unification gate."


def test_residual_debt_and_unification_transition_contract() -> None:
    debt_text = _read(DEBT_PATH)
    unification_text = _read(UNIFICATION_PATH)
    results_text = _read(RESULTS_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)
    plan_text = _read(PLAN_PATH)

    blk01_status = _result_row_status("BLK-01", results_text)
    blk02_status = _result_row_status("BLK-02", results_text)

    blk01_adj = _extract_token(debt_text, "BLK01_RAC_PROMOTION_ADJUDICATION_v0")
    blk02_adj = _extract_token(debt_text, "BLK02_ACTION_RAC_RETIREMENT_ADJUDICATION_v0")
    debt_status = _extract_token(debt_text, "RESIDUAL_GLOBAL_DEBT_STATUS_v0")

    for surface_text, label in ((state_text, "state"), (roadmap_text, "roadmap")):
        assert _extract_token(surface_text, "BLK01_RAC_PROMOTION_ADJUDICATION_v0") == blk01_adj, (
            f"{label}: BLK01 adjudication token drift."
        )
        assert _extract_token(surface_text, "BLK02_ACTION_RAC_RETIREMENT_ADJUDICATION_v0") == blk02_adj, (
            f"{label}: BLK02 adjudication token drift."
        )
        assert _extract_token(surface_text, "TOE_GLOBAL_UNIFICATION_ADJUDICATION_v0") == _extract_token(
            unification_text, "TOE_GLOBAL_UNIFICATION_ADJUDICATION_v0"
        ), f"{label}: unification adjudication token drift."

    unification_adj = _extract_token(unification_text, "TOE_GLOBAL_UNIFICATION_ADJUDICATION_v0")
    composition = _extract_token(unification_text, "TOE_GLOBAL_UNIFICATION_COMPOSITION_STATUS_v0")
    necessity = _extract_token(unification_text, "TOE_GLOBAL_UNIFICATION_NECESSITY_STATUS_v0")
    counterfactual = _extract_token(unification_text, "TOE_GLOBAL_UNIFICATION_COUNTERFACTUAL_STATUS_v0")
    unification_class = _classification(unification_text)

    der_rows = _pillar_derivation_rows(results_text)
    non_theorem_der_rows = [row_id for row_id, label in der_rows if label != "T-PROVED"]

    blockers_open = blk01_status.startswith("B-") or blk02_status.startswith("B-")

    if blockers_open:
        assert debt_status == "ACTIVE", "Residual debt status must remain ACTIVE while BLK rows are blocked."
        assert blk01_adj != "DISCHARGED_v0", "BLK01 adjudication cannot be discharged while BLK-01 is blocked."
        assert blk02_adj != "DISCHARGED_v0", "BLK02 adjudication cannot be discharged while BLK-02 is blocked."
        assert unification_adj != "DISCHARGED_v0", (
            "Global unification adjudication cannot be discharged while residual blockers remain."
        )
        assert "Status: Active Planning" in plan_text, "Action plan must remain Active Planning while residual blockers remain."
        return

    # Even after blocker retirement, global theorem promotion is forbidden until all pillar DER rows are theorem-grade.
    if non_theorem_der_rows:
        assert unification_class == "P-POLICY", (
            "Global unification must remain P-POLICY until all pillar DER rows are theorem-grade. "
            f"Non-theorem rows: {', '.join(non_theorem_der_rows)}"
        )
        assert composition == "PENDING_THEOREM_GRADE_v0"
        assert necessity == "PENDING_THEOREM_GRADE_v0"
        assert counterfactual == "PENDING_THEOREM_GRADE_v0"
        assert unification_adj == "PENDING_THEOREM_GRADE_v0"
        assert "Status: Active Planning" in plan_text, (
            "Action plan must remain Active Planning while theorem-grade DER conversion remains open."
        )
        return

    assert blk01_adj == "DISCHARGED_v0", "BLK01 adjudication must be discharged when BLK-01 is non-blocked."
    assert blk02_adj == "DISCHARGED_v0", "BLK02 adjudication must be discharged when BLK-02 is non-blocked."
    assert unification_class == "T-PROVED", "Global unification must be T-PROVED after theorem-grade DER conversion is complete."
    assert composition == "DISCHARGED_v0", "Unification composition status must be discharged after blocker retirement."
    assert necessity == "DISCHARGED_v0", "Unification necessity status must be discharged after blocker retirement."
    assert counterfactual == "DISCHARGED_v0", "Unification counterfactual status must be discharged after blocker retirement."
    assert unification_adj == "DISCHARGED_v0", "Unification adjudication must be discharged after blocker retirement."

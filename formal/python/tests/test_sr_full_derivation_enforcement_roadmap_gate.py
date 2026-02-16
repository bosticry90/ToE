from __future__ import annotations

from pathlib import Path


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
SR_ENFORCEMENT_ROADMAP_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_sr_enforcement_roadmap_exists_and_pins_authoritative_tokens() -> None:
    text = _read(SR_ENFORCEMENT_ROADMAP_PATH)

    required_tokens = [
        "DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0",
        "TARGET-SR-FULL-DERIVATION-ENFORCEMENT-ROADMAP-PLAN",
        "SR_FULL_DERIVATION_ENFORCEMENT_ADJUDICATION: DISCHARGED_v0_ROADMAP_PINNED",
        "Authoritative no-deviation rule",
        "Phase I — Theorem-object realization",
        "Phase II — Canonical equivalence theorem",
        "Phase III — Assumption minimization discharge",
        "Phase IV — Robustness + negative-control discharge",
        "Phase V — Derivation-completeness gate discharge",
        "Phase VI — Inevitability gate discharge",
        "Phase VII — Package freeze and reopen policy",
        "MATH|DEF|POLICY|SCOPE",
        "TARGET-SR-DERIV-COMPLETENESS-GATE-PLAN",
        "TOE-SR-THM-01",
        "formal/toe_formal/ToeFormal/SR/CovarianceObjectDischargeStub.lean",
        "test_sr_full_derivation_enforcement_roadmap_gate.py",
    ]

    missing = [tok for tok in required_tokens if tok not in text]
    assert not missing, "Missing required SR enforcement-roadmap token(s): " + ", ".join(missing)


def test_sr_enforcement_roadmap_is_synced_with_state_and_physics_roadmap() -> None:
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    required_state_tokens = [
        "TARGET-SR-FULL-DERIVATION-ENFORCEMENT-ROADMAP-PLAN",
        "formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md",
        "SR_FULL_DERIVATION_ENFORCEMENT_ADJUDICATION: DISCHARGED_v0_ROADMAP_PINNED",
        "SR_FULL_DERIVATION_ENFORCEMENT_MODE_v0: AUTHORITATIVE_NO_DEVIATION",
        "SR_FULL_DERIVATION_ENFORCEMENT_PHASE_ORDER_v0: PHASE1_OBJECTS>PHASE2_EQUIV>PHASE3_ASSUMPTIONS>PHASE4_ROBUST_NEGCTRL>PHASE5_DERIVATION_GATE>PHASE6_INEVITABILITY>PHASE7_FREEZE",
    ]
    for token in required_state_tokens:
        assert token in state_text, f"Missing SR enforcement token in state: {token}"

    required_roadmap_tokens = [
        "TARGET-SR-FULL-DERIVATION-ENFORCEMENT-ROADMAP-PLAN",
        "formal/docs/paper/DERIVATION_TARGET_SR_FULL_DERIVATION_ENFORCEMENT_ROADMAP_v0.md",
        "authoritative no-deviation full-derivation/discharge/inevitability roadmap",
    ]
    for token in required_roadmap_tokens:
        assert token in roadmap_text, f"Missing SR enforcement token in physics roadmap: {token}"

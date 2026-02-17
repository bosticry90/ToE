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
PROTOCOL_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "SOLO_PHYSICS_FIRST_PROTOCOL_v0.md"
QM_LEAN_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "QM" / "QMFullDerivationScaffold.lean"
GR_LEAN_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "GR01ActionToOperatorDiscrete.lean"
)
SR_LEAN_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "SR" / "CovarianceObjectDischargeStub.lean"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_solo_physics_first_protocol_is_pinned() -> None:
    text = _read(PROTOCOL_PATH)
    required_phrases = [
        "Solo Physics-First Protocol v0",
        "no timeline, sprint, cadence, or throughput obligations",
        "Physics target first",
        "Governance lock by default",
        "Substance tests only",
        "Counterfactual requirement",
        "Independent necessity-class requirement",
        "Pillar Definition of Done (full contract)",
        "1. Full-derivation done (substantive physics)",
        "2. Discharge done (substantive closure)",
        "3. Inevitability done (substantive necessity)",
        "4. Canonical synchronization done (minimal but required)",
        "5. Disallowed closure patterns",
        "Governance-only closure (docs/tests/tokens without theorem-body delta) is not done.",
    ]
    missing = [tok for tok in required_phrases if tok not in text]
    assert not missing, "Missing solo physics-first protocol phrase(s): " + ", ".join(missing)


def test_qm_gr_and_sr_substance_theorem_tokens_are_present() -> None:
    qm_text = _read(QM_LEAN_PATH)
    gr_text = _read(GR_LEAN_PATH)
    sr_text = _read(SR_LEAN_PATH)

    qm_required = [
        "theorem qm_inevitability_physics_substance_dependency_bundle_v0",
        "theorem qm_inevitability_endpoint_counterfactual_breaks_without_cycle7_dependency_v0",
        "theorem qm_inevitability_independent_necessity_class_from_endpoint_counterfactual_v0",
    ]
    gr_required = [
        "theorem gr01_inevitability_physics_substance_dependency_bundle_v0",
        "theorem gr01_inevitability_endpoint_counterfactual_breaks_without_no_bridge_dependency_v0",
        "theorem gr01_inevitability_independent_necessity_class_from_endpoint_counterfactual_v0",
    ]
    sr_required = [
        "theorem sr_inevitability_physics_substance_dependency_bundle_v0",
        "theorem sr_inevitability_endpoint_counterfactual_breaks_without_interval_dependency_v0",
        "theorem sr_inevitability_independent_necessity_class_from_endpoint_counterfactual_v0",
    ]

    qm_missing = [tok for tok in qm_required if tok not in qm_text]
    gr_missing = [tok for tok in gr_required if tok not in gr_text]
    sr_missing = [tok for tok in sr_required if tok not in sr_text]
    assert not qm_missing, "Missing QM substance theorem token(s): " + ", ".join(qm_missing)
    assert not gr_missing, "Missing GR substance theorem token(s): " + ", ".join(gr_missing)
    assert not sr_missing, "Missing SR substance theorem token(s): " + ", ".join(sr_missing)

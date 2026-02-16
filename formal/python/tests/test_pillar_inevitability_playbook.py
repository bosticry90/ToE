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
PLAYBOOK_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PILLAR_INEVITABILITY_PLAYBOOK_v0.md"
TEMPLATE_PATH = REPO_ROOT / "formal" / "python" / "tests" / "tools" / "pillar_inevitability_gate_template.py"
GR01_TARGET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_GR01_FULL_DERIVATION_DISCHARGE_v0.md"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_playbook_and_template_exist() -> None:
    assert PLAYBOOK_PATH.exists(), "Missing pillar inevitability playbook doc."
    assert TEMPLATE_PATH.exists(), "Missing pillar inevitability gate template module."


def test_playbook_core_invariants_are_pinned() -> None:
    text = _read(PLAYBOOK_PATH)
    required_phrases = [
        "Canonical route invariant",
        "Dual-track inevitability invariant",
        "Anti-circularity invariant",
        "Nontriviality invariant",
        "Promotion invariant",
        "Phase A — Primitive decomposition",
        "Phase B — Constructor route",
        "Phase C — Canonical route composition",
        "Phase D — Gate hardening",
        "Phase E — Substantive discharge",
        "Pilot run refinement log (GR01)",
        "Transfer checklist",
    ]
    missing = [p for p in required_phrases if p not in text]
    assert not missing, "Missing playbook phrase(s): " + ", ".join(missing)


def test_gr01_target_references_playbook_methodology() -> None:
    text = _read(GR01_TARGET_PATH).lower()
    required_tokens = [
        "constructor-routed action-native transport as",
        "canonical weak-field constructor-routed theorem block",
        "nontrivial probe-interface obligations",
    ]
    missing = [tok for tok in required_tokens if tok not in text]
    assert not missing, (
        "GR01 target doc is missing expected methodology transfer tokens: "
        + ", ".join(missing)
    )

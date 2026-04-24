from __future__ import annotations

from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
CLOSURE_STANDARD_PATH = REPO_ROOT / "formal" / "docs" / "release" / "TOE_CLOSURE_SEMANTICS_STANDARD_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"

GATE_REL = "formal/python/tests/test_toe_closure_status_language_ambiguity_guard_gate.py"


REQUIRED_CLOSURE_STANDARD_TOKENS = (
    "TOE_CLOSURE_SEMANTICS_CLOSED_USAGE_RULE_v0: REQUIRE_LAYER_QUALIFIER_IN_STATUS_SURFACES",
    "TOE_DISCHARGED_SEMANTICS_RULE_v0: DISCHARGED_IS_ROUTE_OR_GOVERNANCE_NOT_GLOBAL_PHYSICS_COMPLETENESS",
    "TOE_DISCHARGED_VARIANT_REQUIREMENT_v0: USE_DISCHARGED_v0_BOUNDED_WHEN_CONTINUUM_OR_EQUIVALENCE_OPEN",
    "TOE_CLOSURE_SEMANTICS_AMBIGUITY_GUARD_GATE_v0: formal/python/tests/test_toe_closure_status_language_ambiguity_guard_gate.py",
)

REQUIRED_STATE_MARKERS = (
    "Status-language safety rule: status summaries must not use unqualified `CLOSED` or unqualified `DISCHARGED` as interpretation markers; use layer-qualified closure language and bounded non-claim framing.",
    "`DISCHARGED_v0_*` tokens represent bounded route/governance discharge under pinned assumptions and are not global-physics completeness claims.",
    "Closure status-language ambiguity guard gate pointer: `formal/python/tests/test_toe_closure_status_language_ambiguity_guard_gate.py`.",
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_closure_semantics_standard_has_ambiguity_guard_tokens() -> None:
    text = _read(CLOSURE_STANDARD_PATH)
    for token in REQUIRED_CLOSURE_STANDARD_TOKENS:
        assert token in text


def test_state_surface_has_explicit_qualified_closure_language() -> None:
    text = _read(STATE_PATH)
    for marker in REQUIRED_STATE_MARKERS:
        assert marker in text


def test_ambiguity_guard_gate_is_cross_pinned() -> None:
    closure_text = _read(CLOSURE_STANDARD_PATH)
    state_text = _read(STATE_PATH)

    assert GATE_REL in closure_text
    assert GATE_REL in state_text

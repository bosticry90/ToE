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
QFT_GAUGE_TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_GAUGE_OBJECT_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
QFT_KICKOFF_GATE_PATH = "formal/python/tests/test_qft_gauge_kickoff_scaffold_gate.py"
QFT_BUILD_GATE_PATH = "formal/python/tests/test_lean_build_gate_qft_gauge_object_scaffold.py"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_qft_gauge_target_contains_required_kickoff_tokens() -> None:
    text = _read(QFT_GAUGE_TARGET_PATH)
    required_tokens = [
        "DERIVATION_TARGET_QFT_GAUGE_OBJECT_v0",
        "TARGET-QFT-GAUGE-PLAN",
        "QFT_GAUGE_ADJUDICATION: NOT_YET_DISCHARGED",
        "QFT_GAUGE_SCOPE_BOUNDARY_v0: CONTRACT_OBJECT_SCAFFOLD_ONLY_NONCLAIM",
        "QFT_PREREQS_v0: TARGET-EM-U1-PLAN;TARGET-SR-COV-PLAN",
        "QFT_GAUGE_DELIVERABLE_GROUP_SURFACE_v0: U1_AND_NONABELIAN_PLACEHOLDER_DECLARED",
        "QFT_GAUGE_DELIVERABLE_CONNECTION_SURFACE_v0: A_OBJECT_SURFACE_DECLARED",
        "QFT_GAUGE_DELIVERABLE_CURVATURE_SURFACE_v0: F_EQ_DA_PLUS_A_WEDGE_A_PLACEHOLDER_DECLARED",
        "QFT_GAUGE_DELIVERABLE_TRANSFORM_SURFACE_v0: GAUGE_TRANSFORM_AND_INVARIANCE_STATEMENT_ONLY",
        "QFT_GAUGE_DELIVERABLE_COUPLING_SURFACE_v0: CURRENT_SOURCE_INTERFACE_STATEMENT_ONLY",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "QFT gauge kickoff target is missing required token(s): " + ", ".join(missing)


def test_qft_roadmap_row_is_active_and_scaffold_only() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    rows = [line.strip() for line in roadmap_text.splitlines() if line.strip().startswith("| `PILLAR-QFT` |")]
    assert len(rows) == 1, f"Expected exactly one PILLAR-QFT roadmap row, found {len(rows)}."
    row = rows[0]

    required_row_tokens = [
        "| `ACTIVE` |",
        "TARGET-QFT-GAUGE-PLAN;TARGET-QFT-EVOL-PLAN",
        "formal/docs/paper/DERIVATION_TARGET_QFT_GAUGE_OBJECT_v0.md",
        "formal/docs/paper/DERIVATION_TARGET_QFT_EVOLUTION_OBJECT_v0.md",
        "TARGET-EM-U1-PLAN;TARGET-SR-COV-PLAN",
        "Scaffold-first contract/object activation lane only",
        "no quantization claim",
        "no dynamics claim",
    ]
    missing = [token for token in required_row_tokens if token not in row]
    assert not missing, "PILLAR-QFT roadmap row is missing required kickoff token(s): " + ", ".join(missing)


def test_state_handoff_points_to_qft_gauge_kickoff() -> None:
    text = _read(STATE_PATH)
    required_tokens = [
        "NEXT_PILLAR_FOCUS_v0: PILLAR-QFT",
        "NEXT_PILLAR_PRIMARY_LANE_v0: TARGET-QFT-GAUGE-PLAN",
        "formal/docs/paper/DERIVATION_TARGET_QFT_GAUGE_OBJECT_v0.md",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "State handoff is missing required QFT kickoff token(s): " + ", ".join(missing)


def test_qft_kickoff_nonclaim_boundary_is_explicit() -> None:
    text = _read(QFT_GAUGE_TARGET_PATH)
    required_nonclaim_phrases = [
        "This artifact is planning-only.",
        "This artifact is a non-claim and does not promote theorem/evidence status.",
        "This artifact does not claim Standard Model recovery.",
        "This artifact does not claim quantization closure.",
        "This artifact does not claim dynamics derivation closure.",
        "CONTRACT_OBJECT_SCAFFOLD_ONLY_NONCLAIM",
    ]
    missing = [phrase for phrase in required_nonclaim_phrases if phrase not in text]
    assert not missing, "QFT kickoff non-claim boundary phrase(s) missing: " + ", ".join(missing)


def test_qft_kickoff_and_build_gates_are_pinned_in_authority_surfaces() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)

    for required_path in [QFT_KICKOFF_GATE_PATH, QFT_BUILD_GATE_PATH]:
        assert required_path in roadmap_text, (
            f"Roadmap authority surface must pin `{required_path}`."
        )
        assert required_path in state_text, (
            f"State authority surface must pin `{required_path}`."
        )

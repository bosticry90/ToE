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
QFT_EVOL_TARGET_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_EVOLUTION_OBJECT_v0.md"
QFT_FULL_DISCHARGE_TARGET_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md"
)
QFT_EVOL_OBJECT_SCAFFOLD_LEAN_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "QFT" / "Evolution" / "ObjectScaffold.lean"
)
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"

QFT_FULL_DISCHARGE_TARGET_ID = "TARGET-QFT-FULL-DERIVATION-DISCHARGE-v0"
QFT_FULL_DISCHARGE_DOC_PATH = "formal/docs/paper/DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md"
QFT_FULL_DISCHARGE_GATE_PATH = "formal/python/tests/test_qft_full_derivation_discharge_gate.py"
QFT_EVOL_SATURATION_GATE_PATH = "formal/python/tests/test_qft_evol_scaffold_saturation_gate.py"
QFT_EVOL_HARDENING_MILESTONE_GATE_PATH = (
    "formal/python/tests/test_qft_evol_semantic_hardening_milestone_gate.py"
)
QFT_EVOL_HARDENING_CYCLE3_GATE_PATH = (
    "formal/python/tests/test_qft_evol_semantic_hardening_cycle3_gate.py"
)
QFT_EVOL_HARDENING_CYCLE4_GATE_PATH = (
    "formal/python/tests/test_qft_evol_semantic_hardening_cycle4_gate.py"
)
QFT_EVOL_HARDENING_CYCLE5_GATE_PATH = (
    "formal/python/tests/test_qft_evol_semantic_hardening_cycle5_gate.py"
)
QFT_EVOL_HARDENING_CYCLE6_GATE_PATH = (
    "formal/python/tests/test_qft_evol_semantic_hardening_cycle6_gate.py"
)
QFT_EVOL_HARDENING_CYCLE7_GATE_PATH = (
    "formal/python/tests/test_qft_evol_semantic_hardening_cycle7_gate.py"
)
QFT_EVOL_HARDENING_CYCLE8_GATE_PATH = (
    "formal/python/tests/test_qft_evol_semantic_hardening_cycle8_gate.py"
)

REQUIRED_SECTION_HEADERS = [
    "## TARGET section",
    "## ASSUMPTION_FREEZE section",
    "## CANONICAL_ROUTE section",
    "## ANTI_SHORTCUT section",
    "## COUNTERFACTUAL section",
    "## INDEPENDENT_NECESSITY section",
    "## HARDENING section",
    "## BOUNDED_SCOPE section",
    "## DRIFT_GATES section",
    "## ADJUDICATION_SYNC section",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_qft_full_derivation_discharge_artifacts_exist() -> None:
    assert QFT_EVOL_TARGET_PATH.exists(), "Missing QFT evolution umbrella target document."
    assert QFT_FULL_DISCHARGE_TARGET_PATH.exists(), "Missing QFT full-derivation discharge target document."
    assert QFT_EVOL_OBJECT_SCAFFOLD_LEAN_PATH.exists(), "Missing QFT evolution object scaffold Lean module."
    assert ROADMAP_PATH.exists(), "Missing PHYSICS roadmap document."
    assert STATE_PATH.exists(), "Missing state checkpoint document."


def test_qft_evol_umbrella_references_qft_full_discharge_lane_artifacts() -> None:
    text = _read(QFT_EVOL_TARGET_PATH)
    required_tokens = [
        QFT_FULL_DISCHARGE_TARGET_ID,
        QFT_FULL_DISCHARGE_DOC_PATH,
        QFT_FULL_DISCHARGE_GATE_PATH,
        QFT_EVOL_SATURATION_GATE_PATH,
        QFT_EVOL_HARDENING_MILESTONE_GATE_PATH,
        QFT_EVOL_HARDENING_CYCLE3_GATE_PATH,
        QFT_EVOL_HARDENING_CYCLE4_GATE_PATH,
        QFT_EVOL_HARDENING_CYCLE5_GATE_PATH,
        QFT_EVOL_HARDENING_CYCLE6_GATE_PATH,
        QFT_EVOL_HARDENING_CYCLE7_GATE_PATH,
        QFT_EVOL_HARDENING_CYCLE8_GATE_PATH,
        "QFT_EVOL_SCAFFOLD_SATURATION_v0: MICRO_01_TO_MICRO_52_TRANCHE_01_52_FROZEN",
        "QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_v0: CANONICAL_MOMENTUM_HAMILTONIAN_UNITARITY_CHAIN_PINNED",
        "QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_CYCLE3_v0: CANONICAL_MOMENTUM_INVARIANT_UNITARITY_ROUTE_PINNED",
        "QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_CYCLE4_v0: HAMILTONIAN_TO_GENERATOR_CANONICAL_MOMENTUM_ROUTE_PINNED",
        "QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_CYCLE5_v0: HAMILTONIAN_MEDIATED_REFLECTIVE_CANONICAL_MOMENTUM_GENERATOR_UNITARITY_ROUTE_PINNED",
        "QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_CYCLE6_v0: GENERATOR_UNITARITY_ROUTE_COHERENCE_PINNED",
        "QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_CYCLE7_v0: GENERATOR_UNITARITY_ROUTE_NORMALIZATION_PINNED",
        "QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_CYCLE8_v0: GENERATOR_UNITARITY_ROUTE_NORMALIZATION_COHERENCE_ALIGNMENT_PINNED",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "QFT evolution umbrella target missing discharge-lane token(s): " + ", ".join(missing)


def test_qft_full_discharge_doc_contains_required_tokens_and_headers() -> None:
    text = _read(QFT_FULL_DISCHARGE_TARGET_PATH)
    required_tokens = [
        "DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0",
        QFT_FULL_DISCHARGE_TARGET_ID,
        "QFT_FULL_DERIVATION_ADJUDICATION: NOT_YET_DISCHARGED",
        "QFT_FULL_DERIVATION_INEVITABILITY_ADJUDICATION: NOT_YET_DISCHARGED",
        "QFT_FULL_DERIVATION_PROGRESS_CYCLE1_v0: EVOL_SCAFFOLD_SATURATION_AND_SEMANTIC_HARDENING_PINNED",
        "QFT_FULL_DERIVATION_PROGRESS_CYCLE2_v0: SEMANTIC_HARDENING_MILESTONE_TOKEN_PINNED",
        "QFT_FULL_DERIVATION_PROGRESS_CYCLE3_v0: CANONICAL_MOMENTUM_INVARIANT_UNITARITY_ROUTE_PINNED",
        "QFT_FULL_DERIVATION_PROGRESS_CYCLE4_v0: HAMILTONIAN_TO_GENERATOR_CANONICAL_MOMENTUM_ROUTE_PINNED",
        "QFT_FULL_DERIVATION_PROGRESS_CYCLE5_v0: HAMILTONIAN_MEDIATED_REFLECTIVE_CANONICAL_MOMENTUM_GENERATOR_UNITARITY_ROUTE_PINNED",
        "QFT_FULL_DERIVATION_PROGRESS_CYCLE6_v0: GENERATOR_UNITARITY_ROUTE_COHERENCE_TOKEN_PINNED",
        "QFT_FULL_DERIVATION_PROGRESS_CYCLE7_v0: GENERATOR_UNITARITY_ROUTE_NORMALIZATION_TOKEN_PINNED",
        "QFT_FULL_DERIVATION_PROGRESS_CYCLE8_v0: GENERATOR_UNITARITY_ROUTE_NORMALIZATION_COHERENCE_ALIGNMENT_TOKEN_PINNED",
        "QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_v0: CANONICAL_MOMENTUM_HAMILTONIAN_UNITARITY_CHAIN_PINNED",
        "QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_CYCLE3_v0: CANONICAL_MOMENTUM_INVARIANT_UNITARITY_ROUTE_PINNED",
        "QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_CYCLE4_v0: HAMILTONIAN_TO_GENERATOR_CANONICAL_MOMENTUM_ROUTE_PINNED",
        "QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_CYCLE5_v0: HAMILTONIAN_MEDIATED_REFLECTIVE_CANONICAL_MOMENTUM_GENERATOR_UNITARITY_ROUTE_PINNED",
        "QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_CYCLE6_v0: GENERATOR_UNITARITY_ROUTE_COHERENCE_PINNED",
        "QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_CYCLE7_v0: GENERATOR_UNITARITY_ROUTE_NORMALIZATION_PINNED",
        "QFT_EVOL_SEMANTIC_HARDENING_MILESTONE_CYCLE8_v0: GENERATOR_UNITARITY_ROUTE_NORMALIZATION_COHERENCE_ALIGNMENT_PINNED",
        "qft_evol_canonical_momentum_surface_hardened_v0",
        "qft_evol_canonical_momentum_invariant_step_surface_hardened_v0",
        "qft_evol_hamiltonian_generator_compatibility_hardened_v0",
        "qft_evol_unitarity_injective_step_surface_hardened_v0",
        "qft_evol_generator_unitarity_chain_v0",
        "qft_evol_unitarity_of_canonical_momentum_reflective_invariant_step_v0",
        "qft_evol_generator_canonical_momentum_invariant_of_hamiltonian_compatibility_v0",
        "qft_evol_generator_unitarity_from_reflective_canonical_momentum_route_v0",
        "qft_evol_generator_unitarity_via_hamiltonian_reflective_canonical_momentum_route_v0",
        "qft_evol_generator_unitarity_route_coherence_v0",
        "qft_evol_generator_unitarity_route_normalization_v0",
        "qft_evol_generator_unitarity_route_normalization_coherence_alignment_v0",
        "PILLAR_QFT_FULL_DERIVATION_DISCHARGE_LOCALIZATION_GATE_v0: FULL_DISCHARGE_ARTIFACTS_ONLY",
        "PILLAR_QFT_FULL_DERIVATION_DISCHARGE_NO_PROMOTION_v0: ATTEMPT_ONLY_NO_DISCHARGE",
        "PILLAR_QFT_FULL_DERIVATION_DISCHARGE_BOUNDARY_v0: NO_FULL_DERIVATION_DISCHARGE_OR_INEVITABILITY_PROMOTION",
        "PILLAR_QFT_FULL_DERIVATION_DISCHARGE_ADJUDICATION: NOT_YET_DISCHARGED",
        "formal/toe_formal/ToeFormal/QFT/Evolution/ObjectScaffold.lean",
        QFT_FULL_DISCHARGE_GATE_PATH,
        QFT_EVOL_HARDENING_MILESTONE_GATE_PATH,
        QFT_EVOL_HARDENING_CYCLE3_GATE_PATH,
        QFT_EVOL_HARDENING_CYCLE4_GATE_PATH,
        QFT_EVOL_HARDENING_CYCLE5_GATE_PATH,
        QFT_EVOL_HARDENING_CYCLE6_GATE_PATH,
        QFT_EVOL_HARDENING_CYCLE7_GATE_PATH,
        QFT_EVOL_HARDENING_CYCLE8_GATE_PATH,
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "QFT full-derivation discharge doc missing required token(s): " + ", ".join(missing)

    missing_headers = [header for header in REQUIRED_SECTION_HEADERS if header not in text]
    assert not missing_headers, "QFT full-derivation discharge doc missing required section header(s): " + ", ".join(
        missing_headers
    )


def test_qft_full_discharge_nonclaim_boundary_is_explicit() -> None:
    text = _read(QFT_FULL_DISCHARGE_TARGET_PATH)
    required_nonclaim_phrases = [
        "This artifact is planning-only.",
        "This artifact is a non-claim and does not promote theorem/evidence status.",
        "This artifact does not claim quantization closure.",
        "This artifact does not claim dynamics derivation closure.",
        "This artifact does not claim Standard Model recovery.",
        "This artifact does not claim external truth.",
    ]
    missing = [phrase for phrase in required_nonclaim_phrases if phrase not in text]
    assert not missing, "QFT full-derivation discharge non-claim boundary phrase(s) missing: " + ", ".join(missing)


def test_qft_full_discharge_lean_tokens_are_present() -> None:
    text = _read(QFT_EVOL_OBJECT_SCAFFOLD_LEAN_PATH)
    required_tokens = [
        "def CanonicalMomentumSurface",
        "def CanonicalMomentumInvariantUnderStep",
        "theorem qft_evol_canonical_momentum_surface_hardened_v0",
        "theorem qft_evol_canonical_momentum_invariant_step_surface_hardened_v0",
        "def HamiltonianGeneratorInterfaceStatementOnly",
        "theorem qft_evol_hamiltonian_generator_compatibility_hardened_v0",
        "def UnitarityStatementOnly",
        "theorem qft_evol_unitarity_injective_step_surface_hardened_v0",
        "theorem qft_evol_generator_unitarity_chain_v0",
        "theorem qft_evol_unitarity_of_canonical_momentum_reflective_invariant_step_v0",
        "theorem qft_evol_generator_canonical_momentum_invariant_of_hamiltonian_compatibility_v0",
        "theorem qft_evol_generator_unitarity_from_reflective_canonical_momentum_route_v0",
        "theorem qft_evol_generator_unitarity_via_hamiltonian_reflective_canonical_momentum_route_v0",
        "theorem qft_evol_generator_unitarity_route_coherence_v0",
        "theorem qft_evol_generator_unitarity_route_normalization_v0",
        "theorem qft_evol_generator_unitarity_route_normalization_coherence_alignment_v0",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "QFT evolution Lean scaffold missing full-discharge kickoff token(s): " + ", ".join(missing)


def test_qft_full_discharge_lane_is_pinned_in_authority_surfaces() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    state_text = _read(STATE_PATH)

    required_tokens = [
        QFT_FULL_DISCHARGE_TARGET_ID,
        QFT_FULL_DISCHARGE_DOC_PATH,
        QFT_FULL_DISCHARGE_GATE_PATH,
        QFT_EVOL_SATURATION_GATE_PATH,
        QFT_EVOL_HARDENING_MILESTONE_GATE_PATH,
        QFT_EVOL_HARDENING_CYCLE3_GATE_PATH,
        QFT_EVOL_HARDENING_CYCLE4_GATE_PATH,
        QFT_EVOL_HARDENING_CYCLE5_GATE_PATH,
        QFT_EVOL_HARDENING_CYCLE6_GATE_PATH,
        QFT_EVOL_HARDENING_CYCLE7_GATE_PATH,
        QFT_EVOL_HARDENING_CYCLE8_GATE_PATH,
    ]

    for token in required_tokens:
        assert token in roadmap_text, f"Roadmap authority surface must pin `{token}`."
        assert token in state_text, f"State authority surface must pin `{token}`."


def test_qft_roadmap_row_contains_qft_discharge_target_and_artifact() -> None:
    roadmap_text = _read(ROADMAP_PATH)
    rows = [line.strip() for line in roadmap_text.splitlines() if line.strip().startswith("| `PILLAR-QFT` |")]
    assert len(rows) == 1, f"Expected exactly one PILLAR-QFT roadmap row, found {len(rows)}."

    row = rows[0]
    required_row_tokens = [
        "| `ACTIVE` |",
        "TARGET-QFT-GAUGE-PLAN;TARGET-QFT-EVOL-PLAN;TARGET-QFT-FULL-DERIVATION-DISCHARGE-v0",
        "formal/docs/paper/DERIVATION_TARGET_QFT_EVOLUTION_OBJECT_v0.md;formal/docs/paper/DERIVATION_TARGET_QFT_FULL_DERIVATION_DISCHARGE_v0.md",
    ]
    missing = [token for token in required_row_tokens if token not in row]
    assert not missing, "PILLAR-QFT roadmap row is missing required discharge-lane token(s): " + ", ".join(missing)

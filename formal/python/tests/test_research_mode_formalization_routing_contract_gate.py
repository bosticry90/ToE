from __future__ import annotations

from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.research import harder_qm_stat_target, pilot_pack
from formal.python.research.metadata import ResearchArtifactMetadata, recommend_formalization_route


REPO_ROOT = find_repo_root(Path(__file__))
README_PATH = REPO_ROOT / "README.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
CONTRACT_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "RESEARCH_FORMALIZATION_ROUTING_CONTRACT_20260420_v0.md"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_research_formalization_routing_contract_tokens_and_mirrors_are_pinned() -> None:
    contract_text = _read(CONTRACT_PATH)
    readme_text = _read(README_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    for token in (
        "RESEARCH_FORMALIZATION_ROUTING_STATUS_v0: ACTIVE_NONLIVE_NONCLAIM",
        "RESEARCH_FORMALIZATION_ROUTE_SET_v0: PYTHON_FIRST_PLUS_LEAN4_FIRST_PLUS_PYTHON_THEN_LEAN4_PLUS_DEFER_FORMALIZATION",
        "RESEARCH_FORMALIZATION_ADVISORY_ONLY_RULE_v0: ROUTING_IS_ADVISORY_ONLY_AND_DOES_NOT_AUTHORIZE_CANONICAL_MUTATION_OR_GOVERNANCE_TRANSITION",
        "RESEARCH_FORMALIZATION_GATE_v0: formal/python/tests/test_research_mode_formalization_routing_contract_gate.py",
    ):
        assert token in contract_text

    for ref in (
        "formal/docs/release/RESEARCH_FORMALIZATION_ROUTING_CONTRACT_20260420_v0.md",
        "formal/python/tests/test_research_mode_formalization_routing_contract_gate.py",
    ):
        assert ref in state_text
        assert ref in roadmap_text

    assert "RESEARCH_FORMALIZATION_ROUTING_CONTRACT_20260420_v0.md" in readme_text


def test_research_formalization_routes_match_current_bounded_artifacts() -> None:
    pack = pilot_pack.build_pilot_pack()
    pillar = ResearchArtifactMetadata(**pack["pilots"]["pillar"]["metadata"])
    seam = ResearchArtifactMetadata(**pack["pilots"]["seam"]["metadata"])
    master_action = ResearchArtifactMetadata(**pack["pilots"]["master_action"]["metadata"])

    assert pillar.formalization_route == "PYTHON_THEN_LEAN4"
    assert recommend_formalization_route(pillar) == pillar.formalization_route
    assert seam.formalization_route == "PYTHON_THEN_LEAN4"
    assert recommend_formalization_route(seam) == seam.formalization_route
    assert master_action.formalization_route == "PYTHON_FIRST"
    assert recommend_formalization_route(master_action) == master_action.formalization_route


def test_research_formalization_routes_cover_harder_qm_stat_target() -> None:
    report = harder_qm_stat_target.build_harder_qm_stat_target_report()
    metadata = ResearchArtifactMetadata(**report["artifact"]["metadata"])

    assert metadata.formalization_route == "PYTHON_THEN_LEAN4"
    assert metadata.lean_candidate_target == "QM_STAT_TRANSPORT_MOMENT_STACK_LOCAL_IDENTITIES"
    assert recommend_formalization_route(metadata) == metadata.formalization_route
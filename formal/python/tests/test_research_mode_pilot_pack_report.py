from __future__ import annotations

from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.research import pilot_pack


REPO_ROOT = find_repo_root(Path(__file__))
README_PATH = REPO_ROOT / "README.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_research_mode_pilot_pack_covers_pillar_seam_and_master_action() -> None:
    pack = pilot_pack.build_pilot_pack()

    assert set(pack["pilots"].keys()) == {"pillar", "seam", "master_action"}
    assert pack["pilots"]["pillar"]["metadata"]["target_kind"] == "PILLAR"
    assert pack["pilots"]["seam"]["metadata"]["target_kind"] == "SEAM"
    assert pack["pilots"]["master_action"]["metadata"]["target_kind"] == "MASTER_ACTION"


def test_research_mode_pilot_pack_metrics_show_direct_equation_work() -> None:
    pack = pilot_pack.build_pilot_pack()
    pillar = pack["pilots"]["pillar"]
    seam = pack["pilots"]["seam"]
    master_action = pack["pilots"]["master_action"]

    assert pillar["metrics"]["de_bruijn_gap_abs"] == 0.0
    assert pillar["metrics"]["finite_difference_gap_abs"] < 1.0e-8
    assert seam["metrics"]["continuity_residual_sup_abs"] == 0.0
    assert master_action["metrics"]["baseline_residual_amplitude_abs"] > 0.0
    assert master_action["metrics"]["optimized_residual_amplitude_abs"] == 0.0
    assert master_action["metrics"]["optimized_stationarity_recovered"] is True


def test_research_mode_pilot_pack_observability_remains_fail_closed() -> None:
    pack = pilot_pack.build_pilot_pack()

    assert pack["observability"]["direct_math_artifact_count"] == 3
    assert pack["observability"]["canonical_mutation_attempts"] == 0
    assert pack["summary"]["terminal_outcome"] == "RESEARCH_MODE_PILOT_PACK_MATERIALIZED"
    assert pack["summary"]["step_13_status_v0"] == "COMPLETE_BOUNDED_v0_NONCLAIM"
    assert pack["summary"]["step_14_status_v0"] == "PRELIMINARY_LOOP_SHORTENING_SIGNAL_PRESENT_NONCLAIM"


def test_research_mode_pilot_pack_mirrors_are_cross_pinned() -> None:
    readme_text = _read(README_PATH)
    state_text = _read(STATE_PATH)
    roadmap_text = _read(ROADMAP_PATH)

    for ref in (
        "formal/docs/release/RESEARCH_MODE_PILOT_PACK_20260419_v0.md",
        "formal/python/research/pilot_pack.py",
        "formal/python/tests/test_research_mode_pilot_pack_report.py",
        "formal/output/reports/research_mode_pilot_pack_20260419_v0.json",
        "formal/output/research/research_stat_entropy_balance_probe_20260419_v0.json",
        "formal/output/research/research_qm_stat_transport_witness_probe_20260419_v0.json",
        "formal/output/research/research_master_action_transport_binding_probe_20260419_v0.json",
    ):
        assert ref in state_text
        assert ref in roadmap_text

    assert "RESEARCH_MODE_PILOT_PACK_20260419_v0.md" in readme_text
    assert "test_research_mode_pilot_pack_report.py" in readme_text
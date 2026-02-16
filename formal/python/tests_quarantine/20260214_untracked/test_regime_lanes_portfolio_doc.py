from __future__ import annotations

from pathlib import Path


def test_regime_lanes_portfolio_doc_exists_and_pinned_strings() -> None:
    repo_root = Path(__file__).resolve().parents[3]
    doc_relpath = "formal/docs/release/REGIME_LANES_PORTFOLIO_v0.md"
    doc_path = repo_root / doc_relpath

    assert doc_path.exists(), f"Missing portfolio doc: {doc_relpath}"

    text = doc_path.read_text(encoding="utf-8")
    required_strings = [
        "Regime Lanes Portfolio v0",
        "Scope / claim boundary",
        "How to reproduce",
        "RL01 - Relativistic dispersion limit",
        "RL02 - Nonrelativistic NLSE limit",
        "RL03 - Weak-field Poisson limit",
        "RL04 - Continuity equation lane",
        "RL05 - Wave equation lane",
        "RL06 - Phase winding quantization lane",
        "RL07 - Energy/Noether conservation lane",
        "RL08 - Gauge redundancy invariance lane",
        "RL09 - Dispersion-topology bridge lane",
        "RL10 - Entropy balance lane",
        "RL11 - Causality signal-cone lane",
        "RL12 - Lorentz/Poincare invariance proxy lane",
        "RL13 - Velocity addition group-law lane",
        "RL14 - Time dilation proxy lane",
        "RL15 - Length contraction proxy lane",
        "RL16 - Relativity of simultaneity proxy lane",
        "OV-RL-01_relativistic_dispersion_v0.md",
        "OV-RL-02_nonrelativistic_nlse_v0.md",
        "OV-RL-03_weak_field_poisson_v0.md",
        "OV-RL-04_continuity_v0.md",
        "OV-RL-05_wave_equation_v0.md",
        "OV-RL-06_phase_winding_quantization_v0.md",
        "OV-RL-07_energy_noether_conservation_v0.md",
        "OV-RL-08_gauge_redundancy_invariance_v0.md",
        "OV-RL-09_dispersion_topology_bridge_v0.md",
        "OV-RL-10_entropy_balance_v0.md",
        "OV-RL-11_causality_signal_cone_v0.md",
        "OV-RL-12_lorentz_poincare_invariance_proxy_v0.md",
        "OV-RL-13_velocity_addition_group_law_v0.md",
        "OV-RL-14_time_dilation_proxy_v0.md",
        "OV-RL-15_length_contraction_proxy_v0.md",
        "OV-RL-16_relativity_of_simultaneity_proxy_v0.md",
        "governance_suite.ps1",
    ]
    for required in required_strings:
        assert required in text, f"Portfolio doc missing: {required}"

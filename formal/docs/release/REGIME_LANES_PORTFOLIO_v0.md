# Regime Lanes Portfolio v0

Scope / claim boundary
- This portfolio records reproducible regime correspondences under pinned contracts.
- It does not claim a final theory, empirical superiority, or validity beyond the stated contracts.
- Each lane is a bounded evidence object with explicit inputs, outputs, and tolerance profiles.

How to reproduce
- RL01: `.\py.ps1 -m formal.python.tools.rl01_relativistic_dispersion_front_door` and `.\py.ps1 -m pytest formal/python/tests/test_rl01_relativistic_dispersion_v0_lock.py`
- RL02: `.\py.ps1 -m formal.python.tools.rl02_nonrelativistic_nlse_front_door` and `.\py.ps1 -m pytest formal/python/tests/test_rl02_nonrelativistic_nlse_v0_lock.py`
- RL03: `.\py.ps1 -m formal.python.tools.rl03_weak_field_poisson_front_door` and `.\py.ps1 -m pytest formal/python/tests/test_rl03_weak_field_poisson_v0_lock.py`
- RL04: `.\py.ps1 -m formal.python.tools.rl04_continuity_front_door` and `.\py.ps1 -m pytest formal/python/tests/test_rl04_continuity_v0_lock.py`
- RL05: `.\py.ps1 -m formal.python.tools.rl05_wave_equation_front_door` and `.\py.ps1 -m pytest formal/python/tests/test_rl05_wave_equation_v0_lock.py`
- RL06: `.\py.ps1 -m formal.python.tools.rl06_phase_winding_quantization_front_door` and `.\py.ps1 -m pytest formal/python/tests/test_rl06_phase_winding_quantization_v0_lock.py`
- RL07: `.\py.ps1 -m formal.python.tools.rl07_energy_noether_conservation_front_door` and `.\py.ps1 -m pytest formal/python/tests/test_rl07_energy_noether_conservation_v0_lock.py`
- RL08: `.\py.ps1 -m formal.python.tools.rl08_gauge_redundancy_invariance_front_door` and `.\py.ps1 -m pytest formal/python/tests/test_rl08_gauge_redundancy_invariance_v0_lock.py`
- RL09: `.\py.ps1 -m formal.python.tools.rl09_dispersion_topology_bridge_front_door` and `.\py.ps1 -m pytest formal/python/tests/test_rl09_dispersion_topology_bridge_v0_lock.py`
- RL10: `.\py.ps1 -m formal.python.tools.rl10_entropy_balance_front_door` and `.\py.ps1 -m pytest formal/python/tests/test_rl10_entropy_balance_v0_lock.py`
- RL11: `.\py.ps1 -m formal.python.tools.rl11_causality_signal_cone_front_door` and `.\py.ps1 -m pytest formal/python/tests/test_rl11_causality_signal_cone_v0_lock.py`
- RL12: `.\py.ps1 -m formal.python.tools.rl12_lorentz_poincare_invariance_proxy_front_door` and `.\py.ps1 -m pytest formal/python/tests/test_rl12_lorentz_poincare_invariance_proxy_v0_lock.py`
- RL13: `.\py.ps1 -m formal.python.tools.rl13_velocity_addition_group_law_front_door` and `.\py.ps1 -m pytest formal/python/tests/test_rl13_velocity_addition_group_law_v0_lock.py`
- RL14: `.\py.ps1 -m formal.python.tools.rl14_time_dilation_proxy_front_door` and `.\py.ps1 -m pytest formal/python/tests/test_rl14_time_dilation_proxy_v0_lock.py`
- RL15: `.\py.ps1 -m formal.python.tools.rl15_length_contraction_proxy_front_door` and `.\py.ps1 -m pytest formal/python/tests/test_rl15_length_contraction_proxy_v0_lock.py`
- RL16: `.\py.ps1 -m formal.python.tools.rl16_relativity_of_simultaneity_proxy_front_door` and `.\py.ps1 -m pytest formal/python/tests/test_rl16_relativity_of_simultaneity_proxy_v0_lock.py`
- Governance suite: `pwsh -NoProfile -ExecutionPolicy Bypass -File ./governance_suite.ps1`

Lane index (RL01 - RL16)

RL01 - Relativistic dispersion limit (v0)
- Lock: formal/markdown/locks/observables/OV-RL-01_relativistic_dispersion_v0.md
- Artifacts: formal/external_evidence/relativistic_dispersion_domain_01
- Comparator: formal/python/toe/comparators/rl01_relativistic_dispersion_v0.py
- Contract: formal/docs/rl01_relativistic_dispersion_v0_front_door_contract.md
- Metric: dispersion residuals vs pinned tolerances
- Orthogonality: relativistic dispersion limit recovery

RL02 - Nonrelativistic NLSE limit (v0)
- Lock: formal/markdown/locks/observables/OV-RL-02_nonrelativistic_nlse_v0.md
- Artifacts: formal/external_evidence/rl02_nonrelativistic_limit_nlse_domain_01
- Comparator: formal/python/toe/comparators/rl02_nonrelativistic_nlse_v0.py
- Contract: formal/docs/rl02_nonrelativistic_nlse_v0_front_door_contract.md
- Metric: NLSE limit residuals vs pinned tolerances
- Orthogonality: nonrelativistic reduction limit

RL03 - Weak-field Poisson limit (v0)
- Lock: formal/markdown/locks/observables/OV-RL-03_weak_field_poisson_v0.md
- Artifacts: formal/external_evidence/rl03_weak_field_poisson_domain_01
- Comparator: formal/python/toe/comparators/rl03_weak_field_poisson_v0.py
- Contract: formal/docs/rl03_weak_field_poisson_v0_front_door_contract.md
- Metric: Poisson residual vs pinned tolerance
- Orthogonality: elliptic constraint correspondence

RL04 - Continuity equation lane (v0)
- Lock: formal/markdown/locks/observables/OV-RL-04_continuity_v0.md
- Artifacts: formal/external_evidence/rl04_continuity_domain_01
- Comparator: formal/python/toe/comparators/rl04_continuity_v0.py
- Contract: formal/docs/rl04_continuity_v0_front_door_contract.md
- Metric: continuity residual vs pinned tolerance
- Orthogonality: conservation law correspondence

RL05 - Wave equation lane (v0)
- Lock: formal/markdown/locks/observables/OV-RL-05_wave_equation_v0.md
- Artifacts: formal/external_evidence/rl05_wave_equation_domain_01
- Comparator: formal/python/toe/comparators/rl05_wave_equation_v0.py
- Contract: formal/docs/rl05_wave_equation_v0_front_door_contract.md
- Metric: wave PDE residual vs pinned tolerance
- Orthogonality: hyperbolic propagation correspondence

RL06 - Phase winding quantization lane (v0)
- Lock: formal/markdown/locks/observables/OV-RL-06_phase_winding_quantization_v0.md
- Artifacts: formal/external_evidence/rl06_phase_winding_quantization_domain_01
- Comparator: formal/python/toe/comparators/rl06_phase_winding_quantization_v0.py
- Contract: formal/docs/rl06_phase_winding_quantization_v0_front_door_contract.md
- Metric: integer winding recovery (k-target) with non-integer negative control detection (alpha=0.35)
- Orthogonality: periodic phase winding quantization on a 1D ring
- Suite status: governance suite green on 2026-02-10 (316 passed)

RL07 - Energy/Noether conservation lane (v0)
- Lock: formal/markdown/locks/observables/OV-RL-07_energy_noether_conservation_v0.md
- Artifacts: formal/external_evidence/rl07_energy_noether_conservation_domain_01
- Comparator: formal/python/toe/comparators/rl07_energy_noether_conservation_v0.py
- Contract: formal/docs/rl07_energy_noether_conservation_v0_front_door_contract.md
- Metric: relative energy drift (positive) and energy drop (negative control)
- Orthogonality: Hamiltonian conservation vs dissipative break
- Suite status: governance suite green on 2026-02-10 (316 passed)

RL08 - Gauge redundancy invariance lane (v0)
- Lock: formal/markdown/locks/observables/OV-RL-08_gauge_redundancy_invariance_v0.md
- Artifacts: formal/external_evidence/rl08_gauge_redundancy_invariance_domain_01
- Comparator: formal/python/toe/comparators/rl08_gauge_redundancy_invariance_v0.py
- Contract: formal/docs/rl08_gauge_redundancy_invariance_v0_front_door_contract.md
- Metric: invariance residual (positive) and gauge-break residual (negative control)
- Orthogonality: gauge redundancy invariance vs explicit break
- Suite status: governance suite green on 2026-02-10 (316 passed)

RL09 - Dispersion-topology bridge lane (v0)
- Lock: formal/markdown/locks/observables/OV-RL-09_dispersion_topology_bridge_v0.md
- Artifacts: formal/external_evidence/rl09_dispersion_topology_bridge_domain_01
- Comparator: formal/python/toe/comparators/rl09_dispersion_topology_bridge_v0.py
- Contract: formal/docs/rl09_dispersion_topology_bridge_v0_front_door_contract.md
- Metric: winding target (positive/negative controls)
- Orthogonality: band topology vs dispersion structure
- Suite status: governance suite green on 2026-02-10 (316 passed)

RL10 - Entropy balance lane (v0)
- Lock: formal/markdown/locks/observables/OV-RL-10_entropy_balance_v0.md
- Artifacts: formal/external_evidence/rl10_entropy_balance_domain_01
- Comparator: formal/python/toe/comparators/rl10_entropy_balance_v0.py
- Contract: formal/docs/rl10_entropy_balance_v0_front_door_contract.md
- Metric: entropy production proxy + detailed balance residual (positive/negative controls)
- Orthogonality: detailed balance vs irreversible circulation
- Suite status: governance suite green on 2026-02-10 (316 passed)

RL11 - Causality signal-cone lane (v0)
- Lock: formal/markdown/locks/observables/OV-RL-11_causality_signal_cone_v0.md
- Artifacts: formal/external_evidence/rl11_causality_signal_cone_domain_01
- Comparator: formal/python/toe/comparators/rl11_causality_signal_cone_v0.py
- Contract: formal/docs/rl11_causality_signal_cone_v0_front_door_contract.md
- Metric: leakage_outside_cone (positive/negative controls)
- Orthogonality: causal vs acausal signal-cone admissibility
- Suite status: governance suite green on 2026-02-10 (316 passed)

RL12 - Lorentz/Poincare invariance proxy lane (v0)
- Lock: formal/markdown/locks/observables/OV-RL-12_lorentz_poincare_invariance_proxy_v0.md
- Artifacts: formal/external_evidence/rl12_lorentz_poincare_invariance_proxy_domain_01
- Comparator: formal/python/toe/comparators/rl12_lorentz_poincare_invariance_proxy_v0.py
- Contract: formal/docs/rl12_lorentz_poincare_invariance_proxy_v0_front_door_contract.md
- Metric: invariant_metric (positive/negative controls)
- Orthogonality: Lorentz/Poincare boost invariance vs explicit break
- Suite status: governance suite green on 2026-02-10 (316 passed)

RL13 - Velocity addition group-law lane (v0)
- Lock: formal/markdown/locks/observables/OV-RL-13_velocity_addition_group_law_v0.md
- Artifacts: formal/external_evidence/rl13_velocity_addition_group_law_domain_01
- Comparator: formal/python/toe/comparators/rl13_velocity_addition_group_law_v0.py
- Contract: formal/docs/rl13_velocity_addition_group_law_v0_front_door_contract.md
- Metric: addition_residual (positive/negative controls)
- Orthogonality: Einstein addition vs Galilean break
- Suite status: governance suite green on 2026-02-10 (316 passed)

RL14 - Time dilation proxy lane (v0)
- Lock: formal/markdown/locks/observables/OV-RL-14_time_dilation_proxy_v0.md
- Artifacts: formal/external_evidence/rl14_time_dilation_proxy_domain_01
- Comparator: formal/python/toe/comparators/rl14_time_dilation_proxy_v0.py
- Contract: formal/docs/rl14_time_dilation_proxy_v0_front_door_contract.md
- Metric: dilation_residual (positive/negative controls)
- Orthogonality: Lorentz time dilation vs no-dilation break
- Suite status: governance suite green on 2026-02-10 (316 passed)

RL15 - Length contraction proxy lane (v0)
- Lock: formal/markdown/locks/observables/OV-RL-15_length_contraction_proxy_v0.md
- Artifacts: formal/external_evidence/rl15_length_contraction_proxy_domain_01
- Comparator: formal/python/toe/comparators/rl15_length_contraction_proxy_v0.py
- Contract: formal/docs/rl15_length_contraction_proxy_v0_front_door_contract.md
- Metric: contraction_residual (positive/negative controls)
- Orthogonality: Lorentz length contraction vs no-contraction break
- Suite status: governance suite green on 2026-02-10 (316 passed)

RL16 - Relativity of simultaneity proxy lane (v0)
- Lock: formal/markdown/locks/observables/OV-RL-16_relativity_of_simultaneity_proxy_v0.md
- Artifacts: formal/external_evidence/rl16_relativity_of_simultaneity_proxy_domain_01
- Comparator: formal/python/toe/comparators/rl16_relativity_of_simultaneity_proxy_v0.py
- Contract: formal/docs/rl16_relativity_of_simultaneity_proxy_v0_front_door_contract.md
- Metric: simultaneity_residual (positive/negative controls)
- Orthogonality: Lorentz simultaneity shift vs no-shift break
- Suite status: governance suite green on 2026-02-10 (316 passed)
Governance posture
- Evidence objects are immutable unless version-bumped and re-locked.
- Contract surface freeze tests and lock checks enforce determinism.
- Within-rep is the default interpretability claim; cross-rep requires policy token and proof artifacts.

Next planned lanes (no schedule)
- (none)

Post-RL program: Conditional Theorems (CT)
- Spec: formal/docs/programs/CONDITIONAL_THEOREMS_PROGRAM_v0.md






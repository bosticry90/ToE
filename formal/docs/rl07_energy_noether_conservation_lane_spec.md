# RL07 Energy/Noether Conservation Lane Spec v0

Scope
- RL07 is a regime lane for energy conservation on a discrete, pinned system.
- This spec asserts energy conservation behavior only under the pinned numerical contract.
- No external truth claim is made beyond the pinned discrete setting.

Pinned system (baseline)
- PDE: u_tt = c^2 u_xx (1D linear wave equation)
- Variables: u(x,t), v(x,t) = u_t(x,t)
- Domain: periodic ring, length L=6.283185307179586
- Grid: N=128, dx = L / N
- Parameters: c=1.0

Discrete operators
- D_x uses centered difference: (u_{i+1} - u_{i-1}) / (2*dx)
- D_xx uses second difference: (u_{i+1} - 2*u_i + u_{i-1}) / (dx*dx)

Discrete energy (Hamiltonian)
- E = sum_i [0.5 * v_i^2 + 0.5 * c^2 * (D_x u)_i^2] * dx
- energy conservation is evaluated via relative energy drift

Integrator (positive control)
- Stormer-Verlet (leapfrog) for (u,v)
- Expectation: energy conservation with small drift

Negative control
- Dissipative term: v_t = c^2 u_xx - gamma * v
- gamma=0.02 (pinned)
- Expectation: energy drop over time

Pinned time integration
- dt=0.1*dx
- steps=2000

Pinned pass criteria
- Positive case pass: relative energy drift |E_T - E_0| / E_0 <= eps_drift
- eps_drift=5e-3
- Negative control pass: energy drop (E_0 - E_T) / E_0 >= eps_drop
- eps_drop=0.10

Artifacts (planned)
- reference_report.json: pinned parameters + E_0, E_T, drift, max_drift
- candidate_report.json: same schema and diagnostics

Comparator posture
- expectation-aware pass semantics: positive control passes on low drift, negative control passes on energy drop
- comparisons are bounded to the pinned discrete report schema

# RL10 Entropy Balance Lane Spec v0

Scope
- RL10 targets an entropy-production proxy for detailed balance in a pinned Markov chain.
- Positive control enforces detailed balance with near-zero entropy production.
- Negative control violates detailed balance and yields positive entropy production.
- No external truth claim is made beyond the pinned discrete setting.

Pinned system (Markov chain)
- State count: N=3
- Transition matrix P_pos (positive control):
  - row0: [0.7, 0.2, 0.1]
  - row1: [0.2, 0.6, 0.2]
  - row2: [0.1, 0.2, 0.7]
- Transition matrix P_neg (negative control):
  - row0: [0.7, 0.25, 0.05]
  - row1: [0.05, 0.7, 0.25]
  - row2: [0.25, 0.05, 0.7]

Pinned diagnostics
- Stationary distribution pi (left eigenvector of P with sum=1)
- Entropy production proxy:
  - sigma = sum_{i,j} pi_i * P_{ij} * log((pi_i * P_{ij}) / (pi_j * P_{ji}))

Pinned pass criteria
- positive control: sigma <= eps_balance
- negative control: sigma >= eps_entropy

Pinned tolerances
- eps_balance=1e-8
- eps_entropy=1e-3

Comparator posture
- expectation-aware pass semantics per case kind
- comparisons are bounded to the pinned discrete report schema

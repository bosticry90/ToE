# CT-05 Representation-Invariant Admissibility Class (v0)

Status: Draft (v0)

Purpose
- Establish that admissible update decisions are representation-invariant under the pinned CT-02/CT-03 mapping and RL11 signal-cone gate.

Statement (bounded internal)
- Under the pinned RL11 signal-cone admissibility criteria and the pinned CT-02/CT-03 update-bound functional, admissibility and bound status agree across the representation map within eps.

Assumptions
- CT-02 and CT-03 pinned artifacts are admissible inputs.
- RL11 pinned signal-cone artifacts are admissible inputs.
- The CT-03 representation map is the pinned variant referenced in CT-03.

Controls (expectation-aware)
- Positive control: CT-02 and CT-03 agree on admissibility and bound status within eps.
- Negative control (rep break): a pinned rep-delta induces a bound-residual mismatch.
- Negative control (admissibility): RL11 inadmissibility is detected under both representations.

Pinned tolerances
- eps_rep_invariant
- eps_bound_residual

Required vocabulary
- CT-05
- representation invariance
- CT-02
- CT-03
- RL11
- positive control
- negative control
- eps_rep_invariant
- eps_bound_residual

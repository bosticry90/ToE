# QUANTUM_FREE_FALL_EQUIVALENCE_COMPARATOR

Status: `EXTERNAL_EMPIRICAL_LOW_ENERGY_RECOVERY_TARGET`.
Implementation: `SPEC_ONLY_NOT_IMPLEMENTED`; verification: `NONE`.
No native recovery has been executed.

## Reuse and source correction

This is a VPC-facing specification for the existing
`QG_QEP_FREE_FALL_PHASE_GOLDEN_CONTROL_v1`, not an additional independent
experiment or a replacement for its four-route contract:

- [Existing phase recovery contract](../../../tooling/scientific_compute/model1_installation_preparation/toe_quantum_free_fall_phase_recovery_contract_v1.json).
- [Existing conditional master-action map](../../../tooling/scientific_compute/model1_installation_preparation/toe_quantum_free_fall_master_action_mapping_v1.json).

Those local files are preserved untouched. Their journal-title field uses an
older preprint title. The 2026 journal title is *Observation of the quantum
phase of free fall and the consistency with the equivalence principle*, DOI
[10.1126/sciadv.aec8045](https://doi.org/10.1126/sciadv.aec8045). The author
manuscript inspected here is [arXiv:2502.14535v4](https://arxiv.org/html/2502.14535v4).
Final publisher full text was not retrieved; equation labels below refer to v4.

## Experimental meaning and timing

The experiment compares supported and ballistic rubidium matter-wave arms.
The ideal relative phase is \(-mg^2T^3/(3\hbar)\), with **total ballistic
duration 2T** (v4 Fig. 1 and Eq. 2). Calling T the total duration causes an
eightfold coefficient error. The roughly 2.5% residual is about 2 radians over
an approximately 80-radian phase span relative to the apparatus simulation
(Fig. 3); it is not a universal bound on quantum-gravity or collapse models.
[Author manuscript](https://arxiv.org/html/2502.14535v4).

The external field is effectively classical and weak. This is neither the
first observation of gravity affecting quantum matter nor a demonstration that
gravity is quantum. Oxford explicitly excludes unification and field-quantization
claims and notes the experiment does not reach the proposed massive-collapse
regime. [Oxford research announcement](https://www.physics.ox.ac.uk/news/scientists-observe-einsteins-gravity-quantum-world).

## Quantum--gravity seam

| Stage | Required derivation | Test object |
| --- | --- | --- |
| QF-0 Native -> effective | Matter dynamics plus weak-background and nonrelativistic limits | Explicit inherited/derived status of inertial mass, gravitational coupling and support interaction |
| QF-1 Apparatus -> trajectories | Piecewise magnetic kicks, holding force and recombination | Common endpoints and momenta; finite pulse and gradient corrections |
| QF-2 Lab -> falling frame | Coordinate change and wavefunction transformation | Derived gauge phase, not an inserted compensating term |
| QF-3 Dynamics -> relative phase | Branch actions or Hamiltonian evolution | Relative phase including support, pulse, internal-state and boundary terms |
| QF-4 Phase -> observable | Recombination and detection model | Same output-port probabilities after declared path/port relabeling |
| QF-5 Prediction -> data | Independent calibration and systematics | Residual vector and covariance under a frozen fit/acceptance rule |

For upward z, the useful ideal transformation is

\[
\psi_N(z,t)=\exp\!\left[-\frac{im}{\hbar}
 (gzt+g^2t^3/6)\right]\psi_E(z+gt^2/2,t).
\]

The absolute gauge phase alone is not the observable. The comparison must
preserve the apparatus and reference arm as well as the coordinate map.

## Proposed VPC roots and attacks

Reuse all four existing routes: action, Hamiltonian, frame transformation and
laboratory potential. Pin atomic state, mass, independent g, timing, magnetic
field geometry, pulse phases, output-port orientation, wave-packet boundary
data, visibility and experimental covariance. The existing generic
`LASER_PHASE...` input must be interpreted via an apparatus audit: this atom-chip
sequence uses microwave/RF and magnetic controls; laser phase is not silently
inserted as a force-generating light-pulse-interferometer model.

Roots: ideal rational phase coefficient; trajectory closure; frame-equivalent
relative phase; corrected predicted population; data residuals. The exact phase
subproblem and the numerical trigonometric probability/data comparison receive
separate evidence classes. No new transcendental operation is silently added
to the exact kernel.

Retain existing attacks and add the factor-eight T-versus-2T mutation, omitted
support phase, common-phase-as-observable, wrong path sign, missing gauge term,
g fit in place of independent calibration, and erased systematic corrections.
All numerical thresholds and data exclusions must be fixed before comparison.

Data acquisition, final-paper/version reconciliation and implementation remain
pending. No gravitational entanglement, collapse exclusion, CCFT/master-action
support, new gravity profile qualification or native-theory promotion follows.

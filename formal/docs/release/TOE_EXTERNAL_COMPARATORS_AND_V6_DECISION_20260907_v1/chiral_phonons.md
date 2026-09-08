# ELECTRICALLY_SWITCHABLE_CHIRAL_PHONON_COMPARATOR

Status: `EMERGENCE_SYMMETRY_ORDER_PARAMETER_CONTROL__NO_NATIVE_AUTHORITY_EFFECT`.
Implementation: `SPEC_ONLY_NOT_IMPLEMENTED`; verification: `NONE`.

## What the source supports

Grimes et al. report electrically reversible circular-dichroic RIXS signatures
in ferroelectric BaTiO3, compared with calculated mode angular momenta. The
inspected manuscript gives C4v/g-type momentum structure and warns that mode
assignment is limited by resolution and an incomplete first-principles
electron--phonon RIXS cross-section. Its momentum table changes in-plane
components while keeping q_z=0.42 inverse angstroms; those measurements are
not literal full-vector q -> -q pairs.
[Author manuscript, Figs. 1, 3--4 and Table 1](https://arxiv.org/html/2603.06144v1).
The publisher lists the final paper as *Electric-field switching of g-wave
phonon chirality in ferroelectric BaTiO3*, 7 September 2026,
[DOI 10.1038/s41563-026-02737-w](https://doi.org/10.1038/s41563-026-02737-w).
[Publisher research listing](https://www.nature.com/subjects/ferroelectrics-and-multiferroics).
Full final text was not retrieved; manuscript details are not assumed identical
to every final-paper figure. Data references supplied by the authors are
[ESRF](https://doi.org/10.15151/ESRF-ES-2166894199) and
[computational archive](https://doi.org/10.5281/zenodo.17899320); not ingested here.

## Interpretation locks

Emergent angular-momentum carriers are physically meaningful; they are not
evidence that elementary particles or spacetime are lattice excitations.
The g-wave label describes momentum-space symmetry, not gravitational waves.
Flipping a polar domain does not restore inversion symmetry or change the
point-group name. Broken inversion permits relevant modes; it does not guarantee
every branch and momentum has nonzero angular momentum.

Distinguish mechanical mode angular momentum J, crystal pseudoangular momentum,
and helicity J dot q (or a specified normalized direction). J is axial and q
polar. Under time reversal, matched nonmagnetic branches relate J(-q) to -J(q);
under inversion of the *whole structure*, axial J does not simply change sign
as a polar vector would. Combining the domain map and time reversal can give
opposite J at fixed q in opposite polar domains. Freeze these maps explicitly;
never conflate them with a sample rotation or a detector-coordinate change.

## Proposed emergence and measurement chain

| Stage | Input -> output | Required evidence / attack |
| --- | --- | --- |
| CP-0 State | Structure, strain, temperature, polar domain -> atomic positions | Check poling/domain fraction and coordinate conventions; reverse domain without moving detector axes |
| CP-1 Microscopic response | Source-bound force constants and masses -> dynamical matrix | Hermiticity, translational sum rule, units and convergence; corrupt one off-diagonal or mass weighting |
| CP-2 Collective modes | Dynamical matrix -> frequencies and eigenvectors | Residual/orthonormality checks; track degeneracies as subspaces, not arbitrary vector labels |
| CP-3 Angular momentum | Complex eigenvectors -> J(q) | Independently compute ionic-motion and mode expressions; reject omitted conjugation or wrong handedness |
| CP-4 Symmetry | Crystal/domain/time-reversal maps -> transformed mode observables | Predict signs, zeros and angular patterns under the actual geometry; global eigenvector phase must not change J |
| CP-5 Measurement | J, matrix elements, polarization transport and resolution -> RIXS contrast | Keep inferred assignment distinct from counts; challenge birefringence/background and unresolved-mode mixing |
| CP-6 Data | Predicted contrast + uncertainty -> measured spectral comparison | Unsmoothed count likelihood, calibration and selection policy; no fitted sign after seeing data |

Start with source-bound force constants and a few predefined q points, not a
claim to have independently reproduced all DFT or the full RIXS cross-section.
Record the DFT functional, pseudopotentials, relaxation, meshes, coordinate
frames, atom order, mass normalization and any nonanalytic correction as inputs.

## Proposed acceptance and limits

Require convergence and two independently coded mode-to-J routes; global-phase
invariance; degenerate-subspace handling; declared polarization and momentum
transformations; symmetry-allowed zeros; and a linearly polarized mode control.
A degenerate eigenvector chosen by a solver cannot define unique chirality
without a state/occupation or subspace prescription.

Do not set RIXS contrast equal to J dot q by definition. Preserve the response
model, unknown matrix elements, instrument convolution, birefringence and
finite-resolution uncertainty. An exact symmetry identity may have an exact
certificate while eigenmodes and spectral fits remain numerical and the
measurement inference remains conditional. This is not a rigorous enclosure
unless a containment certificate actually exists.

The benchmark needs local source/data custody, mode matching, numerical and
statistical thresholds, and reviewed operation semantics before execution.
No ether, CCFT, master-action, gravity, SU(5), Route-C or production claim is
promoted. Device proposals and fundamental-ontology analogies are not results
of this proposed benchmark.

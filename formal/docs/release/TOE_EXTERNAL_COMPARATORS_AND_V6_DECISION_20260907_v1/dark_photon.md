# NONLINEAR_PLASMA_DARK_PHOTON_CONSTRAINT_COMPARATOR

Status: `EXTERNAL_COMPARATOR__NO_NATIVE_AUTHORITY_EFFECT`.
Implementation: `SPEC_ONLY_NOT_IMPLEMENTED`; verification: `NONE`.

## Source finding and correction

Hook, Huang and Shalaby report that nonlinear plasma response limits resonant
dark-photon energy deposition. Their PIC work links strong Langmuir excitation
to density/plasma-frequency structure that disrupts continued resonance. The
PRL abstract reports constraint weakening by 3,000--10^7 across ten mass decades.
This addresses an early-universe resonant-conversion exclusion mechanism, not a
dark-photon detection or a repeal of all dark-sector constraints.
[PRL, published 13 August 2026](https://journals.aps.org/prl/abstract/10.1103/98cx-7t43).

The inspected author manuscript introduction gives approximately 10^-14--10^-4
eV, unlike the pasted 10^-15--10^-6 eV. The abstract does not settle the endpoint
discrepancy. Its perturbative diagnostic is the quiver-to-thermal-speed ratio
approaching unity. Numerical mass ranges, exclusion ordinates and applicability
must be reconciled to a pinned final paper/figure before benchmark execution.
[Author manuscript, introduction and Eq. 3](https://arxiv.org/html/2510.13956v1).
The weakening factor must not be relabeled as an energy-deposition ratio or an
experimental sensitivity gain without the corresponding calculation.

## Proposed bounded benchmark

First benchmark: one source-pinned plasma initial condition with a low-drive
linear control and a nonlinear run. Do not initially reproduce an entire
cosmological exclusion plot. Fix dark-photon mass, kinetic mixing, abundance,
electron/ion distributions, density, temperatures, boundary conditions,
expansion approximation, forcing convention, collision/damping model, mesh,
time step, particles per cell and random/input-set identity before comparing.

The diagnostic \(\eta=v_q/v_{\rm th,e}\) is a dimensionless regime indicator,
not a universal hard threshold or a proof of nonlinear validity. A review must
justify the selected threshold and quantify proximity to the model's limits.

## Microscopic-to-observable seam

| Stage | Scientific input -> output | Applicability obligation and adversarial control |
| --- | --- | --- |
| DP-0 Microscopic interaction | Kinetic mixing and abundance -> plasma driving term | Preserve sign, normalization, units and assumed dark-matter fraction; zero-mixing control |
| DP-1 Resonance | Local density and dispersion -> detuning | Distinguish plasma frequency from mass/energy using explicit units; perturb density and require detuning response |
| DP-2 Linear response | Weak drive and background -> early energy transfer | Record eta and neglected terms; reject extrapolation after the predeclared validity condition fails |
| DP-3 Collective feedback | Evolving fields/distributions -> density structure and saturation | Enforce energy accounting and convergence; disable backreaction as an explicitly different-model control |
| DP-4 Thermalization | Transfer and damping -> deposited heat versus time | Wave energy is not automatically thermal energy; account for ions, electrons, losses and expansion |
| DP-5 Cosmology | Heating history -> observable distortion/ionization | Freeze thermal-history and observation models; no extrapolation to compact-object magnetospheres by analogy |
| DP-6 Conditional exclusion | Observable, data and likelihood -> constraint | Store dataset, nuisance priors, confidence convention and invalidating assumptions; no unconditional excluded/allowed label |

Feedback returns from DP-3 to DP-1/DP-2 through the local density. Encoding only
a one-way rate integration would omit the hypothesis being tested.

## Future acceptance

Require zero-drive energy control; low-amplitude agreement with the analytic
linear solution; converged energy budgets and detuning histories; mesh/time-step/
particle-number and box-size controls; an independent numerical route with
documented differences; and preserved negative-control outcomes. Verify that
freezing the density or removing an ion response is labeled a changed model,
not hidden behind the same request identity.

Proposed outputs: regime diagnostics, transferred/deposited energy histories,
saturation comparison, conservation residuals, and (only in a later stage)
the conditional exclusion. Applicability dispositions are **profile-level
proposals**, not new global VPC statuses: `WITHIN_DECLARED_REGIME`,
`OUTSIDE_DECLARED_REGIME`, `REGIME_UNRESOLVED`.

PIC/ODE solver agreement is numerical evidence, not `VERIFIED_ENCLOSURE`.
An exact linear-model calculation remains exact for that model even when its
use as a nonlinear physical prediction is rejected. Keep arithmetic uncertainty,
discretization error, stochastic error and physical-model discrepancy separate.

Missing before execution: local final-paper/supplement custody, numerical input
and simulation-data locators, independent-route specification, convergence
thresholds and any observational likelihood. No simulation, exclusion scan,
dark-photon monitoring, native dark-sector selection or current v6 change occurs.

=====================================================================

ANCHOR\_BEC\_GP.md

=====================================================================



SCOPE AND PURPOSE

This note records an external anchoring candidate for the CP-NLSE / CRFT

core equation family by mapping it to the Gross–Pitaevskii equation (GPE)

used for dilute-gas Bose–Einstein condensates (BECs).



This note does NOT claim empirical confirmation.

It records only the formal correspondence, derived observables, and

requirements for any future status upgrade.



TARGET EXTERNAL THEORY (BEC MEAN-FIELD)

Gross–Pitaevskii equation (GPE), uniform V=0 case:

&nbsp; iħ ∂t Ψ = \[-(ħ^2/2m) ∇^2 + g\_BEC |Ψ|^2] Ψ

with

&nbsp; g\_BEC = 4π ħ^2 a\_s / m

(a\_s is the s-wave scattering length; m is atomic mass).



FORMAL CORRESPONDENCE (DIMENSIONLESS MATCH)

Under standard nondimensionalization, the GPE reduces to an NLSE of the form:

&nbsp; i ∂t ψ = -(1/2) ∇^2 ψ + g (|ψ|^2 - ρ0) ψ

which matches the operational CP-NLSE used in this repository

(up to choice of ρ0 normalization and additive chemical-potential gauge).



DERIVED BEC OBSERVABLES (INTERNAL, NOT EMPIRICAL CLAIMS)

For uniform background density ρ0, linearization yields Bogoliubov dispersion:

&nbsp; ω^2(k) = (1/4) k^4 + (g ρ0) k^2

Define sound speed: c\_s^2 = g ρ0

Then: ω^2(k) = c\_s^2 k^2 + (1/4) k^4



Corresponding derived scales:

&nbsp; healing length: ξ = 1 / sqrt(2 g ρ0)

&nbsp; phonon regime: k ξ << 1  => ω ≈ c\_s k

&nbsp; particle regime: k ξ >> 1 => ω ≈ (1/2) k^2



REPOSITORY ITEMS THIS ANCHOR RELATES TO

\- EQ-01 (CP-NLSE base)

\- EQ-02 (CP-NLSE linearized)

\- DR-01 (linear Schrödinger dispersion)

This note does not alter their internal statuses.



EXTERNAL EVIDENCE REQUIRED FOR STATUS UPGRADE

To assign Derived-from-Established-Physics:

\- Provide a written derivation showing reduction from GPE to CP-NLSE form

&nbsp; and explicit parameter identification (ψ, g, ρ0).

\- Cite authoritative external sources for GPE form and g\_BEC.



To assign Empirically Anchored:

\- Select a specific experimental system and dataset.

\- Compute predicted c\_s, ξ, and/or Bogoliubov ω(k) using reported a\_s, n0, m.

\- Compare against measured values with uncertainty.



CITATION PLACEHOLDERS

\- GPE form and g\_BEC definition

\- Bogoliubov dispersion relation for BEC excitations



END ANCHOR\_BEC\_GP.md

=====================================================================




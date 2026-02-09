TITLE: Physical Anchor — BEC Bogoliubov Dispersion via Bragg Spectroscopy (External)



SCOPE

This note establishes an external physics anchor for the dispersion concept used in ToE/CRFT by mapping the CP–NLSE/GPE linearized excitation spectrum to the experimentally measured Bogoliubov dispersion in dilute alkali Bose–Einstein condensates (BECs).



ANCHOR CLAIM (EXTERNAL)

In dilute weakly interacting Bose gases, the Gross–Pitaevskii equation (GPE) predicts the Bogoliubov excitation spectrum:

ω(k) = sqrt( (μ/m) k^2 + (ħ k^2 / (2m))^2 )

equivalently:

(ħ ω)^2 = ε\_k (ε\_k + 2μ), ε\_k = ħ^2 k^2 / (2m)



EXTERNAL EVIDENCE TARGET (CANONICAL DATASET)

Steinhauer et al., “The Excitation Spectrum of a Bose–Einstein Condensate” (2001) reports a direct two-photon Bragg spectroscopy measurement of ω(k) and quantitative agreement with Bogoliubov theory using measured parameters (notably μ/h ≈ 1.91 ± 0.09 kHz). (arXiv:cond-mat/0111438)



RELATION TO TOE/CRFT ARTIFACTS



LOCK\_CP\_NLSE\_2D\_DISPERSION.md locks the free-particle linear Schrödinger limit (g=0), giving ω = k^2/2 in dimensionless form.



For BEC anchoring, the next required internal lock is the linearization of the CP–NLSE/GPE about ψ = sqrt(ρ0) for g ≠ 0, yielding the Bogoliubov dispersion in ToE units:

ω^2 = (k^2/2) (k^2/2 + 2 g ρ0)

with sound speed c\_s^2 = g ρ0.



EPISTEMIC STATUS IMPLICATION



DR-01 remains Locked (internal).



A new entry (or upgraded entry) may be assigned Derived-from-Established-Physics only after the ToE-side derivation and validation reproduces the Bogoliubov form from the CP–NLSE/GPE linearization.



Empirically Anchored requires quantitative agreement against the Steinhauer ω(k) dataset (or another specified Bragg dataset) within uncertainties, recorded as an external evidence packet.



END


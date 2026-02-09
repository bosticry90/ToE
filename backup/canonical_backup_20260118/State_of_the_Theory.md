STATE OF THE THEORY

Project: ToE

Purpose: Epistemic inventory and stabilization

Last updated: 2026-01-17





HOW TO READ THIS DOCUMENT



This file is the single source of truth for the epistemic status of all major theory components.



This file does NOT:



Argue correctness

Prove results

Justify interpretation



This file ONLY records:



What exists

What it claims

How confident we are

Why that confidence level is assigned



If an item is unclear, it is marked Hypothesis by default.





STATUS LEGEND (CANONICAL)



Use ONLY the following status labels.



Locked

Behavior validated and structure formalized.



Structural (Lean)

Formally consistent definitions or identities. No behavioral claim.



Behavioral (Python)

Numerically observed behavior. No structural guarantee.



Spec-backed

Assumed bridge or interpretation. Explicitly labeled.



Hypothesis

Proposed but not validated or formalized.



Deprecated

Superseded, unused, or intentionally abandoned.



Empirically Anchored

Matched to peer-reviewed experimental data with quantitative agreement.

Evidence must cite external experiments.



Derived-from-Established-Physics

Formally derived as a limit, reduction, or reformulation of an accepted

physical theory (e.g., GrossPitaevskii, Maxwell, NavierStokes).



Open-to-Test

Physically interpretable with clearly defined observables, but not yet

tested or matched to data.



Experimentally Refuted

Shown to disagree with experiment in its claimed domain.



These statuses may only be assigned in State\_of\_the\_Theory.md and must cite evidence external to the repository.





GLOBAL CONSTRAINTS



No item may appear in Lean unless it appears in this file.

No item may be upgraded in status without updating this file.

All Markdown claims must reference an item defined here.



External epistemic statuses record correspondence to physical reality.

They are never established by Markdown, Python, or Lean artifacts and must

be supported by evidence outside this repository.



Canonical inventory IDs (e.g., CT-01, DR-01) may not be reused as IDs for

evidence sections. Evidence blocks must use derived IDs (e.g., CT-01-EVIDENCE-\*).



Dependencies field MUST reference only inventory IDs (or None). No free text or external references.

Evidence field may contain (a) derived evidence-block IDs or (b) repository file paths.



Evidence blocks are bookkeeping artifacts, not claims.

For evidence blocks, Status indicates artifact modality (e.g., Behavioral (Python), Structural (Lean), Deprecated) and does not assert any external epistemic status.

External epistemic statuses (e.g., Empirically Anchored) apply only to inventory claim items, not to evidence blocks.





INVENTORY ENTRY FORMAT (CANONICAL)



Each epistemic object MUST be recorded using the following format.

Do not deviate.



ID:

Name:

Category:

Short description:

Status:

Evidence:

Scope / limits:

Dependencies:

Notes:

External anchor:

External evidence:





INVENTORY





4.1 CORE DYNAMICAL EQUATIONS





ID: EQ-01

Name: CP-NLSE (base)

Category: Equation

Short description: Core nonlinear wave equation

Status: Behavioral (Python)

Evidence: formal/python/crft/cp\_nlse\_2d.py; formal/python/crft/tests/test\_c6\_cp\_nlse\_2d\_dispersion.py

Scope / limits: Weakly nonlinear regime

Dependencies: None

Notes: Linearization used for dispersion analysis

External anchor: None

External evidence: None





ID: EQ-02

Name: CP-NLSE (linearized)

Category: Equation
Short description: Small-amplitude limit of CP-NLSE
Status: Locked

Evidence: formal/toe\_formal/ToeFormal/CPNLSE2D/LinearizedEquation.lean; formal/python/tests/test\_dr01\_eq02\_dispersion.py; EQ-02-EVIDENCE-LEAN-BUILD

Scope / limits: small-amplitude (linearized) regime about ψ=0

Dependencies: EQ-01

Notes: Lean evidence is restricted to a dedicated EQ-02 definition module (LinearizedEquation.lean). Plane-wave reductions live under OP-PW-\*.

External anchor: None

External evidence: None



ID: EQ-02-EVIDENCE-LEAN-BUILD

Name: EQ-02 Lean build target (bookkeeping)

Category: Evidence block

Short description: Bookkeeping record of the intended Lean module build target for EQ-02.

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/CPNLSE2D/LinearizedEquation.lean

Scope / limits: Records build-target intent only; does not include build logs.

Dependencies: None

Notes: Intended build target: ToeFormal.CPNLSE2D.LinearizedEquation.

External anchor: None

External evidence: None





4.2 DISPERSION RELATIONS





ID: DR-01

Name: CP-NLSE dispersion

Category: Dispersion relation

Short description: Omega(k) relation for linearized CP-NLSE

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/Derivation/DR01\_Redundant.lean; formal/python/tests/test\_dr01\_eq02\_dispersion.py

Scope / limits: Linearization about ψ=0 (vacuum/small-amplitude limit); does not encode finite-density phonon slope; A3 operator reductions rely on explicit axioms Dt\_planeWave and Delta\_planeWave; no Mathlib-analytic derivative proof is present.

Dependencies: EQ-02, OP-PW-01, OP-PW-02, OP-PW-03

Notes: Reduction is conditional on Dt\_planeWave / Delta\_planeWave axioms (quarantined in OP-PW-02). Plane-wave reduction scaffolding is tracked under OP-PW-\* (e.g., OP-PW-03) to keep EQ-02 definition evidence separate from operator reduction evidence.

External anchor: None

External evidence: None



ID: DR-01a

Name: DR-01 fit artifact is provenance-stamped (data-backed)

Category: Evidence block

Short description: Defines a minimal DR-01 fit artifact type that carries deterministic provenance fields and a content-based data fingerprint (sha256 of a canonical (k, ω) sample encoding). This prevents “anonymous” fits from being used in downstream bridge locks.

Status: Behavioral (Python)

Evidence: formal/python/toe/dr01_fit.py; formal/python/tests/test_dr01_fit_artifact_provenance.py

Scope / limits: Provenance and hashing contract only; does not assert the fit is empirically anchored to any external dataset.

Dependencies: DR-01

Notes: `data_fingerprint` is computed from `sample_kw` using sorted-by-k fixed-format encoding; library code does not read CSV files.

External anchor: None

External evidence: None



ID: DR-01b

Name: DR-01 curved fit artifact is provenance-stamped (data-backed)

Category: Evidence block

Short description: Defines a second, deterministic DR fit artifact type (`DR01FitCurved1D`) for curvature-aware low-k modeling using the proxy fit ω/k = c0 + βk², preserving provenance fields and `data_fingerprint` discipline and enabling lockable fit-quality metadata in y=ω/k space.

Status: Behavioral (Python)

Evidence: formal/python/toe/dr01_fit_curved.py; formal/python/toe/dr01_fit_quality.py

Scope / limits: Fit-object contract and deterministic fitter only; does not by itself freeze new external-evidence JSON artifacts.

Dependencies: DR-01

Notes: Designed to test whether strict through-origin linearization is too rigid in low-k windows.

External anchor: None

External evidence: None





ID: DR-02

Name: Bogoliubov/LDA dispersion (Steinhauer Fig. 3a)

Category: Dispersion relation

Short description: LDA Bogoliubov excitation dispersion evaluated using μ/h = 1.91 kHz from paper and compared to digitized Fig. 3a points.

Status: Empirically Anchored

Evidence: DR-02-EVIDENCE-DIGITIZATION; formal/external\_evidence/bec\_bragg\_steinhauer\_2001/0111438v1.pdf

Scope / limits: Finite-density trapped BEC excitation regime; LDA/trap-averaging built in; uses σ proxies derived from reported broadening scales; not the paper’s pointwise experimental uncertainties

Dependencies: None

Notes: Derived-from-Established-Physics (Bogoliubov + LDA) used as the model form for the empirical anchor; anchoring is to Steinhauer Fig. 3a under stated σ proxies. χ² is diagnostic only under the σ proxy derived from reported broadening scales; not a definitive goodness-of-fit without pointwise experimental uncertainties.

External anchor: Bragg spectroscopy of ⁸⁷Rb BEC

External evidence: Steinhauer PRL 88, 120407 (2002), Fig. 3a





ID: DR-02-EVIDENCE-DIGITIZATION

Name: Steinhauer Fig. 3a digitization and Bogoliubov/LDA evaluation trace

Category: Evidence block

Short description: Internal reconstruction artifacts and outputs supporting DR-02 empirical anchor.

Status: Behavioral (Python)

Evidence: formal/external\_evidence/bec\_bragg\_steinhauer\_2001/omega\_k\_data.csv; formal/external\_evidence/bec\_bragg\_steinhauer\_2001/extracted\_params.md; formal/external\_evidence/bec\_bragg\_steinhauer\_2001/compare\_omega\_k.py; formal/external\_evidence/bec\_bragg\_steinhauer\_2001/comparison\_results.csv; formal/external\_evidence/bec\_bragg\_steinhauer\_2001/comparison\_plot.png; formal/external\_evidence/bec\_bragg\_steinhauer\_2001/evidence\_summary.txt; formal/external\_evidence/bec\_bragg\_steinhauer\_2001/0111438v1.pdf

Scope / limits: Digitization + parameter-fixed evaluation only; σ proxies used; no pointwise experimental uncertainties; digitization uncertainty not independently quantified.

Dependencies: None

Notes: Supports DR-02 empirical anchor; internal reconstruction artifact set. Empirically Anchored status applies to DR-02 only; this evidence block remains Behavioral (Python). χ² is diagnostic under σ proxy; no definitive goodness-of-fit claim.

External anchor: Bragg spectroscopy of ⁸⁷Rb BEC excitations

External evidence: Steinhauer PRL 88, 120407 (2002), Fig. 3a



ID: DR-04a

Name: DR-04 fit artifact (third low-k window from Steinhauer Fig. 3a)

Category: Evidence block

Short description: Freezes a third `DR01Fit1D`-compatible linearization derived from the same DR-02 digitized Steinhauer Fig. 3a dataset, using a deliberately tighter low-k window choice, with provenance fields and a content-based data fingerprint.

Status: Behavioral (Python)

Evidence: formal/external_evidence/bec_bragg_steinhauer_2001/dr04_fit_artifact.json; formal/external_evidence/bec_bragg_steinhauer_2001/dr04_fit_artifact.md; formal/python/toe/dr01_fit.py

Scope / limits: Encodes one alternate window rule (k <= 1.6 um^-1, through-origin) and fixes u = 0 because the source dataset contains only k > 0 points; does not claim uniqueness or optimality.

Dependencies: DR-01, DR-02

Notes: This is an intentionally different “fit choice” intended for multi-fit robustness bookkeeping; no claim is made that it is more correct than DR-02a or DR-03a.

External anchor: Bragg spectroscopy of ⁸⁷Rb BEC excitations

External evidence: Steinhauer PRL 88, 120407 (2002), Fig. 3a



ID: DR-04c

Name: DR-04c fit artifact (upgraded window from Steinhauer Fig. 3a; N≥5)

Category: Evidence block

Short description: Freezes an additional `DR01Fit1D`-compatible linearization derived from the same DR-02 digitized Steinhauer Fig. 3a dataset, using a k-max choice that yields N≥5 (k <= 2.5 um^-1). Intended to replace DR-04a (k <= 1.6, N=4) in decision-grade 4-window robustness loops that require strict curved-fit adequacy.

Status: Behavioral (Python)

Evidence: formal/external_evidence/bec_bragg_steinhauer_2001/dr04c_fit_artifact.json; formal/external_evidence/bec_bragg_steinhauer_2001/dr04c_fit_artifact.md; formal/python/toe/dr01_fit.py; formal/python/toe/dr01_fit_quality.py

Scope / limits: Encodes one alternate window rule (k <= 2.5 um^-1, through-origin) and fixes u = 0 because the source dataset contains only k > 0 points; does not claim uniqueness or optimality.

Dependencies: DR-01, DR-02

Notes: Introduced to eliminate reliance on the DQ-01_v2 low-N exception in fit-family selection, while retaining a 4-window set.

External anchor: Bragg spectroscopy of ⁸⁷Rb BEC excitations

External evidence: Steinhauer PRL 88, 120407 (2002), Fig. 3a



ID: DR-04b

Name: DR fit-quality diagnostics (DR-02a vs DR-03a vs DR-04a)

Category: Evidence block

Short description: Adds minimal deterministic fit-quality instrumentation (N_points, RMSE, slope stderr, R^2 through-origin) for the frozen DR-01 low-k linearization artifacts and compares DR-02a/DR-03a/DR-04a to separate methodological undersampling effects from true fit-window sensitivity.

Status: Behavioral (Python)

Evidence: formal/python/toe/dr01_fit_quality.py; formal/python/tests/test_dr_fit_quality_present_and_reasonable.py; formal/markdown/locks/bridges/DR_fit_quality_comparison_DR02_DR03_DR04.md

Scope / limits: Diagnostics are for the forced through-origin model omega ~= c_s*k using each artifact’s frozen `sample_kw`; they do not establish external error models or absolute goodness-of-fit.

Dependencies: DR-02a, DR-03a, DR-04a

Notes: This resolves ambiguity in interpreting multi-fit drift gates by making fit-quality visible and lockable.

External anchor: None

External evidence: None



ID: DR-05a

Name: DR-05 fit artifact (intermediate low-k window from Steinhauer Fig. 3a)

Category: Evidence block

Short description: Freezes a fourth `DR01Fit1D`-compatible linearization derived from the same DR-02 digitized Steinhauer Fig. 3a dataset, using an intermediate low-k window (k <= 1.8 um^-1) intended to distinguish monotone drift vs isolated-window outliers. Includes deterministic fit-quality instrumentation and a content-based data fingerprint.

Status: Behavioral (Python)

Evidence: formal/external_evidence/bec_bragg_steinhauer_2001/dr05_fit_artifact.json; formal/external_evidence/bec_bragg_steinhauer_2001/dr05_fit_artifact.md; formal/python/toe/dr01_fit.py; formal/python/toe/dr01_fit_quality.py

Scope / limits: Encodes one alternate window rule (k <= 1.8 um^-1, through-origin) and fixes u = 0 because the source dataset contains only k > 0 points; does not claim uniqueness or optimality.

Dependencies: DR-01, DR-02, DR-04b

Notes: This is an intentionally different “fit choice” intended for monotonicity diagnosis over k-max.

External anchor: Bragg spectroscopy of ⁸⁷Rb BEC excitations

External evidence: Steinhauer PRL 88, 120407 (2002), Fig. 3a



ID: DR-05b

Name: DR fit-quality diagnostics (DR-02a vs DR-03a vs DR-04a vs DR-05a)

Category: Evidence block

Short description: Extends the DR-04b fit-quality comparison by adding the intermediate-window DR-05a artifact to enable monotonicity/outlier diagnosis over k-max.

Status: Behavioral (Python)

Evidence: formal/markdown/locks/bridges/DR_fit_quality_comparison_DR02_DR03_DR04_DR05.md

Scope / limits: Evidence-only table/interpretation; does not establish an external noise model.

Dependencies: DR-05a

Notes: See also the corresponding BR-01 metric comparison extended to DR-05.

External anchor: None

External evidence: None



ID: DR-06a

Name: Curvature-aware DR fit artifacts (DR-02a/DR-03a/DR-04a/DR-05a curved)

Category: Evidence block

Short description: Freezes four curvature-aware DR fit artifacts for the same Steinhauer Fig. 3a digitized samples as DR-02a/03a/04a/05a by fitting ω/k = c0 + βk² on each window’s frozen `sample_kw`. Includes deterministic fit-quality diagnostics in y-space and the derived BR-01 metric fields (unit-density gauge using c0 as c_s(k→0)).

Status: Behavioral (Python)

Evidence: formal/external_evidence/bec_bragg_steinhauer_2001/dr01_fit_artifact_curved.json; formal/external_evidence/bec_bragg_steinhauer_2001/dr01_fit_artifact_curved.md; formal/external_evidence/bec_bragg_steinhauer_2001/dr03_fit_artifact_curved.json; formal/external_evidence/bec_bragg_steinhauer_2001/dr03_fit_artifact_curved.md; formal/external_evidence/bec_bragg_steinhauer_2001/dr04_fit_artifact_curved.json; formal/external_evidence/bec_bragg_steinhauer_2001/dr04_fit_artifact_curved.md; formal/external_evidence/bec_bragg_steinhauer_2001/dr05_fit_artifact_curved.json; formal/external_evidence/bec_bragg_steinhauer_2001/dr05_fit_artifact_curved.md

Scope / limits: Minimal proxy model upgrade only; does not assert a best-fit external physics model.

Dependencies: DR-01b, DR-02a, DR-03a, DR-04a, DR-05a, BR-01

Notes: Intended as the canonical frozen input set for curved BR/OV robustness scans.

External anchor: Bragg spectroscopy of ⁸⁷Rb BEC excitations

External evidence: Steinhauer PRL 88, 120407 (2002), Fig. 3a



ID: DR-06c

Name: Curvature-aware DR fit artifact (DR-04c curved)

Category: Evidence block

Short description: Freezes a curvature-aware DR fit artifact for the DR-04c window sample by fitting ω/k = c0 + βk² on the frozen `sample_kw`. Includes deterministic fit-quality diagnostics in y-space and the derived BR-01 metric fields (unit-density gauge using c0 as c_s(k→0)).

Status: Behavioral (Python)

Evidence: formal/external_evidence/bec_bragg_steinhauer_2001/dr04c_fit_artifact_curved.json; formal/external_evidence/bec_bragg_steinhauer_2001/dr04c_fit_artifact_curved.md; formal/python/toe/dr01_fit_curved.py; formal/python/toe/dr01_fit_quality.py

Scope / limits: Minimal proxy model upgrade only; does not assert a best-fit external physics model.

Dependencies: DR-01b, DR-04c, BR-01

Notes: This is the curved companion artifact enabling strict DQ-01_v1 adequacy across the 4-window set used by OV-01g/POL-01.

External anchor: Bragg spectroscopy of ⁸⁷Rb BEC excitations

External evidence: Steinhauer PRL 88, 120407 (2002), Fig. 3a



ID: DR-06b

Name: DR fit-quality diagnostics (curved proxy; DR-02a vs DR-03a vs DR-04a vs DR-05a)

Category: Evidence block

Short description: Curvature-aware fit-quality comparison for the four DR window choices, computed deterministically in y=ω/k space (RMSE(y), stderr(c0), stderr(β), R²(y)). Intended to separate model-form effects from sampling/conditioning effects.

Status: Behavioral (Python)

Evidence: formal/markdown/locks/bridges/DR_fit_quality_comparison_curved_DR02_DR03_DR04_DR05.md; formal/python/toe/dr01_fit_quality.py; formal/python/toe/dr01_fit_curved.py

Scope / limits: Diagnostic bookkeeping only; R² in y-space can be numerically small when y variation is tiny relative to its mean.

Dependencies: DR-01b, DR-02a, DR-03a, DR-04a, DR-05a

Notes: Curved window artifacts are frozen under DR-06a; this report summarizes their fit-quality diagnostics.

External anchor: None

External evidence: None



ID: DQ-01

Name: DQ-01 curved-fit adequacy gate (DR-01 curved artifacts)

Category: Evidence block

Short description: Defines a deterministic adequacy gate for curvature-aware DR-01 fit artifacts (`DR01FitCurved1D`). Checks N, RMSE(ω/k), stderr(c0), and a conservative β identifiability condition (β SNR or small β stderr). Intentionally does not use R²(y) as a required check.

Status: Behavioral (Python)

Evidence: formal/python/toe/dr01_fit_adequacy.py; formal/python/tests/test_dr01_fit_adequacy_curved_gate.py

Scope / limits: Adequacy is a workflow gate (data-support check), not a claim that the curved proxy is the correct physical model. Thresholds are provisional and should be tightened as additional evidence accumulates.

Dependencies: DR-01b, DR-06a, DR-06c

Notes: Designed to prevent POL-01 from operationalizing “curved” when curvature inference is underpowered in a given window.

External anchor: None

External evidence: None



ID: DQ-01a

Name: DQ-01 curved-fit adequacy table (DR-02/03/04/05 curved)

Category: Evidence block

Short description: Evidence-only table applying DQ-01 adequacy checks to the four frozen curved window artifacts corresponding to DR-02a/03a/04a/05a. Records N, RMSE(ω/k), stderr(c0), β, β_stderr, β_snr, pass/fail, and reason codes.

Status: Evidence (Markdown)

Evidence: formal/markdown/locks/bridges/DR_fit_adequacy_curved_DR02_DR03_DR04_DR05.md

Scope / limits: Uses only the frozen curved artifacts’ stamped diagnostics; does not introduce new fitting.

Dependencies: DQ-01, DR-06a

Notes: Under default thresholds, DR-04 curved fails due to N=4 and β identifiability.

External anchor: None

External evidence: None



ID: DQ-01c

Name: DQ-01 curved-fit adequacy table (DR-02/03/04c/05 curved)

Category: Evidence block

Short description: Evidence-only table applying DQ-01 adequacy checks (DQ-01_v1 strict) to the upgraded 4-window curved artifact set that replaces DR-04a (N=4) with DR-04c (N=7). Records N, RMSE(ω/k), stderr(c0), β, β_stderr, β_snr, pass/fail, and reason codes.

Status: Evidence (Markdown)

Evidence: formal/markdown/locks/bridges/DR_fit_adequacy_curved_DR02_DR03_DR04c_DR05.md

Scope / limits: Uses only the frozen curved artifacts’ stamped diagnostics; does not introduce new fitting.

Dependencies: DQ-01, DR-06a, DR-06c

Notes: Under default strict thresholds, all four windows pass; DQ-01_v2 is no longer required for fit-family selection on this set.

External anchor: None

External evidence: None



ID: DQ-01b

Name: DQ-01 policy comparison table (v1 vs v2; DR-02/03/04/05 curved)

Category: Evidence block

Short description: Evidence-only delta report comparing DQ-01 curved-fit adequacy pass/fail and reason codes under DQ-01_v1 (strict) vs DQ-01_v2 (tiered low-N admissibility with β ignored) for the frozen DR-02/03/04/05 curved artifacts.

Status: Evidence (Markdown)

Evidence: formal/markdown/locks/bridges/DR_fit_adequacy_curved_policy_comparison_v1_v2_DR02_DR03_DR04_DR05.md

Scope / limits: Comparison uses the same frozen curved artifacts and the same adequacy reporting surface; only the policy parameter differs.

Dependencies: DQ-01, DQ-01a

Notes: Under DQ-01_v2, DR-04 curved becomes admissible as low-N with β ignored for inference.

External anchor: None

External evidence: None



ID: DQ-01v2

Name: DQ-01_v2 tiered curved-fit adequacy policy (N=4 conditional)

Category: Policy

Short description: Tiered variant of DQ-01 that preserves strict defaults (N>=5) but allows N==4 conditional admissibility under stricter RMSE and stderr(c0) thresholds and explicitly ignores β identifiability at low N (records `beta_ignored_low_n`).

Status: Behavioral (Python)

Evidence: formal/python/toe/dr01_fit_adequacy.py; formal/python/tests/test_dr01_fit_adequacy_curved_gate.py; formal/markdown/locks/bridges/DR_fit_adequacy_curved_policy_comparison_v1_v2_DR02_DR03_DR04_DR05.md

Scope / limits: Operational workflow policy only; the low-N exception is meant to be temporary until a higher-N smallest-window artifact is generated.

Dependencies: DQ-01b

Notes: Retained for auditability/back-compat; no longer required for live fit-family selection once the DR-04c upgraded window set is used.

External anchor: None

External evidence: None



ID: DR-02a

Name: Canonical DR-01 fit artifact (low-k linearization from DR-02)

Category: Evidence block

Short description: Freezes a canonical `DR01Fit1D`-compatible linearization derived from the DR-02 digitized Steinhauer Fig. 3a dataset using a deterministic low-k window and a data-backed provenance hash. Intended as a stable input artifact for downstream bridge runs (e.g., BR-01 → MT-01) during the discriminative science phase.

Status: Behavioral (Python)

Evidence: formal/external_evidence/bec_bragg_steinhauer_2001/dr01_fit_artifact.json; formal/external_evidence/bec_bragg_steinhauer_2001/dr01_fit_artifact.md; formal/python/toe/dr01_fit.py

Scope / limits: Encodes one specific low-k linearization rule (k <= 3.2 um^-1, through-origin) and fixes u = 0 because the source dataset contains only k > 0 points; does not claim uniqueness or optimality.

Dependencies: DR-01, DR-02

Notes: The artifact carries a content-based `data_fingerprint` (sha256) computed from the canonical (k, omega) sample encoding; no library code reads CSV files.

External anchor: Bragg spectroscopy of ⁸⁷Rb BEC excitations

External evidence: Steinhauer PRL 88, 120407 (2002), Fig. 3a



ID: DR-03a

Name: DR-03 fit artifact (alternate low-k window from Steinhauer Fig. 3a)

Category: Evidence block

Short description: Freezes a second `DR01Fit1D`-compatible linearization derived from the same DR-02 digitized Steinhauer Fig. 3a dataset, using a deliberately different low-k window choice, with provenance fields and a content-based data fingerprint.

Status: Behavioral (Python)

Evidence: formal/external_evidence/bec_bragg_steinhauer_2001/dr03_fit_artifact.json; formal/external_evidence/bec_bragg_steinhauer_2001/dr03_fit_artifact.md; formal/python/toe/dr01_fit.py

Scope / limits: Encodes one alternate window rule (k <= 2.1 um^-1, through-origin) and fixes u = 0 because the source dataset contains only k > 0 points; does not claim uniqueness or optimality.

Dependencies: DR-01, DR-02

Notes: This is an intentionally different “fit choice” intended for cross-fit sensitivity bookkeeping; no claim is made that it is more correct than DR-02a.

External anchor: Bragg spectroscopy of ⁸⁷Rb BEC excitations

External evidence: Steinhauer PRL 88, 120407 (2002), Fig. 3a





4.3 FUNCTIONALS





ID: FN-01

Name: Admissible deformation class P\[ψ] (candidate family)

Category: Functional / Deformation class

Short description: Family of candidate nonlinear deformation terms gated by CT-01 and source-free admissibility

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/Constraints/FN01\_CausalityCoreConsumer.lean; formal/toe\_formal/ToeFormal/Constraints/FN01\_CausalityCoreBridge.lean; formal/toe\_formal/ToeFormal/Constraints/FN01\_DeformationClass.lean; formal/toe\_formal/ToeFormal/Constraints/FN01\_CandidateMembership.lean; formal/toe\_formal/ToeFormal/Constraints/FN01\_CandidateAPI.lean; formal/markdown/locks/functionals/FN-01\_deformation\_class.md; formal/python/tests/test\_fn01\_candidate\_table.py; formal/python/tests/test\_fn01\_near\_plane\_wave\_regression.py; formal/python/tests/test\_fn01\_candidate\_api\_enforced.py; CT-01-EVIDENCE-PHB; CT-01-EVIDENCE-SOLVER-OMEGA

Scope / limits: Organizational pruning framework for candidate deformations under CT-01 + source-free admissibility; probe-relative only.

Dependencies: EQ-01, CT-01, SYM-01, CAUS-01

Notes: No physical interpretation implied; member-level outcomes recorded externally.

External anchor: None

External evidence: None



ID: OV-01c

Name: OV-01 multi-fit stability gate (DR-02a vs DR-03a vs DR-04a)

Category: Evidence block

Short description: Extends OV-01b from a 2-fit cross-fit stability residual to a 3-fit robustness discriminator over three data-backed DR fit choices. Computes all pairwise normalized residuals on the OV-01 observable, summarizes with R_max/R_rms, applies a provisional gate (retain iff R_max ≤ tau), and records a g-grid scan.

Status: Behavioral (Python)

Evidence: formal/python/toe/observables/ov01_multi_fit_stability.py; formal/python/tests/test_ov01_multi_fit_stability.py; formal/markdown/locks/observables/OV-01_multi_fit_stability_DR02_DR03_DR04.md

Scope / limits: Provisional robustness gate only (tau is not claimed “true”); normalized residual cancels multiplicative g for g>0 under the current OV-01 Option A definition.

Dependencies: OV-01b, DR-04a

Notes: This is intended as a stronger robustness stress-test under fit-window perturbations; if it proves too strict or non-discriminating over FN parameter grids, it motivates either (i) revising the observable form (OV-02) or (ii) introducing absolute (non-normalized) residual reporting.

External anchor: None

External evidence: None



ID: OV-01d

Name: OV-01 multi-fit stability gate (DR-02a vs DR-03a vs DR-04a vs DR-05a)

Category: Evidence block

Short description: Extends the OV-01 multi-fit stability envelope to four DR window choices by adding DR-05a (intermediate k-max). Locks the 4-fit R_max/R_rms values and records an interpretation for monotone drift vs isolated-window outliers.

Status: Behavioral (Python)

Evidence: formal/python/toe/observables/ov01_multi_fit_stability.py; formal/python/tests/test_ov01_multi_fit_stability_4fit.py; formal/markdown/locks/observables/OV-01_multi_fit_stability_DR02_DR03_DR04_DR05.md; formal/markdown/locks/observables/OV-01_multi_fit_stability_DR02_DR03_DR04c_DR05.md

Scope / limits: Provisional robustness gate only (tau is not claimed “true”); normalized residual cancels multiplicative g for g>0 under the current OV-01 Option A definition.

Dependencies: OV-01c, DR-05a, DR-04c

Notes: With DR-05a included, the c_s drift appears monotone in k-max, motivating curvature-aware DR modeling as the next science step. DR-04c provides an upgraded N≥5 window set for strict adequacy workflows.

External anchor: None

External evidence: None



ID: OV-01e

Name: OV-01 multi-fit stability gate (curved DR-02a vs DR-03a vs DR-04a vs DR-05a)

Category: Evidence block

Short description: Curvature-aware variant of OV-01d that first fits ω/k = c0 + βk² on each frozen DR window sample and then computes the OV-01 observable values via the curved BR-01 front door. Locks the resulting 4-fit R_max/R_rms envelope and applies the same provisional retain/prune gate.

Status: Behavioral (Python)

Evidence: formal/python/toe/observables/ov01_multi_fit_stability_curved.py; formal/python/tests/test_ov01_multi_fit_stability_curved_4fit.py; formal/markdown/locks/observables/OV-01_multi_fit_stability_curved_DR02_DR03_DR04_DR05.md; formal/markdown/locks/observables/OV-01_multi_fit_stability_curved_DR02_DR03_DR04c_DR05.md

Scope / limits: Curved fit is a minimal proxy model upgrade; BR-01 mapping currently uses c0 as the k→0 sound-speed proxy under the existing unit-density gauge.

Dependencies: OV-01d, DR-01b

Notes: Curvature-aware modeling reduces but does not eliminate cross-window drift under the current τ=0.10 gate.

External anchor: None

External evidence: None



ID: OV-01f

Name: OV-01 multi-fit stability g-grid discriminator (linear vs curved; DR-02a vs DR-03a vs DR-04a vs DR-05a)

Category: Evidence block

Short description: Evidence-only g-grid scan for the 4-fit OV-01 envelope, presented as a direct linear-vs-curved comparison. Includes g=0.0 explicitly, reports per-g observable values and the locked R_max/R_rms envelope values, and reuses the same provisional τ=0.10 gate for retain/prune.

Status: Evidence (Markdown)

Evidence: formal/markdown/locks/observables/OV-01_multi_fit_stability_curved_DR02_DR03_DR04_DR05_ggrid.md; formal/markdown/locks/observables/OV-01_multi_fit_stability_curved_DR02_DR03_DR04c_DR05_ggrid.md

Scope / limits: Under OV-01 Option A (O = g*c_s^2), the normalized residual cancels multiplicative g for all g>0; the scan is included for completeness and explicit g=0 handling.

Dependencies: OV-01d, OV-01e

Notes: Intended to be read alongside OV-01d and OV-01e. Curved fitting reduces the 4-fit envelope but does not pass the current τ=0.10 robustness gate.

External anchor: None

External evidence: None



ID: OV-01g

Name: OV-01 fit-family robustness gate (linear vs curved; DR-02a vs DR-03a vs DR-04a vs DR-05a)

Category: Evidence block

Short description: Promotes the “curved reduces multi-window spread” observation into an explicit fit-family admissibility gate. Computes the 4-window OV-01 stability envelope for both the linear and curved DR families, forms Q = R_max(curved)/R_max(linear), and prefers curved iff Q <= 0.9 and curved fit-quality is admissible under explicit y-space diagnostic thresholds.

Status: Behavioral (Python)

Evidence: formal/python/toe/observables/ov01_fit_family_robustness.py; formal/python/tests/test_ov01_fit_family_robustness_gate.py; formal/markdown/locks/observables/OV-01_fit_family_robustness_DR02_DR03_DR04_DR05.md; formal/markdown/locks/observables/OV-01_fit_family_robustness_DR02_DR03_DR04c_DR05.md

Scope / limits: This selects a preferred DR-fit family for downstream OV bookkeeping; it does not claim the robustness gate itself is “true,” and it does not imply the underlying τ=0.10 retain criterion is satisfied. Under OV-01 Option A (O = g*c_s^2), normalized residuals cancel multiplicative g for g>0.

Dependencies: OV-01d, OV-01e, OV-01f, DR-06b, DQ-01, DQ-01c, FN-01k

Notes: If the gate cannot prefer curved under the provisional thresholds, downstream should treat OV-based family selection as non-decisive (robustness failed).

External anchor: None

External evidence: None



ID: POL-01

Name: Policy — use curved DR family for OV-based pruning when OV-01g prefers curved

Category: Policy

Short description: Makes the OV-01g fit-family robustness gate operational by defining a single front-door selector used by downstream loops: prefer the curved DR family for OV-based pruning iff OV-01g prefers curved and robustness_failed=False; otherwise treat OV pruning as non-decisive for family selection.

Status: Behavioral (Python)

Evidence: formal/python/toe/observables/ov01_family_policy.py; formal/python/tests/test_ov01_family_policy.py

Scope / limits: This is an operational workflow policy, not a physics claim. If selection is undecided, downstream must not silently fall back to linear for OV-based pruning.

Dependencies: OV-01g, DQ-01

Notes: This prevents silent drift back to linear DR family in OV-based robustness bookkeeping. DQ-01_v2 remains available for audit/back-compat but is not required when using the DR-04c upgraded window set.

External anchor: None

External evidence: None





ID: FN-01c

Name: FN-01 CAUS-01 core tightening consumer

Category: Constraint / Criterion (Lean module)

Short description: Thin FN-layer consumer that imports only the CAUS-01 core surface and re-exports the stable admissibility lemma API.

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/Constraints/FN01\_CausalityCoreConsumer.lean

Scope / limits: Imports only CAUS-01 core surface; no CAUS gate-suite claims; no coupling to FN01\_DeformationClass.

Dependencies: FN-01, CAUS-01

Notes: Validates that CAUS-01 tightening is reusable across criteria layers (AD and FN) with minimal churn.

External anchor: None

External evidence: None





ID: FN-01d

Name: FN-01 CAUS-01 core bridge lemma module

Category: Constraint / Criterion (Lean module)

Short description: Bridge module importing FN-01 deformation-class definitions alongside the CAUS-01 core surface and re-exporting the core admissibility lemmas.

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/Constraints/FN01\_CausalityCoreBridge.lean

Scope / limits: Imports CAUS-01 core surface (not CAUS gate-suite); provides structural re-exports only.

Dependencies: FN-01, CAUS-01

Notes: Confirms FN-layer code can reference the CAUS-01 tightening surface without coupling to the CAUS gate suite.

External anchor: None

External evidence: None





ID: FN-01e

Name: FN-01 candidate outcome table (CT-01 / CAUS C1 / SYM gates)

Category: Evidence block

Short description: Deterministic table-driven test mapping representative deformation terms P[ψ] to pass/fail outcomes for CT-01, CAUS C1 (P(0)=0), and SYM-01 (phase/translation/rotation).

Status: Behavioral (Python)

Evidence: formal/python/tests/test_fn01_candidate_table.py

Scope / limits: Probe-level and grid-based numerical checks only; intended as internal pruning bookkeeping, not a physical claim.

Dependencies: FN-01, CT-01, CAUS-01, SYM-01

Notes: Front-door policy: any new FN candidate term must be added to the table with expected outcomes for CT-01, CAUS C1, SYM phase, SYM translation, and SYM rotation (prevents silent candidate sprawl).

External anchor: None

External evidence: None





ID: FN-01f

Name: FN-01 candidate membership entry points + per-candidate DR corollaries

Category: Constraint / Criterion (Lean module)

Short description: Lean-side “front door” entry-point lemmas per candidate (admit via FN01_DeformationClass or explicitly reject), plus one-liner corollaries exporting DR-01 preservation on plane waves per candidate via the existing FN→DR bridge.

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/Constraints/FN01\_CandidateMembership.lean

Scope / limits: Structural-only; most candidates are admitted conditionally (requires the gate predicates as hypotheses) because the linearization extractor is abstract. Includes explicit rejections where a gate is violated definitionally.

Dependencies: FN-01, CT-01, SYM-01, DR-01

Notes: Intended policy: any theorem about a specific FN candidate should import this module and route through the named membership lemma (or a named rejection lemma) before consuming FN→DR consequences.

External anchor: None

External evidence: None





ID: FN-01g

Name: FN-01 near-plane-wave (wavepacket) ω(k) regression check

Category: Evidence block

Short description: Behavioral regression test estimating ω(k) from time evolution of a small Gaussian-enveloped wavepacket, comparing baseline vs perturbations to provide one notch of DR-01 tightening beyond exact plane waves.

Status: Behavioral (Python)

Evidence: formal/python/tests/test_fn01_near_plane_wave_regression.py

Scope / limits: Small-grid, short-time, deterministic numerical check only; not a PDE validation suite and not a physical claim.

Dependencies: FN-01, CT-01, DR-01

Notes: Intended as the next tightening step after the plane-wave-only structural bridge; keeps the CAUS gate-suite untouched.

External anchor: None

External evidence: None





ID: FN-01h

Name: FN-01 Lean candidate API front-door + enforcement test

Category: Evidence block

Short description: Adds a single Lean import surface for FN-01 named candidates and mechanically enforces (via pytest scan) that downstream Lean files cannot reference candidate tokens without importing the FN-01 Candidate API module.

Status: Behavioral (Python)

Evidence: formal/toe\_formal/ToeFormal/Constraints/FN01\_CandidateAPI.lean; formal/python/tests/test\_fn01\_candidate\_api\_enforced.py

Scope / limits: Guardrail policy only; does not add new mathematical content.

Dependencies: FN-01, FN-01f

Notes: Lean-side equivalent of the Python candidate-table front door; prevents casual bypass of the membership API by direct candidate usage.

External anchor: None

External evidence: None



ID: FN-01i

Name: FN-01 plane-wave mode-closure diagnostic table

Category: Evidence block

Short description: Evidence-only diagnostic evaluating each registered FN-01 candidate representative P[ψ] on a single Fourier-mode plane wave and reporting whether the output remains mode-closed (P(ψ) proportional to ψ) along with the induced coefficient alpha. Intended as discriminative bookkeeping for candidates that definitionally break plane-wave closure.

Status: Behavioral (Python)

Evidence: formal/markdown/locks/functionals/FN-01_plane_wave_mode_closure_diagnostic.md; formal/python/tests/test_fn01_candidate_table.py

Scope / limits: Single-mode diagnostic only (one k, one amplitude, one grid); not a PDE suite and not a physical claim.

Dependencies: FN-01, DR-01

Notes: Separates “mode-closed on plane waves” from the FN gate outcomes; candidates that leak modes are not eligible for a literal plane-wave dispersion reading.

External anchor: None

External evidence: None



ID: FN-01j

Name: FN-01 candidate pruning outcome table (mode-closure gate)

Category: Evidence block

Short description: Evidence-only pruning table derived from the FN-01 plane-wave mode-closure diagnostic, recording which registered candidates are mode-closed vs mode-leaking on the tested plane wave and identifying the leading survivor under the combined FN gate outcomes.

Status: Behavioral (Python)

Evidence: formal/markdown/locks/functionals/FN-01_candidate_pruning_outcomes_DR02_DR03.md; formal/markdown/locks/functionals/FN-01_plane_wave_mode_closure_diagnostic.md; formal/python/tests/test_fn01_candidate_table.py

Scope / limits: Pruning bookkeeping only; does not upgrade status; mode-closure diagnostic is independent of BR-01/MT-01 metrics in the current framework.

Dependencies: FN-01, FN-01e, FN-01i

Notes: This is intended as a decision-log input for candidate elimination; any future promotion of a single FN candidate into a public artifact surface must reference this table.

External anchor: None

External evidence: None



ID: FN-01k

Name: FN-01 promoted survivor as typed artifact (P_cubic)

Category: Evidence block

Short description: Introduces a minimal, provenance-stamped FN-01 artifact type (`FN01Artifact1D`) with a deterministic sha256 fingerprint (canonical JSON encoding) and a canonical constructor for the promoted survivor `P_cubic`. This enables downstream bridges/diagnostics to consume a stable “scientific object” rather than importing candidate code or raw arrays.

Status: Behavioral (Python)

Evidence: formal/python/toe/constraints/fn01_artifact.py; formal/python/tests/test_fn01_artifact_provenance.py; formal/python/tests/test_fn01_front_door_enforced.py; formal/python/toe/constraints/fn01_candidates.py

Scope / limits: Artifact plumbing + determinism/provenance guardrail only; does not claim the candidate is physically correct.

Dependencies: FN-01, FN-01j

Notes: Policy mirror of BR-01: internal candidate implementations are quarantined and import-banned; consumers should depend on the artifact surface and named constructors.

External anchor: None

External evidence: None



ID: FN-01l

Name: FN-01 cross-fit metric discriminator (DR-02a vs DR-03a)

Category: Evidence block

Short description: Introduces a single scalar, metric-coupled discriminator that depends on BR-01/MT-01 outputs and therefore changes under DR fit choice. Computes a normalized cross-fit residual on the BR-01-derived metric component g_tt for DR-02a vs DR-03a, and threads the promoted FN artifact fingerprint for lineage.

Status: Behavioral (Python)

Evidence: formal/python/toe/constraints/fn01_metric_discriminator.py; formal/python/tests/test_fn01_cross_fit_metric_residual.py; formal/markdown/locks/functionals/FN-01_cross_fit_metric_residual_DR02_DR03.md

Scope / limits: Minimal discriminator only; currently uses the BR-01 unit-density gauge and u = 0 fits, so g_tt tracks c_s^2 drift under the bridge; does not yet use an FN-dependent weighting beyond fingerprint propagation.

Dependencies: FN-01k, BR-01d, DR-02a, DR-03a, BR-01c

Notes: This is the first explicitly metric-sensitive pruning signal in the FN loop; any future higher-value FN discriminators should reduce to or extend this residual rather than replacing it ad hoc.

External anchor: None

External evidence: None





4.4 METRICS AND GEOMETRY





ID: MT-01

Name: Acoustic metric

Category: Metric

Short description: Effective wave metric

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/CRFT/Geom/AcousticMetric.lean

Scope / limits: Linear wave regime

Dependencies: DR-01

Notes: Structural object exists; usage is optional as an interpretive lens within current scope.

External anchor: None

External evidence: None





ID: MT-01a

Name: MT-01 Python front door + lock regression

Category: Evidence block

Short description: Adds a canonical Python implementation of the MT-01 acoustic-metric formulas and a deterministic regression test (including cross-check vs the archived reference implementation).

Status: Behavioral (Python)

Evidence: formal/python/crft/acoustic_metric.py; formal/python/tests/test_mt01_acoustic_metric_lock.py

Scope / limits: Tests only the locked algebraic identities pointwise; does not claim physical completeness.

Dependencies: MT-01

Notes: Python-side “front door” mirror of the Lean lock; intended to keep the locked formulas stable and executable.

External anchor: None

External evidence: None





ID: MT-01b

Name: MT-01 Lean consumer lemma (1D determinant reduction)

Category: Evidence block

Short description: Adds a thin Lean consumer module proving the 1D determinant reduction lemma for computed acoustic metrics, mirroring the existing 2D reduction lemma.

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/CRFT/Geom/MT01\_AcousticMetricConsumer.lean

Scope / limits: Purely structural lemma over the locked definitions.

Dependencies: MT-01

Notes: Establishes the “consumer” half of the MT-01 lock pattern, keeping the base definition file focused on formulas.

External anchor: None

External evidence: None





4.5 BRIDGES AND REDUCTIONS





ID: BR-01

Name: Dispersion to metric mapping

Category: Bridge

Short description: Maps dispersion relation to effective metric

Status: Spec-backed

Evidence: formal/markdown/locks/geometry/forced\_vs\_optional\_geometry.md

Scope / limits: Linear regime

Dependencies: DR-01, MT-01

Notes: No physical necessity claim

External anchor: None

External evidence: None





ID: BR-01a

Name: BR-01 Python front door + enforcement + roundtrip locks

Category: Evidence block

Short description: Adds a canonical Python import surface for BR-01 (dispersion → metric mapping), enforces that internal candidate modules are not imported directly, and provides deterministic plane-wave and near-plane-wave roundtrip locks.

Status: Behavioral (Python)

Evidence: formal/python/toe/dr01_fit.py; formal/python/toe/bridges/br01_dispersion_to_metric.py; formal/python/toe/bridges/br01_candidates.py; formal/python/tests/test_br01_front_door_enforced.py; formal/python/tests/test_br01_candidate_table.py; formal/python/tests/test_br01_plane_wave_roundtrip.py; formal/python/tests/test_br01_near_plane_wave_roundtrip.py

Scope / limits: Uses a minimal 1D DR-01 data-backed fit artifact (u, c_s, provenance, data_fingerprint) and a deterministic wavepacket phase estimator; this is a bridge lock and policy guardrail, not a physical derivation.

Dependencies: BR-01, DR-01, MT-01

Notes: Establishes the Python-side “front door” and makes BR-01 hard to bypass in downstream code.



ID: BR-01c

Name: BR-01 upgraded to DR-01 fit artifact input (no surrogate fallback)

Category: Evidence block

Short description: Upgrades BR-01 to consume a canonical DR-01 data-backed fit artifact type (front door), implements fit-backed candidates privately, and tightens the roundtrip locks to assert the fit fingerprint and data fingerprint are actually used (preventing accidental fallback to ad-hoc surrogates).

Status: Behavioral (Python) + Structural (Lean)

Evidence: formal/python/toe/dr01_fit.py; formal/python/toe/bridges/br01_dispersion_to_metric.py; formal/python/toe/bridges/br01_candidates.py; formal/python/tests/test_br01_candidate_table.py; formal/python/tests/test_br01_plane_wave_roundtrip.py; formal/python/tests/test_br01_near_plane_wave_roundtrip.py; formal/toe_formal/ToeFormal/Bridges/BR01_DispersionToMetric.lean; formal/toe_formal/ToeFormal/Bridges/Consumers/BR01_UsesMT01.lean

Scope / limits: Still 1D and unit-density gauge; the upgrade is about dependency structure and drift-proof bridge plumbing (fit-typed assumption), not about extending BR-01’s physical scope.

Dependencies: BR-01, DR-01, MT-01

Notes: BR-01 remains hard-to-bypass: candidates are still import-banned; downstream consumers depend only on the front door.

External anchor: None

External evidence: None



ID: BR-01d

Name: BR-01 cross-fit comparison report (DR-02a vs DR-03a)

Category: Evidence block

Short description: Evidence-only report comparing BR-01 output acoustic metrics when driven by two different frozen, data-backed DR fit artifacts (DR-02a vs DR-03a) derived from the Steinhauer Fig. 3a digitization. Records what changes under the fit choice (notably c_s and thus g_tt/c_s2) and what remains invariant under the current unit-density gauge.

Status: Behavioral (Python)

Evidence: formal/markdown/locks/bridges/BR-01_cross_fit_comparison_DR02_DR03.md; formal/python/toe/bridges/br01_dispersion_to_metric.py; formal/external_evidence/bec_bragg_steinhauer_2001/dr01_fit_artifact.json; formal/external_evidence/bec_bragg_steinhauer_2001/dr03_fit_artifact.json

Scope / limits: Cross-fit bookkeeping only; BR-01 remains 1D and unit-density; does not interpret which fit choice is "better".

Dependencies: BR-01, DR-02a, DR-03a, MT-01

Notes: Both fits satisfy BR-01 internal consistency (roundtrip) by construction; the point is sensitivity of downstream metric coefficients to the chosen DR fit window.

External anchor: Bragg spectroscopy of ⁸⁷Rb BEC excitations

External evidence: Steinhauer PRL 88, 120407 (2002), Fig. 3a



ID: BR-01e

Name: BR-01 cross-fit comparison report (curved DR; DR-02a vs DR-03a vs DR-04a vs DR-05a)

Category: Evidence block

Short description: Evidence-only report comparing BR-01 metric-driving quantities across four curvature-aware DR window fits, using c0 from ω/k = c0 + βk² as the k→0 sound-speed proxy.

Status: Behavioral (Python)

Evidence: formal/markdown/locks/bridges/BR-01_cross_fit_comparison_curved_DR02_DR03_DR04_DR05.md; formal/python/toe/bridges/br01_dispersion_to_metric.py; formal/python/toe/dr01_fit_curved.py

Scope / limits: Bookkeeping comparison only; does not claim the curved proxy is physically necessary.

Dependencies: BR-01, DR-01b, DR-02a, DR-03a, DR-04a, DR-05a

Notes: Intended to be read alongside OV-01e.

External anchor: Bragg spectroscopy of ⁸⁷Rb BEC excitations

External evidence: Steinhauer PRL 88, 120407 (2002), Fig. 3a





ID: BR-01b

Name: BR-01 Lean structural bridge + MT-01 consumer composition

Category: Evidence block

Short description: Adds a minimal Lean BR-01 bridge mapping a DR-01 surrogate record to an MT-01 acoustic metric (unit-density gauge) and proves a downstream consumer lemma by routing through the MT-01 consumer reduction.

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/Bridges/BR01\_DispersionToMetric.lean; formal/toe\_formal/ToeFormal/Bridges/Consumers/BR01\_UsesMT01.lean

Scope / limits: Structural mapping only; does not claim uniqueness or physical necessity.

Dependencies: BR-01, DR-01, MT-01

Notes: Lean-side “front door” for BR-01 consumers; demonstrates immediate use by composing into MT-01.

External anchor: None

External evidence: None





4.6 OPERATORS AND AUXILIARY CONSTRUCTS





ID: OP-01

Name: UCFF operator

Category: Operator

Short description: Second-order time evolution operator

Status: Locked

Evidence: formal/toe\_formal/ToeFormal/UCFF/SecondOrderTimeDomain.lean; formal/toe\_formal/ToeFormal/UCFF/SecondOrderNumerics.lean; formal/python/tests/test\_ucff\_core\_symbolic.py; formal/python/tests/test\_ucff\_core\_roundtrip.py; OP-01-EVIDENCE-ARCHIVE-LEGACY

Scope / limits: Homogeneous media

Dependencies: EQ-02

Notes: Locked is asserted jointly: Lean formalization (UCFF modules listed in Evidence) plus Python behavioral checks (formal/python/tests/\*). Locked-status evidence is restricted to non-archived tests under formal/python/tests/\* and the listed Lean modules; OP-01-EVIDENCE-ARCHIVE-LEGACY is included for traceability only and is not part of the Locked-status evidence subset.

External anchor: None

External evidence: None





ID: OP-PW-01

Name: PlaneWave operator definitions (2D)

Category: Operator / Definitions (Lean module)

Short description: Defines opaque operator symbols (Dt, Dxx, Dyy, Delta, L), Field2D, and the planeWave template used for EQ-02 reduction proofs.

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/CPNLSE2D/PlaneWaveOperatorDefs.lean

Scope / limits: Purely structural. Operators are uninterpreted at this layer; no analytic derivative content.

Dependencies: None

Notes: Serves as the definition layer for subsequent axiom and reduction modules; must remain minimal to prevent accidental analytic commitments. Underlying Lean/Mathlib libraries provide technical substrate.

External anchor: None

External evidence: None





ID: OP-PW-02

Name: PlaneWave operator action axioms (Dt/Delta)

Category: Operator / Axiom layer (Lean module)

Short description: Quarantines assumed operator action on planeWave via Dt\_planeWave and Delta\_planeWave, enabling structural reduction without Mathlib derivative development.

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/CPNLSE2D/PlaneWaveOperatorAxioms.lean

Scope / limits: Axiom-only. Encodes the intended behavior of Dt and Delta on planeWave; does not justify or derive these actions from analysis.

Dependencies: OP-PW-01

Notes: This module is the explicit “axiom layer.” Any downstream result relying on these axioms must remain labeled as conditional on Dt\_planeWave / Delta\_planeWave.

External anchor: None

External evidence: None





ID: OP-PW-03

Name: PlaneWave operator reduction lock for EQ-02

Category: Operator / Reduction (Lean module)

Short description: Proves EQ-02 on planeWave reduces to coefficient-equality-times-planeWave under explicit operator-action axioms; no cancellation required.

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/CPNLSE2D/PlaneWaveOperators.lean

Scope / limits: Linearized EQ-02 only; reduction is probe-relative to planeWave; relies on Dt\_planeWave and Delta\_planeWave axioms; no non-vanishing/cancellation lemma is assumed or proven.

Dependencies: EQ-02, OP-PW-01, OP-PW-02

Notes: Establishes the operator-level inevitability step (Phase A3). Extracting ω = eigC would require an additional non-vanishing/cancellation lemma about planeWave (not included here by design).

External anchor: None

External evidence: None





ID: OP-PW-04

Name: PlaneWave eigenstructure and selection principle A2

Category: Operator / Eigenstructure + probe-visibility (Lean module)

Short description: Proves eigenvalue addition closure for plane-wave eigen operators and the A2 selection principle: if O and O+E are dispersion-compatible, then E vanishes on plane-wave probes (probe-invisible).

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/OperatorCore/PlaneWaveEigenstructure.lean

Scope / limits: Plane-wave probe family only; statement is conditional on the project’s definition of DispersionCompatible (which is probe-relative to planeWave); does not claim E=0 globally as an operator, only E.Op(planeWave …)=0.

Dependencies: OP-SIG-01, OP-PW-01, DR-01

Notes: Canonical downstream lemma is dispersionCompatible\_add\_implies\_E\_vanishes\_on\_planeWaves\_fun; use have hE0 := ... hO hOE A kx ky then simp \[hE0] or rw \[hE0].

External anchor: None

External evidence: None





ID: OP-SIG-01

Name: OperatorSignature core (Op2D + DispersionCompatible + PlaneWaveEigen)

Category: Operator / Signature (Lean module)

Short description: Defines Op2D operator signature and core predicates used by operator-core proofs.

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/OperatorCore/OperatorSignature.lean

Scope / limits: Purely structural interface; no analytic commitments.

Dependencies: None

Notes: Upstream definition layer for OP-PW-04. Underlying Lean/Mathlib libraries provide technical substrate.

External anchor: None

External evidence: None





ID: PHB-01

Name: Phase B dispersion-preservation formal scaffold

Category: Constraint / Criterion (Lean module)

Short description: Lean formalization layer used by CT-01c wiring (probe-family preservation lemmas and related predicates).

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/CPNLSE2D/PhaseB/DispersionPreservation.lean

Scope / limits: Structural scaffold only; probe-relative; conditional on OP-PW axiom layer as used downstream.

Dependencies: OP-PW-02, OP-PW-03, EQ-02, DR-01

Notes: Exists to satisfy “IDs only” dependency rule for CT-01c.

External anchor: None

External evidence: None





4.7 CONSTRAINTS





ID: CT-01
Name: DR-01 dispersion-preservation criterion (linearization rule)

Category: Constraint / Criterion

Short description: Classifies perturbations P\[ψ] by whether they introduce a linear term about ψ=0 and thus alter DR-01.

Status: Behavioral (Python)

Evidence: formal/markdown/locks/constraints/dispersion\_preserving\_terms.md; CT-01-EVIDENCE-PHB; CT-01-EVIDENCE-SOLVER-OMEGA

Scope / limits: Linearization about ψ=0 only; CT-01 is defined and evaluated under probe-level semantics (plane-wave coefficient identity). Additional evidence includes solver-level consequence checks that ω̂(k) shifts when CT-01 fails; these do not change CT-01’s semantics.

Dependencies: EQ-02, DR-01, EQ-01

Notes: Expanded tests include a ψ-independent constant source term; it breaks the plane-wave coefficient identity unless the source is zero (evidence that “no linear part at 0” alone does not guarantee probe-level preservation without a separate source-free condition).

External anchor: None

External evidence: None





ID: CT-01a

Name: DR-01 preservation on plane-wave probes (Lean wrapper)

Category: Constraint / Criterion

Short description: Probe-relative preservation: under AdmissibleOnPlaneWave, perturbed EQ-02 on plane waves is equivalent to unperturbed EQ-02 (same reduction target).

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/Constraints/CT01\_Abstract.lean; formal/toe\_formal/ToeFormal/CPNLSE2D/PhaseB/DispersionPreservation.lean

Scope / limits: Plane-wave probe family only; linearized EQ-02 only; conditional on Dt\_planeWave and Delta\_planeWave axioms.

Dependencies: CT-01, DR-01, EQ-02, OP-PW-02, OP-PW-03, PHB-01

Notes: Uses lemmas EQ02Holds\_planeWave\_iff and EQ02Pert\_planeWave\_reduces\_to\_same\_coeff\_equality.

External anchor: None

External evidence: None





ID: CT-01b

Name: LinearizationAt0 probe-relative preservation lemma

Category: Constraint / Criterion (Structural bridge)

Short description: Structural bridge lemma relating abstract linearization surrogate to probe-relative preservation on plane waves.

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/Constraints/CT01\_LinearizationInterface.lean; formal/toe\_formal/ToeFormal/Constraints/CT01\_LinearizationInterfaceProbe.lean; formal/toe\_formal/ToeFormal/Constraints/CT01\_Abstract.lean

Scope / limits: Probe-relative; applies only to the plane-wave family and linearized EQ-02; linearization is axiomatized and not analytically derived.

Dependencies: CT-01a, OP-PW-02, OP-PW-03, EQ-02, DR-01

Notes: None

External anchor: None

External evidence: None





ID: CT-01c

Name: CT-01 abstract scaffold (CT01\_Abstract)

Category: Constraint / Criterion (Structural scaffold)

Short description: Introduces an abstract “no linear part at ψ=0” predicate (not tied to plane waves) and wires a probe-family preservation lemma for plane waves using PhaseB reduction lemmas.

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/Constraints/CT01\_Abstract.lean

Scope / limits: Structural scaffold; abstract predicate is placeholder-only; preservation statement is probe-family only (plane-wave family) and remains conditional on OP-PW axioms and the PhaseB perturbed reduction lemma.

Dependencies: CT-01a, OP-PW-02, OP-PW-03, EQ-02, DR-01, PHB-01

Notes: This is the canonical “abstract hook” for later strengthening: you can later prove NoLinearPartAt0\_Abstract P → NoLinearPartOnPlaneWaves P (if appropriate), and/or replace the probe-family surrogate with a real structural linearization operator once defined.

External anchor: None

External evidence: None





ID: CT-01d

Name: LinearizationAt0 interface (CT01\_LinearizationInterface)

Category: Constraint / Criterion (Lean interface)

Short description: Defines an abstract, non-analytic linearization-at-0 extractor for Field2D perturbations; provides NoLinearPartAt0\_Field2D predicate.

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/Constraints/CT01\_LinearizationInterface.lean

Scope / limits: Structural-only hook; no analytic meaning; does not imply probe-family vanishing without additional assumptions.

Dependencies: OP-PW-01

Notes: Upstream interface used by CT-01c/CT-01f to make “no linear part at 0” meaningful without analysis.

External anchor: None

External evidence: None





ID: CT-01e

Name: Probe-sound linearization interface (CT01\_LinearizationInterfaceProbe)

Category: Constraint / Criterion (Lean interface)

Short description: Packages a LinearizationAt0 extractor with a Probe predicate and a soundness axiom: NoLinearPartAt0 ⇒ perturbation vanishes on the probe family.

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/Constraints/CT01\_LinearizationInterfaceProbe.lean

Scope / limits: Structural-only; soundness is an explicit axiom of the interface; Probe can be specialized (e.g., plane waves).

Dependencies: CT-01d, OP-PW-01

Notes: Provides PlaneWaveProbe and lemma noLinearPartAt0\_implies\_vanishes\_onPlaneWaves for Probe=PlaneWaveProbe.

External anchor: None

External evidence: None





ID: CT-01f

Name: CT-01 abstract criterion ⇒ DR-01 unchanged on plane waves (CT01\_Abstract bridge theorem)

Category: Constraint / Criterion (Lean theorem)

Short description: Uses probe-sound linearization to derive plane-wave admissibility and proves perturbed EQ-02 is equivalent to unperturbed EQ-02 on plane-wave probes (DR-01 unchanged on probes).

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/Constraints/CT01\_Abstract.lean

Scope / limits: Plane-wave probe family only; relies on PhaseB probe-relative preservation lemma; does not upgrade DR-01 to a global statement.

Dependencies: CT-01c, CT-01d, CT-01e, PHB-01, OP-PW-02, OP-PW-03, EQ-02, DR-01

Notes: Theorem name: CT01\_noLinearPartAt0\_preserves\_DR01\_onPlaneWaves. CT-01 abstract bridge theorem exists and is compiled in Lean.



External anchor: None

External evidence: None



ID: CT-01g

Name: CT-01 CP-NLSE instance-layer shim (CT01\_CPNLSE2D\_Instance)

Category: Constraint / Criterion (Lean instance shim)

Short description: Instance-layer re-export of the CT-01 abstract bridge theorem for CP-NLSE downstream imports.

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/Constraints/CT01\_CPNLSE2D\_Instance.lean

Scope / limits: Import-surface shim only; does not change CT-01 semantics; keeps CT01\_Abstract as the authority layer.

Dependencies: CT-01f

Notes: Provides CT01\_CPNLSE2D\_noLinearPartAt0\_preserves\_DR01\_onPlaneWaves as a stable downstream theorem name.

External anchor: None

External evidence: None





ID: SYM-01

Name: Symmetry Gate Suite (Phase / Translation / Rotation)

Category: Constraint / Criterion

Short description: Symmetry-based admissibility gate for deformation terms P\[ψ]; pruning constraint enforcing baseline symmetries of unperturbed linearized dynamics.

Status: Locked

Evidence: formal/toe\_formal/ToeFormal/Constraints/SYM01\_PhaseInvariant.lean; formal/python/tests/test\_sym01\_symmetry\_gates.py; formal/markdown/locks/constraints/SYM-01\_symmetry\_gates.md

Scope / limits: Organizational / pruning constraint only; probe-relative behavioral checks; passing does not imply physical correctness; failing is sufficient for exclusion. Gates: S1 (global phase invariance: ψ ↦ e^(iθ) ψ), S2 (spatial translation invariance: no explicit position dependence), S3 (spatial rotation invariance: isotropy under planar rotations). Rotation semantics: field rotated, reference grid held fixed.

Dependencies: None

Notes: No conservation-law claims; no Noether machinery imported; all symmetry notions are explicitly semantic and probe-relative; discrete numerical artifacts acknowledged and controlled by test design. Orthogonal to CT-01 (linearization) and FN-01 (admissible deformation class); composable with future constraints.

External anchor: None

External evidence: None





ID: CAUS-01

Name: Structural Causality / Well-Posedness Gate (Locality / Admissibility)

Category: Constraint / Criterion

Short description: Structural admissibility gates for candidate deformation terms and/or operator extensions; enforces causality-motivated structural rules without proving well-posedness.

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/Constraints/CAUS01\_CausalityCore.lean; formal/toe\_formal/ToeFormal/Constraints/CAUS01\_CausalityGate.lean; formal/markdown/locks/constraints/CAUS-01\_causality\_admissibility\_gates.md

Scope / limits: Pruning constraint only; passing does not imply well-posedness or physical validity; failing is sufficient for member-level exclusion. Gates: C1 (no ψ-independent forcing: P\[0]=0), C2 (no elliptic-in-time behavior), C3 (locality as structural proxy for causal propagation intent: no nonlocal/integral/global coupling), C4 (time-order sanity: bounded differential order, no mixed time-order escalation under the declared form). All gates are semantic predicates supplied by caller in Lean; C4 is represented as TimeOrderSane(form, P) parameterized by declared EvolForm, and CAUS01\_Admissible instantiates it at the suite's declared form via TimeOrderSaneAt. Lean interface does not attempt PDE classification (hyperbolic/parabolic).

Dependencies: EQ-01, EQ-02

Notes: Makes no conservation-law claims; does not prove well-posedness or establish finite-speed propagation; performs no analytic PDE classification. Intended for conjunctive use with CT-01 and SYM-01.

External anchor: None

External evidence: None



ID: OP-01-EVIDENCE-ARCHIVE-LEGACY

Name: UCFF legacy archive tests (non-canonical)

Category: Evidence block

Short description: Legacy archive-based UCFF tests retained for traceability only; not used for Locked status.

Status: Deprecated

Evidence: archive/tests/test\_ucff\_core\_symbolic.py; archive/tests/test\_ucff\_core\_roundtrip.py

Scope / limits: Legacy only; not canonical evidence for OP-01 status.

Dependencies: None

Notes: Superseded by formal/python/tests/\* UCFF tests.

External anchor: None

External evidence: None





ID: CT-01-EVIDENCE-PHB

Name: Dispersion preservation under probe-level coefficient identity (DR-01)

Category: Evidence block

Short description: Behavioral probe-level regression suite for CT-01 (plane-wave coefficient identity).

Status: Behavioral (Python)

Evidence: formal/python/tests/test\_phaseB\_dispersion\_preservation\_expanded.py

Scope / limits: Probe-level only (plane-wave coefficient identity); linearization about ψ=0; does not validate solver dynamics or physical interpretation.

Dependencies: CT-01, DR-01, EQ-02

Notes: Previously grouped under “PHASE-B EVIDENCE (PYTHON)” and “CT-01 — DR-01 probe-level dispersion preservation (expanded evidence suite)”. Includes pass/fail families (linear vs nonlinear, derivative surrogates with k-edge cases) and constant source term check; last recorded run: 62 passed (expanded) and 69 passed (full suite).

External anchor: None

External evidence: None





ID: CT-01-EVIDENCE-SOLVER-OMEGA

Name: Solver-level ω(k) consequence under CT-01 failure

Category: Evidence block

Short description: Time-evolution frequency-shift checks predicted by probe-level dispersion incompatibility.

Status: Behavioral (Python)

Evidence: formal/python/tests/test\_phaseB\_solver\_omega\_shift.py

Scope / limits: Narrow periodic-box spectral split-step setup; ω̂(k) extraction via mode projection; constant-source detected via k=0/mean growth; diagnostic behavioral consequence only.

Dependencies: CT-01, DR-01, EQ-02

Notes: Tests ω̂(k) shift for linear potential and derivative surrogates, near-unshifted small-amplitude cubic; last recorded run: 7 passed (suite) and 72 passed (full suite).

External anchor: None

External evidence: None



ID: OV-01

Name: FN-dependent observable probe (OV-01)

Category: Observable / Diagnostic

Short description: Defines a minimal, deterministic observable computed from a promoted FN artifact parameterization and the BR-01/MT-01 metric derived from a data-backed DR fit. This is probe-relative and intended as the smallest “FN touches an observable” step.

Status: Behavioral (Python)

Evidence: formal/python/toe/observables/ov01_observable.py

Scope / limits: Option A (consistency residual) only; observable is a deliberately minimal FN×metric scalar with target 0 and residual |obs|; not a physical claim.

Dependencies: FN-01k, BR-01c, MT-01a, DR-01

Notes: OV-01 exists to force FN parameters into an externally anchored (data-backed) pipeline surface; higher-value observables may replace the algebraic form while preserving the report/fingerprint structure.

External anchor: None

External evidence: None



ID: OV-01a

Name: OV-01 scan and sensitivity locks (DR-02a vs DR-03a)

Category: Evidence block

Short description: Evidence-only scan of the OV-01 observable for multiple FN parameter settings (g values) under two different data-backed DR fit choices (DR-02a vs DR-03a), plus lock tests asserting fingerprint propagation and FN/metric sensitivity.

Status: Behavioral (Python)

Evidence: formal/markdown/locks/observables/OV-01_DR02_DR03_scan.md; formal/python/tests/test_ov01_observable_residual.py

Scope / limits: Uses the current BR-01 unit-density gauge and u = 0 fits; observable is probe-relative and minimal.

Dependencies: OV-01, DR-02a, DR-03a

Notes: This is the first FN-dependent observable residual in the data-backed loop; it is intended as an upgrade point for future anchored targets (Option B) and/or additional DR windows.

External anchor: None

External evidence: None

ID: OV-01b

Name: OV-01 cross-fit stability gate (DR-02a vs DR-03a)

Category: Evidence block

Short description: Defines and locks a cross-fit stability residual comparing the same FN artifact’s OV-01 observable under two different data-backed DR fit choices (DR-02a vs DR-03a). Adds a provisional robustness gate (retain iff residual ≤ tau) and records a small g-grid table to make the decision surface explicit.

Status: Behavioral (Python)

Evidence: formal/python/toe/observables/ov01_cross_fit_stability.py; formal/python/tests/test_ov01_cross_fit_stability.py; formal/markdown/locks/observables/OV-01_cross_fit_stability_DR02_DR03.md

Scope / limits: Provisional robustness gate only (tau is not claimed “true”); observable is probe-relative and currently uses the BR-01 unit-density gauge and u = 0 fits.

Dependencies: OV-01a

Notes: This converts OV-01 into an explicit discriminator step (“stable under fit-window perturbation?”). Future upgrades may (i) tighten tau based on external anchors, (ii) introduce ranking over candidate families, or (iii) add a third window (DR-04) for a 3-point stability curve.

External anchor: None

External evidence: None





4.8 BUNDLE





ID: PK-01

Name: StructuralPreservationPaper (Lean bundle)

Category: Packaging / Traceability module

Short description: Packaging bundle aggregating Lean modules supporting structural preservation paper traceability.

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/CPNLSE2D/Paper/StructuralPreservationPaper.lean; formal/toe\_formal/ToeFormal/CPNLSE2D/PlaneWaveOperatorDefs.lean; formal/toe\_formal/ToeFormal/CPNLSE2D/PlaneWaveOperatorAxioms.lean; formal/toe\_formal/ToeFormal/CPNLSE2D/PlaneWaveOperators.lean; formal/toe\_formal/ToeFormal/Constraints/CT01\_LinearizationAt0.lean

Scope / limits: Packaging only.

Dependencies: DR-01, OP-PW-02, CT-01a

Notes: None

External anchor: None

External evidence: None



ID: AD-01

Name: Canonical operator admissibility predicate (AdmissibleOp)

Category: Constraint / Criterion

Short description: Defines AdmissibleOp as conjunction of dispersion-compatibility, SYM-01 compliance, and CAUS-01 admissibility for Op2D operator candidates.

Status: Structural (Lean)

Evidence: formal/toe\_formal/ToeFormal/Constraints/AD01\_CausalityCoreConsumer.lean; formal/toe\_formal/ToeFormal/Constraints/AD01\_AdmissibleOp.lean; formal/toe\_formal/ToeFormal/Constraints/AD01\_Breakage.lean; formal/toe\_formal/ToeFormal/Constraints/AD01\_Canonicals.lean; formal/toe\_formal/ToeFormal/Constraints/AD01\_Instances.lean; formal/toe\_formal/ToeFormal/Constraints/AD01\_TimeOrderTests.lean; formal/toe\_formal/ToeFormal/OperatorCore/Op2DMeta.lean; AD-01-EVIDENCE-PY

Scope / limits: Structural-only; probe-relative where DispersionCompatible is probe-relative; canonicals define a single phase-action and a single CAUS gate suite; CAUS time-order is enforced via explicit declared tag (non-analytic).

Dependencies: OP-SIG-01, OP-PW-04, SYM-01, CAUS-01, DR-01

Notes: AD-01 is the canonical wiring layer for operator candidate admissibility. Breakage theorem links OP-PW-04 to admissibility via dispersion-compatibility closure. Canonical CAUS suite currently fixes EvolForm := firstOrderTime (NLSE-style) for non-circular time-order enforcement. Behavioral (Python) consequence checks are tracked in AD-01-EVIDENCE-PY. No physical claims.

External anchor: None

External evidence: None



ID: AD-01-EVIDENCE-PY

Name: AD-01 Python consequence tests (bookkeeping)

Category: Evidence block

Short description: Behavioral consequence checks confirming AD-01 wiring includes time-order sanity and rejects second-order-time metadata under a first-order canonical suite.

Status: Behavioral (Python)

Evidence: formal/python/tests/test\_ad01\_caus\_time\_order\_gate.py

Scope / limits: Consequence tests only; does not discover constraints; does not assert external epistemic status.

Dependencies: None

Notes: None

External anchor: None

External evidence: None





DEPRECATED OR FROZEN ITEMS



ID:

Name:

Reason deprecated:

Replacement:

Notes:



(Leave empty unless applicable.)





OPEN GAPS (BOOKKEEPING ONLY)



Record missing layers or validations.

These are not failures.



Example entries:



Item ID: FN-01

Missing layer: Lean

Comment: No variational derivation



Item ID: BR-01

Missing layer: Python

Comment: No numerical stress test





CHANGE LOG



Date: 2026-01-10

Change: Added CT-01-EVIDENCE-SOLVER-OMEGA (solver-level ω(k) consequence tests) and linked it under CT-01 Evidence. Updated constant source discriminator to use Option A (k=0 / mean(ψ) growth detection) instead of ω-shift.

Reason: Establish behavioral time-evolution consequence: ω̂(k) shifts when CT-01 fails, while remaining near ω0 for small-amplitude purely nonlinear perturbations. Constant source C is detected via mean growth (k=0 mode injection) since it doesn't directly shift ω̂ for k≠0 modes.



Date: 2026-01-10

Change: Updated CAUS-01 inventory entry to match current Lean interface (TimeOrderSane(form, P) parameterized by EvolForm; instantiated via TimeOrderSaneAt) and linked evidence module name ToeFormal.Constraints.CAUS01\_CausalityGate.

Reason: Align State\_of\_the\_Theory.md with the current CAUS-01 markdown semantics notes and the compiled Lean interface.



Date: 2026-01-10

Change: Clarified evidence scoping ambiguities by (1) separating EQ-02 Lean definition into a dedicated module path, (2) removing archive/\* paths from Locked evidence, and (3) setting DR-02 evidence-block status to Behavioral (Python) while retaining DR-02 as Empirically Anchored.

Reason: Remove ambiguity about what constitutes “current” Locked evidence, and ensure “Empirically Anchored” is applied to claims (inventory items) rather than internal reconstruction artifacts.



Date: 2026-01-10

Change: Added OP-01-EVIDENCE-ARCHIVE-LEGACY (Deprecated) to preserve legacy UCFF archive test paths while keeping OP-01 Locked evidence restricted to formal/python/tests/\*.

Reason: Remove ambiguity about canonical vs legacy evidence provenance for OP-01.





HARD RULES (NON-NEGOTIABLE)



If it is not listed here, it does not exist.

If status is Spec-backed, it must be labeled everywhere.

Aristotle may not modify this document.

Status downgrades are allowed without justification. Upgrades are not.





NEXT REQUIRED ACTION

State-of-the-Theory dependency DAG enforcement (unknown IDs + cycles), then resume ToE development.





Template status: We will keep editing.


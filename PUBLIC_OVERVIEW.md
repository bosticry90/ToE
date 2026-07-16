# Toward a Unified Physical Framework: Public Overview

**Status snapshot:** 2026-07-16  
**Project status:** active research hypothesis; not a completed or empirically confirmed Theory of Everything

## What this repository is

This repository is a research program for stating, deriving, testing, and
criticizing a candidate unified physical framework. It combines:

- explicit mathematical assumptions and derivation targets;
- Lean artifacts for machine-checked statements and dependency boundaries;
- Python simulations, numerical diagnostics, and regression tests;
- frozen evidence packets and separate result reviews; and
- claim controls that distinguish a local result from a pillar, seam, or
  theory-level conclusion.

The central aim is not to treat a large body of calculations as proof of a
unified theory. The repository instead records what has been defined, what has
been checked, what remains conditional, and what has failed or become blocked.

## What has been demonstrated

The clearest current example is a bounded classical Maxwell–Dirac study. Under
frozen dimensional, boundary, gauge, and discretization assumptions, a
unit-complete c-number zero-mode model retained a (1+1)-dimensional gauge field,
two transverse gauge descendants, two opposite-charge species, and both reduced
spin sectors. Its canonical numerical review accepted reproducible matter–field
energy exchange and total-energy conservation within the stated numerical
tolerances.

A later fourteen-row robustness study did **not** earn a broad robustness
claim. Its independent review classified the study as numerically blocked
because four frozen residual ceilings failed in one loose-tolerance solver run.
Thirteen scientific rows passed descriptively, but the frozen all-role rule
prevents those passes from being promoted to conditional or broad robustness.
The descendant-materiality question therefore remains unevaluated.

See [MAXWELL_DIRAC_ROBUSTNESS_SUMMARY.md](MAXWELL_DIRAC_ROBUSTNESS_SUMMARY.md)
for the model, evidence, metrics, limitation, and current follow-up.

## What has not been demonstrated

This repository does not currently establish:

- a complete Theory of Everything;
- empirical confirmation or experimental adequacy;
- a quantum Maxwell–Dirac or QED result from the classical c-number study;
- completion of the electromagnetic, quantum-field, or gravitational pillars;
- closure of the seams between those pillars;
- validation of the broader CCFT proposal or master action; or
- evidence of new physics merely from formalization or numerical agreement.

Formal verification can check that a theorem follows from encoded assumptions.
It cannot, by itself, establish that those assumptions describe nature.
Likewise, a passing simulation can support only the model, domain, observables,
and tolerances that were actually tested.

## How evidence is handled

The repository uses a deliberately conservative evidence chain:

1. freeze the assumptions, observables, thresholds, and run identities;
2. execute the bounded calculation or proof task;
3. preserve outputs and hashes;
4. perform an independent reconstruction or review; and
5. record both the maximum accepted claim and explicit nonclaims.

A passing gate does not automatically authorize a stronger scientific claim.
Blocked and negative results are retained rather than rewritten as successes.
The claim vocabulary is summarized in
[TOE_CLAIM_LADDER_v0.md](TOE_CLAIM_LADDER_v0.md).

## Where to go next

- For repository structure, setup, and validation, read
  [TECHNICAL_REPOSITORY_GUIDE.md](TECHNICAL_REPOSITORY_GUIDE.md).
- For the focused Maxwell–Dirac result, read
  [MAXWELL_DIRAC_ROBUSTNESS_SUMMARY.md](MAXWELL_DIRAC_ROBUSTNESS_SUMMARY.md).
- For the compact developer workflow, read [DEVELOPMENT.md](DEVELOPMENT.md).
- For live internal authority and detailed history, use the surfaces identified
  in the technical guide; the very large `README.md` and
  `State_of_the_Theory.md` are append-only research records, not short public
  introductions.

## Public-use note

No root `LICENSE`, `CITATION.cff`, `CONTRIBUTING.md`, or `SECURITY.md` was
present when this overview was prepared. Public visibility does not itself
grant reuse rights. Those files should be added, with an owner-selected license
and contact policy, before treating the repository as a conventional open-source
release.

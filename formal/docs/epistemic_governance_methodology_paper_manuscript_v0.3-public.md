# A Failure-Resistant Scientific Comparison Pipeline

Author: Ryan Bostic (Independent researcher)
Corresponding author: Ryan Bostic

Date: 2026-01-25

---

## Abstract

Scientific computing pipelines frequently compute comparisons by default whenever numerical data are available, even when the epistemic prerequisites for comparison are ambiguous or absent. This practice risks silently converting uncertainty into inferred claims under automation.

We present a failure-resistant comparison pipeline architecture in which admissibility is treated as an explicit governance concern rather than an implicit assumption. Comparisons are executed only when authorized by a declared admissibility configuration; when authorization is absent, the pipeline deterministically emits a structured “blocked” outcome rather than a partial or inferred result.

The system separates intent declaration from enforcement, uses generated manifests to bind governance decisions to execution, and records both computed and blocked outcomes as canonical, auditable artifacts. Importantly, numerical proximity is never treated as evidence of admissible pairing.

We contribute a failure-resistant governance and execution pattern for scientific comparison pipelines: comparisons run only when explicitly authorized, and otherwise the system deterministically produces an auditable blocked outcome.

## Keywords

- scientific computing
- reproducible workflows
- epistemic governance
- computational auditability
- admissibility
- policy-as-code
- scientific software systems
- failure-resistant pipelines

---

## 1. Introduction

A methodology and epistemic-governance pattern for scientific computing pipelines:

**If a comparison is not explicitly admissible, the correct output is a structured refusal (“blocked”), not an inferred claim.**

This paper is about *how* comparisons are governed and executed responsibly.

### 1.1 What this is not

This manuscript specifies a governance and execution pattern for scientific comparison pipelines. It is evaluated by enforceable behavior under automation (authorized comparison vs blocked outcome), and it reports no new empirical results.

Key contribution: a deterministic pipeline architecture that can output an auditable “no” (blocked) outcome—by design—when admissibility prerequisites are absent.

---

## 2. Positioning relative to prior work

This work sits adjacent to, but is distinct from, several existing lines of practice and research, including reproducible scientific workflows, data provenance systems, policy-as-code frameworks, and computational audit trails.

Reproducible pipelines typically emphasize determinism of execution and repeatability of results. Provenance systems focus on tracking data lineage and transformations. Policy-as-code approaches encode operational constraints that govern system behavior. This pipeline incorporates elements of all three, but addresses a narrower and often under-specified question: **how a scientific system should behave when a comparison is not epistemically authorized**.

Rather than attempting to improve comparison metrics, infer equivalence, or resolve interpretive uncertainty, the system described here enforces a conservative governance posture: absent explicit admissibility, the system must refuse to compare and must record that refusal deterministically. The contribution is therefore not a new analytical method, but a failure-resistant execution pattern that **preserves epistemic boundaries even under automation**.

---

## 3. Approach overview
Many analysis pipelines will compute *something* as soon as numbers exist, even if the justification for comparing them is weak or missing.

This pipeline enforces the opposite posture:

- Comparisons are computed **only** when they are explicitly authorized by an admissibility configuration.
- If authorization is absent, the pipeline emits a **blocked** outcome with explicit blockers.
- “Numeric closeness” is never treated as a substitute for admissibility.

Governance invariant: unauthorized comparisons deterministically yield a blocked outcome with zero comparison rows.

Terminology (used consistently below): a *lane* is a data/analysis channel; a *gate* is an admissibility prerequisite; a *manifest* is the executable enforcement configuration generated from declared intent; a *lock* is a canonical, machine-generated audit artifact recording either a computed result or a blocked outcome.

---

## 4. Pipeline architecture

### 4.1 Architecture at a glance

```

Intent (Lean-authored) --> Enforcement Manifest (JSON) --> Execution (Python) --> Canonical Locks
|                          |                              |                    |
declares gates +             tracks repo paths +           computes only         records either
default enablement              content hashes             if authorized      BLOCKED or COMPUTED

```

Key property: the manifest is an enforcement artifact, not a policy surface.

Enforcement binding: at execution time, comparison jobs consult the manifest to determine whether a computation is authorized and record the decision (authorized vs blocked) in a canonical lock, alongside a content fingerprint for auditability.

Here, “validate” means structural and consistency validation (schema and referenced fingerprints), not a cryptographic security guarantee.

Lean’s role: Lean is used as a declarative intent authoring mechanism for admissibility configuration.

Why Lean: it provides a declarative, type-checked surface for intent that is amenable to structured review and deterministic downstream manifest generation.

Intentional abstraction: admissibility predicates are intentionally left venue- and domain-independent; the contribution is the enforcement pattern (“do not compare unless authorized”), not the semantics of any particular gate.

Blocked outcomes are recorded as canonical locks. Each blocked lock records a comparison identifier, the gating conditions evaluated, explicit blockers (failed gates), zero comparison rows, and a content fingerprint for auditability. This structure distinguishes refusal from missing data and supports deterministic reproduction of the refusal behavior.

### 4.2 Evidence artifacts (what you can inspect)

The artifacts below are machine-generated audit records and configuration surfaces produced by the pipeline; they are cited to demonstrate inspectability, not to require repository familiarity.

Examples:

- A machine-generated audit record documenting a blocked cross-lane comparison.
- A generated admissibility enforcement manifest (JSON) that binds declared intent to execution.
- A manifest updater tool that regenerates the enforcement manifest from declared intent.
- An explicit pairing-evidence mapping surface (mapping tuples); it may be empty without forcing a comparison.

---

## 5. Governance outcomes

This section is intentionally focused on governance behavior under automation: the system either computes an authorized comparison or emits a structured blocked outcome with explicit blockers.

---

## 6. Reproducibility statement (reproduces the refusal)

Goal: deterministically reproduce the **blocked** outcome (not compute a cross-lane score).

Reproduction procedure (conceptual):

1) Update the admissibility enforcement manifest from declared intent.
2) Regenerate the canonical audit locks.
3) Verify the invariant that unauthorized comparisons remain blocked and emit zero rows.

Expected result:

- A representative audit record remains blocked and emits zero rows.

---

## 7. Artifact availability (journal-neutral)

Supplementary materials provide runnable code and canonical audit artifacts to support inspection and deterministic reproduction.

---

## 8. Technical specification (frozen appendix)

**Appendix A (Supplementary; frozen):** detailed governance specification, claim registry, and constrained case study outline.

Appendix A is provided as supplementary material for deeper inspection; the journal narrative is intended to be self-sufficient for first-pass evaluation.

---

## 9. Scope and limits

This manuscript specifies governance behavior under automation rather than introducing domain results: admissibility predicates remain intentionally abstract; the pipeline records both computed and blocked outcomes as canonical locks; and unauthorized comparisons remain blocked (zero-row) rather than being inferred from numerical proximity.

---

## 11. Conclusion

This paper contributes a conservative, failure-resistant execution pattern for scientific comparison pipelines: comparisons are computed only when explicitly authorized, and otherwise the pipeline deterministically produces an auditable refusal. The emphasis is on governance behavior under automation, not on analytical novelty or domain claims.

---

## References (anchoring only)

- Sandve et al., “Ten Simple Rules for Reproducible Computational Research,” *PLOS Computational Biology*, 2013.
- Wilkinson et al., “The FAIR Guiding Principles for scientific data management and stewardship,” *Scientific Data*, 2016.
- Moreau et al., “The PROV Data Model,” W3C Recommendation, 2013.
- Policy-as-code ecosystem reference: Open Policy Agent (OPA) project documentation.
- Di Tommaso et al., “Nextflow enables reproducible computational workflows,” *Nature Biotechnology*, 2017.
- Köster and Rahmann, “Snakemake—a scalable bioinformatics workflow engine,” *Bioinformatics*, 2012.

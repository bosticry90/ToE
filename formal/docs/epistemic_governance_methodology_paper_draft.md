# A Failure-Resistant Scientific Comparison Pipeline

Draft: v0.2 (Sections 1–4; Section 4 is outline-only)

Date: 2026-01-25

Status: COMPLETE (FROZEN)

Freeze declaration (2026-01-25): v0.2 is frozen. No further edits to this document unless correcting a factual/correctness error (typos, broken paths, or scope violations).

## Non-claims (scope guardrails)

This document is **not**:

- A Theory of Everything paper
- A physics unification claim
- A claim of equivalence between any experimental modalities

This document **is**:

- A methodology paper
- An epistemic governance paper
- A reproducibility and failure-resistance paper

Central thesis:

> Scientific comparisons must be explicitly admissible.
> When admissibility is absent, the correct output is a *blocked result*, not a forced claim.

---

## Claim Registry (canonical)

This table is a scope- and interpretation-guardrail: later sections must not introduce claims outside what is enumerated here.

| ID | Statement | Status | Evidence / Enforcement Artifact |
|---:|---|---|---|
| CR-01 | The system can represent “blocked” (not allowed to compare) as a first-class outcome, distinct from “no data” or “mismatch”. | Asserted | `formal/markdown/locks/observables/OV-BR-SND-03_cross_lane_lowk_consistency_audit.md` |
| CR-02 | When required admissibility gates are disabled, gated computations emit **zero comparison rows** (no partial/best-effort evaluation). | Asserted | `formal/markdown/locks/observables/OV-BR-SND-03_cross_lane_lowk_consistency_audit.md` (shows `rows: []` with `status.blocked: true`) |
| CR-03 | Gate enablement intent is declared in Lean; enforcement is performed by a generated manifest consumed by the execution layer. | Asserted | `formal/markdown locks/gates/admissibility_manifest.json` (`origin.path` points to Lean literal; manifest consumed by Python) |
| CR-04 | One-way enablement: disabling is permitted; enabling requires an explicit allow-enable step (preventing “Python-only” silent enablement). | Asserted | `formal/python/tests/tools/update_admissibility_manifest.py` (enforcement) and `formal/markdown locks/gates/admissibility_manifest.json` (enforced state) |
| CR-05 | Deterministic auditability: the enforcement manifest tracks repo-relative sources and content hashes for the intent inputs it depends on. | Asserted | `formal/markdown locks/gates/admissibility_manifest.json` (`origin.sha256`, per-gate `lean_sha256`, `tracked{...}`) |
| CR-06 | Explicit pairing evidence is required before cross-lane comparisons are computed; numerical proximity alone is not treated as evidence of admissible pairing. | Asserted | Governance contract: `formal/external_evidence/bec_bragg_sound_pairing_TBD/ovbr_snd03_bragg_sound_mapping/README.md` and empty mapping: `formal/external_evidence/bec_bragg_sound_pairing_TBD/ovbr_snd03_bragg_sound_mapping/mapping_tuples.json` |
| CR-07 | The existence of gate stubs or manifests implies a physical truth claim about the gated domain. | Explicitly Not Asserted | Scope guardrails in this document (see “Non-claims”) |
| CR-08 | Bragg and sound probe the same physical quantity, or are equivalent/convertible as an interpretation claim. | Explicitly Not Asserted | Scope guardrails in this document (see “Non-claims”) |
| CR-09 | CT01 / SYM01 / CAUS01 are enabled and proven sufficient to authorize the cross-lane comparison. | Deferred | Manifest currently disables all three gates: `formal/markdown locks/gates/admissibility_manifest.json` |
| CR-10 | Any Bragg↔Sound mapping tuples exist (pairings have been justified and entered). | Deferred | Mapping tuples intentionally empty: `formal/external_evidence/bec_bragg_sound_pairing_TBD/ovbr_snd03_bragg_sound_mapping/mapping_tuples.json` |
| CR-11 | This system establishes any external epistemic status (e.g., “empirically anchored”) for a domain claim. | Explicitly Not Asserted | This paper is methodological; external epistemic statuses are out of scope |

---

## 1. Introduction

Modern scientific pipelines frequently *compute comparisons by default*: they merge datasets, align units, calculate residuals, and emit a scalar agreement metric. In practice, this often happens even when the prerequisites for comparison are ambiguous, underspecified, or contested.

The core problem is not a lack of numerical sophistication; it is a lack of **representational capacity** for a critical outcome state:

- **Not allowed to compare (blocked)**.

Many systems can represent:

- “Comparable” (compute a match score)
- “Not comparable” (compute a mismatch score)
- “Missing data” (no score)

But they cannot represent the governance outcome “the comparison is disallowed until specific admissibility conditions are satisfied,” while still remaining deterministic, auditable, and reproducible.

This paper describes a pipeline architecture whose default posture is conservative:

- Comparisons are only computed when an explicit admissibility configuration exists.
- Absent admissibility is surfaced as a first-class result (“blocked”), not silently bypassed.

The contribution is a governance and reproducibility mechanism—not a domain-claim.

---

## 2. Design Principles

### 2.1 Intent vs. enforcement separation

The system separates:

- **Intent**: the authoritative declaration of what gates exist and which are *intended* to be enabled.
- **Enforcement**: a generated, machine-consumable artifact used by the execution layer to decide whether work is permitted.

This prevents informal or accidental changes in the execution layer from being interpreted as a governance decision.

### 2.2 One-way enablement

Enablement is treated as a high-impact action.

- Disabling is always permitted.
- Enabling requires explicit, deliberate invocation (an “allow-enable” step), aligned with the intent layer.

This prevents “Python-only” edits to generated artifacts from silently upgrading governance posture.

### 2.3 Determinism and auditability

Every governance-relevant artifact is designed to be:

- Deterministically regenerated
- Hash-tracked (source files are recorded with content digests)
- Stable under irrelevant changes

This enables the pipeline to support reproducible “why did it run / why did it refuse?” answers.

### 2.4 Absence as a first-class result

The pipeline treats certain absences as meaningful outcomes:

- Missing admissibility → **blocked**
- Missing explicit pairing evidence → **absent / not compared** (even if numbers look close)

This is a governance rule: numerical proximity is never, by itself, evidence of admissible comparability.

---

## 3. System Architecture

The system is organized as three layers plus canonical lock artifacts.

### 3.1 Intent layer (Lean)

The intent layer defines:

- The existence of admissibility gates (as non-claiming interfaces/stubs when proofs are not yet available)
- A repository-declared default enablement intent

Lean is used here as an authoritative, structurally checked source of intent, not as a claim of semantic correctness for the underlying domain.

### 3.2 Governance layer (manifest)

A generated manifest serves as the enforcement artifact consumed downstream.

Properties:

- Repo-relative paths to relevant source-of-intent files
- Content hashes of tracked Lean sources
- A resolved enablement set that the execution layer must honor

Critically, the manifest is not treated as an editable policy surface.

### 3.3 Execution layer (Python)

The execution layer performs deterministic computation conditioned on the manifest.

For gated computations:

- If required gates are disabled, the correct output is a structured **blocked** result.
- When blocked, the system emits **zero comparison rows** (no partial or best-effort evaluation).

### 3.4 Canonical lock artifacts

Lock artifacts are treated as the canonical outputs of the pipeline.

They provide:

- A stable record of computed outputs
- A stable record of governance posture (e.g., blocked vs computed)
- A diff-friendly audit trail for changes across time

(Sections 4+ will present a concrete case study and the failure modes prevented; those are intentionally deferred from this v0.1 draft.)

---

## 4. Case Study (outline only): Sound vs. Bragg low-k comparison

This section is intentionally an outline: it instantiates CR-01 through CR-06 using already-locked artifacts and introduces **no new claims**.

### 4.1 What is being audited (inputs only; no interpretation)

Locked input artifacts referenced by the computed audit record:

- Bragg lane locks:
	- `formal/markdown/locks/observables/OV-BR-02_regime_bridge_record.md`
	- `formal/markdown/locks/observables/OV-BR-03_bragg_dispersion_k_omega_digitized.md`
	- `formal/markdown/locks/observables/OV-BR-04A_bragg_lowk_slope_conditionA.md`
	- `formal/markdown/locks/observables/OV-BR-04B_bragg_lowk_slope_conditionB.md`
- Sound lane locks:
	- `formal/markdown/locks/observables/OV-SND-02_sound_speed_from_propagation.md`
	- `formal/markdown/locks/observables/OV-SND-02B_sound_speed_from_propagation_seriesB.md`

### 4.2 The tempting but invalid “naïve pipeline” (anti-pattern)

Outline of the failure mode this pipeline is designed to prevent:

- Select two numeric summaries from distinct lanes.
- Infer an implicit pairing (“these must correspond”).
- Apply unit conversion heuristics.
- Compute an agreement score.
- Post-hoc justify the pairing using numerical proximity.

(This paper does not claim what the score would be; it claims that producing such a score without admissibility is epistemically invalid.)

### 4.3 What admissibility would need to authorize (constraints only)

This paper does not attempt to prove admissibility; it requires that admissibility be explicit.

Enforcement surfaces:

- Gate enforcement state (manifest): `formal/markdown locks/gates/admissibility_manifest.json`
- Explicit pairing surface (must remain empty absent justification):
	- `formal/external_evidence/bec_bragg_sound_pairing_TBD/ovbr_snd03_bragg_sound_mapping/mapping_tuples.json`
	- `formal/external_evidence/bec_bragg_sound_pairing_TBD/ovbr_snd03_bragg_sound_mapping/README.md`

### 4.4 What this pipeline outputs instead (the formal “no”)

Computed audit lock (the primary evidence artifact for CR-01/CR-02):

- `formal/markdown/locks/observables/OV-BR-SND-03_cross_lane_lowk_consistency_audit.md`

Inspection points (fields to check):

- `status.blocked` is `true`
- `comparability.status` is `blocked`
- `rows` is `[]`

### 4.5 Why it is blocked (traceable governance)

The audit is gated by required admissibility predicates, and must remain blocked while they are disabled.

- Enforcement artifact: `formal/markdown locks/gates/admissibility_manifest.json`
- Updater entrypoint (how the enforcement artifact is produced): `formal/python/tests/tools/update_admissibility_manifest.py`

### 4.6 Why “mapping presence” does not override governance

An explicit mapping surface may exist without authorizing comparison.

- Mapping file exists but is intentionally empty: `formal/external_evidence/bec_bragg_sound_pairing_TBD/ovbr_snd03_bragg_sound_mapping/mapping_tuples.json`
- Governance-only rationale/template: `formal/external_evidence/bec_bragg_sound_pairing_TBD/ovbr_snd03_bragg_sound_mapping/README.md`

### 4.7 Minimal reproducibility recipe (commands only)

This recipe is intended to deterministically reproduce the *refusal* outcome (blocked), not to compute a cross-lane score.

- Update enforcement artifact from intent: `./py.ps1 formal/python/tests/tools/update_admissibility_manifest.py`
- Regenerate canonical locks (lane-specific): `./py.ps1 -m formal.python.tools.regen_canonical_locks --snd-only` and `./py.ps1 -m formal.python.tools.regen_canonical_locks --bragg-only`
- Confirm locked governance invariants: `./py.ps1 -m pytest -q formal/python/tests/test_ov_br_snd03_cross_lane_bridge_audit_lock.py`

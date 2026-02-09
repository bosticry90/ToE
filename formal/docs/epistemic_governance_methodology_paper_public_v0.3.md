# A Failure-Resistant Scientific Comparison Pipeline (Public Note)

Version: v0.3-public (wrapper)
Date: 2026-01-25
Status: DRAFT (public-facing wrapper)

This document is a public-facing wrapper for a frozen technical specification and its enforcement artifacts.
It is intended to be readable without repository context.

Technical Appendix (frozen):
- `formal/docs/epistemic_governance_methodology_paper_draft.md` (v0.2, COMPLETE/FROZEN)

---

## What this is

A methodology and epistemic-governance pattern for scientific computing pipelines:

**If a comparison is not explicitly admissible, the correct output is a structured refusal (“blocked”), not an inferred claim.**

This is about *how* comparisons are governed and executed responsibly—not about proving any domain theory.

## What this is not

This document is **not**:

- a Theory of Everything paper,
- a physics unification claim,
- a claim that any two experimental modalities are equivalent.

It also does **not** claim that any particular admissibility gates are correct or sufficient; it only describes how to enforce the posture “do not compare unless authorized.”

---

## One-sentence contribution

A deterministic pipeline architecture that can output an auditable “no” (blocked) outcome—by design—when admissibility prerequisites are absent.

---

## Positioning relative to prior work

This work sits adjacent to, but is distinct from, several existing lines of practice and research, including reproducible scientific workflows, data provenance systems, policy-as-code frameworks, and computational audit trails.

Reproducible pipelines typically emphasize determinism of execution and repeatability of results. Provenance systems focus on tracking data lineage and transformations. Policy-as-code approaches encode operational constraints that govern system behavior. This pipeline incorporates elements of all three, but addresses a narrower and often under-specified question: **how a scientific system should behave when a comparison is not epistemically authorized**.

Rather than attempting to improve comparison metrics, infer equivalence, or resolve interpretive uncertainty, the system described here enforces a conservative governance posture: absent explicit admissibility, the system must refuse to compare and must record that refusal deterministically. The contribution is therefore not a new analytical method, but a failure-resistant execution pattern that **preserves epistemic boundaries even under automation**.

---

## The core idea (plain language)

Many analysis pipelines will compute *something* as soon as numbers exist, even if the justification for comparing them is weak or missing.

This pipeline enforces the opposite posture:

- Comparisons are computed **only** when they are explicitly authorized by an admissibility configuration.
- If authorization is absent, the pipeline emits a **blocked** outcome with explicit blockers.
- “Numeric closeness” is never treated as a substitute for admissibility.

---

## Architecture at a glance

```

Intent (Lean-authored) ──► Enforcement Manifest (JSON) ──► Execution (Python) ──► Canonical Locks
|                          |                              |                    |
declares gates +             tracks repo paths +           computes only         records either
default enablement              content hashes             if authorized      BLOCKED or COMPUTED

```

Key property: the manifest is an enforcement artifact, not a policy surface.

---

## Evidence artifacts (what you can inspect)

Blocked comparison (example audit record):

- `formal/markdown/locks/observables/OV-BR-SND-03_cross_lane_lowk_consistency_audit.md`

Enforcement manifest:

- `formal/markdown locks/gates/admissibility_manifest.json`

Manifest updater (enforcement point, not the JSON file):

- `formal/python/tests/tools/update_admissibility_manifest.py`

Explicit pairing surface (exists but can remain empty without forcing a comparison):

- `formal/external_evidence/bec_bragg_sound_pairing_TBD/ovbr_snd03_bragg_sound_mapping/README.md`
- `formal/external_evidence/bec_bragg_sound_pairing_TBD/ovbr_snd03_bragg_sound_mapping/mapping_tuples.json`

---

## Common reviewer misreadings (pre-emptive clarifications)

1) “You’re claiming Bragg↔Sound equivalence.”

- No. The only concrete referenced audit artifact is blocked and produces zero rows.

2) “Blocked means you failed to implement the comparison.”

- No. Blocked is a first-class, intentionally enforced outcome of the pipeline. The lock records `rows: []` by design.

3) “Lean proves the physics / gates are active.”

- No. Gates are disabled by default in the manifest. Lean is used for intent declaration, not domain truth claims here.

4) “You can just edit the JSON to enable things.”

- Not by policy. The updater is the enforcement surface; enabling requires an explicit allow-enable step.

5) “Surely numeric closeness implies pairing.”

- Not in this governance model. Pairing evidence must be explicit, and the mapping surface can remain empty without forcing a comparison.

---

## Minimal reproducibility recipe (reproduces the refusal)

Goal: deterministically reproduce the **blocked** outcome (not compute a cross-lane score).

1) Update the enforcement manifest:

- `./py.ps1 formal/python/tests/tools/update_admissibility_manifest.py`

2) Regenerate canonical locks for existing lanes:

- `./py.ps1 -m formal.python.tools.regen_canonical_locks --snd-only`
- `./py.ps1 -m formal.python.tools.regen_canonical_locks --bragg-only`

3) Confirm the invariant in the audit lock:

- `./py.ps1 -m pytest -q formal/python/tests/test_ov_br_snd03_cross_lane_bridge_audit_lock.py`

Expected result:

- `OV-BR-SND-03_cross_lane_lowk_consistency_audit.md` remains blocked and emits zero rows.

---

## Where the full technical specification lives

For the complete claim registry, the constrained case study outline, and the frozen scope rules, see:

- `formal/docs/epistemic_governance_methodology_paper_draft.md` (v0.2, COMPLETE/FROZEN)

Edits to that document are restricted to factual/correctness fixes only.

---

## Alternative approaches you could choose instead

1. Publish only v0.2 as-is

   Works for a highly technical audience already familiar with lock-based governance, but likely to be misread by general reviewers.

2. Convert v0.2 into a full narrative paper

   Not compatible with the freeze posture unless you create a v0.3 rewrite (not a wrapper).

3. Wrapper + frozen appendix (recommended)

   Best balance: public readability + strong non-claim posture + reproducibility.

---

Next checkpoint (optional): pause and treat v0.3 wrapper as content-stable.

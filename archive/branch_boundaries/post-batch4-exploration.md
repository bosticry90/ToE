# Branch Boundary: post-batch4-exploration (policy)

Date: 2026-01-25

Purpose: establish a clean conceptual boundary after Batch 4 and the frozen methodology paper.

Note: This workspace is not a git repository, so this file records the intended branch policy.
If/when this repo is under git, create a branch named `post-batch4-exploration` and keep this policy as the branch README.

## Hard rules

- No changes to Batch 4 artifacts.
- No changes to the frozen methodology paper.

Concretely, do not edit:

- `formal/docs/epistemic_governance_methodology_paper_draft.md` (v0.2 COMPLETE/FROZEN)
- `formal/markdown locks/gates/admissibility_manifest.json`
- `formal/markdown/locks/observables/OV-BR-SND-03_cross_lane_lowk_consistency_audit.md`
- `formal/external_evidence/bec_bragg_sound_pairing_TBD/ovbr_snd03_bragg_sound_mapping/mapping_tuples.json`

## Allowed new work

All new work must be explicitly one of:

A) Gate semantics development (Lean) without enabling gates, or
B) Pairing evidence authoring (mapping tuples) while gates remain disabled, or
C) A new independent lane (Axis C) that reuses the governance machinery.

Do not mix axes within the same batch of work.

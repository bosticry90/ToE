# Public Submission AI Hygiene Standard v0

Document ID:
- `PUBLIC_SUBMISSION_AI_HYGIENE_STANDARD_v0`

Prepared target:
- `prepare_nonclaim_benchmark_intake_and_public_submission_hygiene_tranche`

Outcome token:
- `NONCLAIM_BENCHMARK_INTAKE_AND_PUBLIC_SUBMISSION_HYGIENE_TRANCHE_PREPARED_WITH_NO_THEOREM_DISCHARGE_OR_PROMOTION`

Status:
- `PUBLIC_SUBMISSION_AI_HYGIENE_STANDARD_STATUS_v0: PREPARED_NONCLAIM`

Purpose:
- Define release-facing hygiene requirements for AI-assisted public-submission surfaces.
- Prevent unchecked AI artifacts, unverifiable citations, unclassified equations, and unsupported promotion language from entering public-facing materials.
- Govern the new external benchmark intake artifacts before they are treated as roadmap context.

Scope:
- `README.md`
- `State_of_the_Theory.md`
- `formal/docs/paper/PHYSICS_ROADMAP_v0.md`
- `formal/docs/release/TOE_V01_ALPHA_CLAIM_EVIDENCE_LEDGER_v0.json`
- `formal/docs/release/TOE_V01_ALPHA_EQUATION_LEDGER_v0.json`
- `formal/docs/release/TOE_V01_ALPHA_BLOCKER_LEDGER_v0.json`
- `formal/docs/submission/scalar_paper1/**/*.{md,tex,bib,json}`

Non-claim boundary:
- This standard is a publication-hygiene control surface only.
- It does not discharge theorem gaps.
- It does not validate the candidate master action.
- It does not close seams.
- It does not promote pillar status.
- It does not claim empirical adequacy.
- It does not change `CURRENT_LIVE_NEXT_TARGET_v0`.

Binding policy sentence:
- External science inputs may create benchmark pressure, caution notes, or future target categories, but they do not discharge theorem gaps, validate the master action, close seams, or promote ToE status without repo-local proof objects and verified primary sources.

Required hygiene rules:
- No public-facing submission surface may contain leftover AI meta-commentary.
- No public-facing submission surface may contain fake citation placeholders or unverifiable citation markers.
- No equation may be presented as derived unless the release equation ledger or a cited theorem surface classifies it.
- No external source may be used as ToE evidence unless a later governed route supplies repo-local proof objects and verified primary sources.
- No reviewed external benchmark may authorize master-action promotion, pillar completion, seam closure, Phase 2 readiness, empirical adequacy, canonical ToE status, or QFT-GR source-map closure.

Forbidden promotion flags:
- `master_action_promotion_authorized`
- `pillar_completion_inferred`
- `seam_closure_claim`
- `phase2_readiness_claim`
- `empirical_adequacy_claim`
- `canonical_toe_claim`
- `qft_gr_source_map_closure_authorized`

Allowed role for AI assistance:
- AI may assist with drafting, review, source discovery, formatting, and implementation planning.
- AI output is not authority.
- Public-facing material remains governed by repo artifacts, human-verifiable sources, Lean/test gates, and explicit nonclaim boundaries.

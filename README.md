README.md
A Formal Research Hypothesis Toward a Unified Physical Framework

PROJECT STATUS (2026-03-15)
Tooling is frozen except for bugfixes that preserve existing contracts.
Current work is in the discriminative science phase: evidence-only runs, candidate pruning, and inventory updates.
Governance status is TERMINAL_SATISFIED_v0_NONCLAIM under pinned policy scope.
Physics status is MIXED_PROGRESS_v0 with seam-level physics closure still incomplete.
This is NOT a physics-complete ToE claim.

PHYSICS-FIRST EXECUTION POLICY CHECKPOINT (WS-10-T07B, 2026-03-26)
- Physics-closure blockers are prioritized ahead of governance expansion work.
- Governance remains active as a strict enabling lane for parity, safety, and non-claim boundary integrity.
- Release-gate truth remains unchanged: governance prerequisite plus full pytest branch-health.
- Policy artifact: `formal/docs/release/WS_10_T07B_PHYSICS_FIRST_EXECUTION_POLICY_v0.md`.

STATE-CORE GENERATED-FIRST CUTOVER (2026-03-26)
- Canonical control-plane edit path for migrated WS families is generated-first.
- Canonical steps:
   1) Edit `formal/docs/release/state_core_v0.json`.
   2) Run `./py.ps1 -m formal.python.tools.render_state_core_mirrors --apply-mirrors --verify-mirrors`.
   3) Run `pwsh -NoProfile -ExecutionPolicy Bypass -File ./governance_suite.ps1`.
- Post-tranche safety ladder (exact order, restores generated outputs at the end):
   - `pwsh -NoProfile -ExecutionPolicy Bypass -File ./checkpoint_ladder.ps1`
   - Acceptance requires the runner to finish green **and** leave `git status --short` empty after auto-restore.
- Direct human edits inside `<!-- GENERATED: ... -->` mirror blocks are prohibited.
- Cutover policy artifact: `formal/docs/release/STATE_CORE_GENERATED_FIRST_CUTOVER_POLICY_v0.md`.

RELEASE-GATE POLICY (R1-A, 2026-03-20)
- Governance is the prerequisite lane for release readiness.
- Full pytest is the authoritative branch-health lane.
- A branch is release-gate ready only when both lanes are green.
- Governance lane command: `pwsh -NoProfile -ExecutionPolicy Bypass -File ./governance_suite.ps1`
- Branch-health lane command: `./py.ps1 -m pytest formal/python/tests -q`

CI TRUTH CONTRACT (R5-A, 2026-03-20)
- CI represents governance, full pytest branch-health, and Lean build as explicit lanes in `.github/workflows/ci.yml`.
- Governance remains a prerequisite lane before downstream CI lanes execute.
- Lean lane target is the authoritative Lean project at `formal/toe_formal`.

R6 CONSOLIDATION CHECKPOINT (R6-CLOSEOUT, 2026-03-20)
- Post-truth duplicate-family consolidation is complete for three bounded families.
- Consolidated helper families:
   - `formal/python/tests/cosmo_nonflip_gate_family_helper.py` (COSMO micro21-27 nonflip)
   - `formal/python/tests/sr_m5_cycle_gate_family_helper.py` (SR M5 cycle50-56)
   - `formal/python/tests/qft_evidence_diversification_cycle_gate_family_helper.py` (QFT evidence-diversification cycle02-08)
- All three bounded family subsets were green at consolidation time and retained original gate file paths.
- Consolidation boundary decision: stop at R6 closeout and require explicit authorization before any additional family reduction slice.

Purpose of This Project
This project is an honest attempt to explore whether a very simple idea can be pushed far enough to matter.
The long-term aspiration is to understand whether a single underlying structure could, in principle, support or organize the many laws we use to describe the universe. This aspiration is often called a Theory of Everything.
That is not a claim. It is a direction.
Right now, this project is a formal research hypothesis and an emerging mathematical framework, nothing more.
The immediate goal is not truth, correctness, or unification.
The immediate goal is clarity.

What This Project Is (Right Now)
 A disciplined investigation into whether a consistency-driven field idea can exist without collapsing.
 A test of whether simple rules can generate meaningful structure on their own.
 A sandbox where ideas are allowed to fail cleanly.
This project does not assert:
 that it describes reality,
 that it replaces existing physics,
 or that it is correct.

The Core Research Question
Is it possible to define a simple, internally consistent system whose rules naturally generate structured behavior, without relying on arbitrary fixes or assumptions?
If the answer is no, that is a real and valuable result.

Falsification Criteria
(How This Project Can Fail)
This project is considered rejected if any of the following are true.

1. The idea cannot be clearly stated
   If the basic objects, rules, or behaviors cannot be written down clearly without contradictions or circular reasoning, the hypothesis fails.
   If I cant say what the system is in a clean way, it isnt viable.
2. The rules break themselves
   If every reasonable attempt to define the system leads to instability, undefined behavior, or logical collapse, the hypothesis fails.
   Rules that destroy themselves are not foundations.
3. Nothing meaningful ever emerges
   If the system only produces trivial, frozen, or empty behaviorand never generates patterns, structure, or organizationthe hypothesis fails.
   A foundation that explains nothing explains too much.
4. The system only works when forced
   If structure only appears after heavy tuning, constant patching, or adding rules just to save the idea, the hypothesis fails.
   A foundational idea must work naturally, not by coercion.
5. Complexity grows without bound
   If the idea can only survive by becoming increasingly complex, ad hoc, or special-case-driven, the hypothesis fails its core promise.
   A foundation should simplify, not endlessly grow.
6. Language drift collapses scope boundaries
   If status summaries use COMPLETE, CLOSED, or DISCHARGED without layer qualifiers or bounded-scope framing, the hypothesis framing fails.
   Governance rigor is a claim about process quality, not a claim of global physics adequacy.

Formal Predictions
(What Must Be True If the Idea Is Worth Continuing)
If the hypothesis is viable, the following should naturally occur.

1. The system must be usable
   The rules should be followable step by step, producing outcomes that make sense internally.
   I should be able to run the idea without it breaking.
2. Structure should emerge on its own
   The system should naturally generate patterns, stable forms, or organized behavior without being told exactly what to produce.
   The idea should surprise me.
3. The system should not be fragile
   Small changes to starting conditions should not destroy all structure.
   A serious idea should tolerate imperfection.
4. The same rules should apply broadly
   The same basic setup should work across many situations, not just one carefully constructed example.
   A foundation should generalize.

These are internal predictions, not claims about the real universe.

Minimal Axiom Set
(What Is Allowed to Be Assumed)
This project assumes as little as possible.
Axiom 1  There is something to describe
There exists a space and something that varies within it.
There is a thing, and it can change.

Running the Formal Python Modules
Some of the verification and bridge code lives under formal/python and is exercised via pytest.
To avoid ambiguity between system Python and your venv Python on Windows, prefer running everything through the repo-local PowerShell wrapper script:

- Run tests: `./py.ps1 -m pytest -q`
- Run tooling validation (non-mutating): `pwsh -NoProfile -ExecutionPolicy Bypass -File ./tooling_validate.ps1`
- Run explicit canonical regeneration: `pwsh -NoProfile -ExecutionPolicy Bypass -File ./tooling_regen.ps1`
- Lint mapping tuples: `./py.ps1 -m formal.python.tools.lint_mapping_tuples --fail-fast`

Troubleshooting (Windows)
- If `powershell` is not recognized, you are likely already in PowerShell 7 (`pwsh`). Just run `./py.ps1 ...` directly from your current session.

Local Stack Preflight (Python + Rust)
- Run preflight: `./py.ps1 -m formal.python.tools.dev_stack_preflight`
- Require local Rust for trust-core work: `./py.ps1 -m formal.python.tools.dev_stack_preflight --require-rust`
- If Rust is missing locally, trust-core checks in CI remain blocking. To install locally on Windows:
   - `winget install Rustlang.Rustup`
   - Restart terminal and verify: `cargo --version`

To run modules outside pytest without relying on implicit sys.path behavior, prefer module invocation from the repo root:

`./py.ps1 -m formal.python.toe.bridges.br01_dispersion_to_metric`

Optional quality-of-life (PowerShell):
- `Set-Alias py .\py.ps1` then use `py -m pytest -q`.

If you want imports like formal.python.* to work from arbitrary working directories in development, consider an editable install (`pip install -e .`) once a top-level packaging config is added.

Axiom 2  The system follows rules
The system is lawful, not arbitrary.
Behavior follows rules, not whim.

Axiom 3  Consistency matters
Some behaviors are more coherent or stable than others, and the system reflects this.
Not everything is equally allowed.

Axiom 4  Simplicity is enforced
No assumptions are added solely to rescue the idea.
The idea must stand on its own.

Axiom 5  Interpretation comes last
No assumptions are made about particles, forces, spacetime, or reality itself.
Structure first. Meaning later.

What Success Means (At This Stage)
Success does not mean:
 discovering truth,
 explaining the universe,
 or achieving unification.
Success means:
 the idea survives its own logic,
 its limits are clearly understood,
 and its failures are honest.
If the hypothesis fails, the project still succeeds by producing clarity.

Ownership and Intent
This is my project.
It is guided by:
 curiosity,
 ambition,
 discipline,
 and honesty.
The scientific method is used as a guardrail, not a constraint on creativity.
Ideas are allowed to fail, but not to hide.

One Guiding Sentence
I am testing whether my idea makes sense before asking whether it is true.

All formal documents use UTF-8 plain text with minimal Markdown.

This README is the constitution of the project.
All future work must respect it.


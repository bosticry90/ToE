### Baseline stash
Stash created: "baseline stash before housekeeping verification"
Working tree after stash: clean (git status -sb shows only branch line)
### Baseline verification after Python fix
Lean (lake build): PASS
Python (crft_c6_cp_nlse_2d_dispersion): PASS
Commit: 7424ed1  (fix(python): stabilize 2D CP–NLSE API for C6 dispersion test)
Notes:
- Grid2D.x/y confirmed 2D mesh shape (Nx, Ny) after reload.
## Batch 1 — Docs + locks consolidation
Verification:
- Lean (lake build): PASS
- Python (crft_c6_cp_nlse_2d_dispersion): PASS

Commit: a4e08e3  (chore(docs): consolidate locks, registry, and dev notes)
Moves:
- LOCK_NEURO_SYMBOLIC.md -> docs/locks/LOCK_NEURO_SYMBOLIC.md
- field_theory/docs/dev_notes/Powershell CMDs.txt -> docs/dev_notes/Powershell CMDs.txt
## Batch 2 — Line endings policy
Verification:
- Lean (lake build): PASS
- Python (crft_c6_cp_nlse_2d_dispersion): PASS

Commit: <paste short hash>  (chore(repo): add gitattributes to control line endings)
Notes:
- Policy-only change; no renormalization performed.
## Batch 3 — Archive boundary (minimal)
Actions:
- Added archive/README.md (boundary clarification only; no moves)

Verification:
- Lean (lake build): PASS
- Python (crft_c6_cp_nlse_2d_dispersion): PASS

Commit: <paste short hash>  (chore(repo): add archive boundary README)

## Batch 4 — Lean gate stubs + manifest governance

Actions:
- Added non-claiming Lean gate stubs (CT01/SYM01/CAUS01) and a single import surface.
- Implemented deterministic Lean→manifest tracking (lean relpaths + sha256) and a one-way enablement policy: Python updater refuses false→true without explicit `--allow-enable`.
- Hardened OV-BR-SND-03 posture: while admissibility gates are disabled, record remains `blocked` with `rows: []` regardless of pairing mapping contents.
- Added/updated policy + regression tests covering the above.

Verification:
- Lean (lake build): PASS
- Python (focused pytest): PASS
- Repo tooling smoke: PASS

Commit: <not yet committed>

Freeze declaration (2026-01-25): BATCH 4 FROZEN

State guarantees (locked):
- Lean gates: present, disabled-by-default, Lean-authored intent.
- Manifest: enforcement-only, one-way enablement, audited.
- OV-BR-SND-03: deterministically blocked, emits zero rows.
- OV-BR-SND-03 mapping tuples: empty, non-claiming, ignored while gates disabled.

Scope rule:
- No further changes to this batch unless a correctness bug is discovered.

Documentation milestone (2026-01-25): methodology paper v0.2 COMPLETE (FROZEN)

- Draft: `formal/docs/epistemic_governance_methodology_paper_draft.md`
- Scope: methodology / governance only; includes canonical claim registry + outline-only case study anchored to blocked artifacts.

2026-01-27 - GREEN INVARIANT CHECKPOINT: regen_canonical_locks --bragg-only exit=0; pytest -q => 255 passed, 1 skipped (expected: test_regen_canonical_locks_rejects_conflicting_lane_flags.py:80: --snd-digitization-only not present in regen CLI)

2026-01-27 - GREEN INVARIANT CHECKPOINT: added OV-BR-FN-00/01 stage; regen_canonical_locks --bragg-only exit=0; pytest -q => 260 passed, 1 skipped (expected: test_regen_canonical_locks_rejects_conflicting_lane_flags.py:80: --snd-digitization-only not present in regen CLI)

2026-01-27 - GREEN INVARIANT CHECKPOINT: regen_canonical_locks --bragg-only exit=0; regen_canonical_locks --bragg-only --admissibility-manifest formal/markdown locks/gates/admissibility_manifest_ENABLED_OVERRIDE.json exit=0; focused pytest (OV-BR-FN-00/01 + override manifest true/false + regen bragg-only) => 7 passed; pytest -q => 261 passed, 1 skipped (expected: test_regen_canonical_locks_rejects_conflicting_lane_flags.py:80: --snd-digitization-only not present in regen CLI)

2026-01-27 - GREEN INVARIANT CHECKPOINT: advanced downstream consumer (OV-FN-WT-00/01 stage); regen_canonical_locks --bragg-only exit=0; regen_canonical_locks --bragg-only --admissibility-manifest formal/markdown locks/gates/admissibility_manifest_ENABLED_OVERRIDE.json exit=0; focused pytest (OV-FN-WT-00/01 default+override) => 3 passed; pytest -q => 264 passed, 1 skipped (expected: test_regen_canonical_locks_rejects_conflicting_lane_flags.py:80: --snd-digitization-only not present in regen CLI)

2026-01-27 - GREEN INVARIANT CHECKPOINT: added OV-FN-WT-02 (selected policy) + OV-FN-02 (weighted residual audit); regen_canonical_locks --bragg-only exit=0; regen_canonical_locks --bragg-only --admissibility-manifest formal/markdown locks/gates/admissibility_manifest_ENABLED_OVERRIDE.json exit=0; pytest -q => 267 passed, 1 skipped (expected: test_regen_canonical_locks_rejects_conflicting_lane_flags.py:80: --snd-digitization-only not present in regen CLI)

2026-02-01 - GREEN INVARIANT CHECKPOINT: added pytest guard forbidding `import archive` / `from archive` outside quarantine; acoustic metric reintegration resolved by adopting existing MT-01a Python front door + lock regression (formal/python/crft/acoustic_metric.py; formal/python/tests/test_mt01_acoustic_metric_lock.py); removed redundant duplicate port/test attempt (deleted formal/python/toe/diagnostics/acoustic_metric.py, formal/python/toe/diagnostics/__init__.py, formal/python/tests/test_acoustic_metric.py); updated Legacy_Reintegration_Register.md to mark as already present; pytest -q => 325 passed, 1 skipped (expected: test_regen_canonical_locks_rejects_conflicting_lane_flags.py:80: --snd-digitization-only not present in regen CLI)

2026-02-01 - GREEN INVARIANT CHECKPOINT (2): strengthened archive quarantine with root-level import trap (archive.py) + additional enforcement tests (import failure, sys.path, pytest.ini norecursedirs, bounded-depth __init__.py scan, and tool allowlist for archive path references) + stricter sys.path ordering guard (repo root precedence enforced in tests/conftest.py); pytest -q => 331 passed, 1 skipped (expected: test_regen_canonical_locks_rejects_conflicting_lane_flags.py:80: --snd-digitization-only not present in regen CLI)

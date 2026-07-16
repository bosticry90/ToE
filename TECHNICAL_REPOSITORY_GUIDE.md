# Technical Repository Guide

**Snapshot:** 2026-07-16  
**Purpose:** a compact map for reviewers and contributors

This guide explains how to navigate and validate the repository. It is not a
scientific authority surface and does not replace a dated result review.

## Repository architecture

| Path | Role |
| --- | --- |
| `formal/toe_formal/` | Lean 4 project, theorem objects, derivation aggregates, and release-facing formal bindings |
| `formal/python/tools/` | Deterministic packet builders, validators, reviewers, and numerical executors |
| `formal/python/tests/` | Focused and integration pytest coverage |
| `formal/docs/release/` | Versioned preparation packets, executions, result reviews, policies, and authority records |
| `formal/docs/paper/` | Human-readable paper and pillar summaries |
| `formal/output/` | Generated reports, manifests, architecture records, and canonical numerical outputs |
| `formal/external_evidence/` | External datasets, source citations, and comparator evidence |
| `formal/markdown/` and `formal/markdown locks/` | Working and locked mathematical specifications |
| `formal/rust/toe_trust_core/` | Optional Rust trust-core checks |
| `DEVELOPMENT.md` | Compact environment and validation instructions |
| `README.md` and `State_of_the_Theory.md` | Large append-only status/history surfaces |
| `archive/`, `backup/`, `scratch/` | Historical, recovery, and work-product material; not current authority by default |

Most tracked files live under `formal/`. Do not infer current scientific status
from a filename, a historical packet, or an output file in isolation.

## Authority and evidence order

For a current technical review, read these surfaces together:

1. `formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json`, especially its current
   projection contract and uppercase `CURRENT_LIVE_*` tokens;
2. `formal/docs/release/CURRENT_AUTHORITATIVE_SURFACES_v0.md`;
3. `formal/toe_formal/ToeFormal/Derivation/CurrentTarget.lean` and
   `formal/toe_formal/ToeFormal/Release/CurrentAuthority.lean` for the thin
   machine-checked current-target mirrors;
4. the selected release packet, execution record, and independent result review;
5. the hashes/manifests and canonical outputs bound by that review.

If surfaces disagree, stop at the lower claim. Do not infer a target rotation,
promotion, or scientific result from a newer timestamp alone.

## Toolchain

- Windows PowerShell is the canonical local shell.
- CPython 3.10 is the documented Python baseline.
- Python dependencies are pinned in `requirements.ci.lock` and
  `requirements.active.lock`.
- The Lean project pins `leanprover/lean4:v4.27.0-rc1` in
  `formal/toe_formal/lean-toolchain`.
- Rust/Cargo is optional and scoped to `formal/rust/toe_trust_core`.
- Long Windows paths are required because many versioned evidence filenames are
  intentionally descriptive.

## Bootstrap

From the repository root:

```powershell
git config core.longpaths true
python -m venv .venv
.\.venv\Scripts\python.exe -m pip install --upgrade pip==26.0
.\.venv\Scripts\python.exe -m pip install -r requirements.ci.lock
```

Use the pinned `formal/toe_formal/lake-manifest.json` for normal Lean
restoration. Do not run `lake update` unless dependency refresh is the explicit
task.

## Validation tiers

Start with the narrowest check that matches the change.

### 1. Focused Python or packet validation

```powershell
.\py.ps1 -m pytest -q path\to\focused_test.py
.\py.ps1 -m formal.python.tools.some_validator --check
```

Locate Maxwell–Dirac and robustness checks with:

```powershell
rg --files formal/python/tests | rg -i "dirac_maxwell|robustness"
rg --files formal/python/tools | rg -i "dirac_maxwell|robustness"
```

### 2. Current authority and Lean target checks

```powershell
.\py.ps1 -m formal.python.tools.loop_control_registry_integrity --check
.\run_lean.ps1 -Target ToeFormal.Derivation.CurrentTarget
.\run_lean.ps1 -Target ToeFormal.Release.CurrentAuthority
```

### 3. Full Python suite

```powershell
.\py.ps1 -m pytest -q -p no:cacheprovider formal/python/tests
```

### 4. Exhaustive Lean aggregate

```powershell
.\py.ps1 -m formal.python.tools.generate_lean_all_modules_aggregate --check
.\py.ps1 -m formal.python.tools.lean_bounded_lake --jobs 1 --target ToeFormal --target ToeFormalAll
```

The bounded Lake wrapper is the repository-standard exhaustive path. A timeout
is not a pass or a failure, and a focused pass is not a repository-wide green
claim. The optional Rust check is:

```powershell
cargo check --locked --manifest-path formal/rust/toe_trust_core/Cargo.toml
```

## Working with versioned evidence

- Treat accepted packets, execution records, reviews, manifests, snapshots, and
  canonical output trees as immutable evidence.
- Correct an error with a versioned successor; do not silently normalize or
  regenerate historical bytes.
- Keep preparation, execution, and independent review as distinct stages.
- Bind claims to exact artifacts and preserve explicit nonclaims.
- Do not exclude a failed run after execution unless a pre-existing rule and a
  separately authorized review permit it.
- Prefer `--check` modes for read-only verification.
- Keep cache cleanup separate from evidence changes. `.pytest_cache`, Python
  `__pycache__`, and Rust `target` are rebuildable; Lean package restoration can
  be expensive.

## Review checklist

Before accepting a technical change, verify:

- the selected target and authority surfaces agree;
- every input and output path exists and is uniquely identified;
- generated artifacts reproduce without changing frozen evidence;
- negative controls fail for the intended reason;
- tolerances and classifiers were frozen before execution;
- the result review states both a maximum claim and nonclaims;
- focused tests and Lean targets were run at the scope being reported; and
- unrelated working-tree changes were not overwritten or included.

## Public-repository gaps

At this snapshot the repository has no root license, citation file,
contribution guide, or security policy. Those are governance choices and should
not be invented from technical context. Add owner-approved versions before a
general open-source release.

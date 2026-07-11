# ToE repository development

This is the compact operational entry point. It does not supersede scientific
authority. Read the live target from
`formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json` (`current_projection_v0` and
the uppercase `CURRENT_LIVE_*` tokens), then confirm the human-facing boundary
in `formal/docs/release/CURRENT_AUTHORITATIVE_SURFACES_v0.md`.

The separate non-scientific maintenance authority is
`formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_v0.json`. Its registry-
sharding target does not displace or rotate the scientific target.

The v0 registry-sharding contract is preparation evidence, not migration
authority. Its independent review rejects execution readiness and recommends a
versioned v1 corrective guardrail without selecting it. Registry migration and
both target rotations therefore remain unauthorized.

## Prerequisites

- Windows 10/11 with PowerShell 7 for the canonical local workflow.
- Git with `core.longpaths=true`.
- CPython 3.10.
- Elan/Lean; the project selects its exact toolchain through
  `formal/toe_formal/lean-toolchain`.
- Rust/Cargo only for the optional `formal/rust/toe_trust_core` check.

## Bootstrap

From the repository root:

```powershell
git config core.longpaths true
python -m venv .venv
.\.venv\Scripts\python.exe -m pip install --upgrade pip==26.0
.\.venv\Scripts\python.exe -m pip install -r requirements.ci.lock
```

Normal Lean restoration uses the pinned `lake-manifest.json`. Do not run
`lake update` unless the task is an intentional dependency-refresh tranche.

## Canonical read-only validation

```powershell
.\py.ps1 -m formal.python.tools.loop_control_registry_integrity --check
.\py.ps1 -m formal.python.tools.loop_control_registry_sharding_guardrail --check
.\py.ps1 -m formal.python.tools.loop_control_registry_sharding_guardrail_independent_review --check
.\py.ps1 -m formal.python.tools.generate_lean_all_modules_aggregate --check
.\py.ps1 -m pytest -q -p no:cacheprovider formal/python/tests
.\py.ps1 -m formal.python.tools.lean_bounded_lake --jobs 1 --target ToeFormal --target ToeFormalAll
```

Focused current-authority Lean checks remain available through:

```powershell
.\run_lean.ps1 -Target ToeFormal.Derivation.CurrentTarget
.\run_lean.ps1 -Target ToeFormal.Release.CurrentAuthority
.\run_lean.ps1 -Target ToeFormal.Derivation.CrossPillarClosureFrontier
```

Optional Rust verification:

```powershell
cargo check --locked --manifest-path formal/rust/toe_trust_core/Cargo.toml
```

## Preservation rules

- One immutable scientific tranche should end at one Git checkpoint before its
  independent review begins.
- Do not regenerate, normalize, or bulk-rewrite frozen result, manifest,
  execution-report, review, snapshot, or release-artifact trees.
- Versioned correction records amend effective posture without rewriting
  historical checkpoint bytes.
- A passing test or Lean build establishes only its stated scope. It does not
  authorize theorem discharge, source-map closure, seam or pillar closure,
  release/publication, empirical validation, or master-action promotion.
- Use the memory-bounded Lake wrapper for the exhaustive aggregate. A direct
  unbounded Lake invocation is intentionally not the canonical path.

## Local cache policy

Safe rebuildable cleanup candidates include `.pytest_cache`, Python
`__pycache__`, and `formal/rust/toe_trust_core/target`. Retain
`formal/toe_formal/.lake/packages` unless the cost of a network restore is
acceptable. The `.lake/build` tree is rebuildable but expensive; prune it only
after recording a successful validation when disk pressure justifies the cost.

The 52.341 MB decimal (49.916 MiB) loop-control registry and the tooling snapshots are excluded from VS
Code watching/search through `.vscode/settings.json`; they remain tracked and
available to targeted tools and Git.

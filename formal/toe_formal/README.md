# ToeFormal development guide

This directory contains the Lean formalization used by the ToE repository. The pinned toolchain is declared in `lean-toolchain`; package revisions are declared in `lake-manifest.json`.

## Setup

From the repository root on Windows:

```powershell
git config core.longpaths true
cd formal\toe_formal
lake build
```

`lake build` restores and builds the manifest-pinned dependency graph when packages are absent. Reserve `lake update` for an intentional dependency-refresh tranche because it can rewrite `lake-manifest.json`.

## Validation

The historical default aggregate remains:

```powershell
cd formal\toe_formal
lake build
```

The exhaustive tracked-module validation root is generated and checked with:

```powershell
.\py.ps1 -m formal.python.tools.generate_lean_all_modules_aggregate --check
.\py.ps1 -m formal.python.tools.lean_bounded_lake --jobs 1 --target ToeFormal --target ToeFormalAll
```

Focused current-authority checks can be run from the repository root:

```powershell
.\run_lean.ps1 -Target ToeFormal.Derivation.CurrentTarget
.\run_lean.ps1 -Target ToeFormal.Release.CurrentAuthority
.\run_lean.ps1 -Target ToeFormal.Derivation.CrossPillarClosureFrontier
```

A successful Lean build proves only that the selected modules typecheck under their declared assumptions. It does not discharge retained axioms, validate empirical physics, close a pillar or seam, authorize a release, or promote the candidate master action.

## Cache and provenance policy

- `.lake/build` is a rebuildable local cache.
- `.lake/packages` is reconstructable from `lake-manifest.json`, but restoration is expensive and may require network access.
- Do not edit generated `.olean` files.
- Do not treat tracked release certificates as disposable build output.
- Use `ToeFormalAll.lean` to detect tracked modules that would otherwise sit outside the default aggregate.

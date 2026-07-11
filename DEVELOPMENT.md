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

The corrective v1 guardrail is now prepared for independent review. It freezes
canonical projection/history contracts plus separate byte-exact custody,
external committed trust anchors, strict typed controls, and static consumer
classification. No production migration component or authority change exists.
Independent review accepts v1 only as a preparation guardrail. Executable
closed schemas/controls, runtime shadow coverage, custody payload creation, and
migration execution remain separate open obligations and are unauthorized.

The execution-readiness preparation packet freezes ten closed schemas and the
future validator, four-profile control harness, shadow tracing, byte-custody,
prototype-path, rollback, and readiness contracts. It installs or executes none
of them. Independent review is still required; the current maintenance and
scientific targets remain unchanged and migration execution remains false.
The v0 independent review rejects contract acceptance after demonstrating
profile-composition, payload-custody, repository-path, and report-invariant
false acceptances. V0 remains historical preparation evidence only; a
versioned corrective successor is required before prototype selection.
Corrective v1 preserves the rejected v0 bytes and freezes exact ordered
validator closures, strict payload semantics, resolved root-relative paths,
success-report invariants, and eight permanent readiness regressions. It still
requires independent review and authorizes no prototype or migration work.
Independent v1 review rejects preparation-contract acceptance after finding
remaining validator-interface, path-profile, regression-matrix, identity-byte,
and result-schema defects. V1 is historical corrective evidence only; v2 is
required before a preparation contract can be accepted.
Corrective v2 separates repository and prototype path types, shares one issue
schema across the validator and reports, freezes atomic readiness mutations and
error precedence, completes record/root byte algorithms, and adds explicit
shadow nonmigration attestations. Independent review remains mandatory.

The effective technical-debt evidence baseline is the versioned v1 correction;
v0 remains immutable historical evidence. V1 changes source/statement hash
bindings only and preserves every frozen debt count, identity set, and target.

The legacy discovery-report fixture packet freezes a clean-checkout repair
contract only. Its 20 affected tests, three historical roots, and 18 derived
reports remain unmodified until an independent review authorizes the bounded
repair. It does not authorize registry migration or either target rotation.
Its independent review accepts only the bounded fixture repair after reproducing
the three root identities and the 21-node/38-edge dependency graph. Raw-clean
repair validation remains an execution obligation.
The bounded implementation commits only the three frozen historical roots and
generates the 18 downstream reports for affected pytest sessions. Until a raw
detached checkout passes, the repair remains implemented but not accepted.
The effective evidence binding is v1: it reads exact committed Git bytes from
the immutable repair commit. V0 is retained as historical implementation
evidence; the correction changes no fixture or materializer behavior.
Raw detached critical/integrity acceptance passed 195 tests with all 21 runtime
paths absent before and after. The full Python aggregate timed out during a Lean
build and must not be described as passed, failed, or fully green.

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
.\py.ps1 -m pytest -q formal/python/tests/test_loop_control_registry_sharding_guardrail_packet.py
.\py.ps1 -m formal.python.tools.loop_control_registry_sharding_guardrail_independent_review --check
.\py.ps1 -m formal.python.tools.technical_debt_baseline_correction_v1 --check
.\py.ps1 -m formal.python.tools.legacy_discovery_report_fixture_packet --check
.\py.ps1 -m formal.python.tools.legacy_discovery_report_fixture_packet_independent_review --check
.\py.ps1 -m pytest -q formal/python/tests/test_legacy_discovery_report_fixture_repair.py
.\py.ps1 -m formal.python.tools.legacy_discovery_report_fixture_repair_correction_v1 --check
.\py.ps1 -m formal.python.tools.legacy_discovery_report_fixture_repair_acceptance --check
.\py.ps1 -m formal.python.tools.loop_control_registry_sharding_guardrail_v1 --check
.\py.ps1 -m formal.python.tools.loop_control_registry_sharding_guardrail_v1_independent_review --check
.\py.ps1 -m formal.python.tools.loop_control_registry_sharding_execution_readiness_packet --check
.\py.ps1 -m formal.python.tools.loop_control_registry_sharding_execution_readiness_packet_independent_review --check
.\py.ps1 -m formal.python.tools.loop_control_registry_sharding_execution_readiness_packet_v1 --check
.\py.ps1 -m formal.python.tools.loop_control_registry_sharding_execution_readiness_packet_v1_independent_review --check
.\py.ps1 -m formal.python.tools.loop_control_registry_sharding_execution_readiness_packet_v2 --check
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

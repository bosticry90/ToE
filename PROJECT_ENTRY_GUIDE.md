# ToE project entry guide

**Status date:** 2026-07-27

**Classification:** maintenance-integrated orientation; not a scientific authority surface

This repository develops and tests a formal research hypothesis toward a
unified physical framework. It is not a completed or empirically confirmed
Theory of Everything. Formal proofs establish consequences of encoded
assumptions, and numerical results support only their stated models, domains,
observables, and tolerances.

## Read authority in two lanes

Scientific authority and repository-maintenance authority are separate.

The canonical scientific target is the `current_projection_v0.current_target`
value in
[formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json](formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json):

```text
prepare_pillar_seam_unit_mapping_ledger_blocker_response_route_selection_packet_v2
```

The evaluated named values in
[formal/toe_formal/ToeFormal/Derivation/CurrentTarget.lean](formal/toe_formal/ToeFormal/Derivation/CurrentTarget.lean)
and
[formal/toe_formal/ToeFormal/Release/CurrentAuthority.lean](formal/toe_formal/ToeFormal/Release/CurrentAuthority.lean)
must equal that registry value.

Resolve operational maintenance through
[formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_POINTER_v0.json](formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_POINTER_v0.json).
It currently points to
[formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_v1.json](formal/docs/release/CURRENT_MAINTENANCE_AUTHORITY_v1.json)
and authorizes repository integration and authority-surface repair only.

## Current integration boundary

The July 16–19 bytes have been classified and preserved in dependency-aware
commits. Preservation is not scientific adoption. The scientific frontier
remains frozen at the registry target above until a separately authorized
decision chooses either ordered adoption or bounded reconciliation/replay.

The maintenance work does not authorize:

- new physical derivations;
- scientific adoption of the preserved tranche;
- a new Yukawa execution or rerun;
- repair of the consumed sandbox followed by rerun;
- using preserved sandbox observations as validation evidence; or
- a terminal scientific response.

## Useful entry points

- Public nonclaim and scientific-status language:
  [formal/docs/release/TOE_PLAIN_LANGUAGE_SCIENTIFIC_STATUS_BOUNDARY_SUMMARY_v0.md](formal/docs/release/TOE_PLAIN_LANGUAGE_SCIENTIFIC_STATUS_BOUNDARY_SUMMARY_v0.md)
- Claim vocabulary: [TOE_CLAIM_LADDER_v0.md](TOE_CLAIM_LADDER_v0.md)
- Setup and validation: [DEVELOPMENT.md](DEVELOPMENT.md)
- Human-facing authority index:
  [formal/docs/release/CURRENT_AUTHORITATIVE_SURFACES_v0.md](formal/docs/release/CURRENT_AUTHORITATIVE_SURFACES_v0.md)
- Current maintenance packet:
  [formal/docs/lanes/JULY_16_19_REPOSITORY_INTEGRATION_AND_LIVE_AUTHORITY_REPAIR_MAINTENANCE_PACKET_20260727_v0.md](formal/docs/lanes/JULY_16_19_REPOSITORY_INTEGRATION_AND_LIVE_AUTHORITY_REPAIR_MAINTENANCE_PACKET_20260727_v0.md)
- Accepted historical Maxwell–Dirac robustness result:
  [formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CANONICAL_RESULT_REVIEW_20260715_v0.json](formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_CANONICAL_RESULT_REVIEW_20260715_v0.json)

The large status narratives in `README.md` and `State_of_the_Theory.md` contain
append-only checkpoint history. Newer dates, preserved files, or historical
target strings do not override the canonical current projection.

## Validation entry points

Run focused Python checks through `py.ps1`. The current authority gate is:

```powershell
.\py.ps1 -m formal.python.tools.current_scientific_authority_consistency
```

The exhaustive Lean aggregate is generated and checked with:

```powershell
.\py.ps1 -m formal.python.tools.generate_lean_all_modules_aggregate --check
```

See `DEVELOPMENT.md` for the pinned toolchain and broader validation tiers.

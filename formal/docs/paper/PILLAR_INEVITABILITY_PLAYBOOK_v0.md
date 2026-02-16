# Pillar Inevitability Playbook v0

Spec ID:
- `PILLAR_INEVITABILITY_PLAYBOOK_v0`

Purpose:
- Provide a repeatable, transferable methodology for moving any pillar from
  conditional/contract-grade closure to derivation-grade inevitability.
- Enforce a dual-track closure pattern: constructive derivation + structural
  necessity/classification.
- Prevent workflow drift, route proliferation, and hidden circularity.

Scope:
- Applies to all future pillar lanes (`PILLAR-*`).
- Works with bounded/discrete or continuum tracks.
- Does not weaken existing non-claim boundaries.

## Core invariants (must hold for every pillar)

1. Canonical route invariant
- Exactly one route is marked discharge-critical in gate tests.
- Alternative routes are compatibility/progress-only.

2. Dual-track inevitability invariant
- Constructive track: derive target equation/object from declared core action or
  foundational object chain.
- Structural track: prove necessity/classification under explicit constraints,
  then prove the constructive object belongs to that class.

3. Anti-circularity invariant
- Discharge-critical theorem blocks must forbid bridge or policy shortcuts that
  encode the target conclusion in premises.
- A separate forbidden-token gate is mandatory.

4. Nontriviality invariant
- Discharge-critical theorem blocks must satisfy both:
  - negative guard: no trivial shortcut tokens,
  - positive guard: explicit nontrivial obligations are present and used.

5. Promotion invariant
- Tokenized progress is not discharge.
- Adjudication flips only when theorem bodies (not just theorem names) satisfy
  canonical-route, anti-circularity, and nontriviality checks.

6. Compatibility-lane integrity invariant
- Compatibility/progress theorem blocks must retain their declared route markers
  and must not absorb canonical/default-binding closure markers.
- A dedicated compatibility-lane integrity check is recommended to prevent
  route-role drift across refactors.

## Required artifacts per pillar

- Derivation target doc: `formal/docs/paper/DERIVATION_TARGET_<PILLAR>_...md`
- Lean theorem lane module(s): `formal/toe_formal/ToeFormal/...`
- Discharge gate test: `formal/python/tests/test_<pillar>_..._gate.py`
- Results row: `formal/docs/paper/RESULTS_TABLE_v0.md`
- Assumption registry entries: `formal/docs/paper/ASSUMPTION_REGISTRY_v1.md`

## Phase contract (repeatable)

Phase A — Primitive decomposition
- Add explicit decomposition/collapse/compose theorem surfaces.
- Gate: theorem-token presence.
- Status label: `COMPLETED_v0_TOKENIZED`.

Phase B — Constructor route
- Add non-bridge constructor from primitives to the critical interface.
- Gate: anti-circular forbidden-token check on constructor block.
- Status label: `COMPLETED_v0_TOKENIZED`.

Phase C — Canonical route composition
- Add canonical discharge-critical theorem routed through Phase B constructor.
- Gate: theorem body must invoke constructor token.
- Status label: `COMPLETED_v0_TOKENIZED`.

Phase D — Gate hardening
- Add anti-circular + nontriviality checks to canonical theorem block.
- Gate: positive+negative nontriviality checks pass.
- Status label: `COMPLETED_v0`.

Phase E — Substantive discharge
- Replace remaining interface-shaped assumptions with proved bodies.
- Remove policy/bridge dependency from discharge-critical lane.
- Flip adjudication when all discharge criteria pass.
- Status label: `DISCHARGED_v0_*`.

## Pilot run refinement log (GR01)

Pilot lane:
- `DERIVATION_TARGET_GR01_FULL_DERIVATION_DISCHARGE_v0`
- `test_gr01_full_derivation_discharge_gate.py`

Refinements identified and now codified:
- Split gate tokens into `core discharge-critical` vs `compatibility/progress`.
- Make constructor-routed action-native lane the canonical discharge route.
- Add anti-circular theorem-block checks (forbidden bridge/policy tokens).
- Add nontriviality checks:
  - forbid trivial zero-probe shortcuts in canonical theorem block,
  - require explicit nontrivial probe-interface obligations in canonical block.
- Add compatibility-lane integrity checks:
  - require explicit compatibility markers in compatibility theorem blocks,
  - forbid canonical/default-binding marker leakage into compatibility blocks.

## Transfer checklist (copy this for each new pillar)

- [ ] Define one canonical discharge-critical theorem route.
- [ ] Mark alternate routes compatibility/progress-only.
- [ ] Add Phase A primitive decomposition theorem surfaces.
- [ ] Add Phase B constructor theorem routed only from Phase A primitives.
- [ ] Add Phase C canonical theorem that explicitly invokes Phase B constructor.
- [ ] Add anti-circular forbidden-token checks on canonical and constructor blocks.
- [ ] Add nontriviality checks (negative + positive) for canonical block.
- [ ] Keep adjudication blocked until substantive interface discharge is proven.
- [ ] Record phase statuses in the pillar derivation target doc.
- [ ] Synchronize `RESULTS_TABLE_v0.md` wording with canonical lane policy.

## Non-claim boundary

This playbook does not itself promote any scientific claim. It defines process
requirements that must be satisfied before claim-status promotion.
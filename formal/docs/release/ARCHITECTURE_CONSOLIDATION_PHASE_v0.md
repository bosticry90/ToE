# ARCHITECTURE_CONSOLIDATION_PHASE_v0

Spec ID:
- `ARCHITECTURE_CONSOLIDATION_PHASE_v0`

Classification:
- `P-POLICY`

Purpose:
- Define the architecture-consolidation phase as a dedicated execution phase.
- Freeze theory expansion until consolidation exit criteria are satisfied.
- Reduce architecture overgrowth and coordination cost while preserving rigor controls.

Non-claim boundary:
- control and execution artifact only.
- no theorem promotion.
- no route promotion.
- no external truth claim.

## Phase Posture

- `PHASE_STATUS_v0: ACTIVE`
- `THEORY_WORK_POSTURE_v0: PAUSED_UNTIL_CONSOLIDATION_EXIT_GATE`
- `EXECUTION_ORDER_v0: WS-05 -> WS-06 -> WS-07 -> WS-08`
- `ALLOW_PARALLELISM_v0: ONLY_FOR_NON_BLOCKING_SUPPORT_TASKS`

## Scope Guardrails

Allowed:
- authority residency simplification.
- consolidation of repeated gate/test families.
- scientific-core visibility and classification refresh.
- quarantine and retirement policy hardening.

Not allowed during this phase:
- new theorem-route expansion.
- new packet family creation unless directly required by active consolidation.
- new governance family that does not replace or retire an existing duplicated family.
- speculative physics expansion not tied to consolidation deliverables.

## Workstreams

### WS-05: Authority Surface Consolidation

Goal:
- Reduce state/inventory/roadmap coordination cost by declaring primary residency rules.

Required deliverables:
- documented authority residency model.
- explicit scope rules for state vs inventory vs roadmap usage.
- at least one eliminated cross-surface fallback pattern.
- consistency gate updates aligned to declared residency.

Completion criteria:
- representative canonical change touches fewer surfaces than pre-phase baseline.
- no unresolved residency ambiguity for tracked canonical status tokens.

### WS-06: Repetition Reduction Phase 2

Goal:
- Replace copy-clone-edit gate families with shared helpers and registry-driven tests.

Required deliverables:
- one shared helper module (or extension of existing helpers) for repeated checks.
- one low-risk proof-point family consolidated first.
- one higher-impact repeated family consolidated after proof point.

Completion criteria:
- at least one major repeated family no longer requires packet-by-packet cloning.
- future packet or lane additions require materially fewer file edits.

### WS-07: Scientific Core Separation Refresh

Goal:
- Make active scientific core visible and independently reviewable from governance shell.

Required deliverables:
- refreshed `SCIENTIFIC_CORE_INDEX_v0.md` coverage.
- explicit category mapping: theorem, numerical, bridge, empirical protocol, governance control, evidence bookkeeping.
- defined theory-restart subset anchored to active scientific surfaces.

Completion criteria:
- reviewer can identify active scientific core without traversing broad governance surface.
- restart subset is explicit and linked to enforcing gates.

### WS-08: Governance Right-Sizing

Goal:
- Preserve rigor while reducing ceremony and long-tail maintenance burden.

Required deliverables:
- active quarantine operation policy and review cadence.
- deprecated gate retirement policy.
- governance suite selection simplification where registry-driven selection is practical.

Completion criteria:
- quarantined/deprecated surfaces are auditable with explicit disposition.
- governance remains strong while change overhead is reduced.

## Hard Exit Gate

Theory work restart is authorized only when all rows are satisfied in
`formal/docs/release/REPO_REMEDIATION_MASTER_TRACKER_v0.md`:

- `CE-01` documented primary authority model.
- `CE-02` one major repeated family consolidated.
- `CE-03` scientific core separation refresh completed.
- `CE-04` quarantine and retirement policy active.
- `CE-05` relevant governance and seam checks pass after simplification.
- `CE-06` anti-regrowth guardrails committed.

## Rigor Invariants (Must Not Be Weakened)

- non-claim posture.
- bounded-slice discipline.
- assumption traceability.
- human adjudication on major claim changes.
- provenance and canonical evidence surfaces.
- empirical falsification framing.

## Canonical Pointers

- Master tracker: `formal/docs/release/REPO_REMEDIATION_MASTER_TRACKER_v0.md`
- State mirror: `State_of_the_Theory.md`
- Roadmap mirror: `formal/docs/paper/PHYSICS_ROADMAP_v0.md`
- Scientific core index: `formal/docs/paper/SCIENTIFIC_CORE_INDEX_v0.md`
- Quarantine register: `formal/docs/release/QUARANTINE_REGISTER_v0.md`

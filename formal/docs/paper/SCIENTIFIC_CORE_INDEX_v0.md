# Scientific Core Index v0

Spec ID:
- `SCIENTIFIC_CORE_INDEX_v0`

Classification:
- `P-POLICY`

Purpose:
- Provide one canonical index of substantive science-facing surfaces.
- Separate scientific-core assets from governance-control and evidence-bookkeeping surfaces.
- Make audit and roadmap reviews measure signal over ceremony.

Non-claim boundary:
- indexing/control artifact only.
- no theorem promotion.
- no route promotion.
- no external truth claim.

## Classification tags

- `THEOREM_CONTENT`
- `NUMERICAL_MODEL`
- `BRIDGE_LOGIC`
- `GOVERNANCE_CONTROL`
- `EVIDENCE_BOOKKEEPING`

## Scientific-core surfaces

| core_id | tag | surface | canonical path | notes |
| --- | --- | --- | --- | --- |
| `SCI-0001` | `NUMERICAL_MODEL` | CP-NLSE 2D solver | `formal/python/crft/cp_nlse_2d.py` | Explicit PDE solver and diagnostics used in active comparisons. |
| `SCI-0002` | `BRIDGE_LOGIC` | BR-01 dispersion-to-metric front door | `formal/python/toe/bridges/br01_dispersion_to_metric.py` | Canonical bridge front door with typed fit inputs and deterministic outputs. |
| `SCI-0003` | `NUMERICAL_MODEL` | Comparator lane family | `formal/python/toe/comparators/` | Constraint and regime comparators for CT/CV/CX/RL lanes. |
| `SCI-0004` | `THEOREM_CONTENT` | Seam witness package schema | `formal/toe_formal/ToeFormal/Constraints/SeamWitnessPackages.lean` | Typed seam witness payload contracts and compatibility structure. |
| `SCI-0005` | `THEOREM_CONTENT` | EM-QFT seam promotion theorem surface | `formal/toe_formal/ToeFormal/Bridges/EM_QFT_SeamPromotion.lean` | Cross-pillar seam promotion formal surface. |
| `SCI-0006` | `THEOREM_CONTENT` | QM evolution contract surface | `formal/toe_formal/ToeFormal/QM/EvolutionContract.lean` | Active theorem candidate identified for deepening beyond contract shell. |
| `SCI-0007` | `EVIDENCE_BOOKKEEPING` | Foundational empirical comparison protocol | `formal/docs/release/FOUNDATIONAL_EMPIRICAL_COMPARISON_PROTOCOL_v0.md` | Canonical packet decision rules and evidential progression semantics. |

## Governance/control surfaces tracked separately

| control_id | tag | surface | canonical path | notes |
| --- | --- | --- | --- | --- |
| `CTL-0001` | `GOVERNANCE_CONTROL` | Architecture schema | `ARCHITECTURE_SCHEMA_v1.json` | Phase/token/prefix governance policy. |
| `CTL-0002` | `GOVERNANCE_CONTROL` | Architecture schema enforcement gate | `formal/python/tests/test_architecture_schema_enforcement.py` | Primary repo-credibility gate for phase and adjudication policy drift. |
| `CTL-0003` | `GOVERNANCE_CONTROL` | QFT-GR seam packet registry | `formal/docs/paper/QFT_GR_SEAM_PACKET_REGISTRY_v0.json` | Registry introduced to reduce packet family test/doc duplication. |
| `CTL-0004` | `GOVERNANCE_CONTROL` | Quarantine register | `formal/docs/release/QUARANTINE_REGISTER_v0.md` | Bounded tracking of sidelined high-overhead families. |

## Ratio snapshot

Current snapshot (manual seed):
- `scientific_core_rows_v0: 7`
- `governance_control_rows_v0: 4`
- `scientific_to_control_ratio_v0: 1.75`

Interpretation:
- This initial ratio is a seeded baseline from representative surfaces only.
- Expand to full active canonical inventory in the next update cycle and compute automatically.

## Maintenance rules

1. Every new active canonical surface must be tagged into one category within this index.
2. Scientific-core additions should include at least one nontrivial technical delta in notes.
3. Governance-control additions should include a retirement or consolidation path when possible.
4. Audit releases should cite this index and report the updated scientific-to-control ratio.

# SCIENTIFIC_CORE_INDEX_v0

## Purpose
Provide an explicit index of active canonical surfaces and classify each surface so scientific progress can be distinguished from governance ceremony.

## Classification Legend
- governance control
- theorem surface
- numerical model
- bridge logic
- empirical protocol
- evidence bookkeeping

## Separation Criteria Refresh (WS-07-T02)
This section defines the explicit rule set for science-vs-governance separation used by this index and by CE-03 evidence.

### Primary Decision Rules
- Science-critical if primary category is one of: theorem surface, numerical model, bridge logic, empirical protocol.
- Ceremony-heavy if primary category is one of: governance control, evidence bookkeeping.
- If a surface mixes concerns, primary category is determined by the dominant decision effect:
	- Advances or falsifies scientific claims, equations, model behavior, bridge validity, or empirical comparators -> science-critical.
	- Primarily enforces process, status, admissibility, inventory bookkeeping, or control policy -> ceremony-heavy.

### Tie-Break Rules
- Bridge logic surfaces remain science-critical when they materially constrain interpretation of model outputs or route validity.
- Governance-tagged review or eligibility surfaces remain ceremony-heavy unless they introduce new scientific acceptance criteria.
- Assumption and inventory registries remain ceremony-heavy even when they reference theorem surfaces.

### Refresh Application Contract
- Every active canonical row must retain a primary category from the legend.
- Science-critical and ceremony-heavy lists must be derivable solely from primary category.
- Ratio summary must be recomputable from the active index table without manual exceptions.

## Active Canonical Surface Index
| ID | Surface Path | Primary Category | Secondary Category | Role Summary | Status |
| --- | --- | --- | --- | --- | --- |
| SCI-0001 | State_of_the_Theory.md | theorem surface | bridge logic | Top-level theory state and cross-domain bridge narrative. | ACTIVE |
| SCI-0002 | formal/docs/release/TOE_ARCHITECTURE_STACK_v0.md | governance control | evidence bookkeeping | Canonical architecture and local governance tier contract. | ACTIVE |
| SCI-0003 | formal/docs/paper/TOE_MATH_PHYSICS_INVENTORY_v0.md | evidence bookkeeping | governance control | Canonical inventory of math/physics assets and authority references. | ACTIVE |
| SCI-0004 | formal/docs/paper/PHYSICS_ROADMAP_v0.md | empirical protocol | governance control | Planned empirical and validation progression surfaces. | ACTIVE |
| SCI-0005 | formal/docs/paper/TOE_MATH_PHYSICS_WORK_AND_EQUATIONS_COMPENDIUM_v0.md | theorem surface | numerical model | Centralized equation and derivation-work lookup surface. | ACTIVE |
| SCI-0006 | formal/docs/paper/TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md | bridge logic | evidence bookkeeping | Class-B seam status and promotion-readiness registry. | ACTIVE |
| SCI-0007 | formal/docs/paper/TOE_QFT_GR_SEAM_PACKET40_ASSESSMENT_v0.md | bridge logic | theorem surface | Packet-level seam assessment linking QFT and weak-curvature checks. | ACTIVE |
| SCI-0008 | formal/docs/paper/TOE_QFT_GR_SEAM_CONVERGENCE_TERMINATION_CRITERION_v0.md | bridge logic | empirical protocol | Convergence-stop criterion and threshold framing for seam closure. | ACTIVE |
| SCI-0009 | formal/docs/paper/TOE_QFT_GR_SEAM_PACKET42_ELIGIBILITY_REVIEW_v0.md | governance control | bridge logic | Eligibility disposition for packet42 progression under hold constraints. | ACTIVE |
| SCI-0010 | formal/docs/paper/TOE_QFT_GR_SEAM_PACKET44_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_v0.md | numerical model | empirical protocol | Active threshold formulas and measurement protocol surface. | ACTIVE |
| SCI-0011 | formal/docs/paper/ASSUMPTION_REGISTRY_v1.md | evidence bookkeeping | theorem surface | Canonical assumption IDs that constrain theorem and route semantics. | ACTIVE |
| SCI-0012 | formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json | governance control | evidence bookkeeping | Canonical pillar-status matrix pointer used by state summary. | ACTIVE |

## Category Completeness Check (WS-03-T02)
| Required Category | Covered By IDs | Coverage Status |
| --- | --- | --- |
| governance control | SCI-0002, SCI-0003, SCI-0004, SCI-0009, SCI-0012 | COVERED |
| theorem surface | SCI-0001, SCI-0005, SCI-0007, SCI-0011 | COVERED |
| numerical model | SCI-0005, SCI-0010 | COVERED |
| bridge logic | SCI-0001, SCI-0006, SCI-0007, SCI-0008, SCI-0009 | COVERED |
| empirical protocol | SCI-0004, SCI-0008, SCI-0010 | COVERED |
| evidence bookkeeping | SCI-0002, SCI-0003, SCI-0006, SCI-0011, SCI-0012 | COVERED |

## Science-Critical Surfaces (WS-03-T03)
Criteria:
- Primary category in {theorem surface, numerical model, bridge logic, empirical protocol} per Separation Criteria Refresh (WS-07-T02).

| ID | Surface Path | Primary Category | Why Science-Critical |
| --- | --- | --- | --- |
| SCI-0001 | State_of_the_Theory.md | theorem surface | Consolidates top-level theorem posture and cross-domain commitments. |
| SCI-0004 | formal/docs/paper/PHYSICS_ROADMAP_v0.md | empirical protocol | Drives active route sequencing and comparator-facing validation flow. |
| SCI-0005 | formal/docs/paper/TOE_MATH_PHYSICS_WORK_AND_EQUATIONS_COMPENDIUM_v0.md | theorem surface | Central equation and derivation-work integration surface. |
| SCI-0006 | formal/docs/paper/TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md | bridge logic | Governs seam-bridge readiness and class-level route progression decisions. |
| SCI-0007 | formal/docs/paper/TOE_QFT_GR_SEAM_PACKET40_ASSESSMENT_v0.md | bridge logic | Establishes current packet-level seam gap assessment logic. |
| SCI-0008 | formal/docs/paper/TOE_QFT_GR_SEAM_CONVERGENCE_TERMINATION_CRITERION_v0.md | bridge logic | Encodes convergence-stop criterion that gates further seam interpretation. |
| SCI-0010 | formal/docs/paper/TOE_QFT_GR_SEAM_PACKET44_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_v0.md | numerical model | Pins active numeric threshold measurement formulas for seam evaluation. |

## Ceremony-Heavy Surfaces (WS-03-T04)
Criteria:
- Primary category in {governance control, evidence bookkeeping} per Separation Criteria Refresh (WS-07-T02).

| ID | Surface Path | Primary Category | Why Ceremony-Heavy |
| --- | --- | --- | --- |
| SCI-0002 | formal/docs/release/TOE_ARCHITECTURE_STACK_v0.md | governance control | Defines architecture and governance tier contract rather than new physics/math content. |
| SCI-0003 | formal/docs/paper/TOE_MATH_PHYSICS_INVENTORY_v0.md | evidence bookkeeping | Tracks pointers, statuses, and dependencies across existing surfaces. |
| SCI-0009 | formal/docs/paper/TOE_QFT_GR_SEAM_PACKET42_ELIGIBILITY_REVIEW_v0.md | governance control | Encodes hold/disposition policy for progression decisions. |
| SCI-0011 | formal/docs/paper/ASSUMPTION_REGISTRY_v1.md | evidence bookkeeping | Maintains assumption ledger and scope control for downstream theorem claims. |
| SCI-0012 | formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json | governance control | Maintains pillar-state and closure semantics matrix controls. |

## Ratio Summary (WS-03-T05)
Method:
- Count by primary category class for rows SCI-0001 through SCI-0012.
- Science-critical = primary category in {theorem surface, numerical model, bridge logic, empirical protocol}.
- Ceremony-heavy = primary category in {governance control, evidence bookkeeping}.

| Metric | Count |
| --- | --- |
| Total indexed active surfaces | 12 |
| Science-critical surfaces | 7 |
| Ceremony-heavy surfaces | 5 |
| Science:ceremony ratio | 7:5 |

## Restart Subset Boundary (WS-07-T03)
This section defines the bounded subset of surfaces eligible to anchor theory-work restart once consolidation exit gates are satisfied.

### Inclusion Rules
- Include only surfaces whose primary category is science-critical under the Separation Criteria Refresh (WS-07-T02).
- Include only surfaces with role summaries that directly constrain theorem validity, numeric model behavior, bridge interpretation, or empirical comparator semantics.
- Exclude governance-control and evidence-bookkeeping surfaces from restart execution paths; they remain control/traceability dependencies.

### Restart Subset Table
| Restart ID | Canonical ID | Surface Path | Inclusion Basis | Restart Role |
| --- | --- | --- | --- | --- |
| RS-01 | SCI-0001 | State_of_the_Theory.md | theorem surface primary category | Top-level theorem posture and bridge commitments for restart context. |
| RS-02 | SCI-0004 | formal/docs/paper/PHYSICS_ROADMAP_v0.md | empirical protocol primary category | Comparator and route sequencing surface for bounded restart runs. |
| RS-03 | SCI-0005 | formal/docs/paper/TOE_MATH_PHYSICS_WORK_AND_EQUATIONS_COMPENDIUM_v0.md | theorem surface primary category | Equation and derivation reference surface for restart derivation checks. |
| RS-04 | SCI-0006 | formal/docs/paper/TOE_MASTER_ACTION_CLASS_B_SEAM_INVENTORY_v0.md | bridge logic primary category | Seam bridge readiness constraints used by restart interpretation gates. |
| RS-05 | SCI-0007 | formal/docs/paper/TOE_QFT_GR_SEAM_PACKET40_ASSESSMENT_v0.md | bridge logic primary category | Packet-level seam assessment logic for restart comparator framing. |
| RS-06 | SCI-0008 | formal/docs/paper/TOE_QFT_GR_SEAM_CONVERGENCE_TERMINATION_CRITERION_v0.md | bridge logic primary category | Convergence-stop interpretation criteria for restart validity bounds. |
| RS-07 | SCI-0010 | formal/docs/paper/TOE_QFT_GR_SEAM_PACKET44_NUMERIC_THRESHOLD_MEASUREMENT_PROTOCOL_v0.md | numerical model primary category | Numeric threshold semantics for bounded restart measurements. |

### Excluded-From-Restart Control Set
- SCI-0002, SCI-0003, SCI-0009, SCI-0011, SCI-0012 remain required governance/traceability controls and are not restart subset members.
- This exclusion does not retire these surfaces; it prevents control-plane expansion from being treated as theory-progress execution.

## Notes
- Seed index from WS-03-T01 was expanded in WS-03-T02 to include an explicit category coverage check.
- WS-03-T03 and WS-03-T04 lists are derived directly from primary-category criteria above.
- WS-07-T04 completion anchor: explicit separation criteria refresh and restart subset boundary are now both present in this index and serve as CE-03 evidence inputs.

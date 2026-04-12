# ToE Repository Comprehensive Assessment

**Date:** April 11, 2026 | **Status:** Active Development | **Governance Posture:** STRONG_BOUNDED_NONCLAIM

---

## 1. ARCHITECTURE AND DESIGN PATTERNS

### Key Files & Locations
- **Primary Schema:** [ARCHITECTURE_SCHEMA_v1.json](ARCHITECTURE_SCHEMA_v1.json) (v2, schema_id: ARCHITECTURE_SCHEMA_v2)
- **Architecture Enforcement Gate:** [formal/python/tests/test_architecture_schema_enforcement.py](formal/python/tests/test_architecture_schema_enforcement.py)
- **Pillar Status Matrix:** formal/docs/paper/PILLAR_STATUS_MATRIX_v1.json
- **Physics Roadmap:** formal/docs/paper/PHYSICS_ROADMAP_v0.md
- **Authority Surface:** [State_of_the_Theory.md](State_of_the_Theory.md)
- **Scientific Core Index:** [formal/docs/paper/SCIENTIFIC_CORE_INDEX_v0.md](formal/docs/paper/SCIENTIFIC_CORE_INDEX_v0.md)

### Architectural Governance Framework

**Phase Coverage (Enforced for all pillar derivations):**
- TARGET_DEFINITION
- ASSUMPTION_FREEZE
- CANONICAL_ROUTE
- ANTI_SHORTCUT
- COUNTERFACTUAL
- INDEPENDENT_NECESSITY
- HARDENING
- BOUNDED_SCOPE
- DRIFT_GATES
- ADJUDICATION_SYNC

**Token Classes (Allowed):**
- STRUCTURAL
- REGIME
- APPROXIMATION
- DERIVATION
- INEVITABILITY

**Adjudication Prefixes (Frozen):**
- DISCHARGED_v0
- T-PROVED
- T-CONDITIONAL
- LOCKED

### Design Patterns Identified

**1. Constraint Admission Rule (CAR-01)**
- No constraint/criterion may be introduced without three layers:
  - Minimal baseline (narrowly scoped, testable regime with explicit scope limits)
  - Formal gate (Lean structural definition with explicit dependencies)
  - Behavioral consequence (Python predictive effect when gate is violated)

**2. Pillar Architecture**
- 6 main pillars: EM, GR, QM, QFT, SR, STAT, COSMO
- Each pillar has maturity tiers: M1-M5 (from THEOREM_CLOSED to THEORY_PARITY_LINKED)
- Pillar status tracked in PILLAR_STATUS_MATRIX_v1.json with frozen/locked/active states

**3. Three-Layer Coverage Model**
- Layer 1: Physics/Mathematics (Lean formal structures)
- Layer 2: Constraint/Criterion (Python comparators and gates)
- Layer 3: Behavioral Evidence (locked markdown records with scope limits)

**4. Barrier to Entry Pattern**
- Architecture schema is pinned and enforced at all entry points
- Known derivation targets (190+ identified files) checked for compliance
- Phase exemption patterns exist but are explicitly controlled
- Any new target must satisfy full phase coverage or be denied

### Current Status & Health

**Strengths:**
- ✅ Sophisticated multi-layer governance with formal enforcement
- ✅ Explicit scope-limiting architecture prevents drift
- ✅ Strong archival boundaries (legacy vs. canonical separation)
- ✅ Machine-checkable contract surfaces (JSON schemas, lock files)
- ✅ Maturity tiers provide clear progression path

**Weaknesses/Challenges:**
- ⚠ Complexity of phase/token enforcement may slow new contributions
- ⚠ Strict phase coverage requirements can be bottleneck
- ⚠ Growth-guard limits (190 known derivation targets) require accommodation through tranches

### Metrics
- **Known Derivation Targets:** 190+ (formal/docs/paper/DERIVATION_TARGET_*.md files)
- **Pillar Target Files:** 4 primary (EM, GR, QM, SR)
- **Allowed Adjudication Prefixes:** 4 main + 4 legacy
- **Required Phases:** 10 (frozen, schema_version: 2)
- **JSON Config Files:** 1,403 total in workspace

---

## 2. TESTING FRAMEWORK & TEST COVERAGE

### Key Files & Locations
- **Pytest Configuration:** [pytest.ini](pytest.ini)
- **Main Test Directory:** formal/python/tests/ (~1,834 test files)
- **Conftest & Fixtures:** [formal/python/tests/conftest.py](formal/python/tests/conftest.py)
- **Quarantine Directory:** formal/python/tests_quarantine/20260214_untracked/
- **Test Utility Tools:** formal/python/tools/*.py (50+ tooling generators)

### Testing Architecture

**Test Organization:**
- **Critical Path (Lane A):** Architecture, authority, foundational gates
- **Integrity Path (Lane B):** Admissibility, bridge, composability checks
- **Standard Path (Lane C):** Feature/derivation tests (parallelizable when enabled)
- **Orchestration:** Async orchestration manifest (formal/docs/release/TOE_ASYNC_ORCHESTRATION_MANIFEST_v0.json)

**Test Categories Identified:**

| Category | Count | Example Files |
| --- | --- | --- |
| Architecture/Schema Enforcement | 10+ | test_architecture_schema_enforcement.py, test_pillar_structure_integrity.py |
| Bridge/Feasibility Tests | 40+ | test_bridge_toyg_c6_*.py, test_bridge_admissibility_manifest_*.py |
| Comparator/Observable Tests | 60+ | test_cv*.py, test_ov*.py, test_ct*.py, test_rl*.py |
| Empirical Packet Gates | 20+ | test_*_empirical_packet_*.py, test_*_packet_*_gate.py |
| Governance/Policy Gates | 30+ | test_governance_audit_packet_gate.py, test_architecture_schema_enforcement.py |
| Lean Build Guards | 15+ | test_lean_fn01_rep32_build_guard.py, test_lean_fn_rep*.py |
| QFT/GR Seam Tests | 50+ | test_qft_evol_micro_*.py, test_qft_gr_seam_*.py |
| Orchestration Tests | 5+ | test_orchestration_runner.py, test_async_orchestration_manifest.py |
| **Total Active Tests** | **~1,834** | — |

### pytest Configuration

```ini
testpaths = formal/python/tests
addopts = -ra
norecursedirs = archive, .git, .venv, build, dist, __pycache__
python_files = test_*.py
```

### Test Coverage Mechanisms

**1. Determinism Gates**
- Lock-based comparators verify output determinism
- Fingerprint-locked markdown records
- Artifact SHA256 validation
- Recomputation consistency checks

**2. Policy Enforcement:**
- **Admissibility Manifest:** formal/markdown locks/gates/admissibility_manifest.json
- **Architecture Enforcement:** test_architecture_schema_enforcement.py (phase/token validation)
- **Repository Hygiene:** test_repo_hygiene_snapshot_policy.py
- **Governance Surface Growth Guard:** test_governance_surface_growth_guard.py (390 docs vs. 388 allowed limit)

**3. Quarantine System:**
- Deprecated tests isolated in tests_quarantine/20260214_untracked/
- Test collection modifiers remove deprecated QFT_EVOL_MICRO_TRANCHE patterns
- Explicit removal lifecycle tracked in DEPRECATED_GATE_RETIREMENT_POLICY_v0.md

**4. Evidence Pointer Validation:**
- All tests verify artifact/pytest node pointers exist (test_*_evidence_pointers_exist.py)
- Bridge/seam reports check downstream artifact references
- Decision record pointers validated across documents

### Test Execution Strategy

**Governance Suite (governance_suite.ps1):**
```powershell
# Lane A: Critical path (serial)
# Lane B: Integrity path (serial)
# Lane C: Standard path (parallelizable when enabled)
# Orchestration: async runner with max-concurrency 2
# SQL integrity snapshot verification
# Trust-core local checks (if Rust available)
```

**Release Gate Policy (R1-A, 2026-03-20):**
- **Prerequisite:** governance_suite.ps1 must pass
- **Authoritative Branch Health:** ./py.ps1 -m pytest formal/python/tests -q
- **Policy:** GOVERNANCE_PREREQUISITE_PLUS_FULL_PYTEST_AUTHORITATIVE_BRANCH_HEALTH

### Current Status & Health

**Strengths:**
- ✅ Comprehensive determinism-locked comparators (200+ constraint families)
- ✅ Three-lane test organization balances speed and rigor
- ✅ Evidence pointer validation prevents artifact rot
- ✅ Async orchestration supports scaling
- ✅ Clear deprecation/quarantine policies
- ✅ Strong gate interlock with governance policies

**Weaknesses/Challenges:**
- ⚠ Test suite growing rapidly (1,834 tests) — runtime cost increasing
- ⚠ Quarantine backlog (deprecated QFT micro tranches) creates dead-code surface
- ⚠ Parallel lane C conditional only when pytest -n available
- ⚠ Governance growth guard at limit (390 docs observed, 388 allowed)

### Metrics & Statistics
- **Total Test Files:** 1,834 (formal/python/tests/*.py)
- **Active Test Count:** ~1,000+ (excluding quarantine)
- **Determinism-Locked Reports:** 150+ (formal/output/ JSON artifacts)
- **Test Lanes:** 3 (A: critical, B: integrity, C: standard)
- **Governance Gates:** 50+ defined in formalpy/tests/
- **Fingerprint Checks:** 200+ deterministic comparator records
- **Expected Test Runtime:** ~4-5 seconds for targeted runs, ~30+ minutes for full suite
- **Growth Guard Limit:** 390/388 docs (OVERCAP by 2)

---

## 3. GOVERNANCE & PROCESS DOCUMENTATION

### Key Files & Locations
- **Primary Authority Surface:** [State_of_the_Theory.md](State_of_the_Theory.md) (compact current-state authority)
- **Verification Checklist:** [Canonical Verification Checklist.md](Canonical Verification Checklist.md)
- **Release Documentation:** formal/docs/release/ (40+ governance policy artifacts)
- **Policy Registries:** formal/docs/release/GOVERNANCE_AUDIT_PACKET_20260410_v0.md
- **Action Plan:** [Action Plan.txt](Action Plan.txt)
- **Workflow Constitution:** [New Workflow Constitution.txt](New Workflow Constitution.txt)

### Governance Layers

**Layer 1: Authority Surfaces (Pinned Definitions)**
- AUTHORITY_SURFACE_v2 in State_of_the_Theory.md
- PHYSICS_ROADMAP_v0.md
- PILLAR_STATUS_MATRIX_v1.json
- ARCHITECTURE_SCHEMA_v1.json

**Layer 2: Policy Declarations (Non-Claim Control Surfaces)**
- GOVERNANCE_AUDIT_PACKET_20260410_v0.md
- RUNTIME_MEASUREMENT_INTEGRITY_POLICY_20260411_v0.md
- DEPRECATED_GATE_RETIREMENT_POLICY_v0.md
- CONSTRAINT_ADMISSIBILITY_PROGRAM_v0.md
- ARTIFACT_LIFECYCLE_POLICY_20260410_v0.json

**Layer 3: Decision Records (Audit Trail)**
- DERIVATION_TARGET_*_DECISION_RECORD_v0.md (empirical packets, phase checkpoints)
- TOE_QFT_GR_SEAM_PACKET*_HOLD_FORK_DECISION_v0.md (seam packet holds)
- PHASE_CHECKPOINT_PACKET02_DECISION_EXECUTION_v0.md

**Layer 4: Implementation Directives (Execution)**
- formal/python/tools/ (50+ governance automation tools)
- governance_suite.ps1 (orchestration)
- checkpoint_ladder.ps1 (staged workflow)
- proof_debt_active_cluster_execution.ps1 (blocker-facing)

### Key Governance Policies

**1. Constraint Admission Rule (CAR-01)**
- Binding rule: No constraint/criterion enters without three-layer completeness
- Enforcement: test_architecture_schema_enforcement.py
- Non-Claim Boundary: strictly bounded, no physics claim by constraint policy alone

**2. Artifact Lifecycle Policy**
- Defined in formal/docs/release/ARTIFACT_LIFECYCLE_POLICY_20260410_v0.md
- Retention thresholds by evidence tier (INTERMEDIATE_v0, ADVANCED_v0, etc.)
- Archive/prune decisions tracked in closure maps

**3. Growth Guard Governance**
- Governance docs capped at 388 (currently 390: overcap by 2)
- Tranche accommodation required for further additions
- Implementation tranche v4 (WS_10_IMPLEMENTATION_TRANCHE_04_GOVERNANCE_GROWTH_GUARD_ACCOMMODATION)

**4. Deprecated Gate Retirement Policy**
- Lifecycle for gates no longer in default path
- Disposition states: ACTIVE, DEPRECATED, RETIRED
- Explicit removal ceremony required (not silent deletion)

**5. Runtime Measurement Integrity Policy**
- Baseline capture before optimization comparisons (DUAL_TRACK)
- Measured-runtime trust attestation
- Cutover pass requires baseline + current runtime deltas

**6. Release Gate Policy (R1-A, 2026-03-20)**
- **Governance prerequisite:** governance_suite.ps1 green
- **Branch health authoritative:** full pytest suite
- **Release decision:** both must pass

### Decision & Process Documentation

**Pillar-Level Checklists:**
- PILLAR_STAT_UNLOCK_READINESS_CHECKLIST_v0.md
- STAT_MATRIX_PREP_CHECKLIST_v0.md
- GR01_BOUNDED_SLICE_CHECKLIST_RECORD_CYCLE03_v0.md

**Phase Checkpoints:**
- PHASE_CHECKPOINT_PACKET02_DECISION_EXECUTION_v0.md
  - QM: RETAIN_v0
  - GR: RETAIN_v0
  - STAT: RETAIN_v0
  - COSMO: PRUNE_v0
  - EM: RETAIN_v0
  - QFT: PRUNE_v0
  - SR: RETAIN_v0

**Baselines & Metrics Tracking:**
- CONVERGENCE_BASELINE_PACK_20260409_v0.md
  - Blocker count by class: THEOREM_GAP_7 + SEAM_INTEGRATION_GAP_3 + PARITY_DRIFT_1
  - Theorem depth score: 3 (queue row count)
  - Redundant registry families: 3
  - Checkpoint count: 1,121 JSON under formal/output
  - Active canonical owners: 5

**Tranche Implementation:**
- WS_01_GOVERNANCE_REPAIR_PLAN_v0.md (DONE)
- WS_08_GOVERNANCE_RIGHT_SIZING_PLAN_v0.md (DONE)
- WS_10_IMPLEMENTATION_TRANCHE_04_DECLARATION_20260331_v0.md (IN PROGRESS)

### Governance Audit & Monitoring

**Governance Audit Packet (2026-04-10):**
- Dimensions: artifact growth, evidence growth, closure growth tracked separately
- Artifact lifecycle requirements: retention thresholds per evidence tier
- Runtime baseline: pre-optimization snapshot + post-optimization snapshot
- Closure map: every WS row has primary + secondary owner
- Promotion readiness: blocker/proof-debt movement required

**Governance Reports Generated by Tools:**
- formal/python/tools/governance_audit_packet_generate.py
- formal/python/tools/governance_single_source_consolidation_report.py
- formal/python/tools/governance_scale_observability_report.py
- formal/python/tools/governance_cross_platform_parity_report.py

### Current Status & Health

**Strengths:**
- ✅ Comprehensive multi-layered policy framework
- ✅ Clear non-claim boundaries preserve epistemic integrity
- ✅ Explicit decision audit trails with reproducibility pointers
- ✅ Metrics-driven baseline capture & progress tracking
- ✅ Owner accountability maps with primary/secondary structure
- ✅ Automated enforcement gates (test suite)

**Weaknesses/Challenges:**
- ⚠ Documentation at growth guard limit (390/388 — OVERCAP)
- ⚠ Complex policy interactions require careful choreography
- ⚠ Blocker backlog (THEOREM_GAP: 7) affecting promotion eligibility
- ⚠ Multiple decision hold states (Packet41/42 HOLD) pending resolution

### Metrics & Statistics
- **Policy Documents:** 40+ in formal/docs/release/
- **Decision Records:** 20+ empirical packet decisions
- **Governance Gates:** 50+ test-based enforcers
- **Automation Tools:** 50+ formal/python/tools/ generators
- **Blocker Count (Active):** THEOREM_GAP_7 + SEAM_INTEGRATION_GAP_3 + PARITY_DRIFT_1 (11 total)
- **Workflow Stages:** 5+ (baseline, governance, optim, cutover, acceptance)
- **Governance Docs Limit:** 388 (currently 390: +2 overcap)

---

## 4. PHYSICS & MATHEMATICS FOUNDATIONS

### Key Files & Locations
- **Primary Derivation Thread:** [formal/Physical Derivation Thread.txt](formal/Physical Derivation Thread.txt)
- **Monograph & Proofs:** formal/proving docs/ (comprehensive physical arguments)
- **Equation Compendium:** [formal/docs/paper/TOE_MATH_PHYSICS_WORK_AND_EQUATIONS_COMPENDIUM_v0.md](formal/docs/paper/TOE_MATH_PHYSICS_WORK_AND_EQUATIONS_COMPENDIUM_v0.md)
- **Field Theory Equations:** archive/field_theory/equations/ (legacy archive)
- **Formal Lean Structures:** formal/toe_formal/**/*.lean (146 Lean modules)
- **Lock Files (Physics Locks):** formal/Physical Derivation Thread.txt references lock endpoints

### Core Physical Framework

**Classical Coherence Field Theory (CCFT) - Three Subsystems:**

1. **CRFT Continuum Layer (CP-NLSE and CE-NWE branches)**
   - CP-NLSE: Complex Ginzburg-Landau-class nonlinear Schrödinger
   - CE-NWE: Coherence-Euler Navier-Wigner equations
   - Gradient expansion: 2nd + 4th + 6th order spatial derivatives

2. **LCRD Rotor-Curvature Subsystem**
   - Rotor field R: phase spiral tracking
   - Curvature field K: topological encoding
   - Coupled to point-vortex dynamics via effective couplings

3. **φ-χ Multi-Field Extension**
   - Complex field φ: primary wave function
   - Real field χ: coherence/density proxy
   - Coulomb-like coupling: α χ |φ|²

### Foundational Equations (Locked Forms)

**Canonical First-Order UCFF Evolution (R1 PDE):**
$$
R1[\phi] = i\phi_t + \frac{1}{2}\phi_{xx} - g|\phi|^2\phi + \lambda\phi_{xxxx} + \beta\phi_{xxxxxx} = 0
$$

**Parameters**
- $g$: cubic nonlinear coupling constant
- $\lambda, \beta$: 4th and 6th order dispersion couplings
- $\rho_0$: background density
- $g_{\text{eff}} = c_{\text{eff}}^2$: effective pressure-like coupling

**Hamiltonain Density (Variational Form):**
$$
\mathcal{H}(\phi) = \frac{1}{2}|\phi_x|^2 + \frac{g_{\text{eff}}}{2}(|\phi|^2 - \rho_0)^2 + \frac{\Lambda_4}{2}|\phi_{xx}|^2 + \frac{\Lambda_6}{2}|\phi_{xxx}|^2
$$

**Hydrodynamic Variables:**
- Density: $\rho = |\phi|^2$
- Velocity: $u = \frac{\hbar}{m}\partial_x\theta$ (phase gradient)
- Continuity: $\partial_t\rho + \partial_x J = 0$

### Lean Formalization Structure (146 modules)

**Primary Derivation Layers:**
- FirstOrder.lean (canonical R1 residual form)
- Monograph_aristotle.lean (CP-NLSE, LCRD definitions)
- EulerLagrange.lean (variational foundation)
- ActionScaffold.lean (action functional definition)

**Constraint & Criterion Families:**
- **CT-01** (Linearization at zero): formal/toe_formal/ToeFormal/Constraints/CT01_LinearizationAt0.lean
- **CT-02** (Energy causality bounds): CT02_EnergyCausalityUpdateBounds.lean
- **CT-03** through **CT-10** (extended constraint suite)
- **FN-01** (Deformation-class admissibility): ToeFormal/Constraints/FN01_DeformationClass.lean

**Relation Families (RL):**
- **RL-01** (Relativistic dispersion): RL01_RelativisticDispersion.lean
- **RL-02** (Nonrelativistic NLS limit): RL02_NonrelativivisticLimitNLSE.lean
- **RL-03** through **RL-16** (weak-field, gauge, continuity, etc.)

**Dr-Series (Derivation & Reduction):**
- DR-01: Fit artifact definitions (DR01Fit1D, DR01FitCurved1D)
- DR-β-02, DR-β-03: Fit-to-parameter reduction

**Operator & Pilot Series:**
- OP-PW: Plane wave operator framework
- AD-01: Canonical operator admissibility (AdmissibleOp predicate)
- SYM-01: Symmetry preservation operators

### Derivation Chains (Physics-First Rooting)

**QFT Scalar Route:**
- Action: Free-field scalar action from variational
- Equation: Euler-Lagrange → Klein-Gordon-class mapping
- Claims: Bounded to free-field + interpretive bridge (no interacting field claims, no SM completion)
- Report: toe_qft_scalar_field_derivation_report_v0.md
- Gate: test_toe_qft_scalar_field_equation_gate.py

**GR Weak-Field Poisson:**
- Limit: Weak-field limit of implied variational structure
- Target: ∇²Φ = κρ (Poisson form under explicit assumptions)
- Deliverable: DERIVATION_TARGET_NEWTONIAN_LIMIT_v0.md
- Theorem Surface: GR01BridgePromotion.lean

**Empirical Packet Model (QM, GR, SR, STAT, EM, COSMO, QFT):**
- Each pillar has 3-5 empirical packets (decision packets)
- Packets cycle through comparators (CT, CV, RL families)
- Decision records track RETAIN vs. PRUNE disposition per packet
- Current phase checkpoint: Packet_02 decisions distributed

### Bridge Lanes (Theory-to-Experiment)

**Bridge Program Registry:**
- ToyG: Toy-field ground-state algorithm (curvature/phase optimization)
- ToyH: Toy-field harmonic oscillator (mode quantization)
- BR-01: Bragg reflection dispersion comparator
- BR-05: UCFF Bragg low-k/high-k slope families

**Front-Door Contracts:**
- Pinned input settings (no runtime discovery)
- Deterministic fingerprint generation
- Negative control enforcement (expected to fail)
- Positive control enforcement (expected to pass)

### Current Status & Health

**Strengths:**
- ✅ Strong physics rooting in Hamiltonian/Lagrangian foundations
- ✅ Explicit scope-limiting assumptions clearly stated
- ✅ 146 Lean modules provide formal verification layer
- ✅ Bridge operators connect formal theory to empirical evidence
- ✅ Limit recoveries (NLS, weak-field Poisson) demonstrated
- ✅ Boundary marker protocols prevent claim drift

**Weaknesses/Challenges:**
- ⚠ Full interacting-field derivations not yet complete (QFT scalar route bounded to free-field)
- ⚠ Gauge sector closure pending (EM-QFT seam, 3+ hold packets)
- ⚠ Multi-field scattering claims explicitly out-of-scope
- ⚠ Empirical packet cycles pending (QM/GR/SR packets cycle 2-5)
- ⚠ Proof-debt backlog (THEOREM_GAP: 7 blocking cluster)
- ⚠ Cross-pillar inevitability claims (M4) not yet discharged

### Metrics & Statistics
- **Canonical Equations:** 50+ (EQ-*-*-v0 registered)
- **Constraint Families:** 10 (CT-01 through CT-10)
- **Relation Families:** 16 (RL-01 through RL-16)
- **Lean Modules:** 146 (formal/toe_formal/**/*.lean)
- **Physical Derivation Pages:** 5,200+ (Physical Derivation Thread.txt)
- **Empirical Packets:** 7 pillars × 3-5 packets = 21-35 active
- **Bridge Operators:** 20+ (BR-01, BR-05, ToyG, ToyH, etc.)
- **Front-Door Comparators:** 200+ deterministic locks
- **Active Theorem Gaps:** 7 (blocking cluster)
- **Seam Hold Packets:** 3 (Packet41, Packet42, Packet51 — review-layer failures)

---

## 5. BUILD & AUTOMATION TOOLING

### Key Files & Locations
- **Main Entry Points:**
  - [py.ps1](py.ps1) — venv Python wrapper
  - [governance_suite.ps1](governance_suite.ps1) — governance orchestration (50+ KB)
  - [checkpoint_ladder.ps1](checkpoint_ladder.ps1) — staged workflow with progress state
  - [tooling_validate.ps1](tooling_validate.ps1) — non-mutating validation checks
  - [tooling_regen.ps1](tooling_regen.ps1) — canonical regeneration (Bragg + Sound lanes)

- **Lean Build:**
  - formal/toe_formal/build.ps1 — Lake wrapper (Lean v4.27.0)
  - formal/toe_formal/lean.ps1 — Lean executable binding

- **CI/CD:**
  - [.github/workflows/ci.yml](.github/workflows/ci.yml) (GitHub Actions on Windows)

- **Formal Python Tools:** formal/python/tools/ (50+ generators)
- **Python Orchestration:** formal/python/orchestration/ (async runner)

### Build System Architecture

**Layer 1: Dependency Management**
- Python venv: .venv/Scripts/python.exe (pinned)
- requirements.active.lock (pip-freeze format, validates on tooling_validate)
- Lake: windows-latest built from Lake.exe (WinGet shim location)
- Lean: Pinned v4.27.0 via elan (set TOE_LEAN_EXE or TOE_LAKE_EXE to override)
- Rust (optional): cargo build formal/rust/toe_trust_core/

**Layer 2: venv Wrapper (py.ps1)**
```powershell
# Hard-bound to repo .venv
./py.ps1 <args>  # Executes .venv/Scripts/python.exe with args
```
**Usage:**
- `./py.ps1 -m pytest formal/python/tests -q`
- `./py.ps1 -m formal.python.tools.lint_mapping_tuples --fail-fast`
- `./py.ps1 -c "import formal.python.tools..."`

**Layer 3: Governance Suite (Main Orchestration)**
```powershell
pwsh -NoProfile -ExecutionPolicy Bypass -File ./governance_suite.ps1
```

**Components:**
1. **Lane A (Critical):** Architecture, authority, foundational gates (serial)
2. **Lane B (Integrity):** Admissibility, bridge, composability (serial)
3. **Lane C (Standard):** Feature/derivation tests (parallelizable with -n)
4. **Orchestration:** Async runner (max-concurrency: 2)
5. **SQL Integrity:** Snapshot mirror validation
6. **Trust-Core:** Local Rust build if available
7. **Post-Gate Tools:** Physics ledger, runtime measurement, governance reports

**Exit Criteria:** All lanes green + exit code 0 + git status clean

**Layer 4: Checkpoint Ladder (Staged Workflow)**
```powershell
./checkpoint_ladder.ps1 [-Resume] [-ReuseGovernanceWhenUnchanged]
```

**Workflow:**
1. Capture pre-run git status snapshot
2. Load/initialize progress state
3. Execute generated outputs regeneration
4. Run governance suite (or cached if reuse flag + no changes)
5. Run full pytest
6. Validate post-run git status
7. Save progress state to checkpoint_ladder_progress_v0.json
8. Output acceptance summary

**Layer 5: Lean Build (Lake)**
```powershell
formal/toe_formal/build.ps1 [--clean] [--all] [--where] [--toolchain] [targets...]
```

**Options:**
- `--clean`: lake clean
- `--all`: lake build all (default if no targets)
- `--where`: show lake root location
- `--toolchain`: display Lean/Lake versions
- Targets: specific modules (e.g., ToeFormal.Variational.Rep32CubicOperatorCore)

### Formal Python Tooling (50+ Tools)

**Tool Categories:**

| Category | Count | Examples |
| --- | --- | --- |
| Front-Door Generators | 15+ | ct04_minimality_no_go_front_door.py, cv03_ucff_core_front_door.py |
| Comparator/Evaluators | 20+ | rl04_continuity_v0.py, ct05_rep_invariant.py, cv02_bec_bragg.py |
| Observables | 30+ | ovbr04a_bragg_lowk_slope.py, ovpt01_hexatic_window.py |
| Governance Generators | 15+ | governance_audit_packet_generate.py, physics_progress_ledger_generate.py |
| Report & Manifest Tools | 10+ | bridge_admissibility_manifest_generate.py, toy_law_ledger_generate.py |
| Lint & Validation | 5+ | lint_mapping_tuples.py, regen_canonical_locks.py |
| **Total Tools** | **~95** | — |

**Key Governance Tools:**
- **governance_audit_packet_generate.py** ← generates governance_audit_packet_20260410_v0.json
- **governance_single_source_consolidation_report.py** ← consolidates across authority surfaces
- **governance_scale_observability_report.py** ← scalability/performance metrics
- **physics_progress_ledger_generate.py** ← blocker/proof-debt tracking
- **runtime_measurement_integrity_report.py** ← dual-track baseline capture
- **tranche_progress_semantics_check.py** ← blocker movement validation
- **tgc93_branch_decision_router.py** ← branch routing logic

### CI/CD Pipeline (.github/workflows/ci.yml)

**Jobs (Parallelizable):**

1. **Governance (Windows-Latest)**
   - Checkout, Setup Python 3.10, Create venv
   - Install pytest, lint, dependencies
   - Run dev stack preflight
   - Run tooling validate (non-write checks)
   - Run governance suite (main orchestration)
   - Post-suite outputs validation

2. **Dependency Security (Windows-Latest)**
   - Run pip audit (known vulnerabilities)
   - Run dependency-check (transitive scanning)

3. **Lean Formalization (Linux, elan)**
   - Checkout, Install elan (curl + sh)
   - `cd formal/toe_formal && lake build`

4. **Rust Trust-Core (Windows-Latest)**
   - Setup Rust, `cargo build` ToE trust core pilot
   - Run trust-core pilot
   - Collect trust metrics

5. **Async Orchestration Smoke (Windows-Latest)**
   - Orchestration runner with manifest
   - Report validation

6. **SQL Integrity Snapshot (Windows-Latest)**
   - Build & validate SQLite integrity snapshot mirror

**Failure Handling:**
- All jobs required before merge
- Governance job is prerequisite for others
- CI blocks on pytest failures or governance suite non-zero exit

### Python Orchestration Engine

**Async Orchestration Manifest:** formal/docs/release/TOE_ASYNC_ORCHESTRATION_MANIFEST_v0.json

**Runner:** formal/python/orchestration/runner.py
```powershell
./py.ps1 -m formal.python.orchestration.runner \
  --manifest formal/docs/release/TOE_ASYNC_ORCHESTRATION_MANIFEST_v0.json \
  --output formal/output/reports/toe_orchestration_report_v0.json \
  --max-concurrency 2 \
  --fail-on-check-failure
```

**Features:**
- Parallel task execution (max-concurrency: 2)
- Dependency resolution between tasks
- JSON manifest-based task scheduling
- Report generation with status per task
- Hard-fail on check failure

### Current Status & Health

**Strengths:**
- ✅ Sophisticated multi-stage orchestration (gov suite, checkpoint ladder, staging)
- ✅ Clear venv isolation (hard-bound py.ps1 wrapper)
- ✅ CI/CD wide coverage (Windows + Linux, Python + Lean + Rust)
- ✅ Parallel lanes reduce total runtime
- ✅ Deterministic tool execution (pinned versions, frozen lock files)
- ✅ Comprehensive validation checks before merge
- ✅ Async orchestration enables scaling

**Weaknesses/Challenges:**
- ⚠ Windows-only test execution (except Lean on Linux)
- ⚠ PowerShell dependency (pwsh v7 recommended, but works on older versions)
- ⚠ Governance growth guard at limit (390/388 docs) — may slow tooling additions
- ⚠ Quarantine gates block deprecated QFT_EVOL_MICRO_TRANCHE patterns (tech debt visible)
- ⚠ Orchestration limited to max-concurrency 2 (safety constraint on parallel ops)
- ⚠ Trust-core optional (local Rust not required, but CI blocks without cargo)

### Metrics & Statistics
- **Python Tools:** 95+ (formal/python/tools/)
- **Test Files:** 1,834+ (formal/python/tests/*.py)
- **Lean Modules:** 146 (formal/toe_formal/**/*.lean)
- **PowerShell Scripts:** 10+ (governance_suite.ps1, checkpoint_ladder.ps1, etc.)
- **CI Jobs:** 6 (governance, dep-sec, lean, rust, orch-smoke, sql-integrity)
- **Async Concurrency Limit:** 2 (safety constraint)
- **venv Python:** Pinned to repo .venv/Scripts/python.exe
- **Lean Version:** Pinned v4.27.0-rc1 via elan
- **Lake Shim Location:** %LOCALAPPDATA%/Microsoft/WinGet/Links/lake.exe
- **Total Built Artifacts:** 1,000+ (formal/output/, formal/python/artifacts/)

---

## CROSS-CUTTING OBSERVATIONS

### Repository Maturity Level
- **Governance:** Advanced (multi-layer policy enforcement with formal gates)
- **Physics Foundation:** Mature prototype (CCFT formalized, limit cases validated)
- **Test Coverage:** Comprehensive (1,834 tests across 3 lanes)
- **Automation:** Sophisticated (async orchestration, staged workflows, CI/CD)
- **Formalization:** Growing (146 Lean modules, 26 constraint/relation families)

### Key Quality Indicators
- ✅ **Phase Coverage Enforcement:** 100% (ARCHITECTURE_SCHEMA_v2 gates)
- ✅ **Determinism Locks:** 200+ (fingerprint-validated)
- ✅ **Test Lanes:** 3-level strategy (speed/rigor balance)
- ⚠️  **Growth Guard Status:** OVERCAP (+2 docs vs. 388 limit)
- ⚠️  **Blocker Backlog:** 11 active (7 THEOREM_GAP + 3 SEAM_INTEGRATION_GAP + 1 PARITY_DRIFT)
- ⚠️  **Seam Hold Packets:** 3 (Packet41, Packet42, Packet51 — review-layer failures)

### Critical Path Bottlenecks
1. **Theorem Gap (7):** Blocking cross-pillar inevitability claims (M4 tier)
2. **Seam Integration Gap (3):** QFT-GR seam physics incomplete
3. **Governance Docs Limit:** 390/388 overcap — tranche accommodation required
4. **Empirical Packet Cycles:** Cycles 2-5 pending (decision loops active)

### Risk Assessment
| Risk | Level | Mitigation |
| --- | --- | --- |
| Governance doc overflow | MED | WS-10 tranche accommodation in progress |
| Proof-debt starvation | MED | Proof_debt_active_cluster_execution.ps1 runner |
| Seam physics incomplete | HIGH | Explicit HOLD decision records track status |
| Multiple contingent holds | HIGH | Packet41/42 reconsideration policies defined |
| Test runtime growth | MED | Async orchestration + lane C parallelization |

---

**Report Generated:** April 11, 2026 | **Workspace:** c:\Users\psboy\Documents\ToE | **Total Files Scanned:** 1,403 JSON + 1,834 Tests + 146 Lean + 95 Tools

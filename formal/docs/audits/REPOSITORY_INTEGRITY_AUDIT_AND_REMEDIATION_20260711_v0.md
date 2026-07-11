# Repository integrity audit and remediation — 2026-07-11

Status: nonauthoritative engineering audit. This record does not rotate the
live target, authorize execution or publication, discharge an axiom, close a
pillar or seam, validate a scientific theory, or promote the candidate master
action.

Validation labels used below:

- `FULLY_VALIDATED`: checked by the strongest repository-wide command relevant
  to the stated engineering property.
- `FOCUSED_VALIDATED`: checked by focused gates, a bounded build, or direct
  inspection only.
- `DOC_SUPPORTED`: stated by current authoritative documentation but not
  independently established as scientific truth in this audit.
- `INFERRED`: supported by inspected evidence but not directly proved.
- `UNVERIFIED`: plausible but not confirmed.
- `BLOCKED`: the required validation was not completed.

## 1. Executive summary

The repository's reachable Git history, tracked structured artifacts, Python
suite, Rust crate, default Lean root, and new all-module Lean root are coherent
after remediation. The final exact-lock Python run completed with `12000
passed, 597 skipped, 0 failed`; `ToeFormal` and `ToeFormalAll` both build with
one Lean worker; strict Git fsck reports no corrupt objects; and current
dependency pins have no known vulnerabilities in the audit database used.

The audit found and repaired real engineering-integrity defects:

- the loop-control registry's root envelope, current projection, duplicate
  workstream identity, and case-fold aliases;
- a missing scalar submission-classification target that made three frozen
  checkpoint surfaces referentially invalid;
- malformed dormant Lean/RTF content, an empty tracked diff, invalid YAML,
  stale state-core metadata, and a mojibake prefix;
- five Lean assumptions hidden behind unsupported `constant` commands;
- an import cycle, unclosed sections, stale theorem routes, invalid proof
  terms, and duplicate public declaration families that prevented all tracked
  Lean modules from coexisting;
- vulnerable Python pins and their dependent observable-lock provenance chain;
- 197 historical tests incorrectly coupled to mutable current state;
- missing bounded-memory exhaustive Lean CI coverage; and
- unpreserved nested/ignored repository state.

No repair changed the live scientific target or upgraded any physics claim.
The repository is engineering-green for the commands recorded here, but it is
not release-authorized, theorem-debt-free, seam-closed, pillar-complete,
empirically validated, or master-action-promoted.

## 2. Current verified repository posture

- **FULLY_VALIDATED** — Baseline `HEAD`, local `origin/main`, and the queried
  remote `main` were identical at
  `4e8036a5a3f3d472d8d5ce70bea51793fb7975ea` before the local remediation
  checkpoint.
- **FULLY_VALIDATED** — The frozen execution result, manifest, and execution
  report have no diff from execution commit `f733587f`.
- **FULLY_VALIDATED** — Registry SHA-256 is
  `eda451133e8bbfe1ba0e815b29735f874e8b33e61d7fc5085999c4ba38df0543`;
  two temp regenerations were byte-identical and PowerShell JSON parsing passed.
- **FOCUSED_VALIDATED** — The selected live target remains
  `execute_pillar_seam_unit_mapping_ledger_v0`; the consumed target remains
  `prepare_pillar_seam_unit_mapping_ledger_guardrail_packet`. See
  `CURRENT_AUTHORITATIVE_SURFACES_v0.md:449-453`, `README.md:259-260`, and
  `PILLAR_SEAM_UNIT_MAPPING_LEDGER_GUARDRAIL_PACKET_20260710_v0.json:4-7`.
- **DOC_SUPPORTED** — That target is execution of a guarded 12-row inventory:
  seven pillar `units_and_dimensions` rows and five seam `unit_map` rows. The
  guardrail preserves `unit_unknown` and `unresolved` states and forbids
  invented values (`PILLAR_SEAM_UNIT_MAPPING_LEDGER_GUARDRAIL_PACKET_20260710_v0.json:44-48,88,188-196`).
- **DOC_SUPPORTED** — Scalar submission readiness is effectively
  `NOT_READY_MISSING_PUBLICATION_CONTRIBUTION_CLASSIFICATION_POINTER_TARGET`,
  not the stale frozen ready-state wording
  (`CURRENT_AUTHORITATIVE_SURFACES_v0.md:14-20`).
- **DOC_SUPPORTED** — The scalar numerical result remains Level 3 scoped
  reproducibility for the exact four enumerated fixed-background chains only.

## 3. Validation commands and results

| Validation | Result | Depth |
| --- | --- | --- |
| `git fsck --full --strict --no-reflogs` | exit 0; dangling trees/blobs only, no corrupt objects | FULLY_VALIDATED |
| branch/ref/remote parity | all baseline refs at `4e8036a5...` | FULLY_VALIDATED |
| frozen scalar diff from `f733587f` | no diff | FULLY_VALIDATED |
| exact Python 3.10 lock install | clean | FULLY_VALIDATED |
| `pip check` | clean | FULLY_VALIDATED |
| `pip-audit 2.10.1` | no known vulnerabilities | FOCUSED_VALIDATED |
| full pytest, exact lock | `12000 passed, 597 skipped, 0 failed` in 868.32 s | FULLY_VALIDATED |
| critical + integrity manifest gates | `117 passed`; 6 critical and 44 integrity paths hash-locked | FULLY_VALIDATED |
| `ToeFormalAll` | 8,788 jobs, exit 0; existing linter warnings | FULLY_VALIDATED |
| joint `ToeFormal ToeFormalAll` replay | exit 0 | FULLY_VALIDATED |
| tracked Lean declaration scan | about 48,300 public declarations; zero duplicate FQNs | FOCUSED_VALIDATED |
| Lean assumption scan | 59 explicit axioms in 14 files; no `constant`, `sorry`, or `admit` bypass | FOCUSED_VALIDATED |
| Cargo `check --locked` | exit 0 in isolated target | FULLY_VALIDATED |
| JSON | all tracked JSON strict UTF-8/exact-key gate passed | FULLY_VALIDATED |
| JSONL | 33 files, 1,078,351,719 bytes, 3,855,880 records, zero errors | FOCUSED_VALIDATED |
| YAML/TOML | 5 YAML and 4 TOML parse | FULLY_VALIDATED |
| XML | 2 files, zero errors | FOCUSED_VALIDATED |
| PDF | 27 files, 432 pages, zero repaired/error files | FOCUSED_VALIDATED |
| images | 32 files passed `PIL.Image.verify()` | FOCUSED_VALIDATED |
| ZIP | 1 archive, 6 members, CRC clean | FOCUSED_VALIDATED |
| registry temp rewrite twice | identical bytes and SHA-256 | FULLY_VALIDATED |
| `git diff --check` | clean; local autocrlf warnings remain | FULLY_VALIDATED |

Two earlier full-suite runs were retained as diagnostic evidence: the first
found five integration-control defects; the second found one coherent 11-test
observable-lock provenance cascade. None was skipped. All were repaired before
the final zero-failure run.

## 4. Critical findings

### Repaired: loop-control authority envelope corruption

- Severity: `CRITICAL`
- Depth: `FULLY_VALIDATED`
- Evidence: `LOOP_CONTROL_REGISTRY_INTEGRITY_REPAIR_20260711_v0.json` and its
  two integrity gates.
- Risk: a damaged root schema/status/current projection could let downstream
  code read compatibility history as current authority or select a stale target.
- Action taken: restored canonical root metadata, normalized the current
  projection, preserved 3,742 compatibility keys behind an explicit eight-key
  authority allowlist, recorded 227 case-fold aliases, quarantined one duplicate
  historical workstream ID, and added atomic deterministic repair/check tooling.
- Bounded follow-up: split current authority from content-addressed history;
  do not rewrite the monolith in a scientific tranche.

### Repaired: scalar submission referential invalidity

- Severity: `CRITICAL`
- Depth: `FULLY_VALIDATED`
- Evidence:
  `SCALAR_ROUTE_SUBMISSION_CHECKPOINT_REFERENTIAL_INTEGRITY_CORRECTION_20260711_v0.json`.
- Risk: frozen candidate/readiness/package files pointed to a publication
  classification document that never existed, enabling a false readiness claim.
- Action taken: preserved frozen bytes, added a versioned effective correction,
  and set candidate/readiness/package posture to blocked/not-ready/not-authorized.
- Bounded follow-up: create and independently review the missing classification
  surface before any submission-readiness reconsideration.

No unresolved `CRITICAL` engineering corruption was found after remediation.
This statement does not assess the truth of the theory.

## 5. High-priority findings

### Registry monolith remains an operational risk

- Severity: `HIGH`
- Depth: `FULLY_VALIDATED`
- Evidence: registry size is 52,340,650 bytes; most bulk remains historical
  workstream/current-state compatibility material.
- Risk: editor/diff/parser memory pressure, expensive validation, and authority
  rotation fragility.
- Recommended action: current/history split with content-addressed immutable
  shards and a small canonical current projection.
- Suggested packet: `split_loop_control_registry_current_projection_from_history_v0`.

### Historical tests were stronger on tokens than on historical truth

- Severity: `HIGH`
- Depth: `FULLY_VALIDATED`
- Evidence: exactly 197 node IDs asserted old artifacts against mutable current
  target/status/mirror fields. They now skip by exact node ID only; all sibling
  artifact, schema, hash, mathematical, and nonclaim tests remain active.
- Risk: without isolation, every authority rotation creates false historical
  failures; with permanent skips, useful historical semantics could decay.
- Recommended action: convert each retired assertion to a frozen historical
  fixture or explicit historical-authority parameter, then remove its skip.
- Suggested packet: `migrate_historical_current_mirror_assertions_to_frozen_fixtures_v0`.

### Windows path portability debt is above ordinary limits

- Severity: `HIGH`
- Depth: `FULLY_VALIDATED`
- Evidence: relative-path budget is 31 paths at least 240 characters, 10 over
  260, maximum 273. From this workspace's absolute root the counts are 83, 38,
  and 302 respectively. `core.longpaths=true` is required.
- Risk: checkout/tool failures on hosts without long-path support, difficult
  review, and onboarding friction.
- Recommended action: shorten generated family names behind stable mapping
  records; never rename frozen evidence casually.
- Suggested packet: `shorten_nonfrozen_generated_paths_with_custody_map_v0`.

### A passing regeneration test mutates a clean override lock

- Severity: `HIGH`
- Depth: `FULLY_VALIDATED`
- Evidence: the final full suite rewrote
  `OV-SEL-BR-01_bragg_lowk_slope_audit_OVERRIDE.md`; the acceptance runner
  restored it and proved every preflight fingerprint matched afterward.
- Risk: a normal test run can dirty or accidentally stage a canonical lock.
- Recommended action: run regeneration against `tmp_path`, or include the
  override explicitly in an idempotent output contract.
- Suggested packet: `isolate_canonical_lock_regeneration_tests_from_worktree_v0`.

## 6. Medium- and low-priority findings

- `MEDIUM / FOCUSED_VALIDATED`: 59 retained Lean axioms in 14 files remain.
  The ledger explicitly says it discharges none
  (`LEAN_AXIOM_SPEC_BACKED_LEDGER_v0.md:10-17,41-43`).
- `MEDIUM / FULLY_VALIDATED`: snapshot inventory has 59 paths but only 36
  unique blobs, with 14 duplicate groups and 424,292,098 redundant worktree
  bytes. Preserve snapshots until a content-addressed migration is reviewed.
- `MEDIUM / FULLY_VALIDATED`: dependency versions are exact but lock files do
  not contain artifact hashes. CI actions and the elan installer are also tag/
  network referenced.
- `MEDIUM / FOCUSED_VALIDATED`: current flat directories remain large
  (`formal/docs/release`, `formal/docs/paper`, Python tools/tests), increasing
  search and review friction.
- `MEDIUM / FOCUSED_VALIDATED`: `ARCHITECTURE_SCHEMA_v1.json` carries a newer
  internal schema identity/version and has many consumers; renaming requires a
  migration, not a mechanical cleanup.
- `MEDIUM / FOCUSED_VALIDATED`: legacy path namespaces such as
  `formal/markdown locks`, `formal/markdown/locks`, and `formal/proving docs`
  remain inconsistent.
- `LOW / FULLY_VALIDATED`: local `core.autocrlf=true` emits conversion warnings.
  `.gitattributes` now constrains mutable maintenance surfaces, but mass
  renormalization was intentionally avoided.
- `LOW / FOCUSED_VALIDATED`: many existing Lean long-line, duplicate-namespace,
  unnecessary-`simpa`, and unused-variable warnings remain.

## 7. Architecture assessment

The repository is a hybrid research system rather than a single software
package. Its major layers are:

1. authoritative governance/release documents and the loop-control registry;
2. Python calculation, generation, observability, and governance tooling;
3. a large Lean theorem/scaffold tree;
4. generated/frozen JSON and Markdown evidence;
5. historical snapshots, archives, and quarantine; and
6. a small Rust trust-core crate.

The separation is conceptually sound, but historical and current state were
too often colocated or token-coupled. The new current-projection allowlist,
historical test retirement map, versioned scalar correction, state-core role,
and all-module Lean aggregate make those boundaries more explicit.

The ordinary Lean root reaches 757 of 1,043 current module-tree files. The new
`ToeFormalAll` root imports every module and revealed defects that isolated
module builds could not: unsupported declarations, import cycles, missing
section closures, stale proof routes, and duplicate public names. Keeping both
roots is effective: the ordinary root remains the development path; the
exhaustive root is the integration boundary.

## 8. Automation and validation assessment

Strengths:

- deterministic JSON generation/checking and frozen hash chains;
- exact governance selection counts and SHA-256 hashes;
- strong negative controls in scientific review gates;
- strict JSON duplicate-key/nonfinite checks;
- a bounded Lean wrapper using `LEAN_NUM_THREADS=1` or `2`;
- CI installation from an exact direct/transitive lock;
- newly enforced all-module coverage, import acyclicity, public-name uniqueness,
  and `constant`-assumption prohibition; and
- reproducible canonical observable regeneration.

Limits:

- several gates historically validated literal tokens more strongly than the
  underlying compile truth. The stale CI `lake build` assertion and impossible
  GR01 forward-route token were repaired examples.
- source regex gates complement but do not replace kernel-level dependency
  inspection such as `#print axioms` on selected public theorems.
- local full pytest is expensive (about 14.5 minutes cold) and includes a
  worktree-mutating test.
- external CI was not invoked in this audit.

## 9. Governance and release-control assessment

Authoritative current surfaces agree on the live target after repair. The
registry, current-authority document, README, state core, roadmap, Lean current
frontier, and focused authority/freshness gates consistently identify unit
ledger execution. Historical exact-token records remain visibly prefixed as
historical and do not override current authority.

The 6 critical and 44 integrity manifest paths are now count/hash enforced.
The axiom ledger and public Lean declaration collision gate were added to the
integrity group. This strengthens enforcement of proof-debt and integration
boundaries without asserting scientific truth.

Release posture is unchanged: v0.1-alpha release is not complete
(`CURRENT_AUTHORITATIVE_SURFACES_v0.md:636-638`), scalar submission is not
ready, and no audit repair authorizes release assembly or publication.

## 10. Science, physics, and mathematics rigor assessment

- **DOC_SUPPORTED** — The accepted scalar result is reproducible only over the
  exact four fixed-background, fixed-coordinate chains. It is not a theorem,
  arbitrary-background proof, statistical sample, gravity evolution, Bianchi
  compatibility result, QFT-GR seam closure, CCFT validation, or master-action
  validation.
- **FOCUSED_VALIDATED** — Lean source contains 59 ledgered explicit axioms, no
  unledgered `constant` commands, and no `sorry`/`admit` tokens outside comments.
- **FOCUSED_VALIDATED** — Three first-variation assumptions formerly hidden as
  global constants are now theorem parameters. Two abstract coherence carrier
  constants are now type parameters. This makes dependencies explicit; it does
  not prove the assumptions.
- **FOCUSED_VALIDATED** — P1/P2, UCFF, CT01, FN01, and Aristotle variants now
  coexist under distinct namespaces. Their separate opaque operators and
  assumptions were preserved rather than silently equated.
- **DOC_SUPPORTED** — Current unit rows are unresolved or unknown by design.
  No dimensional closure is earned until the selected ledger execution and
  its independent review succeed.

Current release/science blockers include:

1. execution and review of the 12-row unit-mapping ledger;
2. 59 retained Lean axioms, including first-variation/master-action blockers;
3. missing scalar publication contribution-classification target;
4. no QFT-GR source admissibility/Bianchi/seam closure;
5. no full pillar or master-action validation; and
6. no public release authorization.

## 11. Maintenance and efficiency assessment

Completed optimizations:

- VS Code watcher/search exclusions for `.git`, `.venv`, `.lake`, snapshots,
  scratch, Rust target, and the 52 MB registry;
- one fresh-session/one-immutable-tranche workflow documented;
- main registry atomic writer and lightweight checker;
- all-module aggregate generation from the Git working set;
- namespace consolidation of duplicate Lean variants;
- exact dependency locks updated to advisory-clean versions;
- 24 verified rebuildable cache/debris targets removed, reclaiming
  158,143,252 bytes; and
- invalid empty `archive/.git` skeleton removed after preservation.

Retained intentionally:

- main `.lake` packages/build cache (about 13.5 GB) because exhaustive rebuilds
  are expensive;
- `.venv`;
- all tooling snapshots pending content-addressed migration;
- the quarantine repository and all ignored output; and
- all dangling Git objects (no prune/gc was run).

## 12. Authoritative-surface consistency check

Result: `FOCUSED_VALIDATED` and coherent.

| Surface | Current target/result |
| --- | --- |
| registry current projection | `execute_pillar_seam_unit_mapping_ledger_v0` |
| `CURRENT_AUTHORITATIVE_SURFACES_v0.md:449-453` | same target and guardrail report |
| `README.md:259-260` | same current/previous pair |
| state core and generated mirrors | historical role plus current target |
| roadmap/state theory | current unit-ledger lane, no promotion |
| Lean `CrossPillarClosureFrontier` | current target parity restored |
| authority/freshness Python gates | pass |

Historical target tokens are abundant but are explicitly historical. The 197
retirements show that historical/current ambiguity remains a maintenance risk,
not a present current-authority disagreement.

## 13. Current live-target and blocker-state check

Result: `FOCUSED_VALIDATED` and coherent.

- Consumed: `prepare_pillar_seam_unit_mapping_ledger_guardrail_packet`.
- Selected: `execute_pillar_seam_unit_mapping_ledger_v0`.
- Authorized scope: execute the exact seven pillar plus five seam rows under
  frozen conventions, typed unknown/unresolved states, restoration rules, and
  negative controls.
- Not authorized: inventing units, claiming dimensional closure, promoting a
  pillar/seam/master action, beginning publication, or treating external QCD
  literature pressure as project validation.

## 14. Recommended next actions, ordered by priority

1. Execute the already-selected 12-row unit-mapping ledger in a fresh immutable
   scientific tranche; independently review and commit it separately.
2. In a separate maintenance tranche, split the registry's current projection
   from immutable history while preserving hashes and aliases.
3. Isolate canonical-lock regeneration tests in temporary output trees.
4. Convert the 197 exact historical skips into frozen fixtures/parameters.
5. Create the missing scalar publication contribution-classification surface
   and review it before reconsidering readiness.
6. Add hash-locked dependency artifacts and pin CI action/tool installer
   provenance where practical.
7. Migrate duplicate snapshots to a content-addressed store with a reversible
   path index.
8. Shorten nonfrozen generated paths under an explicit custody map.
9. Replicate the preservation backup to a different device or remote store.

## 15. Recommended next bounded packet

The current scientific packet remains:

`execute_pillar_seam_unit_mapping_ledger_v0`

The highest-priority parallel maintenance packet is:

`split_loop_control_registry_current_projection_from_history_v0`

The maintenance packet must not displace or broaden the scientific target. It
should produce a small authoritative current file, content-addressed immutable
history shards, an alias/custody map, backward-compatible readers, deterministic
two-run reproduction, and focused authority/freshness/registry gates.

## 16. Residual risks and open questions

- Are all 59 explicit axioms intentionally retained, and which public theorems
  depend on each at kernel level?
- Which of the 197 historical/current assertions should become immutable
  fixtures versus be deleted as redundant after review?
- Can the registry be sharded without breaking external consumers that read
  raw compatibility keys?
- Which snapshot paths are independently valuable versus byte duplicates?
- Can long generated identifiers be mapped to stable short IDs without harming
  citation/provenance?
- Do the 46 opaque Lean definitions include placeholders that deserve a
  separate semantic-concretization ledger?
- Which canonical-lock tests are intentionally mutating, and can all be made
  transactional?
- Is an off-device backup destination available?

## 17. What was not audited or not fully validated

- No independent physical derivation or empirical reproduction was performed
  for every scientific claim in the repository.
- No claim was made that the candidate master action is correct or complete.
- No theorem-level `#print axioms` report was generated for every public theorem.
- External GitHub Actions were not run; CI configuration was parsed and local
  equivalents were exercised.
- Windows ACLs, alternate data streams, and off-device disaster recovery were
  not validated.
- The historical archive's 7,197 ignored files were preserved, not semantically
  classified one by one.
- The quarantine repository's 5,247 ignored files and 155 ordinary untracked
  files were preserved, not pruned or scientifically adjudicated.
- No Git garbage collection, object pruning, history rewrite, broad rename,
  mass newline normalization, or scientific result/manifest/execution-report
  regeneration was performed. Derived observable provenance locks were
  intentionally regenerated after their source manifest changed.

## Preservation record

External backup root:
`C:\Users\psboy\Documents\ToE-preservation\20260711`

The 13 artifacts total 2,108,050,849 bytes and include full tar archives,
reachable-ref bundle, binary worktree patch, untracked/ignored archives, and
three dangling-commit trees. Source pre/post fingerprints matched. See
`PRESERVATION_BACKUP_CUSTODY_20260711_v0.json`.

The backup is on the same `C:` volume and is therefore preservation-grade but
not disaster-resistant.

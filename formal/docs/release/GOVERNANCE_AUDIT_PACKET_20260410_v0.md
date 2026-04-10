# GOVERNANCE_AUDIT_PACKET_20260410_v0

## Status
- ACTIVE
- Date: 2026-04-10
- Class: GOVERNANCE_AND_CLOSURE_DIAGNOSTIC_NONCLAIM

## Objective
Publish a machine-readable governance audit packet that separates artifact growth, evidence growth, and closure growth, while pinning runtime baselines and closure-map blocker surfaces.

## Packet pointer
- formal/output/reports/governance_audit_packet_20260410_v0.json

## Required dimensions
1. artifact growth
2. evidence growth
3. closure growth

## Artifact growth tracking requirements
- artifact growth baseline declaration pointer
- artifact growth baseline report pointer
- artifact growth snapshot report pointer
- artifact growth snapshot tool pointer
- baseline counts for formal/output and formal/output/reports JSON artifacts
- current counts for formal/output and formal/output/reports JSON artifacts
- delta vs baseline for both JSON artifact scopes

## Runtime baseline requirements
- governance suite runtime baseline
- branch-health full pytest runtime baseline
- warning and hard budget thresholds for both runtime lanes

## Artifact lifecycle requirements
- lifecycle policy declaration pointer
- machine-readable policy pointer
- retention policy thresholds
- exemption classes and family rule count
- missing archive-destination count must be zero

## Closure-map requirements
- blocker count by class
- unresolved blocker classes
- row count and row-to-blocker distribution
- seam/theorem source pointers
- row owner assignments for all rows
- owner coverage ratio and missing-row list
- blocker-to-closure declaration pointer
- blocker-to-closure report pointer
- blocker class plus owning row/lane per map row
- required closure artifact and exit criterion per map row

## Promotion-readiness requirements
- promotion-readiness declaration pointer
- promotion-readiness report pointer
- readiness score (0 to 100)
- readiness status class
- explicit status-rule threshold string
- component-level sub-scores for ownership, map coverage, runtime, artifact growth, and blocker pressure

## Promotion-action policy requirements
- promotion-action policy declaration pointer
- promotion-action policy report pointer
- exhaustive action mapping for READY, CONDITIONAL, WATCH, BLOCKED
- current-status action selection aligned to readiness status
- blocked status disallows promotion actions
- conditional status allows limited tranche classes only
- watch and blocked statuses require exception artifact pointers

## Freshness requirements
- freshness snapshot declaration pointer
- freshness snapshot report pointer
- max-age budget for required governance inputs
- per-source freshness status and age measurements
- stale-input effect must invalidate readiness and promotion eligibility
- freshness summary must expose stale input list and overall freshness status

## Blocker trend window requirements
- blocker trend window declaration pointer
- blocker trend window report pointer
- window start/end and tranche id
- blocker counts prior/current/net delta
- trend movement status
- movement rule requiring exception when net delta is non-negative
- exception requirement with artifact pointer when required

## Operational closeout requirements
- operational closeout declaration pointer
- operational closeout report pointer
- explicit closeout rule id and required packet section list
- criteria booleans for controls, acceptance, and anchor hygiene
- closeout status is COMPLETE only when all criteria are true
- closeout next-action field reflects complete vs incomplete state

## Gate hook
- formal/python/tests/test_governance_audit_packet_gate.py

## Non-claim boundary
This packet is a repository-local control artifact and does not assert physics or mathematics completeness.

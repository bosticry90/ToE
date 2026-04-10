# ARTIFACT_LIFECYCLE_POLICY_20260410_v0

## Status
- ACTIVE
- Date: 2026-04-10
- Class: RETENTION_AND_ARCHIVE_CONTROL_NONCLAIM

## Objective
Constrain indefinite live-surface growth by assigning retention, archive, and exemption rules to high-growth artifact families.

## Policy pointer
- formal/docs/release/ARTIFACT_LIFECYCLE_POLICY_20260410_v0.json

## Required controls
1. every governed family must define retention threshold and archive destination
2. canonical release packets and baseline locks are exempt from timed archive
3. policy review cadence must be explicitly pinned

## Scope
- formal/output/reports/**/*.json
- formal/output/ws10_*.json
- formal/output/qm_stat_class_b_seam_physics_pilot_cycle*.json
- formal/output/cosmo_sr_class_b_seam_physics_pilot_cycle*.json

## Non-claim boundary
This lifecycle policy is a repository-local operations artifact and does not claim scientific sufficiency.

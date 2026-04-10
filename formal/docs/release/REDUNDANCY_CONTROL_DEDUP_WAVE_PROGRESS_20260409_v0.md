# REDUNDANCY_CONTROL_DEDUP_WAVE_PROGRESS_20260409_v0

Status: ACTIVE_NONLIVE_NONCLAIM
Date: 2026-04-09

Objective:
- Lock completed de-dup migration waves against regression.

Completed waves:
- Wave 1: REGISTRY_TOE_MASTER_ACTION_SEAM_REGISTRY_SINGLETON_COLLAPSE
- Wave 2: SEAM_QM_STAT_CLASS_B_PHYSICS_PILOT_SINGLETON_COLLAPSE

Regression lock criteria:
- Active pilot singleton report paths must remain absent from formal/output/reports.
- Archived pilot singleton report paths must remain present under archive/output/reports.
- Admission semantics must stay targeted to full-family registry and seam indexes.
- Wave declarations and reports must remain present for both completed waves.

Wave declaration pointers:
- formal/docs/release/REDUNDANCY_CONTROL_REGISTRY_DEDUP_WAVE1_DECLARATION_20260409_v0.md
- formal/docs/release/REDUNDANCY_CONTROL_SEAM_DEDUP_WAVE2_DECLARATION_20260409_v0.md

Wave report pointers:
- formal/output/reports/redundancy_control_registry_dedup_wave1_20260409_v0.json
- formal/output/reports/redundancy_control_seam_dedup_wave2_20260409_v0.json

Progress report pointer:
- formal/output/reports/redundancy_control_dedup_wave_progress_20260409_v0.json

Gate:
- formal/python/tests/test_redundancy_control_dedup_wave_progress_gate.py

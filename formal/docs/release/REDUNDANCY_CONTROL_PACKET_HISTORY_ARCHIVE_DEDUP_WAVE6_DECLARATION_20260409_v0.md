# REDUNDANCY_CONTROL_PACKET_HISTORY_ARCHIVE_DEDUP_WAVE6_DECLARATION_20260409_v0

Status: RUN_BOUNDED_v0_NONCLAIM
Date: 2026-04-09
Scope: ONE_SURFACE_ONLY
Family: PACKET_HISTORY_SUPPORT_SURFACES

Objective:
- Retire a redundant active packet-history support surface from the release path while preserving archival traceability and keeping compact packet-posture authority unchanged.

Superseded active support surface removed:
- formal/docs/release/TOE_PACKET_HISTORY_ARCHIVE_v0.md

Archived support surface path:
- archive/docs/release/TOE_PACKET_HISTORY_ARCHIVE_v0.md

Active authority owner after migration:
- State_of_the_Theory.md

Parity pointers updated in this wave:
- State_of_the_Theory.md
- Canonical Verification Checklist.md
- formal/docs/paper/TOE_MATH_PHYSICS_INVENTORY_v0.md
- formal/python/tests/test_redundancy_control_packet_history_archive_dedup_wave6_gate.py

Rule:
- LEGACY_PACKET_HISTORY_SUPPORT_SURFACE_MUST_BE_ARCHIVED_AND_COMPACT_PACKET_POSTURE_AUTHORITY_MUST_REMAIN_ACTIVE
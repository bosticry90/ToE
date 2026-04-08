# Conftest Sys.Path Allowlist Policy v0

Policy ID:
- `CONFTEST_SYS_PATH_ALLOWLIST_POLICY_v0`

Scope:
- governs temporary pre-repo-root path exceptions in `formal/python/tests/conftest.py`.

Canonical posture:
- default allowlist is empty.
- archive-path quarantine is always enforced.

Exception process:
1. exception must be test-scoped and temporary.
2. exception must set `pytest._toe_sys_path_pre_root_allowlist` explicitly.
3. exception rationale must be documented in the test or tranche note.
4. exception must not bypass archive quarantine checks.

Non-claim boundary:
- this policy governs import hygiene only.
- it does not alter release-gate truth or scientific claim posture.
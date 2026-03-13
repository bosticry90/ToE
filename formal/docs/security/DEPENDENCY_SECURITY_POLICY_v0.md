# Dependency Security Policy v0

Policy ID:
- `DEPENDENCY_SECURITY_POLICY_v0`

Scope:
- Active Python environment dependency security for ToE.
- Applies to active lock baseline at `requirements.active.lock`.

Policy controls:
1. Active dependency baseline is maintained in `requirements.active.lock`.
2. Vulnerability scans run against lock baseline using:
- `./dependency_security_scan.ps1`
3. Governance gate coverage includes:
- `formal/python/tests/test_active_dependency_baseline_lock_gate.py`
- `formal/python/tests/test_dependency_security_scan_schedule_gate.py`

Cadence:
- Run dependency security scan weekly and before release packaging.
- Run immediately after dependency upgrades.

Response policy:
1. If vulnerabilities are detected, patch affected packages to fixed versions.
2. Regenerate `requirements.active.lock` after patching.
3. Re-run focused scalar-route suite and governance checks.

Non-claim boundary:
- This policy does not assert zero-day immunity.
- This policy does not replace manual review of high-impact advisories.

# CONFTEST Stability Protocol v0

Document ID: CONFTEST_STABILITY_PROTOCOL_v0
Owner: Governance
Status: Active
Last-Updated: 2026-04-06

## Authority Tokens

CONFTEST_STABILITY_POLICY_v0: REVIEW_AND_GOVERNANCE_SUITE_REQUIRED
CONFTEST_STABILITY_CANONICAL_PATH_v0: formal/python/tests/conftest.py
CONFTEST_STABILITY_SHA256_v0: 21dd95ce36b33932c4bc0b7b4b0160bc5bbe3898c5a51025e0b0bb581e89e393
CONFTEST_STABILITY_NORMALIZATION_v0: LF_NEWLINES_BYTES_SHA256
CONFTEST_STABILITY_APPROVAL_RECORD_v0: DCR_REQUIRED
CONFTEST_STABILITY_GOVERNANCE_GATE_v0: formal/python/tests/test_conftest_signature_stability_gate.py

## Policy

- Any change to `formal/python/tests/conftest.py` requires explicit review.
- Any approved change must update `CONFTEST_STABILITY_SHA256_v0` in this file.
- Any approved change must run `./governance_suite.ps1` before merge.
- Any approved change must retain repository-root path quarantine behavior and archive exclusion behavior.

## Update Procedure

1. Edit `formal/python/tests/conftest.py`.
2. Compute normalized hash using LF newline normalization.
3. Replace `CONFTEST_STABILITY_SHA256_v0` with the new hash.
4. Run `./governance_suite.ps1` and confirm pass.
5. Include a DCR or equivalent approval record in the changeset.

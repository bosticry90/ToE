from __future__ import annotations

import hashlib
import re
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
CONFTEST_PATH = REPO_ROOT / "formal" / "python" / "tests" / "conftest.py"
PROTOCOL_PATH = REPO_ROOT / "formal" / "docs" / "release" / "CONFTEST_STABILITY_PROTOCOL_v0.md"
SUITE_PATH = REPO_ROOT / "governance_suite.ps1"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _normalized_sha256(path: Path) -> str:
    data = path.read_bytes().replace(b"\r\n", b"\n")
    return hashlib.sha256(data).hexdigest()


def _extract_protocol_hash(protocol_text: str) -> str:
    match = re.search(r"\bCONFTEST_STABILITY_SHA256_v0\s*:\s*([0-9a-f]{64})\b", protocol_text)
    assert match is not None, "Missing CONFTEST_STABILITY_SHA256_v0 token in protocol doc."
    return match.group(1)


def test_conftest_stability_protocol_contract_tokens_are_present() -> None:
    text = _read(PROTOCOL_PATH)
    required_tokens = [
        "CONFTEST_STABILITY_PROTOCOL_v0",
        "CONFTEST_STABILITY_POLICY_v0: REVIEW_AND_GOVERNANCE_SUITE_REQUIRED",
        "CONFTEST_STABILITY_CANONICAL_PATH_v0: formal/python/tests/conftest.py",
        "CONFTEST_STABILITY_NORMALIZATION_v0: LF_NEWLINES_BYTES_SHA256",
        "CONFTEST_STABILITY_APPROVAL_RECORD_v0: DCR_REQUIRED",
        "CONFTEST_STABILITY_GOVERNANCE_GATE_v0: formal/python/tests/test_conftest_signature_stability_gate.py",
        "./governance_suite.ps1",
    ]
    missing = [token for token in required_tokens if token not in text]
    assert not missing, "Conftest stability protocol token drift: " + ", ".join(missing)


def test_conftest_signature_matches_protocol_pin() -> None:
    protocol_text = _read(PROTOCOL_PATH)
    expected_hash = _extract_protocol_hash(protocol_text)
    current_hash = _normalized_sha256(CONFTEST_PATH)

    assert current_hash == expected_hash, (
        "conftest.py hash drift detected.\n"
        f"Expected: {expected_hash}\n"
        f"Current:  {current_hash}\n"
        "Update CONFTEST_STABILITY_SHA256_v0 in formal/docs/release/CONFTEST_STABILITY_PROTOCOL_v0.md "
        "after approved conftest changes."
    )


def test_governance_suite_executes_conftest_stability_gate() -> None:
    suite_text = _read(SUITE_PATH)
    gate_relpath = "formal/python/tests/test_conftest_signature_stability_gate.py"
    assert gate_relpath in suite_text, "governance_suite.ps1 must execute the conftest stability gate."

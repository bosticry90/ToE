from __future__ import annotations

import hashlib
import json
import re
import subprocess
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.prompt_dependency_identity import identity_sha256_path


ROOT = find_repo_root(Path(__file__))
BASE_COMMIT = "8f2d2052ab3862db04ea70d85037dbf2d131c8ca"
RECOVERY_ACCEPTED_BASE_COMMIT = (
    "a099c6867493d48a7aaba2f79bf2e29ecbf2cfd3"
)
ADJUDICATION_PATH = (
    ROOT
    / "formal/docs/release/PROMPT_DEPENDENCY_ROLE_ADJUDICATION_20260722_v0.json"
)
LEGACY_CRLF_SHA256 = (
    "2bc6996ea28e96c50e688ed3d30ee24808af411a244eb594aad89ff80fda8433"
)


def _record() -> dict:
    return json.loads(ADJUDICATION_PATH.read_text(encoding="utf-8"))


def _git_bytes(commit: str, path: str) -> bytes:
    return subprocess.check_output(
        ["git", "cat-file", "blob", f"{commit}:{path}"], cwd=ROOT
    )


def test_all_43_consumers_have_exactly_one_reviewed_disposition() -> None:
    record = _record()
    consumers = record["consumers"]
    paths = [item["consumer_path"] for item in consumers]
    allowed = {
        "REMOVE_DEPENDENCY",
        "DEMOTE_TO_NONBLOCKING_PROVENANCE",
        "RETAIN_AS_REPRODUCIBILITY_BLOB_IDENTITY",
        "RETAIN_AS_EXPLICIT_CANONICAL_EXPORT_IDENTITY",
    }
    assert len(consumers) == len(set(paths)) == 43
    assert all(item["disposition"] in allowed for item in consumers)
    assert record["disposition_counts"] == {
        "REMOVE_DEPENDENCY": 0,
        "DEMOTE_TO_NONBLOCKING_PROVENANCE": 41,
        "RETAIN_AS_REPRODUCIBILITY_BLOB_IDENTITY": 2,
        "RETAIN_AS_EXPLICIT_CANONICAL_EXPORT_IDENTITY": 0,
    }
    assert record["blind_global_hash_replacement_performed"] is False


def test_legacy_hash_occurs_only_in_the_adjudicated_consumer_inventory() -> None:
    expected = {item["consumer_path"] for item in _record()["consumers"]}
    observed = {
        path.relative_to(ROOT).as_posix()
        for path in (ROOT / "formal/python/tools").glob("*.py")
        if LEGACY_CRLF_SHA256 in path.read_text(encoding="utf-8")
    }
    assert observed == expected


def test_all_41_demoted_consumers_are_nonblocking_and_checkout_byte_free() -> None:
    demoted = [
        item
        for item in _record()["consumers"]
        if item["disposition"] == "DEMOTE_TO_NONBLOCKING_PROVENANCE"
    ]
    assert len(demoted) == 41
    for item in demoted:
        text = (ROOT / item["consumer_path"]).read_text(encoding="utf-8")
        assert (
            'PROMPT_DEPENDENCY_ROLE = "DEMOTE_TO_NONBLOCKING_PROVENANCE"'
            in text
        )
        assert "prompt_dependency_is_nonblocking" in text
        assert not re.search(
            r"sha256_path\((?:REPO_ROOT|ROOT) / PROMPT_RELATIVE_PATH\)", text
        )
        assert not re.search(r"PROMPT[^\n]*read_bytes|read_bytes[^\n]*PROMPT", text)


def test_v2_pair_retains_reviewed_frozen_git_blob_identity() -> None:
    retained = [
        item
        for item in _record()["consumers"]
        if item["disposition"] == "RETAIN_AS_REPRODUCIBILITY_BLOB_IDENTITY"
    ]
    assert len(retained) == 2
    for item in retained:
        text = (ROOT / item["consumer_path"]).read_text(encoding="utf-8")
        assert "FROZEN_COMMIT_RECORD_RELATIVE_PATH" in text
    generator = (ROOT / retained[0]["consumer_path"]).read_text(encoding="utf-8")
    review = (ROOT / retained[1]["consumer_path"]).read_text(encoding="utf-8")
    combined = generator + review
    assert "_frozen_identity(PROMPT_RELATIVE_PATH)" in combined
    assert '_identity_matches(packet.get("prompt_protection", {}))' in combined


def test_modified_legacy_tests_replace_only_the_raw_byte_obligation() -> None:
    bindings = _record()["modified_test_obligation_source_identities"]
    assert len(bindings) == 39
    for binding in bindings:
        text = (ROOT / binding["path"]).read_text(encoding="utf-8")
        assert "PROMPT_DEPENDENCY_ROLE" in text
        assert not re.search(
            r"sha256_path\([^\n]*PROMPT|read_bytes\([^\n]*PROMPT", text
        )
        assert binding["scientific_content_effect"] == "NONE"


def test_frozen_semantic_generator_identity_preserves_historical_artifacts() -> None:
    sample = next(
        item
        for item in _record()["consumers"]
        if item["disposition"] == "DEMOTE_TO_NONBLOCKING_PROVENANCE"
    )
    path = ROOT / sample["consumer_path"]
    expected = hashlib.sha256(
        _git_bytes(BASE_COMMIT, sample["consumer_path"])
    ).hexdigest()
    assert identity_sha256_path(path, repo_root=ROOT) == expected
    assert hashlib.sha256(path.read_bytes()).hexdigest() != expected


def test_prompt_blob_and_scientific_governance_artifacts_are_unchanged() -> None:
    base_prompt = _git_bytes(BASE_COMMIT, "Prompt.txt")
    head_prompt = _git_bytes("HEAD", "Prompt.txt")
    assert head_prompt == base_prompt
    assert hashlib.sha256(head_prompt).hexdigest() == (
        "35cfeb3dcec5246d926af60afabbc23d1bbe814689d1b54ad8718e02fae924c5"
    )
    changed_output = subprocess.run(
        [
            "git",
            "diff",
            "--name-only",
            BASE_COMMIT,
            RECOVERY_ACCEPTED_BASE_COMMIT,
            "--",
            "formal/output",
        ],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.splitlines()
    assert changed_output
    assert all(
        path.replace("\\", "/").startswith("formal/output/validation_profiles/")
        for path in changed_output
    )
    protected = ["formal/toe_formal", "formal/registry", "registry"]
    changed_protected = subprocess.run(
        [
            "git",
            "diff",
            "--name-only",
            BASE_COMMIT,
            RECOVERY_ACCEPTED_BASE_COMMIT,
            "--",
            *protected,
        ],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.splitlines()
    assert [path.replace("\\", "/") for path in changed_protected] == [
        "formal/toe_formal/build.ps1"
    ]
    subprocess.run(
        [
            "git",
            "merge-base",
            "--is-ancestor",
            RECOVERY_ACCEPTED_BASE_COMMIT,
            "HEAD",
        ],
        cwd=ROOT,
        check=True,
        capture_output=True,
    )


def test_canonical_executor_does_not_validate_prompt_checkout_bytes() -> None:
    path = (
        ROOT
        / "formal/python/tools/"
        "dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
        "canonical_execution_v2.py"
    )
    text = path.read_text(encoding="utf-8")
    loop = (
        "for path, expected in FROZEN_HASHES.items():\n"
        "        if path == PROMPT_PATH:\n"
        "            continue\n"
        "        actual = sha256_path(REPO_ROOT / path)"
    )
    assert loop in text

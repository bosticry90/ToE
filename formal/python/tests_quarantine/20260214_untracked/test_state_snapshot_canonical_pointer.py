from __future__ import annotations

import hashlib
import re
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
OUTPUT_DIR = REPO_ROOT / "formal" / "output"
POINTER = OUTPUT_DIR / "LATEST_STATE_SNAPSHOT.txt"


def _read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def _parse_key_value_lines(text: str) -> dict[str, str]:
    out: dict[str, str] = {}
    for raw in text.splitlines():
        line = raw.strip()
        if not line or ":" not in line:
            continue
        key, value = line.split(":", 1)
        out[key.strip().lower()] = value.strip()
    return out


def _sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _latest_pass_snapshot_relpath() -> str:
    candidates: list[tuple[int, int, str]] = []
    pattern = re.compile(r"state_snapshot_(\d{8})_(\d+)_pass\.md$")
    for p in OUTPUT_DIR.glob("state_snapshot_*_pass.md"):
        m = pattern.match(p.name)
        if m is None:
            continue
        date_token = int(m.group(1))
        pass_count = int(m.group(2))
        candidates.append((date_token, pass_count, f"formal/output/{p.name}"))
    assert candidates, "No pass snapshots found under formal/output."
    candidates.sort()
    return candidates[-1][2]


def _all_pass_snapshot_hashes() -> dict[str, str]:
    out: dict[str, str] = {}
    pattern = re.compile(r"state_snapshot_(\d{8})_(\d+)_pass\.sha256\.txt$")
    for p in OUTPUT_DIR.glob("state_snapshot_*_pass.sha256.txt"):
        if pattern.match(p.name) is None:
            continue
        kv = _parse_key_value_lines(_read_text(p))
        sha = kv.get("sha256", "")
        assert re.fullmatch(r"[0-9a-f]{64}", sha), f"Invalid sha256 entry in {p.as_posix()}"
        out[p.name] = sha
    assert out, "No pass snapshot hash manifests found under formal/output."
    return out


def test_latest_state_snapshot_pointer_is_present_and_correct() -> None:
    assert POINTER.exists(), f"Missing canonical pointer: {POINTER.as_posix()}"
    kv = _parse_key_value_lines(_read_text(POINTER))
    assert "snapshot" in kv, "Pointer is missing 'snapshot' entry."
    assert "sha256" in kv, "Pointer is missing 'sha256' entry."

    snapshot_rel = kv["snapshot"]
    expected_latest = _latest_pass_snapshot_relpath()
    assert snapshot_rel == expected_latest, (
        "Pointer does not reference latest pass snapshot by date/pass count.\n"
        f"expected={expected_latest}\nactual={snapshot_rel}"
    )

    snapshot_path = REPO_ROOT / snapshot_rel
    assert snapshot_path.exists(), f"Pointer snapshot is missing: {snapshot_rel}"
    actual_hash = _sha256_file(snapshot_path)
    assert kv["sha256"] == actual_hash, "Pointer sha256 does not match snapshot bytes."


def test_pass_snapshot_hash_references_are_unique() -> None:
    hashes = _all_pass_snapshot_hashes()
    rev: dict[str, list[str]] = {}
    for fname, sha in hashes.items():
        rev.setdefault(sha, []).append(fname)
    duplicates = {sha: files for sha, files in rev.items() if len(files) > 1}
    assert duplicates == {}, (
        "Duplicate pass-snapshot sha256 references detected:\n"
        + "\n".join(f"{sha}: {sorted(files)}" for sha, files in sorted(duplicates.items()))
    )


def test_docs_and_tests_do_not_hardcode_old_pass_snapshot_paths() -> None:
    kv = _parse_key_value_lines(_read_text(POINTER))
    canonical_snapshot = kv["snapshot"]
    concrete_snapshot_re = re.compile(r"formal/output/state_snapshot_\d{8}_\d+_pass\.md")

    scan_roots = [
        REPO_ROOT / "State_of_the_Theory.md",
        REPO_ROOT / "formal" / "docs",
        REPO_ROOT / "formal" / "python" / "tests",
    ]
    offenders: list[tuple[str, str]] = []
    for root in scan_roots:
        files = [root] if root.is_file() else [p for p in root.rglob("*") if p.is_file()]
        for path in files:
            try:
                text = _read_text(path)
            except UnicodeDecodeError:
                continue
            for m in concrete_snapshot_re.finditer(text):
                hit = m.group(0)
                if hit != canonical_snapshot:
                    offenders.append((path.as_posix(), hit))

    assert offenders == [], (
        "Found non-canonical hardcoded pass snapshot paths in docs/tests:\n"
        + "\n".join(f"{p}: {hit}" for p, hit in offenders)
    )

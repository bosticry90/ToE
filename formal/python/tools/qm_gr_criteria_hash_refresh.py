from __future__ import annotations

if __name__ == "__main__" and (__package__ is None or __package__ == ""):
    from pathlib import Path as _Path

    _tool = _Path(__file__).stem
    raise SystemExit(
        "Do not run this tool as a script.\n"
        "Run it as a module so package imports resolve.\n\n"
        f"  .\\py.ps1 -m formal.python.tools.{_tool} --help\n"
    )

import argparse
import difflib
import hashlib
import re
from dataclasses import dataclass
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


@dataclass(frozen=True)
class HashTokenSpec:
    artifact_relpath: str
    token_label: str
    token_files: tuple[str, ...]


@dataclass(frozen=True)
class HashMismatch:
    artifact_relpath: str
    token_label: str
    token_file: str
    current: str
    expected: str
    identity_type: str = "CANONICAL_ARTIFACT_SHA256"

    def message(self) -> str:
        return (
            f"drift {self.token_label} in {self.token_file}: "
            f"identity_type={self.identity_type} expected={self.expected} "
            f"current={self.current}"
        )



REPO_ROOT = find_repo_root(Path(__file__))

DEFAULT_SPECS: tuple[HashTokenSpec, ...] = (
    HashTokenSpec(
        artifact_relpath="formal/output/qm_full_derivation_discharge_criteria_cycle10_v0.json",
        token_label="QM_FULL_DERIVATION_DISCHARGE_CRITERIA_ARTIFACT_SHA256_v0",
        token_files=(
            "formal/docs/paper/DERIVATION_TARGET_QM_FULL_DERIVATION_DISCHARGE_v0.md",
            "State_of_the_Theory.md",
        ),
    ),
    HashTokenSpec(
        artifact_relpath="formal/output/gr_continuum_discharge_criteria_cycle10_v0.json",
        token_label="GR_CONTINUUM_LIMIT_DISCHARGE_CRITERIA_ARTIFACT_SHA256_v0",
        token_files=(
            "formal/docs/paper/DERIVATION_TARGET_GR_CONTINUUM_LIMIT_BRIDGE_v0.md",
            "State_of_the_Theory.md",
        ),
    ),
    HashTokenSpec(
        artifact_relpath="formal/output/gr_strong_field_discharge_criteria_cycle10_v0.json",
        token_label="GR_STRONG_FIELD_REGIME_DISCHARGE_CRITERIA_ARTIFACT_SHA256_v0",
        token_files=(
            "formal/docs/paper/DERIVATION_TARGET_GR_STRONG_FIELD_REGIME_v0.md",
            "State_of_the_Theory.md",
        ),
    ),
    HashTokenSpec(
        artifact_relpath="formal/output/qm_gr_integrated_discharge_criteria_cycle10_v0.json",
        token_label="QM_GR_INTEGRATED_DISCHARGE_CRITERIA_ARTIFACT_SHA256_v0",
        token_files=(
            "formal/docs/paper/QM_GR_CROSS_LANE_COMPATIBILITY_BUNDLE_v0.md",
            "State_of_the_Theory.md",
        ),
    ),
)


def _sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def _extract_sha_token_value(raw: bytes, token_label: str) -> str | None:
    label = re.escape(token_label.encode("ascii"))
    m = re.search(label + rb":\s*([0-9a-f]{64})", raw)
    if m is None:
        return None
    return m.group(1).decode("ascii")


def _replace_sha_token_value(
    raw: bytes, token_label: str, new_value: str
) -> tuple[bytes, int]:
    label = re.escape(token_label.encode("ascii"))
    pattern = re.compile(rb"(" + label + rb":\s*)([0-9a-f]{64})")
    replacement = rb"\g<1>" + new_value.encode("ascii")
    return pattern.subn(replacement, raw, count=1)


def check_expected_hashes(
    *, repo_root: Path, specs: tuple[HashTokenSpec, ...] = DEFAULT_SPECS
) -> list[HashMismatch]:
    """Check canonical-artifact tokens without writing to the inspected tree."""
    mismatches: list[HashMismatch] = []
    for spec in specs:
        artifact_path = (repo_root / spec.artifact_relpath).resolve()
        if not artifact_path.exists():
            raise FileNotFoundError(f"Missing artifact: {spec.artifact_relpath}")

        expected = _sha256_file(artifact_path)
        for rel in spec.token_files:
            token_file = (repo_root / rel).resolve()
            if not token_file.exists():
                raise FileNotFoundError(f"Missing token file: {rel}")

            current = _extract_sha_token_value(token_file.read_bytes(), spec.token_label)
            if current is None:
                raise ValueError(f"Missing token: {spec.token_label} in {rel}")
            if current != expected:
                mismatches.append(
                    HashMismatch(
                        artifact_relpath=spec.artifact_relpath,
                        token_label=spec.token_label,
                        token_file=rel,
                        current=current,
                        expected=expected,
                    )
                )
    return mismatches


def collect_drift(
    *, repo_root: Path, specs: tuple[HashTokenSpec, ...] = DEFAULT_SPECS
) -> list[str]:
    """Compatibility wrapper returning the former string diagnostics."""
    return [item.message() for item in check_expected_hashes(repo_root=repo_root, specs=specs)]


def proposed_diff(*, repo_root: Path, mismatches: list[HashMismatch]) -> str:
    """Return the maintenance diff that would repair mismatches; never write it."""
    by_file: dict[str, list[HashMismatch]] = {}
    for mismatch in mismatches:
        by_file.setdefault(mismatch.token_file, []).append(mismatch)

    chunks: list[str] = []
    for rel in sorted(by_file):
        before = (repo_root / rel).read_bytes()
        after = before
        for mismatch in by_file[rel]:
            after, count = _replace_sha_token_value(
                after, mismatch.token_label, mismatch.expected
            )
            if count != 1:
                raise ValueError(
                    f"Expected exactly one proposed replacement for "
                    f"{mismatch.token_label} in {rel}, got {count}"
                )
        chunks.extend(
            difflib.unified_diff(
                before.decode("utf-8").splitlines(),
                after.decode("utf-8").splitlines(),
                fromfile=f"a/{rel}",
                tofile=f"b/{rel}",
                lineterm="",
            )
        )
    return "\n".join(chunks)


def apply_updates(
    *,
    repo_root: Path,
    specs: tuple[HashTokenSpec, ...] = DEFAULT_SPECS,
    allow_repository_root: bool = False,
) -> list[str]:
    """Apply authorized maintenance updates while preserving all non-token bytes."""
    if repo_root.resolve() == REPO_ROOT.resolve() and not allow_repository_root:
        raise PermissionError(
            "Repository-root writes require the explicit maintenance CLI authorization flag"
        )

    changed: list[str] = []
    file_cache: dict[Path, bytes] = {}

    for spec in specs:
        artifact_path = (repo_root / spec.artifact_relpath).resolve()
        if not artifact_path.exists():
            raise FileNotFoundError(f"Missing artifact: {spec.artifact_relpath}")

        expected = _sha256_file(artifact_path)
        for rel in spec.token_files:
            token_file = (repo_root / rel).resolve()
            if not token_file.exists():
                raise FileNotFoundError(f"Missing token file: {rel}")

            raw = file_cache.get(token_file)
            if raw is None:
                raw = token_file.read_bytes()

            current = _extract_sha_token_value(raw, spec.token_label)
            if current is None:
                raise ValueError(f"Missing token: {spec.token_label} in {rel}")

            if current == expected:
                file_cache[token_file] = raw
                continue

            updated, count = _replace_sha_token_value(raw, spec.token_label, expected)
            if count != 1:
                raise ValueError(
                    f"Expected exactly one replacement for {spec.token_label} in {rel}, got {count}"
                )
            file_cache[token_file] = updated
            if rel not in changed:
                changed.append(rel)

    for rel in changed:
        token_file = (repo_root / rel).resolve()
        token_file.write_bytes(file_cache[token_file])

    return changed


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(
        description=(
            "Refresh or verify SHA-256 tokens for Cycle-010 QM/GR discharge-criteria manifests."
        )
    )
    ap.add_argument(
        "--mode",
        choices=("check", "write"),
        default="check",
        help="check: verify token drift only; write: refresh token values in tracked markdown files.",
    )
    ap.add_argument(
        "--authorize-maintenance-write",
        action="store_true",
        help="required with --mode write when updating the checked-out repository root",
    )
    args = ap.parse_args(argv)

    if args.mode == "check":
        mismatches = check_expected_hashes(repo_root=REPO_ROOT)
        if mismatches:
            for mismatch in mismatches:
                print(mismatch.message())
            print("PROPOSED_DIFF")
            print(proposed_diff(repo_root=REPO_ROOT, mismatches=mismatches))
            return 1
        print("OK: no hash-token drift")
        return 0

    if not args.authorize_maintenance_write:
        ap.error("--mode write requires --authorize-maintenance-write")

    changed = apply_updates(
        repo_root=REPO_ROOT,
        allow_repository_root=True,
    )
    if changed:
        print("UPDATED")
        for rel in changed:
            print(rel)
    else:
        print("NO_CHANGES")

    mismatches_after = check_expected_hashes(repo_root=REPO_ROOT)
    if mismatches_after:
        for mismatch in mismatches_after:
            print(mismatch.message())
        return 2
    print("OK: no hash-token drift")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

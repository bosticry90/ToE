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
import hashlib
import re
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class HashTokenSpec:
    artifact_relpath: str
    token_label: str
    token_files: tuple[str, ...]


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = _find_repo_root(Path(__file__))

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


def _extract_sha_token_value(text: str, token_label: str) -> str | None:
    m = re.search(rf"{re.escape(token_label)}:\s*([0-9a-f]{{64}})", text)
    if m is None:
        return None
    return m.group(1)


def _replace_sha_token_value(text: str, token_label: str, new_value: str) -> tuple[str, int]:
    pattern = re.compile(rf"({re.escape(token_label)}:\s*)([0-9a-f]{{64}})")
    return pattern.subn(rf"\g<1>{new_value}", text, count=1)


def collect_drift(*, repo_root: Path, specs: tuple[HashTokenSpec, ...] = DEFAULT_SPECS) -> list[str]:
    errors: list[str] = []
    for spec in specs:
        artifact_path = (repo_root / spec.artifact_relpath).resolve()
        if not artifact_path.exists():
            errors.append(f"missing artifact: {spec.artifact_relpath}")
            continue

        expected = _sha256_file(artifact_path)
        for rel in spec.token_files:
            token_file = (repo_root / rel).resolve()
            if not token_file.exists():
                errors.append(f"missing token file: {rel}")
                continue

            text = token_file.read_text(encoding="utf-8")
            current = _extract_sha_token_value(text, spec.token_label)
            if current is None:
                errors.append(f"missing token: {spec.token_label} in {rel}")
                continue
            if current != expected:
                errors.append(
                    f"drift {spec.token_label} in {rel}: expected={expected} current={current}"
                )
    return errors


def apply_updates(*, repo_root: Path, specs: tuple[HashTokenSpec, ...] = DEFAULT_SPECS) -> list[str]:
    changed: list[str] = []
    file_cache: dict[Path, str] = {}

    for spec in specs:
        artifact_path = (repo_root / spec.artifact_relpath).resolve()
        if not artifact_path.exists():
            raise FileNotFoundError(f"Missing artifact: {spec.artifact_relpath}")

        expected = _sha256_file(artifact_path)
        for rel in spec.token_files:
            token_file = (repo_root / rel).resolve()
            if not token_file.exists():
                raise FileNotFoundError(f"Missing token file: {rel}")

            text = file_cache.get(token_file)
            if text is None:
                text = token_file.read_text(encoding="utf-8")

            current = _extract_sha_token_value(text, spec.token_label)
            if current is None:
                raise ValueError(f"Missing token: {spec.token_label} in {rel}")

            if current == expected:
                file_cache[token_file] = text
                continue

            updated, count = _replace_sha_token_value(text, spec.token_label, expected)
            if count != 1:
                raise ValueError(
                    f"Expected exactly one replacement for {spec.token_label} in {rel}, got {count}"
                )
            file_cache[token_file] = updated
            if rel not in changed:
                changed.append(rel)

    for rel in changed:
        token_file = (repo_root / rel).resolve()
        token_file.write_text(file_cache[token_file], encoding="utf-8")

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
    args = ap.parse_args(argv)

    if args.mode == "check":
        drifts = collect_drift(repo_root=REPO_ROOT)
        if drifts:
            for row in drifts:
                print(row)
            return 1
        print("OK: no hash-token drift")
        return 0

    changed = apply_updates(repo_root=REPO_ROOT)
    if changed:
        print("UPDATED")
        for rel in changed:
            print(rel)
    else:
        print("NO_CHANGES")

    drifts_after = collect_drift(repo_root=REPO_ROOT)
    if drifts_after:
        for row in drifts_after:
            print(row)
        return 2
    print("OK: no hash-token drift")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

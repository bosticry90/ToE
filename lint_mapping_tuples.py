from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable

import csv


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    if p.is_file():
        p = p.parent
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


_ALLOWED_PAIR_TYPES = {"same_source", "cross_source_hypothesis"}
_ALLOWED_SPEED_KEYS = {"snd02_single", "snd02b_seriesB"}


@dataclass(frozen=True)
class LintResult:
    errors: list[str]
    warnings: list[str]


def _iter_string_paths(obj: Any) -> Iterable[str]:
    if isinstance(obj, dict):
        for v in obj.values():
            yield from _iter_string_paths(v)
    elif isinstance(obj, list):
        for v in obj:
            yield from _iter_string_paths(v)
    elif isinstance(obj, str):
        yield obj


def lint_mapping_tuples(*, date: str = "2026-01-24", fail_fast: bool = False) -> LintResult:
    """Lint OV-BR-SND-02 mapping tuples for schema/key/path consistency.

    This is governance linting only (no physics validation).
    """

    repo_root = _find_repo_root(Path(__file__))
    mapping_path = (
        repo_root
        / "formal"
        / "external_evidence"
        / "bec_sound_density_secondary_TBD"
        / "ovbr_snd02_density_mapping"
        / "mapping_tuples.json"
    )

    errors: list[str] = []
    warnings: list[str] = []

    if not mapping_path.exists():
        errors.append(f"missing_mapping_file:{mapping_path.as_posix()}")
        if fail_fast:
            raise AssertionError("; ".join(errors))
        return LintResult(errors=errors, warnings=warnings)

    payload = json.loads(mapping_path.read_text(encoding="utf-8"))
    schema = str(payload.get("schema") or "")
    if not schema.startswith("OV-BR-SND-02_explicit_cross_source_density_mapping_tuples/"):
        errors.append("unexpected_schema")

    tuples = payload.get("mapping_tuples")
    if not isinstance(tuples, list):
        errors.append("mapping_tuples_not_list")
        tuples = []

    # Recognized keys.
    available_speed_keys = set(_ALLOWED_SPEED_KEYS)

    density_keys = {"central"}
    secondary_csv = (
        repo_root
        / "formal"
        / "external_evidence"
        / "bec_sound_density_secondary_TBD"
        / "ovsnd03n2_density_digitization"
        / "density_conditions.csv"
    )
    if secondary_csv.exists():
        rows: list[dict[str, str]] = []
        with secondary_csv.open("r", encoding="utf-8", newline="") as f:
            r = csv.DictReader(f)
            for row in r:
                rows.append({str(k): str(v) for k, v in dict(row).items()})
        density_keys |= {str(r.get("density_condition_key")) for r in rows if str(r.get("density_condition_key") or "")}

    seen_speed: set[str] = set()
    seen_den: set[str] = set()

    for idx, t in enumerate(tuples):
        if not isinstance(t, dict):
            errors.append(f"tuple_{idx}_not_object")
            continue

        speed_key = t.get("propagation_condition_key")
        den_key = t.get("density_condition_key")
        source_locators = t.get("source_locators")
        pair_type = t.get("pair_type")

        if not isinstance(speed_key, str) or not speed_key:
            errors.append(f"tuple_{idx}_missing_propagation_condition_key")
        if not isinstance(den_key, str) or not den_key:
            errors.append(f"tuple_{idx}_missing_density_condition_key")
        if not isinstance(source_locators, dict):
            errors.append(f"tuple_{idx}_missing_source_locators")

        if pair_type not in _ALLOWED_PAIR_TYPES:
            errors.append(f"tuple_{idx}_invalid_pair_type")

        if isinstance(speed_key, str) and speed_key:
            if speed_key in seen_speed:
                errors.append(f"duplicate_propagation_condition_key:{speed_key}")
            seen_speed.add(speed_key)
            if available_speed_keys and speed_key not in available_speed_keys:
                errors.append(f"unknown_propagation_condition_key:{speed_key}")

        if isinstance(den_key, str) and den_key:
            if den_key in seen_den:
                errors.append(f"duplicate_density_condition_key:{den_key}")
            seen_den.add(den_key)
            if density_keys and den_key not in density_keys:
                errors.append(f"unknown_density_condition_key:{den_key}")

        # Validate referenced source locator paths exist (best-effort).
        for s in _iter_string_paths(source_locators):
            if s.startswith("formal/") and (repo_root / s).exists() is False:
                errors.append(f"missing_source_locator_path:{s}")

    if len(tuples) < 2:
        warnings.append("mapping_tuples_lt_2")

    if fail_fast and errors:
        raise AssertionError("; ".join(errors))

    return LintResult(errors=errors, warnings=warnings)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--date", default="2026-01-24")
    p.add_argument("--fail-fast", action="store_true")
    args = p.parse_args(argv)

    res = lint_mapping_tuples(date=str(args.date), fail_fast=bool(args.fail_fast))

    if res.errors:
        print("Errors:")
        for e in res.errors:
            print(f"  - {e}")
    if res.warnings:
        print("Warnings:")
        for w in res.warnings:
            print(f"  - {w}")

    return 1 if res.errors else 0


if __name__ == "__main__":
    raise SystemExit(main())

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


_ALLOWED_PAIR_TYPES_DENSITY = {"same_source", "cross_source_hypothesis"}
_ALLOWED_PAIR_TYPES_BRAGG_SOUND = {"same_source", "cross_source_hypothesis", "cross_source_established"}

_ALLOWED_SPEED_KEYS = {"snd02_single", "snd02b_seriesB"}
_ALLOWED_BRAGG_KEYS = {"br04a_conditionA", "br04b_conditionB"}


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


def _lint_ovbr_snd02_density_mapping(*, repo_root: Path) -> LintResult:
    errors: list[str] = []
    warnings: list[str] = []

    mapping_path = (
        repo_root
        / "formal"
        / "external_evidence"
        / "bec_sound_density_secondary_TBD"
        / "ovbr_snd02_density_mapping"
        / "mapping_tuples.json"
    )
    if not mapping_path.exists():
        errors.append(f"missing_mapping_file:{mapping_path.as_posix()}")
        return LintResult(errors=errors, warnings=warnings)

    payload = json.loads(mapping_path.read_text(encoding="utf-8"))
    schema = str(payload.get("schema") or "")
    if not schema.startswith("OV-BR-SND-02_explicit_cross_source_density_mapping_tuples/"):
        errors.append("ovbr_snd02_unexpected_schema")

    tuples = payload.get("mapping_tuples")
    if not isinstance(tuples, list):
        errors.append("ovbr_snd02_mapping_tuples_not_list")
        tuples = []

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
            errors.append(f"ovbr_snd02_tuple_{idx}_not_object")
            continue

        speed_key = t.get("propagation_condition_key")
        den_key = t.get("density_condition_key")
        source_locators = t.get("source_locators")
        pair_type = t.get("pair_type")

        if not isinstance(speed_key, str) or not speed_key:
            errors.append(f"ovbr_snd02_tuple_{idx}_missing_propagation_condition_key")
        if not isinstance(den_key, str) or not den_key:
            errors.append(f"ovbr_snd02_tuple_{idx}_missing_density_condition_key")
        if not isinstance(source_locators, dict):
            errors.append(f"ovbr_snd02_tuple_{idx}_missing_source_locators")

        if pair_type not in _ALLOWED_PAIR_TYPES_DENSITY:
            errors.append(f"ovbr_snd02_tuple_{idx}_invalid_pair_type")

        if isinstance(speed_key, str) and speed_key:
            if speed_key in seen_speed:
                errors.append(f"ovbr_snd02_duplicate_propagation_condition_key:{speed_key}")
            seen_speed.add(speed_key)
            if available_speed_keys and speed_key not in available_speed_keys:
                errors.append(f"ovbr_snd02_unknown_propagation_condition_key:{speed_key}")

        if isinstance(den_key, str) and den_key:
            if den_key in seen_den:
                errors.append(f"ovbr_snd02_duplicate_density_condition_key:{den_key}")
            seen_den.add(den_key)
            if density_keys and den_key not in density_keys:
                errors.append(f"ovbr_snd02_unknown_density_condition_key:{den_key}")

        for s in _iter_string_paths(source_locators):
            if s.startswith("formal/") and (repo_root / s).exists() is False:
                errors.append(f"ovbr_snd02_missing_source_locator_path:{s}")

    if len(tuples) < 2:
        warnings.append("ovbr_snd02_mapping_tuples_lt_2")

    return LintResult(errors=errors, warnings=warnings)


def _lint_ovbr_snd03_bragg_sound_pairing(*, repo_root: Path) -> LintResult:
    errors: list[str] = []
    warnings: list[str] = []

    mapping_path = (
        repo_root
        / "formal"
        / "external_evidence"
        / "bec_bragg_sound_pairing_TBD"
        / "ovbr_snd03_bragg_sound_mapping"
        / "mapping_tuples.json"
    )
    if not mapping_path.exists():
        errors.append(f"missing_mapping_file:{mapping_path.as_posix()}")
        return LintResult(errors=errors, warnings=warnings)

    payload = json.loads(mapping_path.read_text(encoding="utf-8"))
    schema = str(payload.get("schema") or "")
    if not schema.startswith("OV-BR-SND-03_explicit_bragg_sound_pairing_tuples/"):
        errors.append("ovbr_snd03_unexpected_schema")

    tuples = payload.get("mapping_tuples")
    if not isinstance(tuples, list):
        errors.append("ovbr_snd03_mapping_tuples_not_list")
        tuples = []

    seen_ids: set[str] = set()
    for idx, t in enumerate(tuples):
        if not isinstance(t, dict):
            errors.append(f"ovbr_snd03_tuple_{idx}_not_object")
            continue

        tuple_id = t.get("tuple_id")
        bragg_key = t.get("bragg_key")
        sound_key = t.get("sound_key")
        pair_type = t.get("pair_type")
        rationale = t.get("rationale")
        source_locators = t.get("source_locators")

        if not isinstance(tuple_id, str) or not tuple_id:
            errors.append(f"ovbr_snd03_tuple_{idx}_missing_tuple_id")
        else:
            if tuple_id in seen_ids:
                errors.append(f"ovbr_snd03_duplicate_tuple_id:{tuple_id}")
            seen_ids.add(tuple_id)

        if not isinstance(bragg_key, str) or bragg_key not in _ALLOWED_BRAGG_KEYS:
            errors.append(f"ovbr_snd03_tuple_{idx}_invalid_bragg_key")
        if not isinstance(sound_key, str) or sound_key not in _ALLOWED_SPEED_KEYS:
            errors.append(f"ovbr_snd03_tuple_{idx}_invalid_sound_key")
        if pair_type not in _ALLOWED_PAIR_TYPES_BRAGG_SOUND:
            errors.append(f"ovbr_snd03_tuple_{idx}_invalid_pair_type")

        if not isinstance(rationale, str) or not rationale.strip():
            warnings.append(f"ovbr_snd03_tuple_{idx}_missing_rationale")
        if not isinstance(source_locators, dict):
            errors.append(f"ovbr_snd03_tuple_{idx}_missing_source_locators")
        else:
            for s in _iter_string_paths(source_locators):
                if s.startswith("formal/") and (repo_root / s).exists() is False:
                    errors.append(f"ovbr_snd03_missing_source_locator_path:{s}")

    return LintResult(errors=errors, warnings=warnings)


def lint_mapping_tuples(*, date: str = "2026-01-24", fail_fast: bool = False) -> LintResult:
    """Lint mapping tuple artifacts for schema/key/path consistency.

    This is governance linting only (no physics validation).
    """

    _ = date  # Reserved for future date-scoped mapping files.
    repo_root = _find_repo_root(Path(__file__))

    res02 = _lint_ovbr_snd02_density_mapping(repo_root=repo_root)
    res03 = _lint_ovbr_snd03_bragg_sound_pairing(repo_root=repo_root)

    errors = list(res02.errors) + list(res03.errors)
    warnings = list(res02.warnings) + list(res03.warnings)

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

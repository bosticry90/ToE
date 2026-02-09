"""Regenerate canonical markdown locks in a safe, dependency-aware order.

Why this exists
- Many locks embed computed JSON blocks with provenance/fingerprint fields.
- When provenance structure evolves, existing canonical locks can drift from
  `rec.to_jsonable()` and fail regression tests.

Scope
- Regenerates a small, intentionally selected set of *canonical* locks that are
  known to be sensitive to provenance-structure changes.

Usage
  python -m formal.python.tools.regen_canonical_locks --report

Notes
- This tool writes canonical locks only.
- Non-canonical / variant locks (e.g., *_DQ-01_v2.md) are not touched.
"""

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
import csv
import hashlib
import json
import os
from pathlib import Path

from formal.python.toe.observables.ovbr02_regime_bridge_record import write_ovbr02_lock
from formal.python.toe.observables.ovdq02_dq01_v2_threshold_update_record import write_ovdq02_lock
from formal.python.toe.observables.ovdq03_dq01_active_policy_activation_record import write_ovdq03_lock
from formal.python.toe.observables.snddig01_minimal_density_digitization_record import write_snddig01_lock
from formal.python.toe.observables.ovsnd01_sound_propagation_distance_time_digitized import write_ovsnd01_digitized_artifacts
from formal.python.toe.observables.ovsnd01_sound_propagation_distance_time_digitized import write_ovsnd01_digitized_lock
from formal.python.toe.observables.ovsnd01n2_sound_propagation_distance_time_digitized import write_ovsnd01n2_lock
from formal.python.toe.observables.ovsnd01n2_sound_propagation_distance_time_digitized import write_ovsnd01n2_digitized_artifacts
from formal.python.toe.observables.ovsnd01_sound_speed_scaling_record import write_ovsnd01_lock
from formal.python.toe.observables.ovsnd02_sound_speed_from_propagation_record import write_ovsnd02_lock
from formal.python.toe.observables.ovsnd02b_sound_speed_from_propagation_seriesb_record import write_ovsnd02b_lock
from formal.python.toe.observables.ovsnd03n_central_density_digitized import write_ovsnd03n_digitized_artifacts
from formal.python.toe.observables.ovsnd03n_central_density_digitized import write_ovsnd03n_digitized_lock
from formal.python.toe.observables.ovsnd03n_density_coverage_report_record import write_ovsnd03n_coverage_lock
from formal.python.toe.observables.ovsnd03n2_secondary_density_conditions_digitized import write_ovsnd03n2_lock
from formal.python.toe.observables.ovsnd03n2_secondary_density_conditions_digitized import write_ovsnd03n2_digitized_artifacts
from formal.python.toe.observables.ovsnd03_sound_speed_density_scaling_record import write_ovsnd03_lock
from formal.python.toe.observables.ovbr_snd02_cross_source_density_mapping_record import write_ovbr_snd02_lock
from formal.python.toe.observables.ovsnd04_sound_speed_density_constancy_record import write_ovsnd04_lock
from formal.python.toe.observables.ovsel_snd01_sound_anchor_ingestion_audit_record import write_ovsel_snd01_lock
from formal.python.toe.observables.ovsel_snd02_sound_anchor_interaction_stress_test_record import write_ovsel_snd02_lock
from formal.python.toe.observables.ovsel_snd03_sound_speed_derived_audit_record import write_ovsel_snd03_lock
from formal.python.toe.observables.ovsel_snd04_density_dependence_audit_record import write_ovsel_snd04_lock
from formal.python.toe.observables.ovsel_snd05_multi_density_constancy_audit_record import write_ovsel_snd05_lock
from formal.python.toe.observables.ovbr_snd01_sound_vs_bragg_lowk_comparability_record import write_ovbr_snd01_lock
from formal.python.toe.observables.ovsel01_selection_status_record import write_ovsel01_lock
from formal.python.toe.observables.ovxd04_overlap_only_preference_comparison_record import write_ovxd04_lock
from formal.python.toe.observables.ovbr03n_bragg_dispersion_k_omega_digitized import write_ovbr03n_digitized_lock
from formal.python.toe.observables.ovbr04a_bragg_lowk_slope_conditionA_record import write_ovbr04a_lock
from formal.python.toe.observables.ovbr04b_bragg_lowk_slope_conditionB_record import write_ovbr04b_lock
from formal.python.toe.observables.ovbr05_bragg_lowk_slope_summary_record import write_ovbr05_lock
from formal.python.toe.observables.ovdrbr00_br01_prediction_declarations_record import write_ovdrbr00_lock
from formal.python.toe.observables.ovdrbr01_candidate_pruning_table_record import write_ovdrbr01_lock
from formal.python.toe.observables.ovsel_br01_bragg_lowk_slope_audit_record import write_ovsel_br01_lock
from formal.python.toe.observables.ovbr_snd03_cross_lane_lowk_consistency_audit_record import write_ovbr_snd03_lock
from formal.python.toe.observables.ovbrfn00_fn01_metric_residual_prediction_declarations_record import write_ovbrfn00_lock
from formal.python.toe.observables.ovbrfn01_fn01_metric_residual_pruning_table_record import write_ovbrfn01_lock
from formal.python.toe.observables.ovfnwt00_fn01_weight_policy_declarations_record import write_ovfnwt00_lock
from formal.python.toe.observables.ovfnwt01_fn01_weight_policy_pruning_table_record import write_ovfnwt01_lock
from formal.python.toe.observables.ovfnwt02_selected_weight_policy_record import write_ovfnwt02_lock
from formal.python.toe.observables.ovfn02_weighted_residual_audit_record import write_ovfn02_lock
from formal.python.toe.observables.ovsw01_shallow_water_lowk_slope_record import write_ovsw01_lock


def _find_repo_root(start: Path) -> Path:
    p = start.resolve()
    if p.is_file():
        p = p.parent
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def _sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _with_suffix(path: Path, *, suffix: str) -> Path:
    if not suffix:
        return path
    return path.with_name(path.stem + str(suffix) + path.suffix)


def _validate_ovsnd03n2_frozen_artifacts(*, repo_root: Path) -> tuple[bool, str]:
    """Validate frozen OV-SND-03N2 CSV+metadata, without digitization.

    Returns (ok, reason).
    - ok=True: safe to reuse frozen artifacts.
    - ok=False: artifacts missing or invalid; regen should fail fast rather than digitize.
    """

    csv_path = (
        repo_root
        / "formal"
        / "external_evidence"
        / "bec_sound_density_secondary_TBD"
        / "ovsnd03n2_density_digitization"
        / "density_conditions.csv"
    )
    meta_path = (
        repo_root
        / "formal"
        / "external_evidence"
        / "bec_sound_density_secondary_TBD"
        / "ovsnd03n2_density_digitization"
        / "density_conditions.metadata.json"
    )

    if not csv_path.exists() and not meta_path.exists():
        return False, "missing_csv_and_metadata"
    if not csv_path.exists():
        return False, "missing_csv"
    if not meta_path.exists():
        return False, "missing_metadata"

    csv_text = csv_path.read_text(encoding="utf-8")
    meta = json.loads(meta_path.read_text(encoding="utf-8"))
    expected_sha = str(meta.get("dataset", {}).get("csv_sha256") or "")
    if not expected_sha:
        return False, "metadata_missing_csv_sha256"
    actual_sha = _sha256_text(csv_text)
    if actual_sha != expected_sha:
        return False, "csv_sha256_mismatch"

    # Validate parse/schema and row count.
    f = csv_text.splitlines()
    if not f:
        return False, "csv_empty"
    reader = csv.DictReader(f)
    expected_cols = ["density_condition_key", "n0_cm3", "source_locator", "notes"]
    if reader.fieldnames != expected_cols:
        return False, f"csv_unexpected_columns:{reader.fieldnames}"
    rows = list(reader)
    expected_row_count = meta.get("dataset", {}).get("row_count")
    if isinstance(expected_row_count, int) and len(rows) != expected_row_count:
        return False, "row_count_mismatch"
    if len(rows) < 2:
        return False, "row_count_lt_2"

    return True, "ok"


def _validate_ovsnd03n_frozen_artifacts(*, repo_root: Path) -> tuple[bool, str]:
    csv_path = (
        repo_root
        / "formal"
        / "external_evidence"
        / "bec_sound_andrews_1997"
        / "ovsnd03_density_digitization"
        / "central_density.csv"
    )
    meta_path = (
        repo_root
        / "formal"
        / "external_evidence"
        / "bec_sound_andrews_1997"
        / "ovsnd03_density_digitization"
        / "central_density.metadata.json"
    )

    if not csv_path.exists() or not meta_path.exists():
        return False, "missing_csv_or_metadata"

    csv_text = csv_path.read_text(encoding="utf-8")
    meta = json.loads(meta_path.read_text(encoding="utf-8"))
    expected_sha = str(meta.get("dataset", {}).get("csv_sha256") or "")
    if not expected_sha:
        return False, "metadata_missing_csv_sha256"
    actual_sha = _sha256_text(csv_text)
    if actual_sha != expected_sha:
        return False, "csv_sha256_mismatch"

    reader = csv.DictReader(csv_text.splitlines())
    expected_cols = ["condition_id", "n0_cm3"]
    if reader.fieldnames != expected_cols:
        return False, f"csv_unexpected_columns:{reader.fieldnames}"
    rows = list(reader)
    if len(rows) != 1:
        return False, "row_count_ne_1"
    if str(rows[0].get("condition_id")) != "central":
        return False, "condition_id_not_central"

    return True, "ok"


def _validate_ovbr03n_frozen_artifacts(*, repo_root: Path) -> tuple[bool, str]:
    """Validate frozen OV-BR-03N artifacts (two condition CSVs + metadata).

    Returns (ok, reason).
    - ok=True: safe to reuse frozen artifacts (regen must not digitize).
    - ok=False: artifacts missing or invalid; regen should fail fast.
    """

    base = repo_root / "formal" / "external_evidence" / "bec_bragg_shammass_2012" / "ovbr03n_digitization"
    meta_path = base / "k_omega_digitization.metadata.json"
    csv_a = base / "k_omega_conditionA.csv"
    csv_b = base / "k_omega_conditionB.csv"

    if not meta_path.exists() and not csv_a.exists() and not csv_b.exists():
        return False, "missing_all"
    if not meta_path.exists():
        return False, "missing_metadata"
    if not csv_a.exists():
        return False, "missing_conditionA_csv"
    if not csv_b.exists():
        return False, "missing_conditionB_csv"

    meta = json.loads(meta_path.read_text(encoding="utf-8"))
    if meta.get("schema") != "OV-BR-03N_k_omega_digitization_metadata/v1":
        return False, "metadata_schema_unexpected"

    a_text = csv_a.read_text(encoding="utf-8")
    b_text = csv_b.read_text(encoding="utf-8")

    sha_a = _sha256_text(a_text)
    sha_b = _sha256_text(b_text)

    if str(meta.get("condition_A", {}).get("csv_sha256") or "") != sha_a:
        return False, "conditionA_csv_sha256_mismatch"
    if str(meta.get("condition_B", {}).get("csv_sha256") or "") != sha_b:
        return False, "conditionB_csv_sha256_mismatch"

    # Sanity check declared row counts.
    n_a = meta.get("condition_A", {}).get("row_count")
    n_b = meta.get("condition_B", {}).get("row_count")
    if not isinstance(n_a, int) or n_a < 6:
        return False, "conditionA_row_count_lt_6"
    if not isinstance(n_b, int) or n_b < 6:
        return False, "conditionB_row_count_lt_6"

    # Also validate the CSV schema quickly.
    def _count_rows(csv_text: str) -> tuple[bool, int]:
        lines = csv_text.splitlines()
        if not lines:
            return False, 0
        reader = csv.DictReader(lines)
        if reader.fieldnames != ["k_um_inv", "omega_over_2pi_kHz"]:
            return False, 0
        rows = list(reader)
        return True, len(rows)

    ok_a, rows_a = _count_rows(a_text)
    ok_b, rows_b = _count_rows(b_text)
    if not ok_a:
        return False, "conditionA_csv_schema_unexpected"
    if not ok_b:
        return False, "conditionB_csv_schema_unexpected"
    if rows_a != n_a:
        return False, "conditionA_row_count_mismatch"
    if rows_b != n_b:
        return False, "conditionB_row_count_mismatch"

    return True, "ok"


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--report", action="store_true", help="Print written lock paths")
    p.add_argument(
        "--admissibility-manifest",
        default=None,
        help=(
            "Override admissibility manifest path for this regen run (sets TOE_ADMISSIBILITY_MANIFEST). "
            "Useful for explicit enabled-manifest discriminative runs while keeping defaults disabled."
        ),
    )
    p.add_argument(
        "--include-snd",
        action="store_true",
        help="Also regenerate the OV-SND* anchor locks/audits (treated as canonical only if this flag is set)",
    )

    lane = p.add_mutually_exclusive_group()
    lane.add_argument(
        "--snd-only",
        action="store_true",
        help=(
            "Regenerate only sound-lane canonical locks (OV-SND*, OV-SEL-SND*, OV-BR-SND*, SND-DIG-01) and skip "
            "non-sound canonical locks like OV-SEL-01 and benchmark SEL locks."
        ),
    )
    lane.add_argument(
        "--bragg-only",
        action="store_true",
        help=(
            "Regenerate only Bragg-lane canonical locks (currently OV-BR-02 and OV-BR-03N). "
            "This mode never digitizes during regen; it reuses/validates frozen artifacts and fails fast if missing/invalid."
        ),
    )
    lane.add_argument(
        "--sw-only",
        action="store_true",
        help=(
            "Regenerate only shallow-water lane canonical locks (Axis C). "
            "Currently: OV-SW-01 only. This remains blocked-by-default until frozen digitized artifacts exist."
        ),
    )
    p.add_argument(
        "--status-date",
        default="2026-01-23",
        help="Status date string to embed where applicable (default: 2026-01-23)",
    )

    args = p.parse_args(argv)

    if args.admissibility_manifest:
        os.environ["TOE_ADMISSIBILITY_MANIFEST"] = str(args.admissibility_manifest)

    # If an explicit manifest override is provided, treat this regen as a non-canonical
    # discriminative run and write locks to distinct *_OVERRIDE.md files so the default
    # canonical locks remain stable under the default (disabled) manifest.
    lock_suffix = "_OVERRIDE" if bool(args.admissibility_manifest) else ""

    if bool(args.bragg_only) and bool(args.include_snd):
        raise SystemExit("--bragg-only cannot be combined with --include-snd")

    if bool(args.sw_only) and bool(args.include_snd):
        raise SystemExit("--sw-only cannot be combined with --include-snd")

    written: list[str] = []

    if bool(args.sw_only):
        sw_date = "2026-01-25"
        written.append(str(write_ovsw01_lock(date=sw_date)))

        if args.report:
            print("Regenerated canonical locks:")
            for path in written:
                print(f"  - {path}")
        return 0

    if bool(args.bragg_only):
        repo_root = _find_repo_root(Path(__file__))
        manifest_path = Path(args.admissibility_manifest) if args.admissibility_manifest else None
        ok, reason = _validate_ovbr03n_frozen_artifacts(repo_root=repo_root)
        if not ok:
            raise RuntimeError(
                "OV-BR-03N frozen artifacts missing/invalid (" + reason + "). "
                "Run the OV-BR-03N digitizer intentionally to (re)create artifacts, then rerun regen."
            )

        bragg_date = "2026-01-25"
        repo_locks = repo_root / "formal" / "markdown" / "locks"
        obs_dir = repo_locks / "observables"
        written.append(str(write_ovbr02_lock(lock_path=_with_suffix(obs_dir / "OV-BR-02_regime_bridge_record.md", suffix=lock_suffix))))
        written.append(str(write_ovbr03n_digitized_lock(lock_path=_with_suffix(obs_dir / "OV-BR-03N_bragg_dispersion_k_omega_digitized.md", suffix=lock_suffix), date=bragg_date)))
        written.append(str(write_ovbr04a_lock(lock_path=_with_suffix(obs_dir / "OV-BR-04a_bragg_lowk_slope_conditionA.md", suffix=lock_suffix), date=bragg_date, admissibility_manifest_path=manifest_path)))
        written.append(str(write_ovbr04b_lock(lock_path=_with_suffix(obs_dir / "OV-BR-04b_bragg_lowk_slope_conditionB.md", suffix=lock_suffix), date=bragg_date, admissibility_manifest_path=manifest_path)))
        written.append(str(write_ovbr05_lock(lock_path=_with_suffix(obs_dir / "OV-BR-05_bragg_lowk_slope_summary.md", suffix=lock_suffix), date=bragg_date, admissibility_manifest_path=manifest_path)))
        written.append(
            str(
                write_ovdrbr00_lock(
                    lock_path=_with_suffix(obs_dir / "OV-DR-BR-00_br01_prediction_declarations.md", suffix=lock_suffix),
                    date=bragg_date,
                    admissibility_manifest_path=manifest_path,
                )
            )
        )
        written.append(
            str(
                write_ovdrbr01_lock(
                    lock_path=_with_suffix(obs_dir / "OV-DR-BR-01_candidate_pruning_table.md", suffix=lock_suffix),
                    date=bragg_date,
                    admissibility_manifest_path=manifest_path,
                )
            )
        )
        written.append(str(write_ovsel_br01_lock(lock_path=_with_suffix(obs_dir / "OV-SEL-BR-01_bragg_lowk_slope_audit.md", suffix=lock_suffix), status_date=bragg_date)))
        ovbrfn00_path = _with_suffix(obs_dir / "OV-BR-FN-00_fn01_metric_residual_prediction_declarations.md", suffix=lock_suffix)
        written.append(str(write_ovbrfn00_lock(lock_path=ovbrfn00_path, date=bragg_date, admissibility_manifest_path=manifest_path)))
        ovbrfn01_path = _with_suffix(obs_dir / "OV-BR-FN-01_fn01_metric_residual_pruning_table.md", suffix=lock_suffix)
        written.append(
            str(
                write_ovbrfn01_lock(
                    lock_path=ovbrfn01_path,
                    date=bragg_date,
                    pred_decl_lock_path=ovbrfn00_path,
                    admissibility_manifest_path=manifest_path,
                )
            )
        )

        ovfnwt00_path = _with_suffix(obs_dir / "OV-FN-WT-00_fn01_weight_policy_declarations.md", suffix=lock_suffix)
        written.append(str(write_ovfnwt00_lock(lock_path=ovfnwt00_path, date=bragg_date, admissibility_manifest_path=manifest_path)))
        ovfnwt01_path = _with_suffix(obs_dir / "OV-FN-WT-01_fn01_weight_policy_pruning_table.md", suffix=lock_suffix)
        written.append(
            str(
                write_ovfnwt01_lock(
                    lock_path=ovfnwt01_path,
                    date=bragg_date,
                    br_fn_pruning_lock_path=ovbrfn01_path,
                    policy_decl_lock_path=ovfnwt00_path,
                    admissibility_manifest_path=manifest_path,
                )
            )
        )

        ovfnwt02_path = _with_suffix(obs_dir / "OV-FN-WT-02_selected_weight_policy.md", suffix=lock_suffix)
        written.append(
            str(
                write_ovfnwt02_lock(
                    lock_path=ovfnwt02_path,
                    date=bragg_date,
                    pruning_lock_path=ovfnwt01_path,
                    admissibility_manifest_path=manifest_path,
                )
            )
        )

        ovfn02_path = _with_suffix(obs_dir / "OV-FN-02_weighted_residual_audit.md", suffix=lock_suffix)
        written.append(
            str(
                write_ovfn02_lock(
                    lock_path=ovfn02_path,
                    date=bragg_date,
                    selection_lock_path=ovfnwt02_path,
                    admissibility_manifest_path=manifest_path,
                )
            )
        )
        written.append(
            str(
                write_ovbr_snd03_lock(
                    status_date=bragg_date,
                    sound_date="2026-01-24",
                    bragg_date=bragg_date,
                    lock_path=_with_suffix(obs_dir / "OV-BR-SND-03_cross_lane_lowk_consistency_audit.md", suffix=lock_suffix),
                )
            )
        )

        if args.report:
            print("Regenerated canonical locks:")
            for path in written:
                print(f"  - {path}")
        return 0

    # Non-sound canonical locks (default path).
    # Dependency order:
    # - OV-SEL-01 embeds OV-XD-04 state and its fingerprint, so OV-XD-04 must be current.
    if not bool(args.snd_only):
        written.append(str(write_ovxd04_lock()))
        written.append(str(write_ovbr02_lock()))
        written.append(str(write_ovsel01_lock(status_date=str(args.status_date))))
        written.append(str(write_ovdq02_lock()))
        written.append(str(write_ovdq03_lock()))

    # Optional canonical sound anchor regen.
    if bool(args.include_snd) or bool(args.snd_only):
        date = "2026-01-24"

        # Fail fast on mapping tuple drift before regenerating the sound lane.
        try:
            from formal.python.tools.lint_mapping_tuples import lint_mapping_tuples

            lint_mapping_tuples(date=str(date), fail_fast=True)
        except ModuleNotFoundError:
            # Linter added later; keep regen usable even if tool missing.
            pass

        written.append(str(write_ovsnd01_lock(date=date)))
        write_ovsnd01_digitized_artifacts(date=date)
        written.append(str(write_ovsnd01_digitized_lock(date=date)))
        try:
            write_ovsnd01n2_digitized_artifacts(date=date)
        except FileNotFoundError:
            pass
        written.append(str(write_ovsnd01n2_lock(date=date)))
        written.append(str(write_ovsnd02_lock(date=date)))
        written.append(str(write_ovsnd02b_lock(date=date)))

        # Density digitization + scaling (sound lane).
        written.append(str(write_snddig01_lock(date=date)))
        repo_root = _find_repo_root(Path(__file__))
        ok3n, _ = _validate_ovsnd03n_frozen_artifacts(repo_root=repo_root)
        if not ok3n:
            write_ovsnd03n_digitized_artifacts(date=date)
        written.append(str(write_ovsnd03n_digitized_lock(date=date)))
        written.append(str(write_ovsnd03n_coverage_lock(date=date)))
        # Secondary density source (may be blocked until pinned source/table exists).
        repo_root = _find_repo_root(Path(__file__))
        ok, reason = _validate_ovsnd03n2_frozen_artifacts(repo_root=repo_root)
        if ok:
            # Hard guard: when frozen artifacts validate, never invoke pixel digitization during regen.
            pass
        else:
            # Missing artifacts are a normal "blocked" state; do not digitize during regen.
            # If artifacts exist but are inconsistent/corrupt, fail fast.
            if reason not in {"missing_csv_and_metadata", "missing_csv", "missing_metadata"}:
                raise RuntimeError(
                    "OV-SND-03N2 frozen artifacts present but invalid (" + reason + "). "
                    "Repair frozen CSV+metadata or re-digitize intentionally, then re-run regen."
                )
        written.append(str(write_ovsnd03n2_lock(date=date)))
        written.append(str(write_ovsnd03_lock(date=date)))
        written.append(str(write_ovbr_snd02_lock(date=date)))
        written.append(str(write_ovsnd04_lock(date=date)))

        # Sound-lane audits / bridge.
        written.append(str(write_ovsel_snd01_lock(status_date=date)))
        written.append(str(write_ovsel_snd02_lock(status_date=date)))
        written.append(str(write_ovsel_snd03_lock(status_date=date)))
        written.append(str(write_ovsel_snd04_lock(status_date=date)))
        written.append(str(write_ovsel_snd05_lock(status_date=date)))
        written.append(str(write_ovbr_snd01_lock(date=date)))

        # Cross-lane audit is cheap (no digitization) and intentionally conservative.
        written.append(
            str(
                write_ovbr_snd03_lock(
                    status_date="2026-01-25",
                    sound_date=date,
                    bragg_date="2026-01-25",
                )
            )
        )

    if args.report:
        print("Regenerated canonical locks:")
        for path in written:
            print(f"  - {path}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())

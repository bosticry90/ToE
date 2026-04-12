from __future__ import annotations

import argparse
import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
SCHEMA_ID = "GOVERNANCE_INVALIDATION_SELECTION_v0"
MANIFEST_PATH = REPO_ROOT / "formal" / "docs" / "release" / "GOVERNANCE_TEST_MANIFEST_v1.json"
TELEMETRY_DEFAULT_PATH = REPO_ROOT / "formal" / "output" / "reports" / "governance_invalidation_telemetry_v0.json"


def _run_git(args: list[str]) -> str:
    proc = subprocess.run(
        ["git", *args],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    return proc.stdout


def _normalize(path: str) -> str:
    return path.strip().replace("\\", "/")


def _read_manifest_tests() -> set[str]:
    payload = json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    tests = payload.get("groups", {}).get("governance_pytests", {}).get("tests", [])
    return {_normalize(str(p)) for p in tests}


def _mapped_doc_family_tests(changed_path: str, governance_tests: set[str]) -> set[str]:
    mapped: set[str] = set()

    explicit_family_map: dict[str, tuple[str, ...]] = {
        "formal/docs/release/toe_global_completion_matrix_v0.md": (
            "formal/python/tests/test_pillar_status_matrix_consistency_gate.py",
            "formal/python/tests/test_pillar_matrix_roadmap_coverage_gate.py",
            "formal/python/tests/test_governance_audit_packet_gate.py",
        ),
        "formal/docs/release/governance_blocker_trend_window_20260410_v0.md": (
            "formal/python/tests/test_governance_audit_packet_gate.py",
        ),
        "formal/docs/release/governance_blocker_closure_map_20260410_v0.md": (
            "formal/python/tests/test_governance_audit_packet_gate.py",
        ),
        "state_of_the_theory.md": (
            "formal/python/tests/test_state_doc_no_duplicate_gapids.py",
            "formal/python/tests/test_state_doc_cv_lane_wiring.py",
            "formal/python/tests/test_state_doc_mainline_does_not_depend_on_variantA.py",
            "formal/python/tests/test_state_doc_mainline_cannot_claim_beta_nonzero.py",
        ),
        "readme.md": (
            "formal/python/tests/test_local_execution_posture_gate.py",
            "formal/python/tests/test_repository_retention_policy_contract_gate.py",
        ),
        "formal/python/tests/test_physics_progress_ledger_tgc93_consistency_gate.py": (
            "formal/python/tests/test_physics_progress_ledger_tgc93_consistency_gate.py",
            "formal/python/tests/test_governance_audit_packet_gate.py",
        ),
        "formal/python/tests/test_dual_track_cutover_measured_mode_policy_gate.py": (
            "formal/python/tests/test_dual_track_cutover_measured_mode_policy_gate.py",
        ),
        "formal/python/tests/test_governance_invalidation_select_telemetry_gate.py": (
            "formal/python/tests/test_governance_invalidation_select_telemetry_gate.py",
            "formal/python/tests/test_governance_audit_packet_gate.py",
        ),
    }

    normalized = _normalize(changed_path).lower()
    if normalized in explicit_family_map:
        mapped.update(explicit_family_map[normalized])

    if normalized.startswith("formal/docs/release/governance_"):
        mapped.add("formal/python/tests/test_governance_audit_packet_gate.py")

    if normalized.startswith("formal/docs/release/"):
        mapped.update(
            {
                "formal/python/tests/test_governance_audit_packet_gate.py",
                "formal/python/tests/test_pillar_status_matrix_consistency_gate.py",
            }
        )

    if normalized.startswith("formal/python/tools/governance_"):
        mapped.update(
            {
                "formal/python/tests/test_governance_audit_packet_gate.py",
            }
        )

    if normalized.startswith("formal/python/tools/"):
        mapped.update(
            {
                "formal/python/tests/test_governance_audit_packet_gate.py",
                "formal/python/tests/test_dual_track_hardening_closeout_gate.py",
                "formal/python/tests/test_governance_parallel_capability_probe_gate.py",
            }
        )

    if normalized.startswith("formal/docs/release/ws_10_tgc_"):
        mapped.update(
            {
                "formal/python/tests/test_governance_audit_packet_gate.py",
            }
        )

    if normalized.startswith("formal/python/tools/dual_track_"):
        mapped.update(
            {
                "formal/python/tests/test_dual_track_cutover_measured_mode_policy_gate.py",
            }
        )

    if normalized.startswith("formal/output/"):
        mapped.update(
            {
                "formal/python/tests/test_governance_audit_packet_gate.py",
                "formal/python/tests/test_dual_track_hardening_closeout_gate.py",
            }
        )

    if normalized.startswith(".github/workflows/"):
        mapped.update(
            {
                "formal/python/tests/test_local_execution_posture_gate.py",
                "formal/python/tests/test_dual_track_hardening_closeout_gate.py",
            }
        )

    if normalized in {"governance_suite.ps1", "checkpoint_ladder.ps1", "dual_track_execution.ps1"}:
        mapped.update(
            {
                "formal/python/tests/test_local_execution_posture_gate.py",
                "formal/python/tests/test_dual_track_cutover_measured_mode_policy_gate.py",
            }
        )

    return {path for path in mapped if path in governance_tests}


def _load_telemetry(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {
            "schema_id": "GOVERNANCE_INVALIDATION_TELEMETRY_v0",
            "runs_total": 0,
            "subset_runs": 0,
            "full_runs": 0,
            "captured_at_utc": None,
            "last_run": {},
            "reason_counters": {},
        }
    return json.loads(path.read_text(encoding="utf-8"))


def _update_telemetry(path: Path, *, mode: str, reasons: list[str], selected_count: int, changed_count: int) -> None:
    payload = _load_telemetry(path)
    payload["runs_total"] = int(payload.get("runs_total", 0)) + 1
    if mode == "SUBSET":
        payload["subset_runs"] = int(payload.get("subset_runs", 0)) + 1
    else:
        payload["full_runs"] = int(payload.get("full_runs", 0)) + 1

    counters = dict(payload.get("reason_counters", {}))
    for reason in reasons:
        counters[reason] = int(counters.get(reason, 0)) + 1
    payload["reason_counters"] = counters

    runs_total = int(payload.get("runs_total", 0))
    subset_runs = int(payload.get("subset_runs", 0))
    hit_rate = 0.0 if runs_total == 0 else round((subset_runs / runs_total) * 100.0, 3)
    captured_at_utc = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    payload["captured_at_utc"] = captured_at_utc

    payload["last_run"] = {
        "captured_at_utc": captured_at_utc,
        "mode": mode,
        "reasons": reasons,
        "selected_test_count": selected_count,
        "changed_file_count": changed_count,
        "subset_hit_rate_percent": hit_rate,
    }

    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _git_diff_files(base_ref: str) -> set[str]:
    raw = _run_git(["diff", "--name-only", f"{base_ref}..HEAD"])
    return {_normalize(line) for line in raw.splitlines() if line.strip()}


def _git_working_tree_files() -> set[str]:
    raw = _run_git(["status", "--porcelain"])
    changed: set[str] = set()
    for line in raw.splitlines():
        line = line.rstrip()
        if not line:
            continue
        # Porcelain format: XY <path>
        if len(line) >= 4:
            path = line[3:]
            # Handle rename format "old -> new"
            if " -> " in path:
                path = path.split(" -> ", 1)[1]
            changed.add(_normalize(path))
    return changed


def _select_subset(changed_files: set[str], governance_tests: set[str]) -> tuple[str, list[str], list[str]]:
    if not changed_files:
        return "FULL", [], ["no_changed_files_detected"]

    test_changes = {
        p for p in changed_files if p.startswith("formal/python/tests/test_")
    }
    non_test_changes = {p for p in changed_files if p not in test_changes}

    impacted = {p for p in test_changes if p in governance_tests}
    reasons: list[str] = []

    if test_changes and not impacted:
        return "FULL", [], ["changed_tests_not_in_governance_manifest"]

    if non_test_changes:
        mapped_from_non_tests: set[str] = set()
        unmapped_non_tests: list[str] = []
        for path in sorted(non_test_changes):
            mapped = _mapped_doc_family_tests(path, governance_tests)
            if mapped:
                mapped_from_non_tests |= mapped
            else:
                unmapped_non_tests.append(path)

        if unmapped_non_tests:
            return "FULL", [], ["non_test_change_outside_bounded_mapping"]

        impacted |= mapped_from_non_tests
        reasons.append("bounded_non_test_family_subset_selected")

    if not impacted:
        return "FULL", [], ["no_mapped_subset_tests"]

    if test_changes:
        reasons.append("test_change_subset_selected")

    return "SUBSET", sorted(impacted), reasons


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Select governance pytest scope based on changed files.")
    parser.add_argument(
        "--base-ref",
        default="HEAD~1",
        help="Git base ref used for diff range base_ref..HEAD.",
    )
    parser.add_argument(
        "--include-working-tree",
        action="store_true",
        help="Include uncommitted staged/unstaged changes from git status.",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=None,
        help="Optional output file path for JSON payload; otherwise printed to stdout.",
    )
    parser.add_argument(
        "--telemetry-out",
        type=Path,
        default=TELEMETRY_DEFAULT_PATH,
        help="Telemetry JSON path for recording subset/full hit-rate and fallback reasons.",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)

    governance_tests = _read_manifest_tests()

    changed_files = _git_diff_files(ns.base_ref)
    if ns.include_working_tree:
        changed_files |= _git_working_tree_files()

    mode, subset_tests, reasons = _select_subset(changed_files, governance_tests)

    payload: dict[str, Any] = {
        "schema_id": SCHEMA_ID,
        "mode": mode,
        "base_ref": ns.base_ref,
        "include_working_tree": bool(ns.include_working_tree),
        "changed_files": sorted(changed_files),
        "subset_tests": subset_tests,
        "reasons": reasons,
        "non_claim_boundary": "This invalidation selection payload is a repository-local execution optimization artifact and does not assert scientific adequacy.",
    }

    telemetry_path = ns.telemetry_out if ns.telemetry_out.is_absolute() else (REPO_ROOT / ns.telemetry_out)
    _update_telemetry(
        telemetry_path,
        mode=mode,
        reasons=reasons,
        selected_count=len(subset_tests),
        changed_count=len(changed_files),
    )
    payload["telemetry_pointer"] = str(telemetry_path.relative_to(REPO_ROOT)).replace("\\", "/")

    text = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if ns.out is not None:
        out_path = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(text, encoding="utf-8")
    else:
        print(text, end="")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())

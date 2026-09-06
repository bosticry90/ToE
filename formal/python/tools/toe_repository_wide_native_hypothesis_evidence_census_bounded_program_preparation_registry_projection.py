from __future__ import annotations

import subprocess

from formal.python.tools.bounded_program_governance import (
    _registry_json_bytes,
    strict_json_loads,
)
from formal.python.tools.loop_control_registry_integrity import (
    atomic_write_registry,
    repair_registry,
)
from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    REPO_ROOT,
    read_json,
    sha256_path,
)


REGISTRY_PATH = REPO_ROOT / "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"
OLD_TARGET = (
    "close_toe_native_coherence_ontology_and_representation_"
    "v0_after_bounded_result_v0"
)
TARGET = (
    "prepare_toe_repository_wide_native_hypothesis_evidence_census_"
    "bounded_program_v0"
)
KIND = (
    "toe_repository_wide_native_hypothesis_evidence_census_"
    "bounded_program_preparation_v0"
)
EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "ToeRepositoryWideNativeHypothesisEvidenceCensusBoundedProgram"
    "PreparationResultReview.lean"
)
REPORT = (
    "formal/docs/release/"
    "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_"
    "BOUNDED_PROGRAM_PREPARATION_RESULT_REVIEW_20260730_v0.json"
)
REPORT_PATH = REPO_ROOT / REPORT
OUTCOME = (
    "REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_BOUNDED_"
    "PROGRAM_PROPOSAL_PREPARED"
)
STRICT_OUTCOME = (
    "PROPOSAL_ONLY_NOT_INSTALLED_AUTHORIZED_OR_OPEN_NO_ARCHIVE_ADOPTION_"
    "HYPOTHESIS_PROMOTION_FIELD_ACTION_SEAM_OBSERVABLE_OR_AUTOMATIC_SUCCESSOR"
)


def _project(registry: dict) -> dict:
    projection = registry["current_projection_v0"]
    if projection["current_target"] not in {OLD_TARGET, TARGET}:
        raise ValueError("unexpected current target for census proposal projection")
    previous_active = [
        item for item in registry["workstreams"] if item.get("status") == "active"
    ]
    if len(previous_active) != 1:
        raise ValueError("expected exactly one active workstream")
    workstream = previous_active[0]
    if workstream["workstream_id"] not in {OLD_TARGET, TARGET}:
        raise ValueError("unexpected active workstream")
    report_sha = sha256_path(REPORT_PATH) if REPORT_PATH.is_file() else "PENDING"
    workstream.update(
        {
            "workstream_id": TARGET,
            "status": "active",
            "live_lane": "yes",
            "queue_scope": (
                "Repository-wide native-hypothesis evidence-census bounded "
                "program proposal prepared; await separate installation "
                "authority and later separate Stage 1 OPEN authority."
            ),
            "active_lane": TARGET,
            "authorized_target": TARGET,
            "authorized_next_strict_target": TARGET,
            "selected_next_target": TARGET,
            "selected_next_target_kind": KIND,
            "authorization_evidence": EVIDENCE,
            "report": REPORT,
            "report_path": REPORT,
            "report_sha256": report_sha,
            "packet_result": OUTCOME,
            "strict_packet_result": STRICT_OUTCOME,
            "consumed_target": OLD_TARGET,
            "consumed_target_kind": (
                "closed_coherence_result_with_forward_scope_qualification"
            ),
            "claim_ceiling_level": 2,
            "claim_label": "B-PREPARED",
            "claim_status": (
                "Proposal only: no census performed, archive evidence adopted, "
                "hypothesis promoted, program installed, attempt opened, field "
                "or action selected, seam executed, or automatic successor."
            ),
            "review_accepted": "yes" if REPORT_PATH.is_file() else "pending",
        }
    )
    state = registry["current_target_state"]
    state.update(
        {
            "active_lane": TARGET,
            "live_next_target": TARGET,
            "previous_live_next_target": OLD_TARGET,
            "live_next_target_kind": KIND,
            "live_next_target_evidence": EVIDENCE,
            "live_next_target_report": REPORT,
            "live_next_target_outcome": OUTCOME,
            "live_next_target_strict_outcome": STRICT_OUTCOME,
        }
    )
    registry["ACTIVE_LANE_v0"] = TARGET
    registry["CURRENT_LIVE_NEXT_TARGET_v0"] = TARGET
    registry["PREVIOUS_LIVE_NEXT_TARGET_v0"] = OLD_TARGET
    registry["active_lanes"] = [TARGET]
    registry["active_workstream"] = TARGET
    registry["active_workstreams"] = [dict(workstream)]
    coverage = registry["next_strict_target_coverage"]
    if TARGET not in coverage:
        coverage.append(TARGET)
        coverage.sort()
    return repair_registry(registry)


def write_projection(*, from_head: bool = False) -> None:
    if from_head:
        completed = subprocess.run(
            [
                "git",
                "show",
                "HEAD:formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json",
            ],
            cwd=REPO_ROOT,
            check=True,
            capture_output=True,
        )
        registry = strict_json_loads(completed.stdout.decode("utf-8"))
    else:
        registry = read_json(REGISTRY_PATH)
    atomic_write_registry(REGISTRY_PATH, _registry_json_bytes(_project(registry)))


def check_projection() -> None:
    registry = read_json(REGISTRY_PATH)
    projection = registry["current_projection_v0"]
    if projection != {
        "schema_id": "LOOP_CONTROL_CURRENT_PROJECTION_v0",
        "active_lane": TARGET,
        "active_workstream_count": 1,
        "current_target": TARGET,
        "current_target_kind": KIND,
        "current_target_evidence": EVIDENCE,
        "current_target_report": REPORT,
        "current_target_outcome": OUTCOME,
        "current_target_strict_outcome": STRICT_OUTCOME,
        "previous_target": OLD_TARGET,
        "workstream_id": TARGET,
    }:
        raise ValueError("census proposal current projection is not exact")
    active = registry["active_workstreams"]
    if len(active) != 1 or active[0]["report_sha256"] != sha256_path(REPORT_PATH):
        raise ValueError("census proposal review hash is not projected")


def main() -> int:
    import argparse

    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    parser.add_argument(
        "--from-head",
        action="store_true",
        help="reproject from the committed registry to preserve source ordering",
    )
    args = parser.parse_args()
    if args.write:
        write_projection(from_head=args.from_head)
        print("wrote repository-wide census proposal registry projection")
    else:
        check_projection()
        print("repository-wide census proposal registry projection: OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

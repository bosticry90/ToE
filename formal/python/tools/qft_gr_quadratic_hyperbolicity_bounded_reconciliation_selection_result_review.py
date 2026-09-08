from __future__ import annotations

import json
import subprocess

from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    CAPTURED_AT_UTC,
    REPO_ROOT,
    QuadraticHyperbolicityError,
    read_json,
    sha256_path,
    write_or_check,
)


SELECTION_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_HYPERBOLICITY_BOUNDED_RECONCILIATION_"
    "SELECTION_20260728_v0.json"
)
HANDOFF_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "JULY_16_19_POST_MAINTENANCE_SCIENTIFIC_ADOPTION_OR_"
    "BOUNDED_REPLAY_DECISION_HANDOFF_20260727_v0.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_HYPERBOLICITY_BOUNDED_RECONCILIATION_"
    "SELECTION_RESULT_REVIEW_20260728_v0.json"
)
BASE_COMMIT = "e6bac5e96f3b7ae1f3522ae57280fef18be28e50"
EXPECTED_OLD_TARGET = (
    "prepare_pillar_seam_unit_mapping_ledger_blocker_response_"
    "route_selection_packet_v2"
)
EXPECTED_NEXT_TARGET = (
    "prepare_qft_gr_quadratic_hyperbolicity_admissible_source_"
    "and_frozen_theory_packet_v0"
)


def _independent_base_target() -> str:
    completed = subprocess.run(
        [
            "git",
            "show",
            f"{BASE_COMMIT}:formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json",
        ],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
    )
    return json.loads(completed.stdout)["current_projection_v0"]["current_target"]


def build_review() -> dict:
    selection = read_json(SELECTION_PATH)
    handoff = read_json(HANDOFF_PATH)
    checks = {
        "selection_bytes_are_bound": (
            selection["consumed_handoff"]["sha256"] == sha256_path(HANDOFF_PATH)
        ),
        "handoff_was_unselected": handoff["decision"]["selected_route"] is None,
        "base_registry_target_is_exact": (
            _independent_base_target() == EXPECTED_OLD_TARGET
            and selection["authority_before_selection"]["scientific_target"]
            == EXPECTED_OLD_TARGET
        ),
        "bounded_route_is_selected": (
            selection["selected_route"] == "BOUNDED_RECONCILIATION_OR_REPLAY"
            and selection["ordered_adoption_selected"] is False
        ),
        "fresh_path_starts_at_source_packet": (
            selection["fresh_authority_path"][0] == EXPECTED_NEXT_TARGET
            and selection["selected_next_target"] == EXPECTED_NEXT_TARGET
        ),
        "all_preserved_descendants_remain_non_authoritative": (
            selection["boundary"]["preserved_scientific_descendant_adopted"]
            is False
            and selection["boundary"]["preserved_scientific_descendant_rejected"]
            is False
        ),
        "yukawa_and_replay_prohibitions_are_explicit": (
            selection["boundary"]["yukawa_work_authorized"] is False
            and "Yukawa sandbox rerun." in selection["computations_prohibited"]
            and "Automatic replay of preserved scientific executors."
            in selection["computations_prohibited"]
        ),
        "no_scientific_result_is_manufactured": (
            selection["boundary"]["new_physics_result_claimed"] is False
            and selection["boundary"]["quadratic_hyperbolicity_result_claimed"]
            is False
        ),
    }
    failed = [name for name, passed in checks.items() if not passed]
    accepted = not failed
    return {
        "schema_id": (
            "QFT_GR_QUADRATIC_HYPERBOLICITY_BOUNDED_RECONCILIATION_"
            "SELECTION_RESULT_REVIEW_20260728_v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "review_target": (
            "review_post_maintenance_scientific_reconciliation_route_"
            "selection_v0_result"
        ),
        "reviewed_selection": {
            "path": SELECTION_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(SELECTION_PATH),
        },
        "checks": checks,
        "failed_checks": failed,
        "accepted": accepted,
        "selected_route": (
            "BOUNDED_RECONCILIATION_OR_REPLAY" if accepted else None
        ),
        "selected_next_target": (
            EXPECTED_NEXT_TARGET
            if accepted
            else "prepare_post_maintenance_scientific_reconciliation_correction_v0"
        ),
        "selected_next_target_kind": (
            "qft_gr_quadratic_hyperbolicity_admissible_source_"
            "and_frozen_theory_packet_preparation"
            if accepted
            else "scientific_reconciliation_correction"
        ),
        "authority_rotation": {
            "bounded_reconciliation_selected": accepted,
            "source_and_frozen_theory_packet_preparation_authorized": accepted,
            "physical_principal_block_execution_authorized": False,
            "preserved_descendant_adoption_authorized": False,
            "yukawa_work_authorized": False,
        },
        "reviewer_independence": {
            "imports_selection_generator": False,
            "recomputes_base_registry_target": True,
            "recomputes_handoff_hash": True,
            "trusts_selection_combined_pass_flag": False,
        },
        "verdict": (
            "ACCEPT_BOUNDED_RECONCILIATION_SOURCE_PACKET_PREPARATION_ONLY"
            if accepted
            else "B_BLOCKED_RECONCILIATION_SELECTION_REQUIRES_CORRECTION"
        ),
    }


def main() -> int:
    try:
        return write_or_check(
            path=OUTPUT_PATH,
            build=build_review,
            description=(
                "quadratic hyperbolicity bounded-reconciliation "
                "selection result review"
            ),
        )
    except (OSError, KeyError, QuadraticHyperbolicityError) as exc:
        print(f"selection review failed: {exc}")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())

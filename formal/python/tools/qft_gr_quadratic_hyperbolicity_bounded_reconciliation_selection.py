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


HANDOFF_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "JULY_16_19_POST_MAINTENANCE_SCIENTIFIC_ADOPTION_OR_"
    "BOUNDED_REPLAY_DECISION_HANDOFF_20260727_v0.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/docs/release/"
    "QFT_GR_QUADRATIC_HYPERBOLICITY_BOUNDED_RECONCILIATION_"
    "SELECTION_20260728_v0.json"
)
BASE_COMMIT = "e6bac5e96f3b7ae1f3522ae57280fef18be28e50"
FROZEN_JULY_12_TARGET = (
    "prepare_pillar_seam_unit_mapping_ledger_blocker_response_"
    "route_selection_packet_v2"
)
SELECTED_NEXT_TARGET = (
    "prepare_qft_gr_quadratic_hyperbolicity_admissible_source_"
    "and_frozen_theory_packet_v0"
)


def _base_registry_target() -> str:
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
    registry = json.loads(completed.stdout)
    target = registry["current_projection_v0"]["current_target"]
    if target != FROZEN_JULY_12_TARGET:
        raise QuadraticHyperbolicityError("base scientific authority mismatch")
    return target


def build_selection() -> dict:
    handoff = read_json(HANDOFF_PATH)
    if handoff["decision"]["selected_route"] is not None:
        raise QuadraticHyperbolicityError("handoff was expected to be unselected")
    route_ids = [route["route_id"] for route in handoff["routes"]]
    if route_ids != ["ORDERED_ADOPTION", "BOUNDED_RECONCILIATION_OR_REPLAY"]:
        raise QuadraticHyperbolicityError("handoff route set drift")
    return {
        "schema_id": (
            "QFT_GR_QUADRATIC_HYPERBOLICITY_BOUNDED_RECONCILIATION_"
            "SELECTION_20260728_v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "record_kind": "SCIENTIFIC_RECONCILIATION_ROUTE_SELECTION",
        "selection_target": (
            "select_post_maintenance_scientific_reconciliation_route_v0"
        ),
        "consumed_handoff": {
            "path": HANDOFF_PATH.relative_to(REPO_ROOT).as_posix(),
            "sha256": sha256_path(HANDOFF_PATH),
            "decision_status": handoff["decision"]["status"],
        },
        "authority_before_selection": {
            "registry_commit": BASE_COMMIT,
            "scientific_target": _base_registry_target(),
        },
        "selected_route": "BOUNDED_RECONCILIATION_OR_REPLAY",
        "ordered_adoption_selected": False,
        "selection_reasons": [
            "The July 16-19 and post-recovery scientific descendants diverge from the frozen authority point.",
            "Committed or reproducible bytes do not confer scientific adoption.",
            "The July 2026 physical-spin-2 principal-symbol result materially changes the quadratic-gravity question.",
            "A prospective minimal dependency chain avoids retroactive circularity.",
        ],
        "admissible_preserved_inputs": [
            {
                "input_class": "PRESERVED_REPOSITORY_EQUATIONS_AND_CONVENTIONS",
                "use": "CANDIDATE_INPUT_REQUIRING_INDEPENDENT_REBINDING",
            },
            {
                "input_class": "PRESERVED_LITERATURE_LOCATORS",
                "use": "SOURCE_DISCOVERY_ONLY_REQUIRING_PRIMARY_SOURCE_VERIFICATION",
            },
            {
                "input_class": "PRESERVED_TEST_EXPECTATIONS",
                "use": "NEGATIVE_CONTROL_DESIGN_ONLY_NOT_RESULT_ORACLE",
            },
        ],
        "historical_non_authoritative_inputs": [
            "Every post-registry July 13-19 scientific selection, execution, and review.",
            "Every post-recovery QFT-GR selection, execution, and review through e785b98d.",
            "The consumed Yukawa sandbox observations.",
        ],
        "decisions_to_regenerate": [
            "Exact admissible primary-source set.",
            "Frozen action, coefficient strata, and conventions.",
            "Physical spin-2 principal-block derivation.",
            "Algebraic and geometric multiplicities.",
            "Standard-norm and adapted-norm claim boundaries.",
        ],
        "computations_prohibited": [
            "Yukawa sandbox rerun.",
            "Yukawa pipe repair followed by rerun.",
            "Automatic replay of preserved scientific executors.",
            "Order reduction presented as the unmodified theory.",
            "Regularizer or fiducial mode presented as an original physical mode.",
        ],
        "preserved_observations": {
            "decision_bearing_use_authorized": False,
            "validation_use_authorized": False,
            "archival_context_use_authorized": True,
        },
        "fresh_authority_path": [
            SELECTED_NEXT_TARGET,
            "review_qft_gr_quadratic_hyperbolicity_admissible_source_and_frozen_theory_packet_v0_result",
            "derive_qft_gr_quadratic_physical_spin2_principal_block_v0",
            "review_qft_gr_quadratic_physical_spin2_principal_block_v0_result",
            "prepare_qft_gr_quadratic_auxiliary_harmonic_adapted_norm_well_posedness_packet_v0",
        ],
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": (
            "qft_gr_quadratic_hyperbolicity_admissible_source_"
            "and_frozen_theory_packet_preparation"
        ),
        "boundary": {
            "preserved_scientific_descendant_adopted": False,
            "preserved_scientific_descendant_rejected": False,
            "new_physics_result_claimed": False,
            "quadratic_hyperbolicity_result_claimed": False,
            "yukawa_work_authorized": False,
            "source_packet_preparation_authorized_after_review": True,
        },
        "verdict": (
            "SELECT_BOUNDED_RECONCILIATION_OR_REPLAY_NO_RETROACTIVE_ADOPTION"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_selection,
        description="quadratic hyperbolicity bounded-reconciliation selection",
    )


if __name__ == "__main__":
    raise SystemExit(main())

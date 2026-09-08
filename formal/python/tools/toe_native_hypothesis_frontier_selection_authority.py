from __future__ import annotations

from formal.python.tools.qft_gr_quadratic_hyperbolicity_common import (
    REPO_ROOT,
    read_json,
    sha256_path,
    write_or_check,
)


CAPTURED_AT_UTC = "2026-07-29T00:00:00Z"
CONSUMED_TARGET = "close_toe_native_surrogate_v0_after_bounded_result_v0"
SELECTOR_TARGET = "select_next_native_toe_hypothesis_for_bounded_adjudication_v0"
PROPOSED_PROGRAM_PREPARATION_TARGET = (
    "prepare_toe_native_coherence_ontology_and_representation_"
    "bounded_program_v0"
)
REGISTRY_PATH = REPO_ROOT / "formal/docs/release/LOOP_CONTROL_REGISTRY_v0.json"
NATIVE_CLOSEOUT_PATH = REPO_ROOT / (
    "formal/output/CALC-TOE-NATIVE-SURROGATE-V0-BOUNDED-CLOSEOUT-v0.json"
)
QUADRATIC_ROLE_REVIEW_PATH = REPO_ROOT / (
    "formal/docs/release/QFT_GR_QUADRATIC_TOE_ROLE_AFTER_GENERIC_"
    "FROZEN_RESULT_REVIEW_20260729_v0.json"
)
OUTPUT_PATH = REPO_ROOT / (
    "formal/docs/release/TOE_NATIVE_HYPOTHESIS_FRONTIER_SELECTION_"
    "AUTHORITY_PACKET_20260729_v0.json"
)


def build_authority() -> dict:
    registry = read_json(REGISTRY_PATH)
    projection = registry["current_projection_v0"]
    if projection["current_target"] not in {
        CONSUMED_TARGET,
        SELECTOR_TARGET,
        PROPOSED_PROGRAM_PREPARATION_TARGET,
    }:
        raise ValueError("native-hypothesis selector is outside current authority")

    quadratic = registry["bounded_programs_v1"][
        "QFT_GR_QUADRATIC_BOUNDED_CLOSEOUT_V0"
    ]
    native = registry["bounded_programs_v1"]["TOE_NATIVE_SURROGATE_V0"]
    native_closeout = read_json(NATIVE_CLOSEOUT_PATH)
    quadratic_review = read_json(QUADRATIC_ROLE_REVIEW_PATH)
    if not (
        quadratic["state"] == "CLOSED"
        and quadratic["toe_role"] == "REFERENCE_CONTROL_ONLY"
        and quadratic["control_result"] == "UNRESOLVED_AFTER_BOUNDED_ATTEMPT"
    ):
        raise ValueError("quadratic bounded closeout changed")
    if not (
        native["state"] == "CLOSED"
        and native["blocked_stage_id"] == "COHERENCE_REPRESENTATION"
        and native["stage_2_authorized"] is False
        and native["v0_discriminator_result"] == "NO_UNIQUE_TOE_DISCRIMINATOR_V0"
    ):
        raise ValueError("native-surrogate bounded closeout changed")
    if not (
        native_closeout["terminal_outcome"] == "NO_UNIQUE_TOE_DISCRIMINATOR_V0"
        and native_closeout["terminal_boundaries"][
            "new_representation_or_action_requires_separate_v1"
        ]
        and quadratic_review["quadratic_program_terminal"] is True
    ):
        raise ValueError("closed-program evidence changed")

    return {
        "schema_id": (
            "TOE_NATIVE_HYPOTHESIS_FRONTIER_SELECTION_"
            "AUTHORITY_PACKET_20260729_v0"
        ),
        "captured_at_utc": CAPTURED_AT_UTC,
        "consumed_target": CONSUMED_TARGET,
        "authorized_target": SELECTOR_TARGET,
        "authority_class": "BOUNDED_NATIVE_HYPOTHESIS_SELECTION_DECISION",
        "native_hypothesis_tested": "NONE_GOVERNANCE_ONLY",
        "native_relevance": {
            "kind": "NATIVE_FRONTIER_SELECTION",
            "statement": (
                "Selects which native ToE hypothesis may receive a separately "
                "authorized bounded adjudication program."
            ),
        },
        "prerequisite_scope": "AUTHORIZED_SELECTOR_ONLY",
        "closed_predecessors": {
            "quadratic": {
                "program_id": quadratic["program_id"],
                "state": quadratic["state"],
                "toe_role": quadratic["toe_role"],
                "control_result": quadratic["control_result"],
                "review_path": QUADRATIC_ROLE_REVIEW_PATH.relative_to(
                    REPO_ROOT
                ).as_posix(),
                "review_sha256": sha256_path(QUADRATIC_ROLE_REVIEW_PATH),
            },
            "native_surrogate": {
                "program_id": native["program_id"],
                "state": native["state"],
                "blocked_stage_id": native["blocked_stage_id"],
                "stage_2_authorized": native["stage_2_authorized"],
                "terminal_result": native["v0_discriminator_result"],
                "closeout_path": NATIVE_CLOSEOUT_PATH.relative_to(
                    REPO_ROOT
                ).as_posix(),
                "closeout_sha256": sha256_path(NATIVE_CLOSEOUT_PATH),
            },
        },
        "selector_contract": {
            "decision_count": 1,
            "repair_attempt_count": 0,
            "subsidiary_scientific_targets_authorized": False,
            "candidate_paths": [
                "PILLAR_RECOVERY",
                "NATIVE_SEAM_ADJUDICATION",
                "CCFT_COHERENCE_ONTOLOGY_AND_REPRESENTATION",
                "MASTER_ACTION_RECONCILIATION",
            ],
            "required_outputs": [
                "evidence_bound_candidate_matrix",
                "dependency_ordering",
                "one_selected_native_hypothesis",
                "one_future_bounded_program_proposal",
                "explicit_nonselection_reasons",
            ],
            "terminal_outcomes": [
                "SELECT_PILLAR_RECOVERY",
                "SELECT_NATIVE_SEAM_ADJUDICATION",
                "SELECT_CCFT_COHERENCE_ONTOLOGY_AND_REPRESENTATION",
                "SELECT_MASTER_ACTION_RECONCILIATION",
                "NO_NATIVE_HYPOTHESIS_READY",
            ],
        },
        "prohibited_actions": [
            "reopen_QFT_GR_QUADRATIC_BOUNDED_CLOSEOUT_V0",
            "reopen_TOE_NATIVE_SURROGATE_V0",
            "install_or_open_a_new_bounded_program",
            "select_a_real_or_complex_coherence_field",
            "construct_a_native_action_or_interaction",
            "execute_a_pillar_or_seam_calculation",
            "promote_CCFT_or_the_master_action",
            "claim_empirical_validation_or_ToE_completion",
        ],
        "program_installation_authorized_here": False,
        "scientific_calculation_authorized_here": False,
        "selected_next_target": SELECTOR_TARGET,
        "verdict": (
            "ONE_NATIVE_HYPOTHESIS_FRONTIER_SELECTOR_AUTHORIZED_"
            "CLOSED_PROGRAMS_PRESERVED_NO_NEW_PROGRAM_INSTALLED"
        ),
    }


def main() -> int:
    return write_or_check(
        path=OUTPUT_PATH,
        build=build_authority,
        description="native-hypothesis frontier selection authority",
    )


if __name__ == "__main__":
    raise SystemExit(main())

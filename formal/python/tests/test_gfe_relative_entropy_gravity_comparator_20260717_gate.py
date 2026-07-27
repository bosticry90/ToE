from __future__ import annotations

import json
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[3]
COMPARATOR_REPORT = (
    REPO_ROOT
    / "formal/docs/release/GFE_RELATIVE_ENTROPY_GRAVITY_COMPARATOR_20260717_v0.json"
)
PRIORITY_RETURN_REPORT = (
    REPO_ROOT
    / "formal/docs/release/POST_R13_FULL_TOE_PRIORITY_RETURN_SELECTION_20260717_v0.json"
)
COMPARATOR_NOTE = (
    REPO_ROOT
    / "formal/docs/lanes/GFE_RELATIVE_ENTROPY_GRAVITY_COMPARATOR_20260717_v0.md"
)
R13_CLOSEOUT_NOTE = (
    REPO_ROOT
    / "formal/docs/lanes/DIRAC_MAXWELL_R13_MECHANISM_EXPERIMENT_CLOSEOUT_20260717_v0.md"
)
R13_RESULT_REVIEW = (
    REPO_ROOT
    / "formal/docs/release/"
    "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
    "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_OBSERVABLE_SEMANTICS_"
    "RECONCILIATION_RESULT_REVIEW_20260717_v2.json"
)


def _json(path: Path) -> dict[str, object]:
    value = json.loads(path.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_comparator_is_registered_high_relevance_dormant_and_not_adopted() -> None:
    report = _json(COMPARATOR_REPORT)
    assert report["registry_entry_id"] == "GFE_RELATIVE_ENTROPY_GRAVITY_COMPARATOR"
    assert report["classification"] == [
        "RELATED_WORK",
        "HIGH_RELEVANCE",
        "NOT_ADOPTED",
        "DORMANT_COMPARATOR",
    ]
    assert report["verdict"] == (
        "REGISTERED_RELATED_WORK_HIGH_RELEVANCE_NOT_ADOPTED_DORMANT"
    )


def test_exact_fifteen_question_contract_is_frozen() -> None:
    questions = _json(COMPARATOR_REPORT)["comparator_questions"]
    assert isinstance(questions, list)
    assert len(questions) == 15
    assert len(set(questions)) == 15
    assert questions[0] == "What exactly are the physical and induced metric operators?"
    assert questions[-1] == (
        "What parts, if any, can be formalized as a bounded ToE candidate route?"
    )


def test_primary_action_and_thermodynamics_sources_are_separately_pinned() -> None:
    sources = _json(COMPARATOR_REPORT)["primary_sources"]
    assert isinstance(sources, list)
    assert [source["role"] for source in sources] == [
        "FOUNDATIONAL_GFE_ACTION",
        "GFE_THERMODYNAMICS_AND_FRW_COSMOLOGY",
    ]
    assert sources[0]["doi"] == "10.1103/PhysRevD.111.066001"
    assert sources[0]["arxiv_url"] == "https://arxiv.org/abs/2408.14391"
    assert sources[1]["doi"] == "10.1103/26kn-thgp"
    assert sources[1]["arxiv_url"] == "https://arxiv.org/abs/2510.22545"
    assert "CORRECTIONS_2025_07_14_AND_2026_03_19" in sources[0][
        "correction_boundary"
    ]


def test_gqre_terminology_and_nonclaim_boundary_are_exact() -> None:
    report = _json(COMPARATOR_REPORT)
    terminology = report["terminology"]
    assert terminology == {
        "accepted_abbreviation": "GQRE",
        "expanded_name": "Geometric Quantum Relative Entropy",
        "qgre_alias_adopted": False,
    }
    impact = report["formal_impact"]
    assert isinstance(impact, dict)
    assert not any(impact.values())


def test_human_note_forbids_structure_formation_and_toe_validation_inferences() -> None:
    note = COMPARATOR_NOTE.read_text(encoding="utf-8")
    for required in (
        "GFE_VALIDATES_TOE",
        "GFE_VALIDATES_C_K",
        "ENTROPY_DENSITY_DECREASE_IMPLIES_STRUCTURE_FORMATION",
        "GR_LIMIT_CLAIM_IMPLIES_EMPIRICAL_ADEQUACY",
    ):
        assert required in note


def test_priority_return_preserves_r13_and_selects_non_r13_preparation() -> None:
    selection = _json(PRIORITY_RETURN_REPORT)
    assert selection["consumed_target"].startswith("terminate_dirac_maxwell")
    assert selection["selected_next_target"] == (
        "prepare_sr_pillar_coordinate_convention_and_constant_restoration_packet"
    )
    decision = selection["decision"]
    assert isinstance(decision, dict)
    assert decision["selected_pillar_code"] == "SR"
    assert decision["selected_route"] == "CONVENTION_AND_CONSTANT_RESTORATION"
    assert decision["r13_reopened"] is False
    assert decision["gfe_comparator_remains_dormant"] is True
    assert decision["selected_lane_executes_now"] is False


def test_preserved_r13_status_matches_authoritative_result_review() -> None:
    selection = _json(PRIORITY_RETURN_REPORT)["preserved_r13_status"]
    r13 = _json(R13_RESULT_REVIEW)["preserved_scientific_core"]
    assert isinstance(selection, dict)
    assert isinstance(r13, dict)
    assert selection["H_A_through_H_E"] == r13["H_A_through_H_E"]
    assert selection["canonical_robustness"] == r13["fourteen_row_robustness"]
    assert selection["root_mechanism"] == r13["R13_root_mechanism"]
    assert selection["new_E_REPRO"] == r13["new_E_REPRO"]


def test_priority_return_hash_binds_accepted_inputs() -> None:
    inputs = _json(PRIORITY_RETURN_REPORT)["authority_inputs"]
    assert isinstance(inputs, dict)
    assert inputs["r13_result_review"]["sha256"] == (
        "da2cbf87a042a387b84f469ffec106746f19976e6acdc193469e21aa3e0a619e"
    )
    assert inputs["accepted_selector_review"]["sha256"] == (
        "e84d7a00a29a21dae59a8d3fb26f56a6a97cf3b6021766a6b176fde81a3d610d"
    )
    assert inputs["accepted_route_map_review"]["sha256"] == (
        "6dac3d95a29e7ab0d29a99d5903b682bf235b92e025b044890a2e927d8b6f875"
    )


def test_human_closeout_preserves_preterminal_and_phase_test_boundaries() -> None:
    note = R13_CLOSEOUT_NOTE.read_text(encoding="utf-8")
    for required in (
        "UNRESOLVED_EVIDENCE_SEMANTICS_BLOCK",
        "PREDICATE_INVARIANT",
        "BLOCKED_OBSERVABLE_DECISION_INSTABILITY",
        "full repository green:\nNOT CLAIMED",
        "prepare_sr_pillar_coordinate_convention_and_constant_restoration_packet",
    ):
        assert required in note

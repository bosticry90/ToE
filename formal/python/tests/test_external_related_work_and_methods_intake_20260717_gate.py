from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


ROOT = find_repo_root(Path(__file__))
RELATED = (
    ROOT
    / "formal/docs/lanes/EXTERNAL_RELATED_WORK_AND_BENCHMARK_INTAKE_20260717_v0.md"
)
SPRINT = ROOT / "formal/docs/paper/AI_THEOREM_SPRINT_PROTOCOL_v0.md"
METHODS = ROOT / "formal/docs/paper/FUTURE_SPECIALIZED_METHODS_REGISTRY_v0.md"
INDEX = (
    ROOT
    / "formal/docs/release/EXTERNAL_RELATED_WORK_AND_METHODS_INTAKE_20260717_v0.json"
)
R13_REVIEW = (
    ROOT
    / "formal/docs/release/DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
    "ROBUSTNESS_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_OBSERVABLE_SEMANTICS_"
    "RECONCILIATION_RESULT_REVIEW_20260717_v2.json"
)


def _text(path: Path) -> str:
    assert path.is_file(), f"missing intake artifact: {path}"
    return path.read_text(encoding="utf-8")


def _json(path: Path) -> dict:
    value = json.loads(_text(path))
    assert isinstance(value, dict)
    return value


def test_all_three_nonlive_intake_artifacts_and_index_exist() -> None:
    for path in (RELATED, SPRINT, METHODS, INDEX):
        assert path.is_file()


def test_related_work_and_benchmark_inventory_is_exact() -> None:
    text = _text(RELATED)
    ids = [
        "COMPUTATIONAL-SEAM-FLIBE-FRAGMENTATION-CASE-STUDY",
        "AI-CLOSED-THEOREM-SPRINT-METHODOLOGY-CASE",
        "GR-WEAK-ROTATING-SOURCE-BENCHMARK",
        "QM-GEOMETRY-TO-NONLINEAR-MECHANICAL-RESPONSE",
    ]
    assert "ENTRY_COUNT: 4" in text
    for entry_id in ids:
        assert text.count(f"## `{entry_id}`") == 1
    assert "NEW_ACTIVE_LANE_COUNT: 0" in text
    assert "THEOREM_DISCHARGE_COUNT: 0" in text
    assert "SCIENTIFIC_STATUS_CHANGE_COUNT: 0" in text


def test_fl_be_case_records_the_local_global_error_separation() -> None:
    text = _text(RELATED)
    assert "0.7 kcal/mol" in text
    assert "0.3 kcal/mol" in text
    assert "12 kcal/mol" in text
    assert "110 kcal/mol" in text
    assert "fragment construction, rather than fragment solution" in text
    assert "https://arxiv.org/abs/2606.30402" in text


def test_gr_and_qm_benchmarks_are_dormant_and_bounded() -> None:
    text = _text(RELATED)
    assert "DORMANT_UNTIL_GR_LANE_INTENTIONALLY_SELECTED" in text
    assert (
        "DORMANT_UNTIL_QM_STAT_EFFECTIVE_MATTER_OR_NONLINEAR_RESPONSE_IS_SELECTED"
        in text
    )
    assert "g_0i" in text and "T_0i" in text
    assert "Quantum-state-space nonmetricity is not identified" in text
    assert "https://www.nature.com/articles/s41586-026-10715-0" in text
    assert "https://journals.aps.org/prl/abstract/10.1103/jg6l-gzfr" in text


def test_ai_theorem_sprint_has_eligibility_execution_and_three_acceptance_gates() -> None:
    text = _text(SPRINT)
    for heading in (
        "## Eligibility gate",
        "## Frozen sprint packet",
        "## Execution",
        "### Logical correctness",
        "### Statement correspondence",
        "### Physical applicability",
        "## Stopping rule",
    ):
        assert heading in text
    assert "PROVED" in text
    assert "REFUTED_BY_COUNTEREXAMPLE" in text
    assert "ASSUMPTIONS_INSUFFICIENT" in text
    assert "UNRESOLVED_WITH_EXACT_GAP" in text
    assert "Parallel agents are optional" in text
    assert "This protocol proves nothing by itself" in text


def test_ai_source_caution_does_not_import_unverified_formalization_claim() -> None:
    combined = _text(RELATED) + _text(SPRINT)
    assert "does not record the external proof as refereed" in combined
    assert "machine-verified" in combined
    assert "cdc_proof.pdf" in combined
    assert "cdc_prompt.pdf" in combined


def test_analog_floquet_method_has_full_activation_and_encoding_seam_gate() -> None:
    text = _text(METHODS)
    assert "REGISTERED_METHOD_COUNT: 1" in text
    assert "ACTIVE_METHOD_COUNT: 0" in text
    assert text.count("## `ANALOG_FLOQUET_QUBO_SOLVER`") == 1
    assert "FUTURE_SPECIALIZED_TOOL_CANDIDATE" in text
    assert "No global-optimum guarantee" in text
    assert "scientific problem -> binary variables -> QUBO -> Ising Hamiltonian" in text
    assert "https://journals.aps.org/prx/abstract/10.1103/kgfb-5g2w" in text
    assert "purchasing or operating hardware" in text


def test_release_index_registers_exactly_five_actions_with_no_promotion() -> None:
    payload = _json(INDEX)
    assert payload["status"] == "PREPARED_NONLIVE_NONCLAIM"
    assert payload["registered_action_count"] == 5
    assert len(payload["registered_actions"]) == 5
    assert payload["new_active_lane_count"] == 0
    assert payload["theorem_discharge_count"] == 0
    assert payload["scientific_status_change_count"] == 0
    assert payload["source_verification"]["unverified_lean_project_claim_imported"] is False
    assert not any(payload["preserved_boundaries"].values())


def test_external_intake_does_not_reopen_or_reclassify_r13() -> None:
    intake = _json(INDEX)
    r13 = _json(R13_REVIEW)
    assert intake["r13_posture"]["reconciliation_lane_terminated"] is True
    assert intake["r13_posture"]["terminal_classification"] == (
        "NOT_ASSIGNED_PRETERMINAL"
    )
    assert intake["r13_posture"]["H_A_through_H_E"] == "NOT_EVALUATED"
    assert intake["r13_posture"]["root_mechanism"] == (
        "UNRESOLVED_EVIDENCE_SEMANTICS_BLOCK"
    )
    assert r13["hard_stop"]["reconciliation_lane_terminated"] is True
    assert r13["preserved_scientific_core"]["H_A_through_H_E"] == "NOT_EVALUATED"


def test_prohibited_overclaims_are_absent() -> None:
    combined = "\n".join(_text(path) for path in (RELATED, SPRINT, METHODS))
    for phrase in (
        "proves the ToE",
        "confirms the ToE",
        "CCFT is validated",
        "master action is validated",
        "NP-hard problems are solved",
        "global optimum is guaranteed",
    ):
        assert phrase not in combined

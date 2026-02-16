from __future__ import annotations

import json
import re
from pathlib import Path


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
QM_EVOLUTION_TARGET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_QM_EVOLUTION_HARDENING_v0.md"
)
QM_EVOLUTION_OBJECT_TARGET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_QM_EVOLUTION_OBJECT_v0.md"
)
QM_PILLAR_SUMMARY_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QM_EVOLUTION_PILLAR_SUMMARY_v0.md"
)
QM_CHAIN_MAP_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_QM_EVOLUTION_CANONICAL_CHAIN_MAP_v0.md"
)
QM_EVOLUTION_LEAN_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "QM" / "EvolutionContract.lean"
)
QM_ASSUMPTION_LEDGER_LEAN_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "QM" / "QMEvolutionAssumptionLedger.lean"
)
QM_ASSUMPTION_LEDGER_PATH = (
    REPO_ROOT / "formal" / "markdown" / "locks" / "policy" / "QM_EVOLUTION_ASSUMPTION_LEDGER_v0.md"
)
QM_ROBUSTNESS_RECORD_PATH = (
    REPO_ROOT / "formal" / "markdown" / "locks" / "policy" / "QM_EVOLUTION_ROBUSTNESS_RECORD_v0.md"
)
QM_NEGATIVE_CONTROL_RECORD_PATH = (
    REPO_ROOT
    / "formal"
    / "markdown"
    / "locks"
    / "policy"
    / "QM_EVOLUTION_NEGATIVE_CONTROL_RECORD_v0.md"
)
QM_RESOLUTION_TREND_RECORD_PATH = (
    REPO_ROOT
    / "formal"
    / "markdown"
    / "locks"
    / "policy"
    / "QM_EVOLUTION_RESOLUTION_TREND_RECORD_v0.md"
)
QM_PILLAR_PACKAGE_PATH = (
    REPO_ROOT / "formal" / "markdown" / "locks" / "policy" / "QM_EVOLUTION_PILLAR_PACKAGE_v0.md"
)
QM_ROBUSTNESS_TIME_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "qm_evolution_robustness_perturb_time_parameter_small_v0.json"
)
QM_ROBUSTNESS_STATE_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "qm_evolution_robustness_perturb_state_carrier_small_v0.json"
)
QM_ROBUSTNESS_OPERATOR_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "qm_evolution_robustness_perturb_operator_step_small_v0.json"
)
QM_NEGCTRL_BROKEN_STEP_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "qm_evolution_negative_control_broken_step_contract_v0.json"
)
QM_NEGCTRL_INVALID_CONTEXT_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "qm_evolution_negative_control_invalid_context_v0.json"
)
QM_NEGCTRL_INCOMPATIBLE_CARRIER_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "qm_evolution_negative_control_incompatible_state_carrier_v0.json"
)
QM_RESOLUTION_32_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "qm_evolution_resolution_trend_32_v0.json"
)
QM_RESOLUTION_64_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "qm_evolution_resolution_trend_64_v0.json"
)
QM_RESOLUTION_128_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "qm_evolution_resolution_trend_128_v0.json"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _extract_qm_hardening_adjudication(text: str, label: str) -> str:
    m = re.search(
        r"QM_EVOLUTION_HARDENING_ADJUDICATION:\s*"
        r"(NOT_YET_HARDENED_v0|DISCHARGED_v0_CONTRACT_HARDENED)",
        text,
    )
    assert m is not None, f"Missing QM_EVOLUTION_HARDENING_ADJUDICATION token in {label}."
    return m.group(1)


def test_qm_evolution_hardening_target_exists_and_pins_required_sections() -> None:
    text = _read(QM_EVOLUTION_TARGET_PATH)

    required_tokens = [
        "DERIVATION_TARGET_QM_EVOLUTION_HARDENING_v0",
        "QM_EVOLUTION_HARDENING_ADJUDICATION:",
        "Phase I — Canonicalization & Hygiene",
        "Phase II — Assumption minimization",
        "Phase III — Robustness stress tests",
        "Phase IIIb — Negative controls",
        "Phase IV — Optional trend checks",
        "Phase V — Package freeze",
        "QMEvolutionAssumptions_v0",
        "QM_EVOLUTION_ASSUMPTION_LEDGER_v0",
        "QM_EVOLUTION_ROBUSTNESS_RECORD_v0",
        "QM_EVOLUTION_NEGATIVE_CONTROL_RECORD_v0",
        "QM_EVOLUTION_RESOLUTION_TREND_RECORD_v0",
        "QM_EVOLUTION_PILLAR_PACKAGE_v0",
    ]
    missing = [tok for tok in required_tokens if tok not in text]
    assert not missing, "Missing required QM hardening-target token(s): " + ", ".join(missing)


def test_qm_evolution_hardening_adjudication_is_in_sync_with_state_doc() -> None:
    target_text = _read(QM_EVOLUTION_TARGET_PATH)
    state_text = _read(STATE_PATH)

    target_adj = _extract_qm_hardening_adjudication(target_text, "QM evolution hardening target")
    state_adj = _extract_qm_hardening_adjudication(state_text, "State_of_the_Theory.md")

    assert target_adj == state_adj, (
        "QM evolution hardening adjudication token drift between target doc and state doc: "
        f"target={target_adj}, state={state_adj}"
    )


def test_qm_evolution_phase_artifacts_exist_with_template_tokens() -> None:
    required_files = [
        QM_ASSUMPTION_LEDGER_PATH,
        QM_ROBUSTNESS_RECORD_PATH,
        QM_NEGATIVE_CONTROL_RECORD_PATH,
        QM_RESOLUTION_TREND_RECORD_PATH,
        QM_PILLAR_PACKAGE_PATH,
    ]
    missing = [str(path) for path in required_files if not path.exists()]
    assert not missing, "Missing required QM hardening template artifacts: " + ", ".join(missing)

    ledger_text = _read(QM_ASSUMPTION_LEDGER_PATH)
    for token in [
        "QM_EVOLUTION_ASSUMPTION_LEDGER_v0",
        "QMEvolutionAssumptions_v0",
        "QMEvolutionAssumptions_v0_min1",
        "QM_EVOLUTION_ASSUMPTION_LEDGER_PROGRESS_v0: BUNDLE_POPULATED",
        "QM_EVOLUTION_ASSUMPTION_LEDGER_PROGRESS_v0: BUNDLE_MIN1_POPULATED",
        "QM_EVOLUTION_RECLASSIFICATION_v0_MIN1: hStepTotalPolicy_POLICY_TO_MATH_via_qm_step_total_of_definition",
        "MATH",
        "DEF",
        "POLICY",
        "SCOPE",
    ]:
        assert token in ledger_text, f"Missing assumption-ledger token: {token}"

    lean_ledger_text = _read(QM_ASSUMPTION_LEDGER_LEAN_PATH)
    for token in [
        "inductive QMEvolutionAssumptionClass_v0",
        "def qmEvolutionAssumptionClass_v0",
        "def QMEvolutionOperatorStepTotal",
        "theorem qm_step_total_of_definition",
        "structure QMEvolutionAssumptions_v0",
        "structure QMEvolutionAssumptions_v0_min1",
        "theorem qm_evolution_of_QMEvolutionAssumptions_v0",
        "theorem qm_evolution_of_QMEvolutionAssumptions_v0_min1",
    ]:
        assert token in lean_ledger_text, f"Missing Lean assumption-ledger token: {token}"

    robustness_text = _read(QM_ROBUSTNESS_RECORD_PATH)
    for token in [
        "QM_EVOLUTION_ROBUSTNESS_RECORD_v0",
        "QM_EVOLUTION_ROBUSTNESS_STATUS_v0: TEMPLATE_PINNED",
        "QM_EVOLUTION_ROBUSTNESS_PROGRESS_v0: ROW_PERTURB_TIME_PARAMETER_SMALL_POPULATED",
        "QM_EVOLUTION_ROBUSTNESS_PROGRESS_v0: ROW_PERTURB_STATE_CARRIER_SMALL_POPULATED",
        "QM_EVOLUTION_ROBUSTNESS_PROGRESS_v0: ROW_PERTURB_OPERATOR_STEP_SMALL_POPULATED",
        "QM_EVOLUTION_ROBUSTNESS_PROGRESS_v0: ALL_REQUIRED_PERTURBATION_ROWS_POPULATED",
        "PERTURB_TIME_PARAMETER_SMALL_v0",
        "PERTURB_STATE_CARRIER_SMALL_v0",
        "PERTURB_OPERATOR_STEP_SMALL_v0",
        "OUTCOME_STILL_SATISFIES_CONTRACT",
        "OUTCOME_FAILS_INFORMATIVE",
    ]:
        assert token in robustness_text, f"Missing robustness token: {token}"

    negative_text = _read(QM_NEGATIVE_CONTROL_RECORD_PATH)
    for token in [
        "QM_EVOLUTION_NEGATIVE_CONTROL_RECORD_v0",
        "QM_EVOLUTION_NEGATIVE_CONTROL_STATUS_v0: TEMPLATE_PINNED",
        "QM_EVOLUTION_NEGATIVE_CONTROL_PROGRESS_v0: ROW_NEGCTRL_INVALID_EVOLUTION_CONTEXT_POPULATED",
        "QM_EVOLUTION_NEGATIVE_CONTROL_PROGRESS_v0: ROW_NEGCTRL_BROKEN_STEP_CONTRACT_POPULATED",
        "QM_EVOLUTION_NEGATIVE_CONTROL_PROGRESS_v0: ROW_NEGCTRL_INCOMPATIBLE_STATE_CARRIER_POPULATED",
        "QM_EVOLUTION_NEGATIVE_CONTROL_PROGRESS_v0: ALL_REQUIRED_NEGATIVE_ROWS_POPULATED",
        "NEGCTRL_INVALID_EVOLUTION_CONTEXT_v0",
        "NEGCTRL_BROKEN_STEP_CONTRACT_v0",
        "NEGCTRL_INCOMPATIBLE_STATE_CARRIER_v0",
        "OUTCOME_FAILS_INFORMATIVE",
    ]:
        assert token in negative_text, f"Missing negative-control token: {token}"

    trend_text = _read(QM_RESOLUTION_TREND_RECORD_PATH)
    for token in [
        "QM_EVOLUTION_RESOLUTION_TREND_RECORD_v0",
        "QM_EVOLUTION_RESOLUTION_TREND_STATUS_v0: TEMPLATE_PINNED",
        "QM_EVOLUTION_RESOLUTION_TREND_PROGRESS_v0: ROW_QM_RESOLUTION_32_POPULATED",
        "QM_EVOLUTION_RESOLUTION_TREND_PROGRESS_v0: ROW_QM_RESOLUTION_64_POPULATED",
        "QM_EVOLUTION_RESOLUTION_TREND_PROGRESS_v0: ROW_QM_RESOLUTION_128_POPULATED",
        "QM_EVOLUTION_RESOLUTION_TREND_PROGRESS_v0: ALL_REQUIRED_RESOLUTION_ROWS_POPULATED",
        "QM_RESOLUTION_32_v0",
        "QM_RESOLUTION_64_v0",
        "QM_RESOLUTION_128_v0",
        "residual_norm",
        "convergence_trend",
        "limit_break_annotation",
    ]:
        assert token in trend_text, f"Missing resolution-trend token: {token}"


def test_qm_evolution_package_freeze_and_reopen_policy_are_pinned() -> None:
    pkg_text = _read(QM_PILLAR_PACKAGE_PATH)
    summary_text = _read(QM_PILLAR_SUMMARY_PATH)
    chain_map_text = _read(QM_CHAIN_MAP_PATH)
    required_tokens = [
        "QM_EVOLUTION_PILLAR_PACKAGE_v0",
        "QM_EVOLUTION_PILLAR_PACKAGE_STATUS_v0: FROZEN_CONTENTS_PINNED",
        "QM_EVOLUTION_PILLAR_PACKAGE_PROGRESS_v0: REQUIRED_CONTENTS_PINNED",
        "QM_EVOLUTION_REOPEN_POLICY_v0: FROZEN_WATCH_REOPEN_ON_REGRESSION",
        "REOPEN_TRIGGER_QM_CANONICAL_TOKEN_DRIFT_v0",
        "REOPEN_TRIGGER_QM_ROBUSTNESS_NEGCTRL_REGRESSION_v0",
        "REOPEN_TRIGGER_QM_TREND_BREAK_v0",
        "DERIVATION_TARGET_QM_EVOLUTION_HARDENING_v0.md",
        "TOE_QM_EVOLUTION_PILLAR_SUMMARY_v0.md",
        "TOE_QM_EVOLUTION_CANONICAL_CHAIN_MAP_v0.md",
        "QM_EVOLUTION_ASSUMPTION_LEDGER_v0.md",
        "QM_EVOLUTION_ROBUSTNESS_RECORD_v0.md",
        "QM_EVOLUTION_NEGATIVE_CONTROL_RECORD_v0.md",
        "QM_EVOLUTION_RESOLUTION_TREND_RECORD_v0.md",
        "EvolutionContract.lean",
    ]
    missing = [tok for tok in required_tokens if tok not in pkg_text]
    assert not missing, "Missing QM package token(s): " + ", ".join(missing)

    target_adj = _extract_qm_hardening_adjudication(
        _read(QM_EVOLUTION_TARGET_PATH),
        "QM evolution hardening target",
    )
    state_adj = _extract_qm_hardening_adjudication(
        _read(STATE_PATH),
        "State_of_the_Theory.md",
    )
    summary_adj = _extract_qm_hardening_adjudication(
        summary_text,
        "TOE_QM_EVOLUTION_PILLAR_SUMMARY_v0.md",
    )
    assert target_adj == state_adj == summary_adj, (
        "QM hardening adjudication drift across target/state/summary: "
        f"target={target_adj}, state={state_adj}, summary={summary_adj}"
    )

    for token in [
        "TOE_QM_EVOLUTION_PILLAR_SUMMARY_v0",
        "QM_EVOLUTION_ROBUSTNESS_PROGRESS_v0: ALL_REQUIRED_PERTURBATION_ROWS_POPULATED",
        "QM_EVOLUTION_NEGATIVE_CONTROL_PROGRESS_v0: ALL_REQUIRED_NEGATIVE_ROWS_POPULATED",
        "QM_EVOLUTION_RESOLUTION_TREND_PROGRESS_v0: ALL_REQUIRED_RESOLUTION_ROWS_POPULATED",
    ]:
        assert token in summary_text, f"Missing QM summary token: {token}"

    for token in [
        "TOE_QM_EVOLUTION_CANONICAL_CHAIN_MAP_v0",
        "TimeParameter",
        "EvolutionOperator",
        "EvolutionContext",
        "QMStateEvolvesUnderContract",
        "qm_evolution_under_contract_assumptions",
        "QMEvolutionAssumptions_v0",
        "QMEvolutionAssumptions_v0_min1",
        "qm_step_total_of_definition",
    ]:
        assert token in chain_map_text, f"Missing QM chain-map token: {token}"


def test_qm_evolution_canonical_theorem_and_handoff_focus_are_pinned() -> None:
    lean_text = _read(QM_EVOLUTION_LEAN_PATH)
    object_target_text = _read(QM_EVOLUTION_OBJECT_TARGET_PATH)
    state_text = _read(STATE_PATH)

    for token in [
        "theorem qm_evolution_under_contract_assumptions",
        "Contract-only theorem surface.",
        "No Schrodinger derivation claim and no external truth claim.",
    ]:
        assert token in lean_text, f"Missing canonical QM evolution token in Lean module: {token}"

    for token in [
        "PILLAR-QM",
        "TARGET-QM-EVOL-PLAN",
        "TOE-QM-THM-01",
    ]:
        assert token in object_target_text, f"Missing QM object target token: {token}"

    for token in [
        "NEXT_PILLAR_FOCUS_v0: PILLAR-QM",
        "NEXT_PILLAR_PRIMARY_LANE_v0: TARGET-QM-EVOL-PLAN",
    ]:
        assert token in state_text, f"Missing next-pillar focus token in state: {token}"


def test_qm_evolution_phase3_time_perturbation_row_is_populated_and_artifact_pinned() -> None:
    robustness_text = _read(QM_ROBUSTNESS_RECORD_PATH)

    m = re.search(
        r"^\|\s*`PERTURB_TIME_PARAMETER_SMALL_v0`\s*\|\s*`(.*?)`\s*\|\s*`(.*?)`\s*\|\s*`(.*?)`\s*\|\s*`(.*?)`\s*\|\s*`?(formal/output/qm_evolution_robustness_perturb_time_parameter_small_v0\.json)`?\s*\|\s*$",
        robustness_text,
        flags=re.MULTILINE,
    )
    assert m is not None, (
        "Missing or malformed populated row for PERTURB_TIME_PARAMETER_SMALL_v0 in QM robustness record."
    )

    input_delta, expected_outcome, observed_outcome, reason_code, artifact_rel = m.groups()
    for cell, label in [
        (input_delta, "input delta"),
        (expected_outcome, "expected outcome"),
        (observed_outcome, "observed outcome"),
        (reason_code, "reason code"),
    ]:
        assert "TBD" not in cell, f"PERTURB_TIME_PARAMETER_SMALL_v0 {label} must be populated (not TBD)."

    assert expected_outcome == "OUTCOME_STILL_SATISFIES_CONTRACT", (
        "PERTURB_TIME_PARAMETER_SMALL_v0 expected outcome must be OUTCOME_STILL_SATISFIES_CONTRACT."
    )
    assert observed_outcome == "OUTCOME_STILL_SATISFIES_CONTRACT", (
        "PERTURB_TIME_PARAMETER_SMALL_v0 observed outcome must be OUTCOME_STILL_SATISFIES_CONTRACT."
    )

    artifact_path = REPO_ROOT / artifact_rel
    assert artifact_path == QM_ROBUSTNESS_TIME_ARTIFACT_PATH, (
        "QM time-perturbation robustness artifact path drift detected."
    )
    payload = json.loads(_read(artifact_path))

    assert payload.get("record_id") == "QM_EVOLUTION_ROBUSTNESS_RECORD_v0"
    assert payload.get("perturbation_id") == "PERTURB_TIME_PARAMETER_SMALL_v0"
    assert payload.get("expected_outcome") == "OUTCOME_STILL_SATISFIES_CONTRACT"
    assert payload.get("observed_outcome") == "OUTCOME_STILL_SATISFIES_CONTRACT"
    assert isinstance(payload.get("reason_code"), str) and payload.get("reason_code")
    assert payload.get("scope") == "contract_only_qm_evolution_v0"
    determinism = payload.get("determinism")
    assert isinstance(determinism, dict)
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"


def test_qm_evolution_phase3_broken_step_negative_row_is_populated_and_artifact_pinned() -> None:
    negative_text = _read(QM_NEGATIVE_CONTROL_RECORD_PATH)

    m = re.search(
        r"^\|\s*`NEGCTRL_BROKEN_STEP_CONTRACT_v0`\s*\|\s*`(.*?)`\s*\|\s*`(.*?)`\s*\|\s*`(.*?)`\s*\|\s*`(.*?)`\s*\|\s*`?(formal/output/qm_evolution_negative_control_broken_step_contract_v0\.json)`?\s*\|\s*$",
        negative_text,
        flags=re.MULTILINE,
    )
    assert m is not None, (
        "Missing or malformed populated row for NEGCTRL_BROKEN_STEP_CONTRACT_v0 in QM negative-control record."
    )

    injected_violation, expected_failure, observed_failure, reason_code, artifact_rel = m.groups()
    for cell, label in [
        (injected_violation, "injected violation"),
        (expected_failure, "expected failure token"),
        (observed_failure, "observed failure token"),
        (reason_code, "reason code"),
    ]:
        assert "TBD" not in cell, f"NEGCTRL_BROKEN_STEP_CONTRACT_v0 {label} must be populated (not TBD)."

    assert expected_failure == "QMStateEvolvesUnderContract", (
        "NEGCTRL_BROKEN_STEP_CONTRACT_v0 expected failure token must be QMStateEvolvesUnderContract."
    )
    assert observed_failure == "QMStateEvolvesUnderContract", (
        "NEGCTRL_BROKEN_STEP_CONTRACT_v0 observed failure token must be QMStateEvolvesUnderContract."
    )

    artifact_path = REPO_ROOT / artifact_rel
    assert artifact_path == QM_NEGCTRL_BROKEN_STEP_ARTIFACT_PATH, (
        "QM broken-step negative-control artifact path drift detected."
    )
    payload = json.loads(_read(artifact_path))

    assert payload.get("record_id") == "QM_EVOLUTION_NEGATIVE_CONTROL_RECORD_v0"
    assert payload.get("negative_id") == "NEGCTRL_BROKEN_STEP_CONTRACT_v0"
    assert payload.get("expected_outcome") == "OUTCOME_FAILS_INFORMATIVE"
    assert payload.get("observed_outcome") == "OUTCOME_FAILS_INFORMATIVE"
    assert payload.get("expected_failure_token") == "QMStateEvolvesUnderContract"
    assert payload.get("observed_failure_token") == "QMStateEvolvesUnderContract"
    assert isinstance(payload.get("reason_code"), str) and payload.get("reason_code")
    assert payload.get("scope") == "contract_only_qm_evolution_v0"
    determinism = payload.get("determinism")
    assert isinstance(determinism, dict)
    assert determinism.get("schema_version") == "v0"
    assert determinism.get("fingerprint_method") == "literal-json-lock"


def test_qm_evolution_phase3_state_perturbation_row_is_populated_and_artifact_pinned() -> None:
    robustness_text = _read(QM_ROBUSTNESS_RECORD_PATH)

    m = re.search(
        r"^\|\s*`PERTURB_STATE_CARRIER_SMALL_v0`\s*\|\s*`(.*?)`\s*\|\s*`(.*?)`\s*\|\s*`(.*?)`\s*\|\s*`(.*?)`\s*\|\s*`?(formal/output/qm_evolution_robustness_perturb_state_carrier_small_v0\.json)`?\s*\|\s*$",
        robustness_text,
        flags=re.MULTILINE,
    )
    assert m is not None, (
        "Missing or malformed populated row for PERTURB_STATE_CARRIER_SMALL_v0 in QM robustness record."
    )

    input_delta, expected_outcome, observed_outcome, reason_code, artifact_rel = m.groups()
    for cell in [input_delta, expected_outcome, observed_outcome, reason_code]:
        assert "TBD" not in cell

    assert expected_outcome == "OUTCOME_STILL_SATISFIES_CONTRACT"
    assert observed_outcome == "OUTCOME_STILL_SATISFIES_CONTRACT"

    artifact_path = REPO_ROOT / artifact_rel
    assert artifact_path == QM_ROBUSTNESS_STATE_ARTIFACT_PATH
    payload = json.loads(_read(artifact_path))

    assert payload.get("record_id") == "QM_EVOLUTION_ROBUSTNESS_RECORD_v0"
    assert payload.get("perturbation_id") == "PERTURB_STATE_CARRIER_SMALL_v0"
    assert payload.get("expected_outcome") == "OUTCOME_STILL_SATISFIES_CONTRACT"
    assert payload.get("observed_outcome") == "OUTCOME_STILL_SATISFIES_CONTRACT"
    assert payload.get("scope") == "contract_only_qm_evolution_v0"


def test_qm_evolution_phase3_operator_perturbation_row_is_populated_and_artifact_pinned() -> None:
    robustness_text = _read(QM_ROBUSTNESS_RECORD_PATH)

    m = re.search(
        r"^\|\s*`PERTURB_OPERATOR_STEP_SMALL_v0`\s*\|\s*`(.*?)`\s*\|\s*`(.*?)`\s*\|\s*`(.*?)`\s*\|\s*`(.*?)`\s*\|\s*`?(formal/output/qm_evolution_robustness_perturb_operator_step_small_v0\.json)`?\s*\|\s*$",
        robustness_text,
        flags=re.MULTILINE,
    )
    assert m is not None, (
        "Missing or malformed populated row for PERTURB_OPERATOR_STEP_SMALL_v0 in QM robustness record."
    )

    input_delta, expected_outcome, observed_outcome, reason_code, artifact_rel = m.groups()
    for cell in [input_delta, expected_outcome, observed_outcome, reason_code]:
        assert "TBD" not in cell

    assert expected_outcome == "OUTCOME_STILL_SATISFIES_CONTRACT"
    assert observed_outcome == "OUTCOME_STILL_SATISFIES_CONTRACT"

    artifact_path = REPO_ROOT / artifact_rel
    assert artifact_path == QM_ROBUSTNESS_OPERATOR_ARTIFACT_PATH
    payload = json.loads(_read(artifact_path))

    assert payload.get("record_id") == "QM_EVOLUTION_ROBUSTNESS_RECORD_v0"
    assert payload.get("perturbation_id") == "PERTURB_OPERATOR_STEP_SMALL_v0"
    assert payload.get("expected_outcome") == "OUTCOME_STILL_SATISFIES_CONTRACT"
    assert payload.get("observed_outcome") == "OUTCOME_STILL_SATISFIES_CONTRACT"
    assert payload.get("scope") == "contract_only_qm_evolution_v0"


def test_qm_evolution_phase3_invalid_context_negative_row_is_populated_and_artifact_pinned() -> None:
    negative_text = _read(QM_NEGATIVE_CONTROL_RECORD_PATH)

    m = re.search(
        r"^\|\s*`NEGCTRL_INVALID_EVOLUTION_CONTEXT_v0`\s*\|\s*`(.*?)`\s*\|\s*`(.*?)`\s*\|\s*`(.*?)`\s*\|\s*`(.*?)`\s*\|\s*`?(formal/output/qm_evolution_negative_control_invalid_context_v0\.json)`?\s*\|\s*$",
        negative_text,
        flags=re.MULTILINE,
    )
    assert m is not None, (
        "Missing or malformed populated row for NEGCTRL_INVALID_EVOLUTION_CONTEXT_v0 in QM negative-control record."
    )

    injected_violation, expected_failure, observed_failure, reason_code, artifact_rel = m.groups()
    for cell in [injected_violation, expected_failure, observed_failure, reason_code]:
        assert "TBD" not in cell

    assert expected_failure == "EvolutionContext"
    assert observed_failure == "EvolutionContext"

    artifact_path = REPO_ROOT / artifact_rel
    assert artifact_path == QM_NEGCTRL_INVALID_CONTEXT_ARTIFACT_PATH
    payload = json.loads(_read(artifact_path))

    assert payload.get("record_id") == "QM_EVOLUTION_NEGATIVE_CONTROL_RECORD_v0"
    assert payload.get("negative_id") == "NEGCTRL_INVALID_EVOLUTION_CONTEXT_v0"
    assert payload.get("expected_outcome") == "OUTCOME_FAILS_INFORMATIVE"
    assert payload.get("observed_outcome") == "OUTCOME_FAILS_INFORMATIVE"
    assert payload.get("expected_failure_token") == "EvolutionContext"
    assert payload.get("observed_failure_token") == "EvolutionContext"
    assert payload.get("scope") == "contract_only_qm_evolution_v0"


def test_qm_evolution_phase3_incompatible_carrier_negative_row_is_populated_and_artifact_pinned() -> None:
    negative_text = _read(QM_NEGATIVE_CONTROL_RECORD_PATH)

    m = re.search(
        r"^\|\s*`NEGCTRL_INCOMPATIBLE_STATE_CARRIER_v0`\s*\|\s*`(.*?)`\s*\|\s*`(.*?)`\s*\|\s*`(.*?)`\s*\|\s*`(.*?)`\s*\|\s*`?(formal/output/qm_evolution_negative_control_incompatible_state_carrier_v0\.json)`?\s*\|\s*$",
        negative_text,
        flags=re.MULTILINE,
    )
    assert m is not None, (
        "Missing or malformed populated row for NEGCTRL_INCOMPATIBLE_STATE_CARRIER_v0 in QM negative-control record."
    )

    injected_violation, expected_failure, observed_failure, reason_code, artifact_rel = m.groups()
    for cell in [injected_violation, expected_failure, observed_failure, reason_code]:
        assert "TBD" not in cell

    assert expected_failure == "QMState"
    assert observed_failure == "QMState"

    artifact_path = REPO_ROOT / artifact_rel
    assert artifact_path == QM_NEGCTRL_INCOMPATIBLE_CARRIER_ARTIFACT_PATH
    payload = json.loads(_read(artifact_path))

    assert payload.get("record_id") == "QM_EVOLUTION_NEGATIVE_CONTROL_RECORD_v0"
    assert payload.get("negative_id") == "NEGCTRL_INCOMPATIBLE_STATE_CARRIER_v0"
    assert payload.get("expected_outcome") == "OUTCOME_FAILS_INFORMATIVE"
    assert payload.get("observed_outcome") == "OUTCOME_FAILS_INFORMATIVE"
    assert payload.get("expected_failure_token") == "QMState"
    assert payload.get("observed_failure_token") == "QMState"
    assert payload.get("scope") == "contract_only_qm_evolution_v0"


def test_qm_evolution_phase4_resolution_32_row_is_populated_and_artifact_pinned() -> None:
    trend_text = _read(QM_RESOLUTION_TREND_RECORD_PATH)

    m = re.search(
        r"^\|\s*`QM_RESOLUTION_32_v0`\s*\|\s*`32`\s*\|\s*`(.*?)`\s*\|\s*`(.*?)`\s*\|\s*`(.*?)`\s*\|\s*`?(formal/output/qm_evolution_resolution_trend_32_v0\.json)`?\s*\|\s*$",
        trend_text,
        flags=re.MULTILINE,
    )
    assert m is not None, "Missing or malformed populated row for QM_RESOLUTION_32_v0 in trend record."

    residual_norm, convergence_trend, limit_break_annotation, artifact_rel = m.groups()
    for cell in [residual_norm, convergence_trend, limit_break_annotation]:
        assert "TBD" not in cell

    artifact_path = REPO_ROOT / artifact_rel
    assert artifact_path == QM_RESOLUTION_32_ARTIFACT_PATH
    payload = json.loads(_read(artifact_path))
    assert payload.get("record_id") == "QM_EVOLUTION_RESOLUTION_TREND_RECORD_v0"
    assert payload.get("resolution_id") == "QM_RESOLUTION_32_v0"
    assert int(payload.get("grid_size")) == 32


def test_qm_evolution_phase4_resolution_64_row_is_populated_and_artifact_pinned() -> None:
    trend_text = _read(QM_RESOLUTION_TREND_RECORD_PATH)

    m = re.search(
        r"^\|\s*`QM_RESOLUTION_64_v0`\s*\|\s*`64`\s*\|\s*`(.*?)`\s*\|\s*`(.*?)`\s*\|\s*`(.*?)`\s*\|\s*`?(formal/output/qm_evolution_resolution_trend_64_v0\.json)`?\s*\|\s*$",
        trend_text,
        flags=re.MULTILINE,
    )
    assert m is not None, "Missing or malformed populated row for QM_RESOLUTION_64_v0 in trend record."

    residual_norm, convergence_trend, limit_break_annotation, artifact_rel = m.groups()
    for cell in [residual_norm, convergence_trend, limit_break_annotation]:
        assert "TBD" not in cell

    artifact_path = REPO_ROOT / artifact_rel
    assert artifact_path == QM_RESOLUTION_64_ARTIFACT_PATH
    payload = json.loads(_read(artifact_path))
    assert payload.get("record_id") == "QM_EVOLUTION_RESOLUTION_TREND_RECORD_v0"
    assert payload.get("resolution_id") == "QM_RESOLUTION_64_v0"
    assert int(payload.get("grid_size")) == 64


def test_qm_evolution_phase4_resolution_128_row_is_populated_and_artifact_pinned() -> None:
    trend_text = _read(QM_RESOLUTION_TREND_RECORD_PATH)

    m = re.search(
        r"^\|\s*`QM_RESOLUTION_128_v0`\s*\|\s*`128`\s*\|\s*`(.*?)`\s*\|\s*`(.*?)`\s*\|\s*`(.*?)`\s*\|\s*`?(formal/output/qm_evolution_resolution_trend_128_v0\.json)`?\s*\|\s*$",
        trend_text,
        flags=re.MULTILINE,
    )
    assert m is not None, "Missing or malformed populated row for QM_RESOLUTION_128_v0 in trend record."

    residual_norm, convergence_trend, limit_break_annotation, artifact_rel = m.groups()
    for cell in [residual_norm, convergence_trend, limit_break_annotation]:
        assert "TBD" not in cell

    artifact_path = REPO_ROOT / artifact_rel
    assert artifact_path == QM_RESOLUTION_128_ARTIFACT_PATH
    payload = json.loads(_read(artifact_path))
    assert payload.get("record_id") == "QM_EVOLUTION_RESOLUTION_TREND_RECORD_v0"
    assert payload.get("resolution_id") == "QM_RESOLUTION_128_v0"
    assert int(payload.get("grid_size")) == 128


def test_qm_evolution_phase4_resolution_trend_quality_is_monotonic_nonincreasing() -> None:
    payload_32 = json.loads(_read(QM_RESOLUTION_32_ARTIFACT_PATH))
    payload_64 = json.loads(_read(QM_RESOLUTION_64_ARTIFACT_PATH))
    payload_128 = json.loads(_read(QM_RESOLUTION_128_ARTIFACT_PATH))

    residual_32 = float(payload_32["residual_norm"])
    residual_64 = float(payload_64["residual_norm"])
    residual_128 = float(payload_128["residual_norm"])

    assert residual_64 <= residual_32, (
        "QM resolution trend quality regression: residual_norm at 64 must be <= 32. "
        f"Observed 32={residual_32}, 64={residual_64}."
    )
    assert residual_128 <= residual_64, (
        "QM resolution trend quality regression: residual_norm at 128 must be <= 64. "
        f"Observed 64={residual_64}, 128={residual_128}."
    )

    assert payload_64.get("convergence_trend") == "improving_vs_32_v0"
    assert payload_128.get("convergence_trend") == "improving_vs_64_v0"

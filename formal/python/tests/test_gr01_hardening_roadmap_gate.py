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
HARDENING_TARGET_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_GR01_HARDENING_v0.md"
)
CANONICAL_GR01_FILES = [
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Variational" / "GR01EndToEndClosure.lean",
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Variational" / "GR01DerivationScaffoldPromotion.lean",
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Variational" / "GR01BridgePromotion.lean",
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Variational" / "WeakFieldPoissonLimit.lean",
]
WEAK_FIELD_FILE = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Variational" / "WeakFieldPoissonLimit.lean"
)
ASSUMPTION_LEDGER_LOCK_PATH = (
    REPO_ROOT / "formal" / "markdown" / "locks" / "policy" / "GR01_ASSUMPTION_LEDGER_v0.md"
)
ASSUMPTION_LEDGER_LEAN_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Variational" / "GR01AssumptionLedger.lean"
)
ROBUSTNESS_RECORD_PATH = (
    REPO_ROOT / "formal" / "markdown" / "locks" / "policy" / "GR01_ROBUSTNESS_RECORD_v0.md"
)
NEGATIVE_CONTROL_RECORD_PATH = (
    REPO_ROOT / "formal" / "markdown" / "locks" / "policy" / "GR01_NEGATIVE_CONTROL_RECORD_v0.md"
)
RESOLUTION_TREND_RECORD_PATH = (
    REPO_ROOT / "formal" / "markdown" / "locks" / "policy" / "GR01_RESOLUTION_TREND_RECORD_v0.md"
)
PILLAR_PACKAGE_PATH = (
    REPO_ROOT / "formal" / "markdown" / "locks" / "policy" / "GR01_PILLAR_PACKAGE_v0.md"
)
PILLAR_SUMMARY_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_GR01_PILLAR_SUMMARY_v0.md"
)
CHAIN_MAP_PATH = (
    REPO_ROOT / "formal" / "docs" / "paper" / "TOE_GR01_CANONICAL_CHAIN_MAP_v0.md"
)
RESOLUTION_32_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "gr01_resolution_trend_32_v0.json"
)
RESOLUTION_64_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "gr01_resolution_trend_64_v0.json"
)
RESOLUTION_128_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "gr01_resolution_trend_128_v0.json"
)
ROBUSTNESS_RHO_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "gr01_robustness_perturb_rho_small_v0.json"
)
ROBUSTNESS_PHI_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "gr01_robustness_perturb_phi_small_v0.json"
)
ROBUSTNESS_DISCRETIZATION_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "gr01_robustness_perturb_discretization_params_v0.json"
)
ROBUSTNESS_BOUNDARY_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "gr01_robustness_perturb_boundary_handling_v0.json"
)
ROBUSTNESS_PROJECTION_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "gr01_robustness_perturb_projection_conditions_v0.json"
)
NEGCTRL_WRONG_KAPPA_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "gr01_negative_control_wrong_kappa_sign_v0.json"
)
NEGCTRL_BROKEN_SCALING_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "gr01_negative_control_broken_scaling_hierarchy_v0.json"
)
NEGCTRL_BROKEN_WEAK_FIELD_BOUND_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "gr01_negative_control_broken_weak_field_bound_v0.json"
)
NEGCTRL_BROKEN_SYMMETRY_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "gr01_negative_control_broken_symmetry_obligation_v0.json"
)
NEGCTRL_INCOMPATIBLE_CARRIERS_ARTIFACT_PATH = (
    REPO_ROOT / "formal" / "output" / "gr01_negative_control_incompatible_carriers_v0.json"
)
ROBUSTNESS_ARTIFACT_PATHS = [
    ROBUSTNESS_RHO_ARTIFACT_PATH,
    ROBUSTNESS_PHI_ARTIFACT_PATH,
    ROBUSTNESS_DISCRETIZATION_ARTIFACT_PATH,
    ROBUSTNESS_BOUNDARY_ARTIFACT_PATH,
    ROBUSTNESS_PROJECTION_ARTIFACT_PATH,
]
NEGATIVE_CONTROL_ARTIFACT_PATHS = [
    NEGCTRL_WRONG_KAPPA_ARTIFACT_PATH,
    NEGCTRL_BROKEN_SCALING_ARTIFACT_PATH,
    NEGCTRL_BROKEN_WEAK_FIELD_BOUND_ARTIFACT_PATH,
    NEGCTRL_BROKEN_SYMMETRY_ARTIFACT_PATH,
    NEGCTRL_INCOMPATIBLE_CARRIERS_ARTIFACT_PATH,
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _extract_hardening_adjudication(text: str, label: str) -> str:
    m = re.search(
        r"GR01_HARDENING_ADJUDICATION:\s*"
        r"(NOT_YET_HARDENED_v0|DISCHARGED_v0_DISCRETE_HARDENED)",
        text,
    )
    assert m is not None, f"Missing GR01_HARDENING_ADJUDICATION token in {label}."
    return m.group(1)


def _extract_structure_block(text: str, structure_name: str) -> str:
    m = re.search(
        rf"structure\s+{re.escape(structure_name)}\b[\s\S]*?(?=\n(?:structure|theorem|def)\s+|\Z)",
        text,
    )
    assert m is not None, f"Could not locate structure block: {structure_name}"
    return m.group(0)


def _extract_state_token(text: str, token: str) -> str:
    m = re.search(rf"{re.escape(token)}:\s*([^\n`]+)", text)
    assert m is not None, f"Missing required state token: {token}"
    return m.group(1).strip()


def test_gr01_hardening_target_exists_and_pins_required_sections() -> None:
    text = _read(HARDENING_TARGET_PATH)

    required_tokens = [
        "DERIVATION_TARGET_GR01_HARDENING_v0",
        "GR01_HARDENING_ADJUDICATION:",
        "Hardening done criteria (exit criteria)",
        "Phase I — Canonicalization & Hygiene",
        "Phase II — Assumption minimization",
        "Phase III — Robustness stress tests",
        "Phase IV — Optional continuum-alignment sanity checks",
        "Phase V — Pillar package freeze",
        "MATH",
        "DEF",
        "POLICY",
        "SCOPE",
        "GR01Assumptions_v0",
        "GR01_ROBUSTNESS_RECORD_v0",
        "GR01_NEGATIVE_CONTROL_RECORD_v0",
        "GR01_RESOLUTION_TREND_RECORD_v0",
    ]
    missing = [tok for tok in required_tokens if tok not in text]
    assert not missing, "Missing required hardening-target token(s): " + ", ".join(missing)


def test_gr01_hardening_adjudication_is_in_sync_with_state_doc() -> None:
    target_text = _read(HARDENING_TARGET_PATH)
    state_text = _read(STATE_PATH)

    target_adj = _extract_hardening_adjudication(target_text, "hardening target doc")
    state_adj = _extract_hardening_adjudication(state_text, "State_of_the_Theory.md")

    assert target_adj == state_adj, (
        "GR01 hardening adjudication token drift between target doc and state doc: "
        f"target={target_adj}, state={state_adj}"
    )


def test_gr01_phase2_assumption_ledger_artifacts_are_pinned() -> None:
    lock_text = _read(ASSUMPTION_LEDGER_LOCK_PATH)
    lean_text = _read(ASSUMPTION_LEDGER_LEAN_PATH)

    required_lock_tokens = [
        "GR01_ASSUMPTION_LEDGER_v0",
        "GR01Assumptions_v0",
        "GR01Assumptions_v0_min1",
        "GR01Assumptions_v0_min2",
        "GR01Assumptions_v0_min3",
        "GR01_RECLASSIFICATION_v0_MIN1: hP_POLICY_TO_MATH_via_P_rep32_def",
        "GR01_RECLASSIFICATION_v0_MIN2: hHigherOrderTermsNegligible_POLICY_TO_MATH_via_FirstOrderRemainderSuppressed",
        "GR01_RECLASSIFICATION_v0_MIN3: hAction_POLICY_TO_MATH_via_default_binding_route",
        "MATH",
        "DEF",
        "POLICY",
        "SCOPE",
    ]
    missing_lock = [tok for tok in required_lock_tokens if tok not in lock_text]
    assert not missing_lock, "Missing required assumption-ledger lock token(s): " + ", ".join(missing_lock)

    required_lean_tokens = [
        "inductive GR01AssumptionClass_v0",
        "def gr01AssumptionClass_v0",
        "structure GR01Assumptions_v0",
        "structure GR01Assumptions_v0_min1",
        "structure GR01Assumptions_v0_min2",
        "structure GR01Assumptions_v0_min3",
        "gr01_end_to_end_poisson_equation_of_GR01Assumptions_v0",
        "gr01_end_to_end_poisson_equation_of_GR01Assumptions_v0_min1",
        "gr01_poisson_equation_of_GR01Assumptions_v0_min2",
        "gr01_poisson_equation_of_GR01Assumptions_v0_min3",
        "| .pRep32DefaultBinding => .MATH",
        "| .actionDefaultBinding => .MATH",
        "| .higherOrderTermsNegligible => .MATH",
        "| .firstOrderRemainderSuppressedDirect => .MATH",
    ]
    missing_lean = [tok for tok in required_lean_tokens if tok not in lean_text]
    assert not missing_lean, "Missing required assumption-ledger Lean token(s): " + ", ".join(missing_lean)


def test_gr01_phase3_robustness_and_negative_control_records_are_pinned() -> None:
    robustness_text = _read(ROBUSTNESS_RECORD_PATH)
    negative_text = _read(NEGATIVE_CONTROL_RECORD_PATH)

    required_robustness_tokens = [
        "GR01_ROBUSTNESS_RECORD_v0",
        "GR01_ROBUSTNESS_STATUS_v0: TEMPLATE_PINNED",
        "PERTURB_RHO_SMALL_v0",
        "PERTURB_PHI_SMALL_v0",
        "PERTURB_DISCRETIZATION_PARAMS_v0",
        "PERTURB_BOUNDARY_HANDLING_v0",
        "PERTURB_PROJECTION_CONDITIONS_v0",
        "OUTCOME_STILL_DERIVES_POISSON_RESIDUAL",
        "OUTCOME_FAILS_INFORMATIVE",
    ]
    missing_robustness = [tok for tok in required_robustness_tokens if tok not in robustness_text]
    assert not missing_robustness, (
        "Missing required robustness-record token(s): " + ", ".join(missing_robustness)
    )
    assert "GR01_ROBUSTNESS_PROGRESS_v0: ALL_REQUIRED_PERTURBATION_ROWS_POPULATED" in robustness_text, (
        "Robustness completion token missing after all required perturbation families are populated."
    )

    required_negative_tokens = [
        "GR01_NEGATIVE_CONTROL_RECORD_v0",
        "GR01_NEGATIVE_CONTROL_STATUS_v0: TEMPLATE_PINNED",
        "NEGCTRL_WRONG_KAPPA_SIGN_v0",
        "NEGCTRL_BROKEN_SCALING_HIERARCHY_v0",
        "NEGCTRL_BROKEN_WEAK_FIELD_BOUND_v0",
        "NEGCTRL_BROKEN_SYMMETRY_OBLIGATION_v0",
        "NEGCTRL_INCOMPATIBLE_CARRIERS_v0",
    ]
    missing_negative = [tok for tok in required_negative_tokens if tok not in negative_text]
    assert not missing_negative, (
        "Missing required negative-control record token(s): " + ", ".join(missing_negative)
    )
    assert "GR01_NEGATIVE_CONTROL_PROGRESS_v0: ROW_NEGCTRL_WRONG_KAPPA_SIGN_POPULATED" in negative_text, (
        "Negative-control progress token missing for populated wrong-kappa-sign row."
    )
    assert "GR01_NEGATIVE_CONTROL_PROGRESS_v0: ROW_NEGCTRL_BROKEN_SCALING_HIERARCHY_POPULATED" in negative_text, (
        "Negative-control progress token missing for populated broken-scaling row."
    )
    assert "GR01_NEGATIVE_CONTROL_PROGRESS_v0: ROW_NEGCTRL_BROKEN_WEAK_FIELD_BOUND_POPULATED" in negative_text, (
        "Negative-control progress token missing for populated broken-weak-field-bound row."
    )
    assert "GR01_NEGATIVE_CONTROL_PROGRESS_v0: ROW_NEGCTRL_BROKEN_SYMMETRY_OBLIGATION_POPULATED" in negative_text, (
        "Negative-control progress token missing for populated broken-symmetry-obligation row."
    )
    assert "GR01_NEGATIVE_CONTROL_PROGRESS_v0: ROW_NEGCTRL_INCOMPATIBLE_CARRIERS_POPULATED" in negative_text, (
        "Negative-control progress token missing for populated incompatible-carriers row."
    )
    assert "GR01_NEGATIVE_CONTROL_PROGRESS_v0: ALL_REQUIRED_NEGATIVE_ROWS_POPULATED" in negative_text, (
        "Negative-control completion token missing after all required negative rows are populated."
    )


def test_gr01_phase4_resolution_trend_record_is_pinned() -> None:
    trend_text = _read(RESOLUTION_TREND_RECORD_PATH)

    required_tokens = [
        "GR01_RESOLUTION_TREND_RECORD_v0",
        "GR01_RESOLUTION_TREND_STATUS_v0: TEMPLATE_PINNED",
        "RESOLUTION_32_v0",
        "RESOLUTION_64_v0",
        "RESOLUTION_128_v0",
        "residual_norm",
        "convergence_trend",
        "kappa_calibration_stability",
        "limit_break_annotation",
    ]
    missing = [tok for tok in required_tokens if tok not in trend_text]
    assert not missing, "Missing required resolution-trend token(s): " + ", ".join(missing)
    assert "GR01_RESOLUTION_TREND_PROGRESS_v0: ROW_RESOLUTION_32_POPULATED" in trend_text, (
        "Resolution-trend progress token missing for populated 32-grid row."
    )
    assert "GR01_RESOLUTION_TREND_PROGRESS_v0: ROW_RESOLUTION_64_POPULATED" in trend_text, (
        "Resolution-trend progress token missing for populated 64-grid row."
    )
    assert "GR01_RESOLUTION_TREND_PROGRESS_v0: ROW_RESOLUTION_128_POPULATED" in trend_text, (
        "Resolution-trend progress token missing for populated 128-grid row."
    )
    assert "GR01_RESOLUTION_TREND_PROGRESS_v0: ALL_REQUIRED_RESOLUTION_ROWS_POPULATED" in trend_text, (
        "Resolution-trend completion token missing after all required rows are populated."
    )


def test_gr01_phase5_pillar_package_is_frozen_and_complete() -> None:
    pkg_text = _read(PILLAR_PACKAGE_PATH)
    summary_text = _read(PILLAR_SUMMARY_PATH)
    chain_map_text = _read(CHAIN_MAP_PATH)

    required_pkg_tokens = [
        "GR01_PILLAR_PACKAGE_v0",
        "GR01_PILLAR_PACKAGE_STATUS_v0: FROZEN_CONTENTS_PINNED",
        "GR01_REOPEN_POLICY_v0: FROZEN_WATCH_REOPEN_ON_REGRESSION",
        "REOPEN_TRIGGER_CANONICAL_TOKEN_DRIFT_v0",
        "REOPEN_TRIGGER_ROBUSTNESS_NEGCTRL_REGRESSION_v0",
        "REOPEN_TRIGGER_RESOLUTION_TREND_BREAK_v0",
        "TOE_GR01_PILLAR_SUMMARY_v0.md",
        "GR01_ASSUMPTION_LEDGER_v0.md",
        "TOE_GR01_CANONICAL_CHAIN_MAP_v0.md",
        "GR01_ROBUSTNESS_RECORD_v0.md",
        "GR01_NEGATIVE_CONTROL_RECORD_v0.md",
        "GR01_RESOLUTION_TREND_RECORD_v0.md",
        "LIMIT_NO_CONTINUUM_GR_CLAIM_v0",
        "LIMIT_NO_BLACK_HOLE_CLAIM_v0",
        "LIMIT_NO_UNIQUENESS_INFINITE_DOMAIN_CLAIM_v0",
    ]
    missing_pkg = [tok for tok in required_pkg_tokens if tok not in pkg_text]
    assert not missing_pkg, "Missing required pillar-package token(s): " + ", ".join(missing_pkg)

    required_summary_tokens = [
        "TOE_GR01_PILLAR_SUMMARY_v0",
        "GR01_HARDENING_ADJUDICATION: DISCHARGED_v0_DISCRETE_HARDENED",
        "GR01_ROBUSTNESS_PROGRESS_v0: ALL_REQUIRED_PERTURBATION_ROWS_POPULATED",
        "GR01_NEGATIVE_CONTROL_PROGRESS_v0: ALL_REQUIRED_NEGATIVE_ROWS_POPULATED",
        "GR01_RESOLUTION_TREND_PROGRESS_v0: ALL_REQUIRED_RESOLUTION_ROWS_POPULATED",
        "Known limitations",
    ]
    missing_summary = [tok for tok in required_summary_tokens if tok not in summary_text]
    assert not missing_summary, "Missing required pillar-summary token(s): " + ", ".join(missing_summary)

    required_chain_tokens = [
        "TOE_GR01_CANONICAL_CHAIN_MAP_v0",
        "gr01_poisson_equation_of_GR01Assumptions_v0_min3",
        "gr01_discrete_residual_from_bridge_promotion_chain_default_binding",
        "ELImpliesOperatorResidualTransport",
        "gr01_el_implies_discrete_poisson_residual_from_operator_transport",
        "gr01_end_to_end_poisson_equation_under_promoted_assumptions",
        "ELImpliesProjectedResidual",
    ]
    missing_chain = [tok for tok in required_chain_tokens if tok not in chain_map_text]
    assert not missing_chain, "Missing required canonical-chain token(s): " + ", ".join(missing_chain)


def test_gr01_phase4_resolution_32_row_is_populated_and_artifact_pinned() -> None:
    trend_text = _read(RESOLUTION_TREND_RECORD_PATH)

    m = re.search(
        r"^\|\s*`RESOLUTION_32_v0`\s*\|\s*`32`\s*\|\s*`(.*?)`\s*\|\s*`(.*?)`\s*\|\s*`(.*?)`\s*\|\s*`(.*?)`\s*\|\s*`?(formal/output/gr01_resolution_trend_32_v0\.json)`?\s*\|\s*$",
        trend_text,
        flags=re.MULTILINE,
    )
    assert m is not None, "Missing or malformed populated row for RESOLUTION_32_v0 in resolution trend record."

    residual_norm, convergence_trend, kappa_stability, limit_break_annotation, artifact_rel = m.groups()
    for cell, label in [
        (residual_norm, "residual_norm"),
        (convergence_trend, "convergence_trend"),
        (kappa_stability, "kappa_calibration_stability"),
        (limit_break_annotation, "limit_break_annotation"),
    ]:
        assert "TBD" not in cell, f"RESOLUTION_32_v0 {label} must be populated (not TBD)."

    artifact_path = REPO_ROOT / artifact_rel
    assert artifact_path == RESOLUTION_32_ARTIFACT_PATH, "Resolution-32 artifact path drift detected."
    payload = json.loads(_read(artifact_path))

    assert payload.get("record_id") == "GR01_RESOLUTION_TREND_RECORD_v0"
    assert payload.get("resolution_id") == "RESOLUTION_32_v0"
    assert int(payload.get("grid_size")) == 32
    assert "residual_norm" in payload
    assert "convergence_trend" in payload
    assert "kappa_calibration_stability" in payload
    assert "limit_break_annotation" in payload


def test_gr01_phase4_resolution_64_row_is_populated_and_artifact_pinned() -> None:
    trend_text = _read(RESOLUTION_TREND_RECORD_PATH)

    m = re.search(
        r"^\|\s*`RESOLUTION_64_v0`\s*\|\s*`64`\s*\|\s*`(.*?)`\s*\|\s*`(.*?)`\s*\|\s*`(.*?)`\s*\|\s*`(.*?)`\s*\|\s*`?(formal/output/gr01_resolution_trend_64_v0\.json)`?\s*\|\s*$",
        trend_text,
        flags=re.MULTILINE,
    )
    assert m is not None, "Missing or malformed populated row for RESOLUTION_64_v0 in resolution trend record."

    residual_norm, convergence_trend, kappa_stability, limit_break_annotation, artifact_rel = m.groups()
    for cell, label in [
        (residual_norm, "residual_norm"),
        (convergence_trend, "convergence_trend"),
        (kappa_stability, "kappa_calibration_stability"),
        (limit_break_annotation, "limit_break_annotation"),
    ]:
        assert "TBD" not in cell, f"RESOLUTION_64_v0 {label} must be populated (not TBD)."

    artifact_path = REPO_ROOT / artifact_rel
    assert artifact_path == RESOLUTION_64_ARTIFACT_PATH, "Resolution-64 artifact path drift detected."
    payload = json.loads(_read(artifact_path))

    assert payload.get("record_id") == "GR01_RESOLUTION_TREND_RECORD_v0"
    assert payload.get("resolution_id") == "RESOLUTION_64_v0"
    assert int(payload.get("grid_size")) == 64
    assert "residual_norm" in payload
    assert "convergence_trend" in payload
    assert "kappa_calibration_stability" in payload
    assert "limit_break_annotation" in payload


def test_gr01_phase4_resolution_128_row_is_populated_and_artifact_pinned() -> None:
    trend_text = _read(RESOLUTION_TREND_RECORD_PATH)

    m = re.search(
        r"^\|\s*`RESOLUTION_128_v0`\s*\|\s*`128`\s*\|\s*`(.*?)`\s*\|\s*`(.*?)`\s*\|\s*`(.*?)`\s*\|\s*`(.*?)`\s*\|\s*`?(formal/output/gr01_resolution_trend_128_v0\.json)`?\s*\|\s*$",
        trend_text,
        flags=re.MULTILINE,
    )
    assert m is not None, "Missing or malformed populated row for RESOLUTION_128_v0 in resolution trend record."

    residual_norm, convergence_trend, kappa_stability, limit_break_annotation, artifact_rel = m.groups()
    for cell, label in [
        (residual_norm, "residual_norm"),
        (convergence_trend, "convergence_trend"),
        (kappa_stability, "kappa_calibration_stability"),
        (limit_break_annotation, "limit_break_annotation"),
    ]:
        assert "TBD" not in cell, f"RESOLUTION_128_v0 {label} must be populated (not TBD)."

    artifact_path = REPO_ROOT / artifact_rel
    assert artifact_path == RESOLUTION_128_ARTIFACT_PATH, "Resolution-128 artifact path drift detected."
    payload = json.loads(_read(artifact_path))

    assert payload.get("record_id") == "GR01_RESOLUTION_TREND_RECORD_v0"
    assert payload.get("resolution_id") == "RESOLUTION_128_v0"
    assert int(payload.get("grid_size")) == 128
    assert "residual_norm" in payload
    assert "convergence_trend" in payload
    assert "kappa_calibration_stability" in payload
    assert "limit_break_annotation" in payload


def test_gr01_phase3_rho_perturbation_row_is_populated_and_artifact_pinned() -> None:
    robustness_text = _read(ROBUSTNESS_RECORD_PATH)

    m = re.search(
        r"^\|\s*`PERTURB_RHO_SMALL_v0`\s*\|\s*(.*?)\s*\|\s*(.*?)\s*\|\s*(.*?)\s*\|\s*(.*?)\s*\|\s*`?(formal/output/gr01_robustness_perturb_rho_small_v0\.json)`?\s*\|\s*$",
        robustness_text,
        flags=re.MULTILINE,
    )
    assert m is not None, "Missing or malformed populated row for PERTURB_RHO_SMALL_v0 in robustness record."

    input_delta, expected_outcome, observed_outcome, reason_code, artifact_rel = m.groups()
    for cell, label in [
        (input_delta, "input delta"),
        (expected_outcome, "expected outcome"),
        (observed_outcome, "observed outcome"),
        (reason_code, "reason code"),
    ]:
        assert "TBD" not in cell, f"PERTURB_RHO_SMALL_v0 {label} must be populated (not TBD)."

    assert expected_outcome == "`OUTCOME_STILL_DERIVES_POISSON_RESIDUAL`", (
        "PERTURB_RHO_SMALL_v0 expected outcome must be OUTCOME_STILL_DERIVES_POISSON_RESIDUAL."
    )
    assert observed_outcome == "`OUTCOME_STILL_DERIVES_POISSON_RESIDUAL`", (
        "PERTURB_RHO_SMALL_v0 observed outcome must be OUTCOME_STILL_DERIVES_POISSON_RESIDUAL."
    )

    artifact_path = REPO_ROOT / artifact_rel
    assert artifact_path == ROBUSTNESS_RHO_ARTIFACT_PATH, "Rho robustness artifact path drift detected."
    artifact_text = _read(artifact_path)
    payload = json.loads(artifact_text)

    assert payload.get("record_id") == "GR01_ROBUSTNESS_RECORD_v0"
    assert payload.get("perturbation_id") == "PERTURB_RHO_SMALL_v0"
    assert payload.get("expected_outcome") == "OUTCOME_STILL_DERIVES_POISSON_RESIDUAL"
    assert payload.get("observed_outcome") == "OUTCOME_STILL_DERIVES_POISSON_RESIDUAL"
    assert isinstance(payload.get("reason_code"), str) and payload.get("reason_code"), (
        "Rho robustness artifact must include non-empty reason_code."
    )


def test_gr01_phase3_phi_perturbation_row_is_populated_and_artifact_pinned() -> None:
    robustness_text = _read(ROBUSTNESS_RECORD_PATH)

    m = re.search(
        r"^\|\s*`PERTURB_PHI_SMALL_v0`\s*\|\s*(.*?)\s*\|\s*(.*?)\s*\|\s*(.*?)\s*\|\s*(.*?)\s*\|\s*`?(formal/output/gr01_robustness_perturb_phi_small_v0\.json)`?\s*\|\s*$",
        robustness_text,
        flags=re.MULTILINE,
    )
    assert m is not None, "Missing or malformed populated row for PERTURB_PHI_SMALL_v0 in robustness record."

    input_delta, expected_outcome, observed_outcome, reason_code, artifact_rel = m.groups()
    for cell, label in [
        (input_delta, "input delta"),
        (expected_outcome, "expected outcome"),
        (observed_outcome, "observed outcome"),
        (reason_code, "reason code"),
    ]:
        assert "TBD" not in cell, f"PERTURB_PHI_SMALL_v0 {label} must be populated (not TBD)."

    assert expected_outcome == "`OUTCOME_STILL_DERIVES_POISSON_RESIDUAL`", (
        "PERTURB_PHI_SMALL_v0 expected outcome must be OUTCOME_STILL_DERIVES_POISSON_RESIDUAL."
    )
    assert observed_outcome == "`OUTCOME_STILL_DERIVES_POISSON_RESIDUAL`", (
        "PERTURB_PHI_SMALL_v0 observed outcome must be OUTCOME_STILL_DERIVES_POISSON_RESIDUAL."
    )

    artifact_path = REPO_ROOT / artifact_rel
    assert artifact_path == ROBUSTNESS_PHI_ARTIFACT_PATH, "Phi robustness artifact path drift detected."
    artifact_text = _read(artifact_path)
    payload = json.loads(artifact_text)

    assert payload.get("record_id") == "GR01_ROBUSTNESS_RECORD_v0"
    assert payload.get("perturbation_id") == "PERTURB_PHI_SMALL_v0"
    assert payload.get("expected_outcome") == "OUTCOME_STILL_DERIVES_POISSON_RESIDUAL"
    assert payload.get("observed_outcome") == "OUTCOME_STILL_DERIVES_POISSON_RESIDUAL"
    assert isinstance(payload.get("reason_code"), str) and payload.get("reason_code"), (
        "Phi robustness artifact must include non-empty reason_code."
    )


def test_gr01_phase3_discretization_perturbation_row_is_populated_and_artifact_pinned() -> None:
    robustness_text = _read(ROBUSTNESS_RECORD_PATH)

    m = re.search(
        r"^\|\s*`PERTURB_DISCRETIZATION_PARAMS_v0`\s*\|\s*(.*?)\s*\|\s*(.*?)\s*\|\s*(.*?)\s*\|\s*(.*?)\s*\|\s*`?(formal/output/gr01_robustness_perturb_discretization_params_v0\.json)`?\s*\|\s*$",
        robustness_text,
        flags=re.MULTILINE,
    )
    assert m is not None, (
        "Missing or malformed populated row for PERTURB_DISCRETIZATION_PARAMS_v0 in robustness record."
    )

    input_delta, expected_outcome, observed_outcome, reason_code, artifact_rel = m.groups()
    for cell, label in [
        (input_delta, "input delta"),
        (expected_outcome, "expected outcome"),
        (observed_outcome, "observed outcome"),
        (reason_code, "reason code"),
    ]:
        assert "TBD" not in cell, (
            f"PERTURB_DISCRETIZATION_PARAMS_v0 {label} must be populated (not TBD)."
        )

    assert expected_outcome == "`OUTCOME_STILL_DERIVES_POISSON_RESIDUAL`", (
        "PERTURB_DISCRETIZATION_PARAMS_v0 expected outcome must be OUTCOME_STILL_DERIVES_POISSON_RESIDUAL."
    )
    assert observed_outcome == "`OUTCOME_STILL_DERIVES_POISSON_RESIDUAL`", (
        "PERTURB_DISCRETIZATION_PARAMS_v0 observed outcome must be OUTCOME_STILL_DERIVES_POISSON_RESIDUAL."
    )

    artifact_path = REPO_ROOT / artifact_rel
    assert artifact_path == ROBUSTNESS_DISCRETIZATION_ARTIFACT_PATH, (
        "Discretization robustness artifact path drift detected."
    )
    artifact_text = _read(artifact_path)
    payload = json.loads(artifact_text)

    assert payload.get("record_id") == "GR01_ROBUSTNESS_RECORD_v0"
    assert payload.get("perturbation_id") == "PERTURB_DISCRETIZATION_PARAMS_v0"
    assert payload.get("expected_outcome") == "OUTCOME_STILL_DERIVES_POISSON_RESIDUAL"
    assert payload.get("observed_outcome") == "OUTCOME_STILL_DERIVES_POISSON_RESIDUAL"
    assert isinstance(payload.get("reason_code"), str) and payload.get("reason_code"), (
        "Discretization robustness artifact must include non-empty reason_code."
    )


def test_gr01_phase3_boundary_perturbation_row_is_populated_and_artifact_pinned() -> None:
    robustness_text = _read(ROBUSTNESS_RECORD_PATH)

    m = re.search(
        r"^\|\s*`PERTURB_BOUNDARY_HANDLING_v0`\s*\|\s*(.*?)\s*\|\s*(.*?)\s*\|\s*(.*?)\s*\|\s*(.*?)\s*\|\s*`?(formal/output/gr01_robustness_perturb_boundary_handling_v0\.json)`?\s*\|\s*$",
        robustness_text,
        flags=re.MULTILINE,
    )
    assert m is not None, (
        "Missing or malformed populated row for PERTURB_BOUNDARY_HANDLING_v0 in robustness record."
    )

    input_delta, expected_outcome, observed_outcome, reason_code, artifact_rel = m.groups()
    for cell, label in [
        (input_delta, "input delta"),
        (expected_outcome, "expected outcome"),
        (observed_outcome, "observed outcome"),
        (reason_code, "reason code"),
    ]:
        assert "TBD" not in cell, (
            f"PERTURB_BOUNDARY_HANDLING_v0 {label} must be populated (not TBD)."
        )

    assert expected_outcome == "`OUTCOME_STILL_DERIVES_POISSON_RESIDUAL`", (
        "PERTURB_BOUNDARY_HANDLING_v0 expected outcome must be OUTCOME_STILL_DERIVES_POISSON_RESIDUAL."
    )
    assert observed_outcome == "`OUTCOME_STILL_DERIVES_POISSON_RESIDUAL`", (
        "PERTURB_BOUNDARY_HANDLING_v0 observed outcome must be OUTCOME_STILL_DERIVES_POISSON_RESIDUAL."
    )

    artifact_path = REPO_ROOT / artifact_rel
    assert artifact_path == ROBUSTNESS_BOUNDARY_ARTIFACT_PATH, (
        "Boundary robustness artifact path drift detected."
    )
    artifact_text = _read(artifact_path)
    payload = json.loads(artifact_text)

    assert payload.get("record_id") == "GR01_ROBUSTNESS_RECORD_v0"
    assert payload.get("perturbation_id") == "PERTURB_BOUNDARY_HANDLING_v0"
    assert payload.get("expected_outcome") == "OUTCOME_STILL_DERIVES_POISSON_RESIDUAL"
    assert payload.get("observed_outcome") == "OUTCOME_STILL_DERIVES_POISSON_RESIDUAL"
    assert isinstance(payload.get("reason_code"), str) and payload.get("reason_code"), (
        "Boundary robustness artifact must include non-empty reason_code."
    )


def test_gr01_phase3_projection_perturbation_row_is_populated_and_artifact_pinned() -> None:
    robustness_text = _read(ROBUSTNESS_RECORD_PATH)

    m = re.search(
        r"^\|\s*`PERTURB_PROJECTION_CONDITIONS_v0`\s*\|\s*(.*?)\s*\|\s*(.*?)\s*\|\s*(.*?)\s*\|\s*(.*?)\s*\|\s*`?(formal/output/gr01_robustness_perturb_projection_conditions_v0\.json)`?\s*\|\s*$",
        robustness_text,
        flags=re.MULTILINE,
    )
    assert m is not None, (
        "Missing or malformed populated row for PERTURB_PROJECTION_CONDITIONS_v0 in robustness record."
    )

    input_delta, expected_outcome, observed_outcome, reason_code, artifact_rel = m.groups()
    for cell, label in [
        (input_delta, "input delta"),
        (expected_outcome, "expected outcome"),
        (observed_outcome, "observed outcome"),
        (reason_code, "reason code"),
    ]:
        assert "TBD" not in cell, (
            f"PERTURB_PROJECTION_CONDITIONS_v0 {label} must be populated (not TBD)."
        )

    assert expected_outcome == "`OUTCOME_STILL_DERIVES_POISSON_RESIDUAL`", (
        "PERTURB_PROJECTION_CONDITIONS_v0 expected outcome must be OUTCOME_STILL_DERIVES_POISSON_RESIDUAL."
    )
    assert observed_outcome == "`OUTCOME_STILL_DERIVES_POISSON_RESIDUAL`", (
        "PERTURB_PROJECTION_CONDITIONS_v0 observed outcome must be OUTCOME_STILL_DERIVES_POISSON_RESIDUAL."
    )

    artifact_path = REPO_ROOT / artifact_rel
    assert artifact_path == ROBUSTNESS_PROJECTION_ARTIFACT_PATH, (
        "Projection-condition robustness artifact path drift detected."
    )
    artifact_text = _read(artifact_path)
    payload = json.loads(artifact_text)

    assert payload.get("record_id") == "GR01_ROBUSTNESS_RECORD_v0"
    assert payload.get("perturbation_id") == "PERTURB_PROJECTION_CONDITIONS_v0"
    assert payload.get("expected_outcome") == "OUTCOME_STILL_DERIVES_POISSON_RESIDUAL"
    assert payload.get("observed_outcome") == "OUTCOME_STILL_DERIVES_POISSON_RESIDUAL"
    assert isinstance(payload.get("reason_code"), str) and payload.get("reason_code"), (
        "Projection-condition robustness artifact must include non-empty reason_code."
    )


def test_gr01_phase3_wrong_kappa_negative_row_is_populated_and_artifact_pinned() -> None:
    negative_text = _read(NEGATIVE_CONTROL_RECORD_PATH)

    m = re.search(
        r"^\|\s*`NEGCTRL_WRONG_KAPPA_SIGN_v0`\s*\|\s*(.*?)\s*\|\s*(.*?)\s*\|\s*(.*?)\s*\|\s*(.*?)\s*\|\s*`?(formal/output/gr01_negative_control_wrong_kappa_sign_v0\.json)`?\s*\|\s*$",
        negative_text,
        flags=re.MULTILINE,
    )
    assert m is not None, (
        "Missing or malformed populated row for NEGCTRL_WRONG_KAPPA_SIGN_v0 in negative-control record."
    )

    injected_violation, expected_failure, observed_failure, reason_code, artifact_rel = m.groups()
    for cell, label in [
        (injected_violation, "injected violation"),
        (expected_failure, "expected failure token"),
        (observed_failure, "observed failure token"),
        (reason_code, "reason code"),
    ]:
        assert "TBD" not in cell, (
            f"NEGCTRL_WRONG_KAPPA_SIGN_v0 {label} must be populated (not TBD)."
        )

    assert expected_failure == "`ELImpliesOperatorResidualUnderBound`", (
        "NEGCTRL_WRONG_KAPPA_SIGN_v0 expected failure token must be ELImpliesOperatorResidualUnderBound."
    )
    assert observed_failure == "`ELImpliesOperatorResidualUnderBound`", (
        "NEGCTRL_WRONG_KAPPA_SIGN_v0 observed failure token must be ELImpliesOperatorResidualUnderBound."
    )

    artifact_path = REPO_ROOT / artifact_rel
    assert artifact_path == NEGCTRL_WRONG_KAPPA_ARTIFACT_PATH, (
        "Wrong-kappa negative-control artifact path drift detected."
    )
    artifact_text = _read(artifact_path)
    payload = json.loads(artifact_text)

    assert payload.get("record_id") == "GR01_NEGATIVE_CONTROL_RECORD_v0"
    assert payload.get("negative_id") == "NEGCTRL_WRONG_KAPPA_SIGN_v0"
    assert payload.get("expected_outcome") == "OUTCOME_FAILS_INFORMATIVE"
    assert payload.get("observed_outcome") == "OUTCOME_FAILS_INFORMATIVE"
    assert payload.get("expected_failure_token") == "ELImpliesOperatorResidualUnderBound"
    assert payload.get("observed_failure_token") == "ELImpliesOperatorResidualUnderBound"
    assert isinstance(payload.get("reason_code"), str) and payload.get("reason_code"), (
        "Wrong-kappa negative-control artifact must include non-empty reason_code."
    )


def test_gr01_phase3_broken_scaling_negative_row_is_populated_and_artifact_pinned() -> None:
    negative_text = _read(NEGATIVE_CONTROL_RECORD_PATH)

    m = re.search(
        r"^\|\s*`NEGCTRL_BROKEN_SCALING_HIERARCHY_v0`\s*\|\s*(.*?)\s*\|\s*(.*?)\s*\|\s*(.*?)\s*\|\s*(.*?)\s*\|\s*`?(formal/output/gr01_negative_control_broken_scaling_hierarchy_v0\.json)`?\s*\|\s*$",
        negative_text,
        flags=re.MULTILINE,
    )
    assert m is not None, (
        "Missing or malformed populated row for NEGCTRL_BROKEN_SCALING_HIERARCHY_v0 in negative-control record."
    )

    injected_violation, expected_failure, observed_failure, reason_code, artifact_rel = m.groups()
    for cell, label in [
        (injected_violation, "injected violation"),
        (expected_failure, "expected failure token"),
        (observed_failure, "observed failure token"),
        (reason_code, "reason code"),
    ]:
        assert "TBD" not in cell, (
            f"NEGCTRL_BROKEN_SCALING_HIERARCHY_v0 {label} must be populated (not TBD)."
        )

    assert expected_failure == "`WeakFieldScalingHierarchy`", (
        "NEGCTRL_BROKEN_SCALING_HIERARCHY_v0 expected failure token must be WeakFieldScalingHierarchy."
    )
    assert observed_failure == "`WeakFieldScalingHierarchy`", (
        "NEGCTRL_BROKEN_SCALING_HIERARCHY_v0 observed failure token must be WeakFieldScalingHierarchy."
    )

    artifact_path = REPO_ROOT / artifact_rel
    assert artifact_path == NEGCTRL_BROKEN_SCALING_ARTIFACT_PATH, (
        "Broken-scaling negative-control artifact path drift detected."
    )
    artifact_text = _read(artifact_path)
    payload = json.loads(artifact_text)

    assert payload.get("record_id") == "GR01_NEGATIVE_CONTROL_RECORD_v0"
    assert payload.get("negative_id") == "NEGCTRL_BROKEN_SCALING_HIERARCHY_v0"
    assert payload.get("expected_outcome") == "OUTCOME_FAILS_INFORMATIVE"
    assert payload.get("observed_outcome") == "OUTCOME_FAILS_INFORMATIVE"
    assert payload.get("expected_failure_token") == "WeakFieldScalingHierarchy"
    assert payload.get("observed_failure_token") == "WeakFieldScalingHierarchy"
    assert isinstance(payload.get("reason_code"), str) and payload.get("reason_code"), (
        "Broken-scaling negative-control artifact must include non-empty reason_code."
    )


def test_gr01_phase3_broken_weak_field_bound_negative_row_is_populated_and_artifact_pinned() -> None:
    negative_text = _read(NEGATIVE_CONTROL_RECORD_PATH)

    m = re.search(
        r"^\|\s*`NEGCTRL_BROKEN_WEAK_FIELD_BOUND_v0`\s*\|\s*(.*?)\s*\|\s*(.*?)\s*\|\s*(.*?)\s*\|\s*(.*?)\s*\|\s*`?(formal/output/gr01_negative_control_broken_weak_field_bound_v0\.json)`?\s*\|\s*$",
        negative_text,
        flags=re.MULTILINE,
    )
    assert m is not None, (
        "Missing or malformed populated row for NEGCTRL_BROKEN_WEAK_FIELD_BOUND_v0 in negative-control record."
    )

    injected_violation, expected_failure, observed_failure, reason_code, artifact_rel = m.groups()
    for cell, label in [
        (injected_violation, "injected violation"),
        (expected_failure, "expected failure token"),
        (observed_failure, "observed failure token"),
        (reason_code, "reason code"),
    ]:
        assert "TBD" not in cell, (
            f"NEGCTRL_BROKEN_WEAK_FIELD_BOUND_v0 {label} must be populated (not TBD)."
        )

    assert expected_failure == "`WeakFieldUniformBound`", (
        "NEGCTRL_BROKEN_WEAK_FIELD_BOUND_v0 expected failure token must be WeakFieldUniformBound."
    )
    assert observed_failure == "`WeakFieldUniformBound`", (
        "NEGCTRL_BROKEN_WEAK_FIELD_BOUND_v0 observed failure token must be WeakFieldUniformBound."
    )

    artifact_path = REPO_ROOT / artifact_rel
    assert artifact_path == NEGCTRL_BROKEN_WEAK_FIELD_BOUND_ARTIFACT_PATH, (
        "Broken-weak-field-bound negative-control artifact path drift detected."
    )
    artifact_text = _read(artifact_path)
    payload = json.loads(artifact_text)

    assert payload.get("record_id") == "GR01_NEGATIVE_CONTROL_RECORD_v0"
    assert payload.get("negative_id") == "NEGCTRL_BROKEN_WEAK_FIELD_BOUND_v0"
    assert payload.get("expected_outcome") == "OUTCOME_FAILS_INFORMATIVE"
    assert payload.get("observed_outcome") == "OUTCOME_FAILS_INFORMATIVE"
    assert payload.get("expected_failure_token") == "WeakFieldUniformBound"
    assert payload.get("observed_failure_token") == "WeakFieldUniformBound"
    assert isinstance(payload.get("reason_code"), str) and payload.get("reason_code"), (
        "Broken-weak-field-bound negative-control artifact must include non-empty reason_code."
    )


def test_gr01_phase3_broken_symmetry_negative_row_is_populated_and_artifact_pinned() -> None:
    negative_text = _read(NEGATIVE_CONTROL_RECORD_PATH)

    m = re.search(
        r"^\|\s*`NEGCTRL_BROKEN_SYMMETRY_OBLIGATION_v0`\s*\|\s*(.*?)\s*\|\s*(.*?)\s*\|\s*(.*?)\s*\|\s*(.*?)\s*\|\s*`?(formal/output/gr01_negative_control_broken_symmetry_obligation_v0\.json)`?\s*\|\s*$",
        negative_text,
        flags=re.MULTILINE,
    )
    assert m is not None, (
        "Missing or malformed populated row for NEGCTRL_BROKEN_SYMMETRY_OBLIGATION_v0 in negative-control record."
    )

    injected_violation, expected_failure, observed_failure, reason_code, artifact_rel = m.groups()
    for cell, label in [
        (injected_violation, "injected violation"),
        (expected_failure, "expected failure token"),
        (observed_failure, "observed failure token"),
        (reason_code, "reason code"),
    ]:
        assert "TBD" not in cell, (
            f"NEGCTRL_BROKEN_SYMMETRY_OBLIGATION_v0 {label} must be populated (not TBD)."
        )

    assert expected_failure == "`ProjectionMapWellFormed`", (
        "NEGCTRL_BROKEN_SYMMETRY_OBLIGATION_v0 expected failure token must be ProjectionMapWellFormed."
    )
    assert observed_failure == "`ProjectionMapWellFormed`", (
        "NEGCTRL_BROKEN_SYMMETRY_OBLIGATION_v0 observed failure token must be ProjectionMapWellFormed."
    )

    artifact_path = REPO_ROOT / artifact_rel
    assert artifact_path == NEGCTRL_BROKEN_SYMMETRY_ARTIFACT_PATH, (
        "Broken-symmetry negative-control artifact path drift detected."
    )
    artifact_text = _read(artifact_path)
    payload = json.loads(artifact_text)

    assert payload.get("record_id") == "GR01_NEGATIVE_CONTROL_RECORD_v0"
    assert payload.get("negative_id") == "NEGCTRL_BROKEN_SYMMETRY_OBLIGATION_v0"
    assert payload.get("expected_outcome") == "OUTCOME_FAILS_INFORMATIVE"
    assert payload.get("observed_outcome") == "OUTCOME_FAILS_INFORMATIVE"
    assert payload.get("expected_failure_token") == "ProjectionMapWellFormed"
    assert payload.get("observed_failure_token") == "ProjectionMapWellFormed"
    assert isinstance(payload.get("reason_code"), str) and payload.get("reason_code"), (
        "Broken-symmetry negative-control artifact must include non-empty reason_code."
    )


def test_gr01_phase3_incompatible_carriers_negative_row_is_populated_and_artifact_pinned() -> None:
    negative_text = _read(NEGATIVE_CONTROL_RECORD_PATH)

    m = re.search(
        r"^\|\s*`NEGCTRL_INCOMPATIBLE_CARRIERS_v0`\s*\|\s*(.*?)\s*\|\s*(.*?)\s*\|\s*(.*?)\s*\|\s*(.*?)\s*\|\s*`?(formal/output/gr01_negative_control_incompatible_carriers_v0\.json)`?\s*\|\s*$",
        negative_text,
        flags=re.MULTILINE,
    )
    assert m is not None, (
        "Missing or malformed populated row for NEGCTRL_INCOMPATIBLE_CARRIERS_v0 in negative-control record."
    )

    injected_violation, expected_failure, observed_failure, reason_code, artifact_rel = m.groups()
    for cell, label in [
        (injected_violation, "injected violation"),
        (expected_failure, "expected failure token"),
        (observed_failure, "observed failure token"),
        (reason_code, "reason code"),
    ]:
        assert "TBD" not in cell, (
            f"NEGCTRL_INCOMPATIBLE_CARRIERS_v0 {label} must be populated (not TBD)."
        )

    assert expected_failure == "`ProjectionCarrierWitness`", (
        "NEGCTRL_INCOMPATIBLE_CARRIERS_v0 expected failure token must be ProjectionCarrierWitness."
    )
    assert observed_failure == "`ProjectionCarrierWitness`", (
        "NEGCTRL_INCOMPATIBLE_CARRIERS_v0 observed failure token must be ProjectionCarrierWitness."
    )

    artifact_path = REPO_ROOT / artifact_rel
    assert artifact_path == NEGCTRL_INCOMPATIBLE_CARRIERS_ARTIFACT_PATH, (
        "Incompatible-carriers negative-control artifact path drift detected."
    )
    artifact_text = _read(artifact_path)
    payload = json.loads(artifact_text)

    assert payload.get("record_id") == "GR01_NEGATIVE_CONTROL_RECORD_v0"
    assert payload.get("negative_id") == "NEGCTRL_INCOMPATIBLE_CARRIERS_v0"
    assert payload.get("expected_outcome") == "OUTCOME_FAILS_INFORMATIVE"
    assert payload.get("observed_outcome") == "OUTCOME_FAILS_INFORMATIVE"
    assert payload.get("expected_failure_token") == "ProjectionCarrierWitness"
    assert payload.get("observed_failure_token") == "ProjectionCarrierWitness"
    assert isinstance(payload.get("reason_code"), str) and payload.get("reason_code"), (
        "Incompatible-carriers negative-control artifact must include non-empty reason_code."
    )


def test_gr01_canonical_surfaces_forbid_legacy_projected_bridge_token() -> None:
    forbidden = "ELImpliesProjectedResidual"
    offenders: list[str] = []
    for path in CANONICAL_GR01_FILES:
        text = _read(path)
        if forbidden in text:
            offenders.append(str(path))
    assert not offenders, (
        "Forbidden legacy bridge token appears in canonical GR01 surface: "
        + ", ".join(offenders)
    )


def test_gr01_hardening_discharge_requires_non_placeholder_obligation_structures() -> None:
    target_text = _read(HARDENING_TARGET_PATH)
    adjudication = _extract_hardening_adjudication(target_text, "hardening target doc")

    if adjudication != "DISCHARGED_v0_DISCRETE_HARDENED":
        return

    weak_field_text = _read(WEAK_FIELD_FILE)
    structures_in_scope = [
        "ProjectionMapWellFormed",
        "WeakFieldTruncationSound",
    ]

    for structure_name in structures_in_scope:
        block = _extract_structure_block(weak_field_text, structure_name)
        assert ": True" not in block, (
            f"Hardening adjudication cannot be DISCHARGED while {structure_name} still has placeholder True fields."
        )


def test_gr01_hardening_discharge_requires_ledgers_and_records() -> None:
    target_text = _read(HARDENING_TARGET_PATH)
    adjudication = _extract_hardening_adjudication(target_text, "hardening target doc")

    if adjudication != "DISCHARGED_v0_DISCRETE_HARDENED":
        return

    required_paths = [
        REPO_ROOT / "formal" / "markdown" / "locks" / "policy" / "GR01_ROBUSTNESS_RECORD_v0.md",
        REPO_ROOT / "formal" / "markdown" / "locks" / "policy" / "GR01_NEGATIVE_CONTROL_RECORD_v0.md",
        ASSUMPTION_LEDGER_LOCK_PATH,
    ]

    missing = [str(path) for path in required_paths if not path.exists()]
    assert not missing, (
        "Hardening adjudication cannot be DISCHARGED without required hardening record artifacts: "
        + ", ".join(missing)
    )

    ledger_text = _read(required_paths[2])
    required_classes = ["MATH", "DEF", "POLICY", "SCOPE"]
    missing_classes = [cls for cls in required_classes if cls not in ledger_text]
    assert not missing_classes, (
        "Assumption ledger must include hardening class taxonomy labels: "
        + ", ".join(missing_classes)
    )


def test_gr01_phase4_resolution_trend_quality_is_monotonic_nonincreasing() -> None:
    payload_32 = json.loads(_read(RESOLUTION_32_ARTIFACT_PATH))
    payload_64 = json.loads(_read(RESOLUTION_64_ARTIFACT_PATH))
    payload_128 = json.loads(_read(RESOLUTION_128_ARTIFACT_PATH))

    residual_32 = float(payload_32["residual_norm"])
    residual_64 = float(payload_64["residual_norm"])
    residual_128 = float(payload_128["residual_norm"])

    assert residual_64 <= residual_32, (
        "Resolution trend quality regression: residual_norm at 64 must be <= 32. "
        f"Observed 32={residual_32}, 64={residual_64}."
    )
    assert residual_128 <= residual_64, (
        "Resolution trend quality regression: residual_norm at 128 must be <= 64. "
        f"Observed 64={residual_64}, 128={residual_128}."
    )

    assert payload_64.get("convergence_trend") == "improving_vs_32_v0", (
        "Resolution-64 convergence label drift: expected improving_vs_32_v0."
    )
    assert payload_128.get("convergence_trend") == "improving_vs_64_v0", (
        "Resolution-128 convergence label drift: expected improving_vs_64_v0."
    )


def test_gr01_phase3_and_phase4_artifact_schema_is_consistent() -> None:
    for artifact_path in ROBUSTNESS_ARTIFACT_PATHS + NEGATIVE_CONTROL_ARTIFACT_PATHS + [
        RESOLUTION_32_ARTIFACT_PATH,
        RESOLUTION_64_ARTIFACT_PATH,
        RESOLUTION_128_ARTIFACT_PATH,
    ]:
        payload = json.loads(_read(artifact_path))
        assert isinstance(payload.get("artifact_id"), str) and payload.get("artifact_id"), (
            f"Artifact schema drift in {artifact_path.name}: non-empty artifact_id is required."
        )
        assert payload.get("scope") == "bounded_discrete_weak_field_v0", (
            f"Artifact schema drift in {artifact_path.name}: scope must remain bounded_discrete_weak_field_v0."
        )
        assert isinstance(payload.get("witness_tokens"), list) and payload.get("witness_tokens"), (
            f"Artifact schema drift in {artifact_path.name}: witness_tokens must be a non-empty list."
        )
        determinism = payload.get("determinism")
        assert isinstance(determinism, dict), (
            f"Artifact schema drift in {artifact_path.name}: determinism block is required."
        )
        assert determinism.get("schema_version") == "v0", (
            f"Artifact schema drift in {artifact_path.name}: determinism.schema_version must remain v0."
        )
        assert determinism.get("fingerprint_method") == "literal-json-lock", (
            f"Artifact schema drift in {artifact_path.name}: determinism.fingerprint_method must remain literal-json-lock."
        )


def test_gr01_next_pillar_focus_is_explicit_and_points_to_sr() -> None:
    state_text = _read(STATE_PATH)
    focus_value = _extract_state_token(state_text, "NEXT_PILLAR_FOCUS_v0")
    lane_value = _extract_state_token(state_text, "NEXT_PILLAR_PRIMARY_LANE_v0")

    assert focus_value == "PILLAR-SR", (
        "Next pillar focus drift: NEXT_PILLAR_FOCUS_v0 must remain PILLAR-SR."
    )
    assert lane_value == "TARGET-SR-COV-PLAN", (
        "Next pillar lane drift: NEXT_PILLAR_PRIMARY_LANE_v0 must remain TARGET-SR-COV-PLAN."
    )

    sr_target_text = _read(
        REPO_ROOT / "formal" / "docs" / "paper" / "DERIVATION_TARGET_SR_COVARIANCE_OBJECT_v0.md"
    )
    required_sr_tokens = [
        "DERIVATION_TARGET_SR_COVARIANCE_OBJECT_v0",
        "TARGET-SR-COV-PLAN",
        "covariance/kinematics closure posture",
    ]
    missing = [tok for tok in required_sr_tokens if tok not in sr_target_text]
    assert not missing, "SR covariance target token drift: " + ", ".join(missing)

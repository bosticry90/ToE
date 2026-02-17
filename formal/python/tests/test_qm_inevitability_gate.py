from __future__ import annotations

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
RESULTS_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "RESULTS_TABLE_v0.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
TARGET_GATE_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_QM_INEVITABILITY_GATE_v0.md"
)
TARGET_FULL_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_QM_FULL_DERIVATION_DISCHARGE_v0.md"
)
LEAN_PATH = REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "QM" / "QMFullDerivationScaffold.lean"


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _extract_status(text: str, label: str) -> str:
    m = re.search(
        r"QM_FULL_DERIVATION_INEVITABILITY_ADJUDICATION:\s*"
        r"(NOT_YET_DISCHARGED_v0|DISCHARGED_v0_BOUNDED)",
        text,
    )
    assert m is not None, f"Missing QM inevitability adjudication token in {label}."
    return m.group(1)


def _assert_tokens_in_order(text: str, tokens: list[str], label: str) -> None:
    cursor = -1
    for token in tokens:
        idx = text.find(token, cursor + 1)
        assert idx != -1, f"Missing required token in {label}: {token}"
        assert idx > cursor, f"Token-order drift in {label}: {token}"
        cursor = idx


def _theorem_block(text: str, theorem_name: str) -> str:
    start_token = f"theorem {theorem_name}"
    start_idx = text.find(start_token)
    assert start_idx != -1, f"Missing theorem token in Lean file: {start_token}"

    next_markers = [
        text.find("\n\ntheorem ", start_idx + len(start_token)),
        text.find("\n\ndef ", start_idx + len(start_token)),
        text.find("\n\nstructure ", start_idx + len(start_token)),
        text.find("\nend", start_idx + len(start_token)),
    ]
    next_markers = [idx for idx in next_markers if idx != -1]
    end_idx = min(next_markers) if next_markers else len(text)
    return text[start_idx:end_idx]


def test_qm_inevitability_gate_doc_is_pinned() -> None:
    text = _read(TARGET_GATE_PATH)
    required = [
        "DERIVATION_TARGET_QM_INEVITABILITY_GATE_v0",
        "TARGET-QM-INEVITABILITY-GATE-PLAN",
        "QM_FULL_DERIVATION_INEVITABILITY_ADJUDICATION:",
        "qm_inevitability_necessity_under_minimized_assumptions_v0",
        "qm_inevitability_counterfactual_breaks_without_required_assumption_v0",
        "qm_inevitability_structural_classification_of_constructive_route_v0",
        "qm_inevitability_discharge_ready_bundle_v0",
        "qm_inevitability_route_bundle_without_shortcuts_v0",
        "QMInevitabilityMinimizedAssumptions_v0",
        "QMInevitabilityCanonicalConstructiveRoute_v0",
        "QMInevitabilityUnitaryConsistencyRoute_v0",
        "QMInevitabilityNoDirectSchrodingerInsertionRoute_v0",
        "QMNoDirectInsertionEliminationLemmaChain_v0",
        "QMDirectSchrodingerInsertionRouteUsed_v0",
        "QMContractBridgeCompatibilityWrapperRouteUsed_v0",
        "QMInevitabilityClosureSurface_v0",
        "(hMin : QMInevitabilityMinimizedAssumptions_v0 h)",
        "¬QMInevitabilityClosureSurface_v0",
        "qm_inevitability_counterfactual_breaks_without_canonical_constructive_route_assumption_v0",
        "qm_inevitability_counterfactual_breaks_without_unitary_consistency_assumption_v0",
        "qm_inevitability_counterfactual_breaks_without_no_direct_schrodinger_insertion_assumption_v0",
        "QMInevitabilityConstructiveRouteClassification_v0",
        "QM_FORBIDDEN_DIRECT_SCHRODINGER_INSERTION_v0",
        "QM_ANTI_CIRCULARITY_GUARD_v0: NO_DIRECT_SCHRODINGER_INSERTION",
    ]
    missing = [tok for tok in required if tok not in text]
    assert not missing, "Missing QM inevitability gate token(s): " + ", ".join(missing)


def test_qm_inevitability_obligation_tokens_synced_to_full_target() -> None:
    gate_text = _read(TARGET_GATE_PATH)
    full_text = _read(TARGET_FULL_PATH)

    obligation_tokens = [
        "qm_inevitability_necessity_under_minimized_assumptions_v0",
        "qm_inevitability_counterfactual_breaks_without_required_assumption_v0",
        "qm_inevitability_structural_classification_of_constructive_route_v0",
        "qm_inevitability_discharge_ready_bundle_v0",
        "qm_inevitability_route_bundle_without_shortcuts_v0",
        "QMInevitabilityMinimizedAssumptions_v0",
        "QMInevitabilityCanonicalConstructiveRoute_v0",
        "QMInevitabilityUnitaryConsistencyRoute_v0",
        "QMInevitabilityNoDirectSchrodingerInsertionRoute_v0",
        "QMNoDirectInsertionEliminationLemmaChain_v0",
        "QMDirectSchrodingerInsertionRouteUsed_v0",
        "QMContractBridgeCompatibilityWrapperRouteUsed_v0",
        "QMInevitabilityClosureSurface_v0",
        "(hMin : QMInevitabilityMinimizedAssumptions_v0 h)",
        "¬QMInevitabilityClosureSurface_v0",
        "qm_inevitability_counterfactual_breaks_without_canonical_constructive_route_assumption_v0",
        "qm_inevitability_counterfactual_breaks_without_unitary_consistency_assumption_v0",
        "qm_inevitability_counterfactual_breaks_without_no_direct_schrodinger_insertion_assumption_v0",
        "QMInevitabilityConstructiveRouteClassification_v0",
    ]

    missing_in_gate = [tok for tok in obligation_tokens if tok not in gate_text]
    missing_in_full = [tok for tok in obligation_tokens if tok not in full_text]
    assert not missing_in_gate, "QM inevitability obligation token(s) missing in gate target: " + ", ".join(missing_in_gate)
    assert not missing_in_full, "QM inevitability obligation token(s) missing in full target: " + ", ".join(missing_in_full)


def test_qm_inevitability_obligation_token_order_synced_between_gate_and_full() -> None:
    ordered_theorem_tokens = [
        "qm_inevitability_necessity_under_minimized_assumptions_v0",
        "qm_inevitability_counterfactual_breaks_without_required_assumption_v0",
        "qm_inevitability_structural_classification_of_constructive_route_v0",
        "qm_inevitability_discharge_ready_bundle_v0",
        "qm_inevitability_route_bundle_without_shortcuts_v0",
    ]
    ordered_counterfactual_detail_tokens = [
        "qm_inevitability_counterfactual_breaks_without_canonical_constructive_route_assumption_v0",
        "qm_inevitability_counterfactual_breaks_without_unitary_consistency_assumption_v0",
        "qm_inevitability_counterfactual_breaks_without_no_direct_schrodinger_insertion_assumption_v0",
    ]
    ordered_anchor_tokens = [
        "QMInevitabilityMinimizedAssumptions_v0",
        "QMInevitabilityCanonicalConstructiveRoute_v0",
        "QMInevitabilityUnitaryConsistencyRoute_v0",
        "QMInevitabilityNoDirectSchrodingerInsertionRoute_v0",
        "QMNoDirectInsertionEliminationLemmaChain_v0",
        "QMDirectSchrodingerInsertionRouteUsed_v0",
        "QMContractBridgeCompatibilityWrapperRouteUsed_v0",
        "QMInevitabilityClosureSurface_v0",
        "(hMin : QMInevitabilityMinimizedAssumptions_v0 h)",
        "¬QMInevitabilityClosureSurface_v0",
        "QMInevitabilityConstructiveRouteClassification_v0",
    ]
    _assert_tokens_in_order(_read(TARGET_GATE_PATH), ordered_theorem_tokens, "QM inevitability gate target theorem-order")
    _assert_tokens_in_order(_read(TARGET_FULL_PATH), ordered_theorem_tokens, "QM full-derivation target theorem-order")
    _assert_tokens_in_order(_read(TARGET_GATE_PATH), ordered_counterfactual_detail_tokens, "QM inevitability gate target counterfactual-detail-order")
    _assert_tokens_in_order(_read(TARGET_FULL_PATH), ordered_counterfactual_detail_tokens, "QM full-derivation target counterfactual-detail-order")
    _assert_tokens_in_order(_read(TARGET_GATE_PATH), ordered_anchor_tokens, "QM inevitability gate target anchor-order")
    _assert_tokens_in_order(_read(TARGET_FULL_PATH), ordered_anchor_tokens, "QM full-derivation target anchor-order")


def test_qm_inevitability_linkage_section_precedes_scope_in_full_target() -> None:
    full_text = _read(TARGET_FULL_PATH)
    linkage_idx = full_text.find("Inevitability obligation linkage")
    scope_idx = full_text.find("Scope boundary:")
    if scope_idx == -1:
        scope_idx = full_text.find("Scope:")

    assert linkage_idx != -1, "QM full-derivation target is missing inevitability obligation linkage section."
    assert scope_idx != -1, "QM full-derivation target is missing Scope section."
    assert linkage_idx < scope_idx, (
        "QM inevitability obligation linkage must appear before Scope to keep structural placement stable."
    )


def test_qm_inevitability_status_is_synced_across_surfaces() -> None:
    gate_text = _read(TARGET_GATE_PATH)
    full_text = _read(TARGET_FULL_PATH)
    state_text = _read(STATE_PATH)

    gate = _extract_status(gate_text, "QM inevitability gate target")
    full = _extract_status(full_text, "QM full-derivation target")
    state = _extract_status(state_text, "State_of_the_Theory")

    assert gate == full == state, (
        "QM inevitability adjudication drift across surfaces: "
        f"gate={gate}, full={full}, state={state}"
    )


def test_qm_inevitability_promotion_requires_theorem_body_tokens() -> None:
    status = _extract_status(_read(TARGET_GATE_PATH), "QM inevitability gate target")
    lean_text = _read(LEAN_PATH)

    forbidden_tautological_route_defs = [
        "def QMInevitabilityCanonicalConstructiveRoute_v0\n    (h : QMEvolutionAssumptions_v0_min1) : Prop :=\n  True",
        "def QMInevitabilityUnitaryConsistencyRoute_v0\n    (h : QMEvolutionAssumptions_v0_min1)\n    (norm : h.State → ℝ) : Prop :=\n  True",
        "def QMInevitabilityNoDirectSchrodingerInsertionRoute_v0 : Prop :=\n  True",
        "def QMInevitabilityClosureSurface_v0\n    (h : QMEvolutionAssumptions_v0_min1)\n    (norm : h.State → ℝ) : Prop :=\n  True",
        "def QMInevitabilityNoDirectSchrodingerInsertionRoute_v0 : Prop :=\n  QMAntiCircularityGuardNoDirectSchrodingerInsertion ∧\n    ∀ (hLocal : QMEvolutionAssumptions_v0_min1),\n      QMStateEvolvesUnderContract hLocal.ctx hLocal.t hLocal.initialState hLocal.finalState →\n      QMStateEvolvesUnderContract hLocal.ctx hLocal.t hLocal.initialState hLocal.finalState",
        "def QMDirectSchrodingerInsertionRouteUsed_v0 : Prop :=\n  False",
        "def QMContractBridgeCompatibilityWrapperRouteUsed_v0 : Prop :=\n  False",
    ]
    unexpected_tautologies = [tok for tok in forbidden_tautological_route_defs if tok in lean_text]
    assert not unexpected_tautologies, (
        "QM inevitability route contains forbidden tautological definition(s): "
        + ", ".join(unexpected_tautologies)
    )

    required_route_anchors = [
        "structure QMInevitabilityMinimizedAssumptions_v0",
        "qm_inevitability_canonical_constructive_dependency_from_cycle1_v0",
        "def QMInevitabilityCanonicalConstructiveRoute_v0",
        "def QMInevitabilityUnitaryConsistencyRoute_v0",
        "def QMInevitabilityNoDirectSchrodingerInsertionRoute_v0",
        "def QMNoDirectInsertionEliminationLemmaChain_v0",
        "def QMDirectSchrodingerInsertionRouteUsed_v0",
        "def QMContractBridgeCompatibilityWrapperRouteUsed_v0",
        "qm_full_derivation_cycle3_no_direct_schrodinger_insertion_guard_v0 =",
        "qm_full_derivation_cycle1_contract_bridge_token_v0 =",
        "QMInevitabilityNoDirectSchrodingerInsertionRoute_v0 : Prop :=\n  QMAntiCircularityGuardNoDirectSchrodingerInsertion ∧\n    QMNoDirectInsertionEliminationLemmaChain_v0",
        "def QMInevitabilityClosureSurface_v0",
        "(hMin : QMInevitabilityMinimizedAssumptions_v0 h)",
        "¬QMInevitabilityClosureSurface_v0",
        "qm_inevitability_counterfactual_breaks_without_canonical_constructive_route_assumption_v0",
        "qm_inevitability_counterfactual_breaks_without_unitary_consistency_assumption_v0",
        "qm_inevitability_counterfactual_breaks_without_no_direct_schrodinger_insertion_assumption_v0",
        "QMInevitabilityConstructiveRouteClassification_v0",
    ]
    missing_route_anchors = [tok for tok in required_route_anchors if tok not in lean_text]
    assert not missing_route_anchors, (
        "QM inevitability theorem route is missing minimized-assumption/counterfactual anchors: "
        + ", ".join(missing_route_anchors)
    )

    required_theorem_tokens = [
        "theorem qm_inevitability_necessity_under_minimized_assumptions_v0",
        "theorem qm_inevitability_counterfactual_breaks_without_required_assumption_v0",
        "theorem qm_inevitability_structural_classification_of_constructive_route_v0",
        "theorem qm_inevitability_discharge_ready_bundle_v0",
        "theorem qm_inevitability_route_bundle_without_shortcuts_v0",
    ]

    if status == "DISCHARGED_v0_BOUNDED":
        missing = [tok for tok in required_theorem_tokens if tok not in lean_text]
        assert not missing, "QM inevitability is marked discharged without theorem-body tokens: " + ", ".join(missing)
    else:
        assert "No inevitability discharge claim" in _read(RESULTS_PATH), (
            "QM inevitability is not discharged but results table no longer carries non-claim boundary text."
        )
        assert "inevitability is not yet discharged" in _read(ROADMAP_PATH), (
            "QM inevitability is not discharged but roadmap does not reflect that status."
        )


def test_qm_constructive_route_theorem_body_is_wrapper_free() -> None:
    lean_text = _read(LEAN_PATH)

    required_theorems = [
        "qm_inevitability_constructive_route_without_compatibility_wrappers_v0",
        "qm_inevitability_counterfactual_breaks_when_constructive_route_missing_v0",
    ]
    for theorem_name in required_theorems:
        assert f"theorem {theorem_name}" in lean_text, f"Missing theorem token in Lean file: {theorem_name}"

    block = _theorem_block(
        lean_text,
        "qm_inevitability_constructive_route_without_compatibility_wrappers_v0",
    )
    forbidden_wrapper_tokens = [
        "qm_full_derivation_cycle1_contract_bridge_token_v0",
        "qm_full_derivation_cycle4_composition_bundle_token_v0",
        "qm_full_derivation_cycle7_derivation_exit_row_closure_token_v0",
    ]
    leaked = [tok for tok in forbidden_wrapper_tokens if tok in block]
    assert not leaked, "QM constructive-route theorem should be wrapper-free but contains: " + ", ".join(leaked)
    assert "qm_inevitability_canonical_constructive_dependency_from_cycle1_v0 h" in block, (
        "QM constructive-route theorem must use cycle1 dependency theorem for canonical route."
    )


def test_qm_positive_dependency_theorem_calls_core_lemmas() -> None:
    lean_text = _read(LEAN_PATH)
    theorem_name = "qm_inevitability_positive_dependency_core_lemma_bundle_v0"
    assert f"theorem {theorem_name}" in lean_text, f"Missing theorem token in Lean file: {theorem_name}"

    block = _theorem_block(lean_text, theorem_name)
    required_core_calls = [
        "qm_inevitability_discharge_ready_bundle_v0 h hMin",
        "qm_inevitability_constructive_route_without_compatibility_wrappers_v0 h hMin",
        "qm_full_derivation_cycle5_policy_to_math_reclassification_token_v0 h",
        "qm_inevitability_canonical_constructive_dependency_from_cycle1_v0 h",
    ]
    missing = [tok for tok in required_core_calls if tok not in block]
    assert not missing, "QM positive-dependency theorem is missing required core-lemma calls: " + ", ".join(missing)


def test_qm_physics_substance_dependency_theorem_calls_core_lemmas() -> None:
    lean_text = _read(LEAN_PATH)
    theorem_name = "qm_inevitability_physics_substance_dependency_bundle_v0"
    assert f"theorem {theorem_name}" in lean_text, f"Missing theorem token in Lean file: {theorem_name}"

    block = _theorem_block(lean_text, theorem_name)
    required_core_calls = [
        "qm_full_derivation_cycle7_derivation_exit_row_closure_token_v0 h hMin.norm hMin.unitaryConsistencyRoute",
        "qm_full_derivation_cycle9_assumption_minimization_exit_row_closure_token_v0 h",
        "qm_full_derivation_cycle5_policy_to_math_reclassification_token_v0 h",
    ]
    missing = [tok for tok in required_core_calls if tok not in block]
    assert not missing, "QM physics-substance theorem is missing required core-lemma calls: " + ", ".join(missing)


def test_qm_endpoint_counterfactual_theorem_calls_cycle7_dependency() -> None:
    lean_text = _read(LEAN_PATH)
    theorem_name = "qm_inevitability_endpoint_counterfactual_breaks_without_cycle7_dependency_v0"
    assert f"theorem {theorem_name}" in lean_text, f"Missing theorem token in Lean file: {theorem_name}"

    block = _theorem_block(lean_text, theorem_name)
    required_core_calls = [
        "qm_full_derivation_cycle7_derivation_exit_row_closure_token_v0 h hMin.norm hMin.unitaryConsistencyRoute",
    ]
    missing = [tok for tok in required_core_calls if tok not in block]
    assert not missing, "QM endpoint-counterfactual theorem is missing required dependency calls: " + ", ".join(missing)


def test_qm_independent_necessity_class_theorem_uses_endpoint_counterfactual_route() -> None:
    lean_text = _read(LEAN_PATH)
    theorem_name = "qm_inevitability_independent_necessity_class_from_endpoint_counterfactual_v0"
    assert f"theorem {theorem_name}" in lean_text, f"Missing theorem token in Lean file: {theorem_name}"

    block = _theorem_block(lean_text, theorem_name)
    required_core_calls = [
        "qm_inevitability_physics_substance_dependency_bundle_v0 h hMin",
        "qm_inevitability_endpoint_counterfactual_breaks_without_cycle7_dependency_v0",
    ]
    missing = [tok for tok in required_core_calls if tok not in block]
    assert not missing, "QM independent necessity-class theorem is missing required dependency calls: " + ", ".join(missing)

    forbidden_direct_restatement = [
        "qm_inevitability_necessity_under_minimized_assumptions_v0 h hMin",
    ]
    leaked = [tok for tok in forbidden_direct_restatement if tok in block]
    assert not leaked, "QM independent necessity-class theorem must not be a direct necessity restatement: " + ", ".join(leaked)

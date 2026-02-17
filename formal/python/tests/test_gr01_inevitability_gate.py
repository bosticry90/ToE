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
TARGET_GATE_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_GR01_INEVITABILITY_GATE_v0.md"
)
TARGET_FULL_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_GR01_FULL_DERIVATION_DISCHARGE_v0.md"
)
LEAN_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "GR01ActionToOperatorDiscrete.lean"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _extract_status(text: str, label: str) -> str:
    m = re.search(
        r"FULL_DERIVATION_INEVITABILITY_ADJUDICATION:\s*"
        r"(NOT_YET_DISCHARGED_v0|DISCHARGED_v0_BOUNDED)",
        text,
    )
    assert m is not None, f"Missing GR inevitability adjudication token in {label}."
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


def test_gr01_inevitability_gate_doc_is_pinned() -> None:
    text = _read(TARGET_GATE_PATH)
    required = [
        "DERIVATION_TARGET_GR01_INEVITABILITY_GATE_v0",
        "TARGET-GR01-INEVITABILITY-GATE-PLAN",
        "FULL_DERIVATION_INEVITABILITY_ADJUDICATION:",
        "gr01_inevitability_necessity_under_minimized_assumptions_v0",
        "gr01_inevitability_counterfactual_breaks_without_required_assumption_v0",
        "gr01_inevitability_structural_classification_of_constructive_route_v0",
        "gr01_inevitability_discharge_ready_bundle_v0",
        "gr01_inevitability_route_bundle_without_bridge_shortcuts_v0",
        "GR01InevitabilityMinimizedAssumptions_v0",
        "GR01InevitabilityCanonicalActionNativeRoute_v0",
        "GR01InevitabilityNoBridgeShortcutRoute_v0",
        "GR01InevitabilityBoundedWeakFieldClosureRoute_v0",
        "GR01NoBridgeShortcutEliminationLemmaChain_v0",
        "GR01BridgeWitnessConstructorRouteUsed_v0",
        "GR01BridgeTransportConstructorRouteUsed_v0",
        "GR01BridgeTransportFromRadialEvaluatorRouteUsed_v0",
        "GR01InevitabilityBoundedClosureSurface_v0",
        "(hMin : GR01InevitabilityMinimizedAssumptions_v0)",
        "¬GR01InevitabilityBoundedClosureSurface_v0",
        "gr01_inevitability_counterfactual_breaks_without_canonical_action_native_route_assumption_v0",
        "gr01_inevitability_counterfactual_breaks_without_no_bridge_shortcut_assumption_v0",
        "gr01_inevitability_counterfactual_breaks_without_bounded_weak_field_closure_assumption_v0",
        "GR01InevitabilityConstructiveRouteClassification_v0",
    ]
    missing = [tok for tok in required if tok not in text]
    assert not missing, "Missing GR inevitability gate token(s): " + ", ".join(missing)


def test_gr01_inevitability_obligation_tokens_synced_to_full_target() -> None:
    gate_text = _read(TARGET_GATE_PATH)
    full_text = _read(TARGET_FULL_PATH)

    obligation_tokens = [
        "gr01_inevitability_necessity_under_minimized_assumptions_v0",
        "gr01_inevitability_counterfactual_breaks_without_required_assumption_v0",
        "gr01_inevitability_structural_classification_of_constructive_route_v0",
        "gr01_inevitability_discharge_ready_bundle_v0",
        "gr01_inevitability_route_bundle_without_bridge_shortcuts_v0",
        "GR01InevitabilityMinimizedAssumptions_v0",
        "GR01InevitabilityCanonicalActionNativeRoute_v0",
        "GR01InevitabilityNoBridgeShortcutRoute_v0",
        "GR01InevitabilityBoundedWeakFieldClosureRoute_v0",
        "GR01NoBridgeShortcutEliminationLemmaChain_v0",
        "GR01BridgeWitnessConstructorRouteUsed_v0",
        "GR01BridgeTransportConstructorRouteUsed_v0",
        "GR01BridgeTransportFromRadialEvaluatorRouteUsed_v0",
        "GR01InevitabilityBoundedClosureSurface_v0",
        "(hMin : GR01InevitabilityMinimizedAssumptions_v0)",
        "¬GR01InevitabilityBoundedClosureSurface_v0",
        "gr01_inevitability_counterfactual_breaks_without_canonical_action_native_route_assumption_v0",
        "gr01_inevitability_counterfactual_breaks_without_no_bridge_shortcut_assumption_v0",
        "gr01_inevitability_counterfactual_breaks_without_bounded_weak_field_closure_assumption_v0",
        "GR01InevitabilityConstructiveRouteClassification_v0",
    ]

    missing_in_gate = [tok for tok in obligation_tokens if tok not in gate_text]
    missing_in_full = [tok for tok in obligation_tokens if tok not in full_text]
    assert not missing_in_gate, "GR inevitability obligation token(s) missing in gate target: " + ", ".join(missing_in_gate)
    assert not missing_in_full, "GR inevitability obligation token(s) missing in full target: " + ", ".join(missing_in_full)


def test_gr01_inevitability_obligation_token_order_synced_between_gate_and_full() -> None:
    ordered_base_theorem_tokens = [
        "gr01_inevitability_necessity_under_minimized_assumptions_v0",
        "gr01_inevitability_counterfactual_breaks_without_required_assumption_v0",
        "gr01_inevitability_structural_classification_of_constructive_route_v0",
        "gr01_inevitability_discharge_ready_bundle_v0",
        "gr01_inevitability_route_bundle_without_bridge_shortcuts_v0",
    ]
    ordered_counterfactual_detail_tokens = [
        "gr01_inevitability_counterfactual_breaks_without_canonical_action_native_route_assumption_v0",
        "gr01_inevitability_counterfactual_breaks_without_no_bridge_shortcut_assumption_v0",
        "gr01_inevitability_counterfactual_breaks_without_bounded_weak_field_closure_assumption_v0",
    ]
    ordered_anchor_tokens = [
        "GR01InevitabilityMinimizedAssumptions_v0",
        "GR01InevitabilityCanonicalActionNativeRoute_v0",
        "GR01InevitabilityNoBridgeShortcutRoute_v0",
        "GR01InevitabilityBoundedWeakFieldClosureRoute_v0",
        "GR01NoBridgeShortcutEliminationLemmaChain_v0",
        "GR01BridgeWitnessConstructorRouteUsed_v0",
        "GR01BridgeTransportConstructorRouteUsed_v0",
        "GR01BridgeTransportFromRadialEvaluatorRouteUsed_v0",
        "GR01InevitabilityBoundedClosureSurface_v0",
        "(hMin : GR01InevitabilityMinimizedAssumptions_v0)",
        "¬GR01InevitabilityBoundedClosureSurface_v0",
        "GR01InevitabilityConstructiveRouteClassification_v0",
    ]
    _assert_tokens_in_order(_read(TARGET_GATE_PATH), ordered_base_theorem_tokens, "GR inevitability gate target theorem-order")
    _assert_tokens_in_order(_read(TARGET_FULL_PATH), ordered_base_theorem_tokens, "GR full-derivation target theorem-order")
    _assert_tokens_in_order(_read(TARGET_GATE_PATH), ordered_counterfactual_detail_tokens, "GR inevitability gate target counterfactual-detail-order")
    _assert_tokens_in_order(_read(TARGET_FULL_PATH), ordered_counterfactual_detail_tokens, "GR full-derivation target counterfactual-detail-order")
    _assert_tokens_in_order(_read(TARGET_GATE_PATH), ordered_anchor_tokens, "GR inevitability gate target anchor-order")
    _assert_tokens_in_order(_read(TARGET_FULL_PATH), ordered_anchor_tokens, "GR full-derivation target anchor-order")


def test_gr01_inevitability_linkage_section_precedes_scope_in_full_target() -> None:
    full_text = _read(TARGET_FULL_PATH)
    linkage_idx = full_text.find("Inevitability obligation linkage")
    scope_idx = full_text.find("Scope boundary:")
    if scope_idx == -1:
        scope_idx = full_text.find("Scope:")

    assert linkage_idx != -1, "GR full-derivation target is missing inevitability obligation linkage section."
    assert scope_idx != -1, "GR full-derivation target is missing Scope section."
    assert linkage_idx < scope_idx, (
        "GR inevitability obligation linkage must appear before Scope to keep structural placement stable."
    )


def test_gr01_inevitability_status_is_synced_across_surfaces() -> None:
    gate_text = _read(TARGET_GATE_PATH)
    full_text = _read(TARGET_FULL_PATH)
    state_text = _read(STATE_PATH)

    gate = _extract_status(gate_text, "GR inevitability gate target")
    full = _extract_status(full_text, "GR full-derivation target")
    state = _extract_status(state_text, "State_of_the_Theory")

    assert gate == full == state, (
        "GR inevitability adjudication drift across surfaces: "
        f"gate={gate}, full={full}, state={state}"
    )


def test_gr01_inevitability_promotion_requires_theorem_body_tokens() -> None:
    status = _extract_status(_read(TARGET_GATE_PATH), "GR inevitability gate target")
    lean_text = _read(LEAN_PATH)

    forbidden_tautological_route_defs = [
        "def GR01InevitabilityCanonicalActionNativeRoute_v0 : Prop :=\n  True",
        "def GR01InevitabilityNoBridgeShortcutRoute_v0 : Prop :=\n  True",
        "def GR01InevitabilityBoundedWeakFieldClosureRoute_v0 : Prop :=\n  True",
        "def GR01InevitabilityBoundedClosureSurface_v0 : Prop :=\n  True",
        "def GR01InevitabilityCanonicalActionNativeRoute_v0 : Prop :=\n  ∃ ε : ℝ, ε > 0",
        "def GR01InevitabilityNoBridgeShortcutRoute_v0 : Prop :=\n  ∀ (bridgeShortcutUsed : Prop), bridgeShortcutUsed → False",
        "def GR01BridgeWitnessConstructorRouteUsed_v0 : Prop :=\n  False",
        "def GR01BridgeTransportConstructorRouteUsed_v0 : Prop :=\n  False",
        "def GR01BridgeTransportFromRadialEvaluatorRouteUsed_v0 : Prop :=\n  False",
    ]
    unexpected_tautologies = [tok for tok in forbidden_tautological_route_defs if tok in lean_text]
    assert not unexpected_tautologies, (
        "GR inevitability route contains forbidden tautological definition(s): "
        + ", ".join(unexpected_tautologies)
    )

    required_route_anchors = [
        "structure GR01InevitabilityMinimizedAssumptions_v0",
        "def GR01InevitabilityCanonicalActionNativeRoute_v0",
        "GR01InevitabilityCanonicalActionNativeRoute_v0 : Prop :=\n  GR01InevitabilityBoundedWeakFieldClosureRoute_v0",
        "def GR01InevitabilityNoBridgeShortcutRoute_v0",
        "GR01InevitabilityNoBridgeShortcutRoute_v0 : Prop :=\n  GR01NoBridgeShortcutEliminationLemmaChain_v0",
        "def GR01InevitabilityBoundedWeakFieldClosureRoute_v0",
        "def GR01NoBridgeShortcutEliminationLemmaChain_v0",
        "def GR01BridgeWitnessConstructorRouteUsed_v0",
        "def GR01BridgeTransportConstructorRouteUsed_v0",
        "def GR01BridgeTransportFromRadialEvaluatorRouteUsed_v0",
        "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_bridge_witness_constructor_v0 =",
        "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_bridge_transport_constructor_v0 =",
        "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_bridge_transport_from_radial_evaluator_constructor_v0 =",
        "def GR01InevitabilityBoundedClosureSurface_v0",
        "(hMin : GR01InevitabilityMinimizedAssumptions_v0)",
        "¬GR01InevitabilityBoundedClosureSurface_v0",
        "gr01_inevitability_counterfactual_breaks_without_canonical_action_native_route_assumption_v0",
        "gr01_inevitability_counterfactual_breaks_without_no_bridge_shortcut_assumption_v0",
        "gr01_inevitability_counterfactual_breaks_without_bounded_weak_field_closure_assumption_v0",
        "GR01InevitabilityConstructiveRouteClassification_v0",
    ]
    missing_route_anchors = [tok for tok in required_route_anchors if tok not in lean_text]
    assert not missing_route_anchors, (
        "GR inevitability theorem route is missing minimized-assumption/counterfactual anchors: "
        + ", ".join(missing_route_anchors)
    )

    required_theorem_tokens = [
        "theorem gr01_inevitability_necessity_under_minimized_assumptions_v0",
        "theorem gr01_inevitability_counterfactual_breaks_without_required_assumption_v0",
        "theorem gr01_inevitability_structural_classification_of_constructive_route_v0",
        "theorem gr01_inevitability_discharge_ready_bundle_v0",
        "theorem gr01_inevitability_route_bundle_without_bridge_shortcuts_v0",
    ]

    if status == "DISCHARGED_v0_BOUNDED":
        missing = [tok for tok in required_theorem_tokens if tok not in lean_text]
        assert not missing, "GR inevitability is marked discharged without theorem-body tokens: " + ", ".join(missing)
    else:
        results_text = _read(RESULTS_PATH)
        assert "TOE-GR-01 | `B-BLOCKED`" in results_text
        assert "TOE-GR-THM-01 | `B-BLOCKED`" in results_text
        assert "No inevitability discharge claim" in results_text


def test_gr01_constructive_route_theorem_body_is_bridge_wrapper_free() -> None:
    lean_text = _read(LEAN_PATH)

    required_theorems = [
        "gr01_inevitability_constructive_route_without_compatibility_wrappers_v0",
        "gr01_inevitability_counterfactual_breaks_when_constructive_route_missing_v0",
    ]
    for theorem_name in required_theorems:
        assert f"theorem {theorem_name}" in lean_text, f"Missing theorem token in Lean file: {theorem_name}"

    block = _theorem_block(
        lean_text,
        "gr01_inevitability_constructive_route_without_compatibility_wrappers_v0",
    )
    forbidden_wrapper_tokens = [
        "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_bridge_witness_constructor_v0",
        "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_bridge_transport_constructor_v0",
        "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_bridge_transport_from_radial_evaluator_constructor_v0",
        "gr01_operator_residual_transport_from_bound_bridge_assumptions",
    ]
    leaked = [tok for tok in forbidden_wrapper_tokens if tok in block]
    assert not leaked, "GR constructive-route theorem should be bridge-wrapper-free but contains: " + ", ".join(leaked)


def test_gr01_positive_dependency_theorem_calls_core_lemmas() -> None:
    lean_text = _read(LEAN_PATH)
    theorem_name = "gr01_inevitability_positive_dependency_core_lemma_bundle_v0"
    assert f"theorem {theorem_name}" in lean_text, f"Missing theorem token in Lean file: {theorem_name}"

    block = _theorem_block(lean_text, theorem_name)
    required_core_calls = [
        "gr01_inevitability_discharge_ready_bundle_v0 hMin",
        "gr01_inevitability_constructive_route_without_compatibility_wrappers_v0 hMin",
        "gr01_inevitability_route_bundle_without_bridge_shortcuts_v0 hMin",
    ]
    missing = [tok for tok in required_core_calls if tok not in block]
    assert not missing, "GR positive-dependency theorem is missing required core-lemma calls: " + ", ".join(missing)


def test_gr01_physics_substance_dependency_theorem_calls_core_lemmas() -> None:
    lean_text = _read(LEAN_PATH)
    theorem_name = "gr01_inevitability_physics_substance_dependency_bundle_v0"
    assert f"theorem {theorem_name}" in lean_text, f"Missing theorem token in Lean file: {theorem_name}"

    block = _theorem_block(lean_text, theorem_name)
    required_core_calls = [
        "actionRep32_fd_expansion_and_vanishing_to_radial_evaluator_transport_constructor_v0",
        "actionRep32_el_implies_operator_residual_transport_from_fd_expansion_constructor_of_rac_default_binding_from_probe_model_v0",
        "actionRep32_weak_field_poisson_limit_under_default_binding_assumptions_of_action_native_transport_constructor_from_fd_expansion_v0",
    ]
    missing = [tok for tok in required_core_calls if tok not in block]
    assert not missing, "GR physics-substance theorem is missing required core-lemma calls: " + ", ".join(missing)


def test_gr01_endpoint_counterfactual_theorem_calls_no_bridge_dependency() -> None:
    lean_text = _read(LEAN_PATH)
    theorem_name = "gr01_inevitability_endpoint_counterfactual_breaks_without_no_bridge_dependency_v0"
    assert f"theorem {theorem_name}" in lean_text, f"Missing theorem token in Lean file: {theorem_name}"

    block = _theorem_block(lean_text, theorem_name)
    required_core_calls = [
        "gr01_inevitability_route_bundle_without_bridge_shortcuts_v0 hMin",
    ]
    missing = [tok for tok in required_core_calls if tok not in block]
    assert not missing, "GR endpoint-counterfactual theorem is missing required dependency calls: " + ", ".join(missing)


def test_gr01_independent_necessity_class_theorem_uses_endpoint_counterfactual_route() -> None:
    lean_text = _read(LEAN_PATH)
    theorem_name = "gr01_inevitability_independent_necessity_class_from_endpoint_counterfactual_v0"
    assert f"theorem {theorem_name}" in lean_text, f"Missing theorem token in Lean file: {theorem_name}"

    block = _theorem_block(lean_text, theorem_name)
    required_core_calls = [
        "gr01_inevitability_physics_substance_dependency_bundle_v0 hMin",
        "gr01_inevitability_endpoint_counterfactual_breaks_without_no_bridge_dependency_v0",
    ]
    missing = [tok for tok in required_core_calls if tok not in block]
    assert not missing, "GR independent necessity-class theorem is missing required dependency calls: " + ", ".join(missing)

    forbidden_direct_restatement = [
        "gr01_inevitability_necessity_under_minimized_assumptions_v0 hMin",
    ]
    leaked = [tok for tok in forbidden_direct_restatement if tok in block]
    assert not leaked, "GR independent necessity-class theorem must not be a direct necessity restatement: " + ", ".join(leaked)

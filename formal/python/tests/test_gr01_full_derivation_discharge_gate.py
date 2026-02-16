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
TARGET_DOC = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "DERIVATION_TARGET_GR01_FULL_DERIVATION_DISCHARGE_v0.md"
)
RESULTS_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "RESULTS_TABLE_v0.md"
ACTION_QUAD_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "ActionRep32QuadraticCubic.lean"
)
ACTION_DEF_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "ActionRep32Def.lean"
)
FIRST_VARIATION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "FirstVariationRep32Def.lean"
)
DISCHARGE_PCUBIC_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "DischargeELMatchesFN01Rep32Pcubic.lean"
)
A2O_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "GR01ActionToOperatorDiscrete.lean"
)
ACTION_CUBIC_LANE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "ActionRep32CubicLane.lean"
)
BRIDGE_PROMOTION_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "GR01BridgePromotion.lean"
)
WEAK_FIELD_LIMIT_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "WeakFieldPoissonLimit.lean"
)
DER01_SCAFFOLD_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "GR01DerivationScaffoldPromotion.lean"
)
END_TO_END_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Variational"
    / "GR01EndToEndClosure.lean"
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _result_status_for(row_id: str, results_text: str) -> str:
    pattern = rf"^\| {re.escape(row_id)} \| `([^`]+)` \|"
    m = re.search(pattern, results_text, flags=re.MULTILINE)
    assert m is not None, f"Missing result row: {row_id}"
    return m.group(1)


def _full_derivation_adjudication(doc_text: str) -> str:
    m = re.search(
        r"FULL_DERIVATION_ADJUDICATION:\s*"
        r"(NOT_YET_DISCHARGED_v0|DISCHARGED_v0_DISCRETE)",
        doc_text,
    )
    assert m is not None, (
        "Missing FULL_DERIVATION_ADJUDICATION token in full-derivation target doc."
    )
    return m.group(1)


def _theorem_block(text: str, theorem_name: str) -> str:
    start_match = re.search(rf"\btheorem\s+{re.escape(theorem_name)}\b", text)
    assert start_match is not None, f"Missing theorem token: {theorem_name}"
    start = start_match.start()
    next_match = re.search(
        r"\n(?:theorem|def|abbrev|structure)\s+",
        text[start_match.end() :],
    )
    if next_match is None:
        return text[start:]
    end = start_match.end() + next_match.start()
    return text[start:end]


def _assert_block_policy(
    block_name: str,
    block_text: str,
    *,
    required_tokens: list[str] | None = None,
    forbidden_tokens: list[str] | None = None,
    forbidden_param_patterns: list[str] | None = None,
) -> None:
    required_tokens = required_tokens or []
    forbidden_tokens = forbidden_tokens or []
    forbidden_param_patterns = forbidden_param_patterns or []

    missing = [tok for tok in required_tokens if tok not in block_text]
    assert not missing, (
        f"{block_name} is missing required policy token(s): " + ", ".join(missing)
    )

    present = [tok for tok in forbidden_tokens if tok in block_text]
    assert not present, (
        f"{block_name} contains forbidden policy token(s): " + ", ".join(present)
    )

    for pattern in forbidden_param_patterns:
        assert re.search(pattern, block_text) is None, (
            f"{block_name} contains forbidden signature-parameter pattern: {pattern}"
        )


def test_gr01_full_derivation_target_doc_tokens_present() -> None:
    text = _read(TARGET_DOC)
    required_tokens = [
        "DERIVATION_TARGET_GR01_FULL_DERIVATION_DISCHARGE_v0",
        "FULL_DERIVATION_ADJUDICATION:",
        "differenceQuotientRep32_cubic_deviation_expand",
        "ActionRep32Def.lean",
        "FirstVariationRep32Def.lean",
        "DischargeELMatchesFN01Rep32Pcubic.lean",
    ]
    for token in required_tokens:
        assert token in text, f"Missing required full-derivation token: {token}"


def test_gr01_full_derivation_progress_token_exists() -> None:
    text = _read(ACTION_QUAD_PATH)
    assert "theorem differenceQuotientRep32_cubic_deviation_expand" in text, (
        "Missing progress theorem token required by full-derivation blocker tracking."
    )
    assert "theorem ActionRep32FiniteDifferenceDeviationFromP_of_cubic" in text, (
        "Missing algebraic finite-difference deviation theorem token in ActionRep32QuadraticCubic."
    )
    assert "def ActionRep32CubicTotalDeviationZeroAtStep" in text, (
        "Missing fixed-step total-deviation object token in ActionRep32QuadraticCubic."
    )
    assert "theorem ActionRep32CubicTotalDeviationZeroAtStep_of_components" in text, (
        "Missing component-to-total-deviation theorem token in ActionRep32QuadraticCubic."
    )
    assert "theorem ActionRep32FiniteDifferenceRepresentsP_of_cubic_totalDeviationZeroAtStep" in text, (
        "Missing total-deviation-to-representability theorem token in ActionRep32QuadraticCubic."
    )
    lane_text = _read(ACTION_CUBIC_LANE_PATH)
    assert (
        "theorem EL_toe_rep32_equals_Pcubic_under_default_quotient_assumptions_of_hP"
        in lane_text
    ), "Missing explicit-of_hP derivation route token in ActionRep32CubicLane."
    required_lane_tokens = [
        "abbrev ActionRep32CubicDeviationZeroAtStep",
        "theorem ActionRep32CubicDeviationZeroAtStep_of_RAC",
        "theorem ActionRep32FiniteDifferenceRepresentsP_cubic_of_deviationZeroAtStep",
        "theorem ActionVariationBridgeRep32At_cubic_of_deviationZeroAtStep",
    ]
    missing_lane = [t for t in required_lane_tokens if t not in lane_text]
    assert not missing_lane, (
        "Missing algebraic deviation lane token(s) in ActionRep32CubicLane: "
        + ", ".join(missing_lane)
    )
    bridge_text = _read(BRIDGE_PROMOTION_PATH)
    assert "theorem gr01_discrete_residual_from_bridge_promotion_chain_of_hP" in bridge_text, (
        "Missing explicit-of_hP bridge-promotion token in GR01BridgePromotion."
    )
    assert (
        "theorem gr01_discrete_residual_from_bridge_promotion_chain_minimal_of_hP"
        in bridge_text
    ), "Missing minimal explicit-of_hP bridge-promotion token in GR01BridgePromotion."
    assert (
        "theorem gr01_discrete_residual_from_bridge_promotion_chain_default_binding_of_hP"
        in bridge_text
    ), "Missing default-binding bridge-promotion token in GR01BridgePromotion."
    assert (
        "theorem gr01_el_implies_discrete_poisson_residual_from_bridge_promotion"
        in bridge_text
    ), "Missing derived EL->discrete-residual constructor token in GR01BridgePromotion."
    assert (
        "theorem TOE_GR01_weak_field_poisson_limit_under_default_quotient_assumptions_derived_from_bridge_minimal_of_hP"
        in bridge_text
    ), "Missing minimal bridge-derived weak-field theorem token in GR01BridgePromotion."
    assert (
        "theorem TOE_GR01_weak_field_poisson_limit_under_default_binding_assumptions_derived_from_bridge_of_hP"
        in bridge_text
    ), "Missing default-binding bridge-derived weak-field theorem token in GR01BridgePromotion."
    assert (
        "def ELImpliesOperatorResidualTransport"
        in bridge_text
    ), "Missing operator-residual transport surface token in GR01BridgePromotion."
    assert (
        "theorem gr01_el_implies_discrete_poisson_residual_from_operator_transport"
        in bridge_text
    ), "Missing EL->discrete-residual from operator-transport token in GR01BridgePromotion."
    assert (
        "theorem gr01_operator_residual_transport_from_bound_bridge_assumptions"
        in bridge_text
    ), "Missing operator-transport constructor from bound-bridge assumptions in GR01BridgePromotion."
    assert (
        "theorem TOE_GR01_weak_field_poisson_limit_under_default_quotient_assumptions_derived_from_operator_transport_minimal_of_hP"
        in bridge_text
    ), "Missing minimal operator-transport weak-field theorem token in GR01BridgePromotion."
    weak_field_text = _read(WEAK_FIELD_LIMIT_PATH)
    assert (
        "theorem TOE_GR01_weak_field_poisson_limit_under_default_quotient_assumptions_of_hP"
        in weak_field_text
    ), "Missing explicit-of_hP weak-field theorem token in WeakFieldPoissonLimit."
    assert (
        "theorem TOE_GR01_weak_field_poisson_limit_under_default_quotient_assumptions_minimal_of_hP"
        in weak_field_text
    ), "Missing minimal explicit-of_hP weak-field theorem token in WeakFieldPoissonLimit."
    assert (
        "theorem TOE_GR01_weak_field_poisson_limit_under_default_binding_assumptions_of_hP"
        in weak_field_text
    ), "Missing default-binding weak-field theorem token in WeakFieldPoissonLimit."
    scaffold_text = _read(DER01_SCAFFOLD_PATH)
    assert (
        "theorem gr01_der01_scaffold_bundle_under_promoted_assumptions_of_hP"
        in scaffold_text
    ), "Missing explicit-of_hP scaffold bundle token in GR01DerivationScaffoldPromotion."
    end_to_end_text = _read(END_TO_END_PATH)
    required_end_to_end_tokens = [
        "theorem gr01_end_to_end_chain_bundle_under_promoted_assumptions_of_hP",
        "theorem gr01_end_to_end_poisson_equation_under_promoted_assumptions_of_hP",
    ]
    missing = [t for t in required_end_to_end_tokens if t not in end_to_end_text]
    assert not missing, (
        "Missing explicit-of_hP end-to-end token(s): " + ", ".join(missing)
    )
    a2o_text = _read(A2O_PATH)
    core_required_a2o_tokens = [
        "def actionRep32_algebraic_deviation_surface_discrete_v0",
        "theorem actionRep32_variation_deviation_sequence_discrete_v0",
        "theorem actionRep32_variation_deviation_sequence_discrete_default_binding_v0",
        "theorem actionRep32_fd_deviation_with_Pcubic_from_algebraic_surface_v0",
        "theorem actionRep32_cubic_deviation_collapse_from_vanishing_v0",
        "theorem actionRep32_fd_equals_Pcubic_from_algebraic_surface_and_vanishing_v0",
        "def actionRep32_el_core_implies_probe_pcubic_pairing_zero_interface_v0",
        "def actionRep32_probe_fd_matches_radial_evaluator_interface_v0",
        "def actionRep32_probe_pairing_matches_radial_evaluator_interface_v0",
        "structure actionRep32_probe_pairing_to_radial_model_assumptions_v0",
        "theorem actionRep32_probe_pairing_matches_radial_evaluator_from_model_assumptions_v0",
        "theorem actionRep32_probe_fd_matches_radial_evaluator_from_pairing_and_fd_expansion_v0",
        "theorem actionRep32_el_to_radial_evaluator_zero_from_fd_expansion_and_probe_interfaces_v0",
        "theorem actionRep32_fd_expansion_and_vanishing_to_radial_evaluator_transport_constructor_v0",
        "theorem actionRep32_variation_bridge_sequence_from_algebraic_deviation_v0",
        "theorem actionRep32_variation_bridge_sequence_from_algebraic_deviation_default_binding_v0",
        "theorem actionRep32_produces_operator_equation_discrete_from_algebraic_deviation_v0",
        "theorem actionRep32_produces_operator_equation_discrete_of_transport_from_algebraic_deviation_v0",
        "theorem actionRep32_produces_operator_equation_discrete_of_el_to_residual_transport_from_algebraic_deviation_v0",
        "def actionRep32_fd_expansion_and_vanishing_to_radial_evaluator_transport_interface_v0",
        "theorem actionRep32_el_to_evalRadial_rep32_cubic_zero_from_fd_expansion_and_vanishing_v0",
        "theorem actionRep32_el_to_evalRadial_rep32_cubic_zero_from_fd_expansion_constructor_v0",
        "theorem actionRep32_el_to_evalRadial_rep32_cubic_zero_from_fd_expansion_constructor_default_binding_v0",
        "theorem actionRep32_el_implies_operator_residual_transport_from_fd_expansion_constructor_of_rac_v0",
        "theorem actionRep32_el_implies_operator_residual_transport_from_fd_expansion_constructor_of_rac_default_binding_v0",
        "theorem actionRep32_operator_residual_transport_from_radial_evaluator_interface_v0",
        "theorem actionRep32_operator_residual_under_bound_from_radial_evaluator_interface_v0",
        "theorem actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_operator_transport_witness_v0",
        "theorem actionRep32_weak_field_poisson_limit_under_default_binding_assumptions_of_operator_transport_witness_v0",
        "theorem actionRep32_weak_field_poisson_limit_under_default_binding_assumptions_of_action_native_transport_constructor_from_fd_expansion_v0",
    ]

    compatibility_progress_tokens = [
        "def actionRep32_probeVariation_zero_v0",
        "def actionRep32_probeState_zero_v0",
        "def evalRadial_from_probe_fd_v0",
        "def evalRadial_from_zero_probe_fd_v0",
        "theorem actionRep32_probe_fd_matches_evalRadial_from_probe_fd_v0",
        "theorem actionRep32_el_core_implies_probe_pcubic_pairing_zero_of_zero_probe_v0",
        "theorem actionRep32_el_to_zero_probe_evaluator_zero_from_fd_expansion_v0",
        "theorem actionRep32_el_implies_operator_residual_transport_from_fd_expansion_v0",
        "theorem actionRep32_el_implies_operator_residual_transport_from_fd_expansion_constructor_v0",
        "theorem actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_bridge_transport_constructor_v0",
        "theorem actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_bridge_transport_from_radial_evaluator_constructor_v0",
        "theorem actionRep32_produces_operator_equation_discrete_of_bridge_witness_constructor_from_algebraic_deviation_v0",
        "theorem actionRep32_operator_residual_transport_of_bridge_witness_constructor_v0",
        "theorem actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_action_native_evaluator_transport_from_fd_expansion_v0",
        "theorem actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_action_native_transport_constructor_from_fd_expansion_v0",
        "theorem actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_bridge_witness_constructor_v0",
    ]

    missing_a2o = [t for t in core_required_a2o_tokens if t not in a2o_text]
    assert not missing_a2o, (
        "Missing core algebraic derivation token(s) in GR01ActionToOperatorDiscrete: "
        + ", ".join(missing_a2o)
    )
    missing_compat = [t for t in compatibility_progress_tokens if t not in a2o_text]
    assert not missing_compat, (
        "Missing compatibility/progress token(s) in GR01ActionToOperatorDiscrete: "
        + ", ".join(missing_compat)
    )
    sig_match = re.search(
        r"theorem\s+"
        r"actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_"
        r"of_action_native_evaluator_transport_from_fd_expansion_v0"
        r"[\s\S]*?:\s*\n\s*WeakFieldPoissonLimitStatement\s*:=\s*by",
        a2o_text,
    )
    assert sig_match is not None, (
        "Missing theorem signature block for the action-native weak-field route token."
    )
    sig_text = sig_match.group(0)
    assert "bridge_witness_constructor" not in sig_text, (
        "Action-native weak-field route signature must not reference bridge witness constructors."
    )
    constructor_routed_block = _theorem_block(
        a2o_text,
        "actionRep32_weak_field_poisson_limit_under_default_binding_assumptions_of_action_native_transport_constructor_from_fd_expansion_v0",
    )
    assert (
        "actionRep32_el_implies_operator_residual_transport_from_fd_expansion_constructor_of_rac_default_binding_from_probe_model_v0"
        in constructor_routed_block
    ), (
        "Canonical constructor-routed weak-field theorem must invoke packaged-probe-model default-binding RAC-premise constructor EL->operator transport token."
    )
    forbidden_old_transport_tokens = [
        "actionRep32_el_implies_operator_residual_transport_from_fd_expansion_constructor_of_rac_v0",
        "actionRep32_el_implies_operator_residual_transport_from_fd_expansion_v0",
        "actionRep32_el_implies_operator_residual_transport_from_fd_expansion_constructor_v0",
    ]
    for tok in forbidden_old_transport_tokens:
        assert tok not in constructor_routed_block, (
            "Canonical constructor-routed weak-field theorem must not route through older EL->transport token: "
            + tok
        )
    assert (
        "actionRep32_weak_field_poisson_limit_under_default_binding_assumptions_of_operator_transport_witness_v0"
        in constructor_routed_block
    ), (
        "Canonical constructor-routed weak-field theorem must close through default-binding operator-transport witness token."
    )
    assert (
        "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_operator_transport_witness_v0"
        not in constructor_routed_block
    ), (
        "Canonical constructor-routed weak-field theorem must not route through quotient-assumptions operator-transport witness wrapper token."
    )
    forbidden_explicit_action_plumbing_tokens = [
        "hAction",
        "hP",
    ]
    for tok in forbidden_explicit_action_plumbing_tokens:
        assert re.search(rf"\b{re.escape(tok)}\b", constructor_routed_block) is None, (
            "Canonical constructor-routed weak-field theorem must not reintroduce explicit action/plumbing token: "
            + tok
        )
    assert "hRAC" in constructor_routed_block, (
        "Canonical constructor-routed weak-field theorem must keep RAC-premise routing explicit."
    )
    assert (
        "actionRep32_el_implies_operator_residual_transport_from_fd_expansion_constructor_v0"
        not in constructor_routed_block
    ), (
        "Canonical constructor-routed weak-field theorem should route through RAC-premise constructor token, not the older explicit-hDevZero constructor token."
    )
    assert (
        "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_action_native_evaluator_transport_from_fd_expansion_v0"
        not in constructor_routed_block
    ), (
        "Canonical constructor-routed weak-field theorem must not route through the older interface-routed weak-field theorem."
    )
    assert (
        "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_action_native_transport_constructor_from_fd_expansion_v0"
        not in constructor_routed_block
    ), (
        "Canonical constructor-routed weak-field theorem must not route through the older quotient-assumption transport-constructor weak-field wrapper theorem."
    )
    forbidden_interface_tokens = [
        "hEvalFromFDExpansionAndVanishing",
        "actionRep32_fd_expansion_and_vanishing_to_radial_evaluator_transport_interface_v0",
    ]
    for tok in forbidden_interface_tokens:
        assert tok not in constructor_routed_block, (
            "Canonical constructor-routed weak-field theorem must avoid interface-shaped transport token: "
            + tok
        )
    forbidden_local_plumbing_tokens = [
        "hDevZero",
        "ActionRep32CubicDeviationZeroAtStep_of_RAC",
    ]
    for tok in forbidden_local_plumbing_tokens:
        assert tok not in constructor_routed_block, (
            "Canonical constructor-routed weak-field theorem must avoid local deviation-plumbing token: "
            + tok
        )
    assert (
        "TOE_GR01_weak_field_poisson_limit_under_default_quotient_assumptions_derived_from_operator_transport_minimal_of_hP"
        not in constructor_routed_block
    ), (
        "Canonical constructor-routed weak-field theorem must not directly call bridge-derived weak-field closure token."
    )
    forbidden_bridge_transport_tokens = [
        "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_bridge_transport_constructor_v0",
        "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_bridge_transport_from_radial_evaluator_constructor_v0",
        "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_bridge_witness_constructor_v0",
    ]
    for tok in forbidden_bridge_transport_tokens:
        assert tok not in constructor_routed_block, (
            "Canonical constructor-routed weak-field theorem must not route through compatibility bridge transport token: "
            + tok
        )
    forbidden_trivial_probe_tokens = [
        "actionRep32_probeVariation_zero_v0",
        "actionRep32_probeState_zero_v0",
        "evalRadial_from_zero_probe_fd_v0",
        "actionRep32_el_to_zero_probe_evaluator_zero_from_fd_expansion_v0",
    ]
    for tok in forbidden_trivial_probe_tokens:
        assert tok not in constructor_routed_block, (
            "Canonical constructor-routed weak-field theorem regressed to trivial zero-probe token: "
            + tok
        )
    assert "hProbePairingModelPackage" in constructor_routed_block, (
        "Canonical constructor-routed weak-field theorem must thread packaged probe-model witness token hProbePairingModelPackage."
    )
    forbidden_probe_plumbing_in_canonical = [
        "hProbeFDMatchesEvaluator",
        "hELCoreImpliesProbePairingZero",
        "probeVariation",
        "probeState",
    ]
    for tok in forbidden_probe_plumbing_in_canonical:
        assert tok not in constructor_routed_block, (
            "Canonical constructor-routed weak-field theorem must avoid direct probe-interface plumbing token: "
            + tok
        )

    default_binding_eval_zero_block = _theorem_block(
        a2o_text,
        "actionRep32_el_to_evalRadial_rep32_cubic_zero_from_fd_expansion_constructor_default_binding_v0",
    )
    required_nontrivial_probe_tokens = [
        "actionRep32_probe_pairing_matches_radial_evaluator_interface_v0",
        "actionRep32_probe_pairing_to_radial_model_assumptions_v0",
        "actionRep32_probe_pairing_matches_radial_evaluator_from_model_assumptions_v0",
        "hProbePairingModel",
        "pairing_zero",
        "hProbePairingMatchesEvaluator",
        "actionRep32_probe_fd_matches_radial_evaluator_from_pairing_and_fd_expansion_v0",
        "actionRep32_probe_fd_matches_radial_evaluator_interface_v0",
        "actionRep32_el_core_implies_probe_pcubic_pairing_zero_interface_v0",
        "hProbeFDMatchesEvaluator",
    ]
    missing_nontrivial_probe = [
        tok for tok in required_nontrivial_probe_tokens if tok not in default_binding_eval_zero_block
    ]
    assert not missing_nontrivial_probe, (
        "Default-binding evaluator-zero constructor theorem is missing required "
        "nontrivial probe-interface token(s): " + ", ".join(missing_nontrivial_probe)
    )
    for tok in forbidden_trivial_probe_tokens:
        assert tok not in default_binding_eval_zero_block, (
            "Default-binding evaluator-zero constructor theorem regressed to trivial zero-probe token: "
            + tok
        )

    compatibility_constructor_block = _theorem_block(
        a2o_text,
        "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_action_native_transport_constructor_from_fd_expansion_v0",
    )
    required_compatibility_constructor_tokens = [
        "hRAC",
        "hELToEvalZero",
        "hWeakFieldUniformBound",
        "actionRep32_el_implies_operator_residual_transport_from_fd_expansion_constructor_of_rac_default_binding_v0",
        "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_operator_transport_witness_v0",
    ]
    missing_compatibility_constructor_tokens = [
        tok
        for tok in required_compatibility_constructor_tokens
        if tok not in compatibility_constructor_block
    ]
    assert not missing_compatibility_constructor_tokens, (
        "Compatibility quotient-assumptions constructor weak-field theorem is "
        "missing required token(s): "
        + ", ".join(missing_compatibility_constructor_tokens)
    )
    forbidden_compatibility_constructor_tokens = [
        "actionRep32_weak_field_poisson_limit_under_default_binding_assumptions_of_operator_transport_witness_v0",
        "actionRep32_action_default_binding",
        "P_rep32_def",
    ]
    for tok in forbidden_compatibility_constructor_tokens:
        assert tok not in compatibility_constructor_block, (
            "Compatibility quotient-assumptions constructor weak-field theorem "
            "must avoid default-binding wrapper/marker token: " + tok
        )
    retired_compatibility_constructor_tokens = [
        "hAction",
        "hP",
    ]
    for tok in retired_compatibility_constructor_tokens:
        assert re.search(rf"\b{re.escape(tok)}\b", compatibility_constructor_block) is None, (
            "Compatibility quotient-assumptions constructor weak-field theorem "
            "must not reintroduce retired explicit quotient marker token: " + tok
        )

    quotient_operator_witness_block = _theorem_block(
        a2o_text,
        "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_operator_transport_witness_v0",
    )
    compat_core_operator_witness_block = _theorem_block(
        a2o_text,
        "actionRep32_weak_field_poisson_limit_from_operator_transport_compat_core_v0",
    )
    canonical_core_operator_witness_block = _theorem_block(
        a2o_text,
        "actionRep32_weak_field_poisson_limit_from_operator_transport_core_v0",
    )
    minimal_without_hP_block = _theorem_block(
        a2o_text,
        "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_minimal_without_hP_premise_v0",
    )
    required_quotient_operator_witness_tokens = [
        "hRAC",
        "P_rep32_def",
        "hWeakFieldUniformBound",
        "gr01_projection_map_well_formed_from_uniform_bound_v0",
        "weakFieldTruncationSound_default_v0",
        "actionRep32_weak_field_poisson_limit_from_operator_transport_compat_core_v0",
    ]
    missing_quotient_operator_witness = [
        tok
        for tok in required_quotient_operator_witness_tokens
        if tok not in quotient_operator_witness_block
    ]
    assert not missing_quotient_operator_witness, (
        "Quotient operator-transport witness theorem is missing required "
        "uniform-bound/local-constructor token(s): "
        + ", ".join(missing_quotient_operator_witness)
    )
    retired_quotient_operator_witness_tokens = [
        "hAction",
        "hP",
    ]
    for tok in retired_quotient_operator_witness_tokens:
        assert re.search(rf"\b{re.escape(tok)}\b", quotient_operator_witness_block) is None, (
            "Quotient operator-transport witness theorem must not reintroduce "
            "retired explicit quotient marker token: " + tok
        )
    assert (
        "TOE_GR01_weak_field_poisson_limit_under_default_quotient_assumptions_derived_from_operator_transport_minimal_of_hP"
        not in quotient_operator_witness_block
    ), (
        "Quotient operator-transport witness theorem must not directly call bridge-labeled weak-field closure token."
    )
    for block_name, block_text in {
        "compat_core": compat_core_operator_witness_block,
        "canonical_core": canonical_core_operator_witness_block,
    }.items():
        for tok in [
            "ELImpliesDiscretePoissonResidual",
            "OperatorToDiscreteResidual",
            "mkWeakFieldProjectionFromCore",
            "weakFieldResidualFromProjection",
            "EL_toe_rep32_equals_Pcubic_under_default_quotient_assumptions",
            "actionRep32_action_default_binding",
        ]:
            assert tok in block_text, (
                "Operator-transport core closure block is missing required direct-closure token "
                + tok
                + " in "
                + block_name
            )
        assert (
            "TOE_GR01_weak_field_poisson_limit_under_default_quotient_assumptions_derived_from_operator_transport_minimal_of_hP"
            not in block_text
        ), (
            "Operator-transport core closure block must not call bridge-derived weak-field closure token in "
            + block_name
        )
        assert (
            "TOE_GR01_weak_field_poisson_limit_under_default_quotient_assumptions_minimal_of_hP"
            not in block_text
        ), (
            "Operator-transport core closure block must not directly call minimal weak-field closure token in "
            + block_name
        )
        assert (
            "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_minimal_without_hP_premise_v0"
            not in block_text
        ), (
            "Operator-transport core closure block must not fallback to minimal-without-hP helper token in "
            + block_name
        )
        assert "P_rep32_def" not in block_text, (
            "Operator-transport core closure block must not fallback to scaffold token P_rep32_def in "
            + block_name
        )
        assert (
            "actionRep32_el_core_equals_pcubic_from_cubic_lane_default_binding_v0"
            not in block_text
        ), (
            "Operator-transport core closure block must not call cubic-lane default-binding EL-core helper token in "
            + block_name
        )
        assert (
            "EL_toe_rep32_equals_Pcubic_under_default_binding_assumptions"
            not in block_text
        ), (
            "Operator-transport core closure block must not call older default-binding EL-core equality token in "
            + block_name
        )
        assert (
            "actionRep32_el_core_equals_pcubic_from_action_binding_and_rac_v0"
            not in block_text
        ), (
            "Operator-transport core closure block must not call helper EL-core equality token in "
            + block_name
        )
    for tok in [
        "mkWeakFieldProjectionFromCore",
        "weakFieldResidualFromProjection",
        "EL_toe_rep32_equals_Pcubic_under_default_quotient_assumptions",
        "actionRep32_action_default_binding",
    ]:
        assert tok in minimal_without_hP_block, (
            "Minimal-without-hP closure theorem is missing required direct projection token: "
            + tok
        )
    assert (
        "Rep32_cubic_lane_default_binding"
        not in minimal_without_hP_block
    ), (
        "Minimal-without-hP closure theorem must not fallback to direct cubic-lane bundle token."
    )
    assert (
        "actionRep32_el_core_equals_pcubic_from_cubic_lane_default_binding_v0"
        not in minimal_without_hP_block
    ), (
        "Minimal-without-hP closure theorem must not fallback to cubic-lane default-binding EL-core helper token."
    )
    assert (
        "EL_toe_rep32_equals_Pcubic_under_default_binding_assumptions"
        not in minimal_without_hP_block
    ), (
        "Minimal-without-hP closure theorem must not fallback to older default-binding EL-core equality token."
    )
    assert (
        "actionRep32_el_core_equals_pcubic_from_action_binding_and_rac_v0"
        not in minimal_without_hP_block
    ), (
        "Minimal-without-hP closure theorem must not fallback to helper EL-core equality token."
    )
    assert "EL_toe_eq_Pcubic_rep32" not in minimal_without_hP_block, (
        "Minimal-without-hP closure theorem must not fallback to scaffold equality token EL_toe_eq_Pcubic_rep32."
    )
    assert "P_rep32_def" not in minimal_without_hP_block, (
        "Minimal-without-hP closure theorem must not fallback to P_rep32_def token."
    )

    legacy_evaluator_compat_block = _theorem_block(
        a2o_text,
        "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_action_native_evaluator_transport_from_fd_expansion_v0",
    )
    required_legacy_evaluator_compat_tokens = [
        "actionRep32_action_default_binding",
        "P_rep32_def",
        "hRAC",
        "hWeakFieldUniformBound",
        "actionRep32_el_implies_operator_residual_transport_from_fd_expansion_v0",
        "actionRep32_weak_field_poisson_limit_under_default_binding_assumptions_of_operator_transport_witness_v0",
    ]
    missing_legacy_evaluator_compat = [
        tok
        for tok in required_legacy_evaluator_compat_tokens
        if tok not in legacy_evaluator_compat_block
    ]
    assert not missing_legacy_evaluator_compat, (
        "Legacy quotient action-native evaluator transport theorem is missing "
        "required reduced-marker token(s): "
        + ", ".join(missing_legacy_evaluator_compat)
    )
    retired_legacy_evaluator_compat_tokens = [
        "hAction",
        "hP",
    ]
    for tok in retired_legacy_evaluator_compat_tokens:
        assert re.search(rf"\b{re.escape(tok)}\b", legacy_evaluator_compat_block) is None, (
            "Legacy quotient action-native evaluator transport theorem must not "
            "reintroduce retired explicit quotient marker token: " + tok
        )

    bridge_transport_wrapper_block = _theorem_block(
        a2o_text,
        "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_bridge_transport_constructor_v0",
    )
    required_bridge_transport_wrapper_tokens = [
        "hRAC",
        "hWeakFieldUniformBound",
        "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_operator_transport_witness_v0",
    ]
    missing_bridge_transport_wrapper = [
        tok
        for tok in required_bridge_transport_wrapper_tokens
        if tok not in bridge_transport_wrapper_block
    ]
    assert not missing_bridge_transport_wrapper, (
        "Bridge transport compatibility wrapper is missing required reduced-marker "
        "token(s): "
        + ", ".join(missing_bridge_transport_wrapper)
    )
    retired_bridge_transport_wrapper_tokens = [
        "hAction",
        "hP",
    ]
    for tok in retired_bridge_transport_wrapper_tokens:
        assert re.search(rf"\b{re.escape(tok)}\b", bridge_transport_wrapper_block) is None, (
            "Bridge transport compatibility wrapper must not reintroduce retired "
            "explicit quotient marker token: " + tok
        )

    bridge_witness_wrapper_block = _theorem_block(
        a2o_text,
        "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_bridge_witness_constructor_v0",
    )
    required_bridge_witness_wrapper_tokens = [
        "hRAC",
        "hWeakFieldUniformBound",
        "hELImpliesOperatorResidualUnderBound",
        "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_bridge_transport_from_radial_evaluator_constructor_v0",
    ]
    missing_bridge_witness_wrapper = [
        tok
        for tok in required_bridge_witness_wrapper_tokens
        if tok not in bridge_witness_wrapper_block
    ]
    assert not missing_bridge_witness_wrapper, (
        "Bridge witness compatibility wrapper is missing required reduced-marker "
        "token(s): "
        + ", ".join(missing_bridge_witness_wrapper)
    )
    retired_bridge_witness_wrapper_tokens = [
        "hAction",
        "hP",
    ]
    for tok in retired_bridge_witness_wrapper_tokens:
        assert re.search(rf"\b{re.escape(tok)}\b", bridge_witness_wrapper_block) is None, (
            "Bridge witness compatibility wrapper must not reintroduce retired "
            "explicit quotient marker token: " + tok
        )

    bridge_eval_wrapper_block = _theorem_block(
        a2o_text,
        "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_bridge_transport_from_radial_evaluator_constructor_v0",
    )
    required_bridge_eval_wrapper_tokens = [
        "hRAC",
        "hWeakFieldUniformBound",
        "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_action_native_transport_constructor_from_fd_expansion_v0",
    ]
    missing_bridge_eval_wrapper = [
        tok
        for tok in required_bridge_eval_wrapper_tokens
        if tok not in bridge_eval_wrapper_block
    ]
    assert not missing_bridge_eval_wrapper, (
        "Bridge-from-radial-evaluator compatibility wrapper is missing required "
        "reduced-marker token(s): "
        + ", ".join(missing_bridge_eval_wrapper)
    )
    retired_bridge_eval_wrapper_tokens = [
        "hAction",
        "hP",
    ]
    for tok in retired_bridge_eval_wrapper_tokens:
        assert re.search(rf"\b{re.escape(tok)}\b", bridge_eval_wrapper_block) is None, (
            "Bridge-from-radial-evaluator compatibility wrapper must not "
            "reintroduce retired explicit quotient marker token: " + tok
        )

    compatibility_wrapper_names = [
        "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_operator_transport_witness_v0",
        "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_action_native_evaluator_transport_from_fd_expansion_v0",
        "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_action_native_transport_constructor_from_fd_expansion_v0",
        "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_bridge_transport_constructor_v0",
        "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_bridge_witness_constructor_v0",
        "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_bridge_transport_from_radial_evaluator_constructor_v0",
    ]
    compatibility_wrapper_blocks = {
        name: _theorem_block(a2o_text, name) for name in compatibility_wrapper_names
    }
    for name, block in compatibility_wrapper_blocks.items():
        assert "hWeakFieldUniformBound" in block, (
            "Compatibility weak-field wrapper must keep explicit uniform-bound "
            "threading token hWeakFieldUniformBound: " + name
        )
        forbidden_legacy_wrapper_param_patterns = [
            r"\(hProjectionMapWellFormed\s*:",
            r"\(hWeakFieldTruncationSound\s*:",
            r"\(hAction\s*:",
            r"\(hP\s*:",
        ]
        for pattern in forbidden_legacy_wrapper_param_patterns:
            assert re.search(pattern, block) is None, (
                "Compatibility weak-field wrapper must avoid retired legacy "
                "signature parameter pattern "
                + pattern
                + ": "
                + name
            )

    default_binding_transport_block = _theorem_block(
        a2o_text,
        "actionRep32_el_implies_operator_residual_transport_from_fd_expansion_constructor_of_rac_default_binding_v0",
    )
    required_default_binding_transport_tokens = [
        "actionRep32_action_default_binding",
        "P_rep32_def",
        "hRAC",
        "hELToEvalZero",
        "actionRep32_operator_residual_transport_from_radial_evaluator_interface_v0",
    ]
    missing_default_binding_transport_tokens = [
        tok
        for tok in required_default_binding_transport_tokens
        if tok not in default_binding_transport_block
    ]
    assert not missing_default_binding_transport_tokens, (
        "Default-binding RAC transport constructor theorem is missing required "
        "closure token(s): " + ", ".join(missing_default_binding_transport_tokens)
    )
    assert (
        "actionRep32_el_implies_operator_residual_transport_from_fd_expansion_constructor_of_rac_v0"
        not in default_binding_transport_block
    ), (
        "Default-binding RAC transport constructor theorem must not route through "
        "the older RAC-wrapper transport theorem."
    )
    for tok in forbidden_bridge_transport_tokens:
        assert tok not in default_binding_transport_block, (
            "Default-binding RAC transport constructor theorem must not route through compatibility bridge transport token: "
            + tok
        )

    default_binding_operator_witness_block = _theorem_block(
        a2o_text,
        "actionRep32_weak_field_poisson_limit_under_default_binding_assumptions_of_operator_transport_witness_v0",
    )
    required_default_binding_operator_witness_tokens = [
        "actionRep32_action_default_binding",
        "hRAC",
        "P_rep32_def",
        "hWeakFieldUniformBound",
        "gr01_projection_map_well_formed_from_uniform_bound_v0",
        "weakFieldTruncationSound_default_v0",
        "hOperatorTransport",
        "actionRep32_weak_field_poisson_limit_from_operator_transport_core_v0",
    ]
    missing_default_binding_operator_witness = [
        tok
        for tok in required_default_binding_operator_witness_tokens
        if tok not in default_binding_operator_witness_block
    ]
    assert not missing_default_binding_operator_witness, (
        "Default-binding operator-transport witness theorem is missing required "
        "token(s): " + ", ".join(missing_default_binding_operator_witness)
    )
    assert (
        "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_operator_transport_witness_v0"
        not in default_binding_operator_witness_block
    ), (
        "Default-binding operator-transport witness theorem must not route through "
        "the older quotient-assumptions operator-transport witness wrapper theorem."
    )
    assert (
        "TOE_GR01_weak_field_poisson_limit_under_default_quotient_assumptions_derived_from_operator_transport_minimal_of_hP"
        not in default_binding_operator_witness_block
    ), (
        "Default-binding operator-transport witness theorem must not directly call bridge-labeled weak-field closure token."
    )
    for tok in forbidden_explicit_action_plumbing_tokens:
        assert (
            re.search(rf"\b{re.escape(tok)}\b", default_binding_operator_witness_block)
            is None
        ), (
            "Default-binding operator-transport witness theorem must not reintroduce explicit action/plumbing token: "
            + tok
        )

    canonical_blocks_for_compat_route_guard = {
        "constructor_routed": constructor_routed_block,
        "default_binding_transport": default_binding_transport_block,
        "default_binding_operator_witness": default_binding_operator_witness_block,
    }
    forbidden_compat_route_patterns = [
        r"actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_"
        r"(?:bridge_transport_constructor|bridge_witness_constructor|bridge_transport_from_radial_evaluator_constructor|"
        r"action_native_transport_constructor_from_fd_expansion|action_native_evaluator_transport_from_fd_expansion|"
        r"operator_transport_witness)_v0",
    ]
    for block_name, block_text in canonical_blocks_for_compat_route_guard.items():
        for pattern in forbidden_compat_route_patterns:
            assert re.search(pattern, block_text) is None, (
                "Canonical block regressed to compatibility weak-field wrapper route pattern "
                + pattern
                + " in "
                + block_name
            )

    legacy_signature_param_patterns = [
        r"\(hAction\s*:",
        r"\(hP\s*:",
        r"\(hProjectionMapWellFormed\s*:",
        r"\(hWeakFieldTruncationSound\s*:",
    ]
    compact_policy_table = [
        {
            "name": "canonical:constructor_routed",
            "block": constructor_routed_block,
            "required": [
                "actionRep32_el_implies_operator_residual_transport_from_fd_expansion_constructor_of_rac_default_binding_from_probe_model_v0",
                "actionRep32_weak_field_poisson_limit_under_default_binding_assumptions_of_operator_transport_witness_v0",
            ],
            "forbidden": [
                "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_operator_transport_witness_v0",
                "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_bridge_transport_constructor_v0",
                "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_bridge_witness_constructor_v0",
            ],
            "forbidden_params": legacy_signature_param_patterns,
        },
        {
            "name": "canonical:default_binding_transport",
            "block": default_binding_transport_block,
            "required": [
                "actionRep32_action_default_binding",
                "P_rep32_def",
            ],
            "forbidden": [
                "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_bridge_transport_constructor_v0",
                "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_bridge_witness_constructor_v0",
            ],
            "forbidden_params": legacy_signature_param_patterns,
        },
        {
            "name": "canonical:default_binding_operator_witness",
            "block": default_binding_operator_witness_block,
            "required": [
                "actionRep32_action_default_binding",
                "P_rep32_def",
                "hWeakFieldUniformBound",
            ],
            "forbidden": [
                "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_operator_transport_witness_v0",
                "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_bridge_transport_constructor_v0",
                "TOE_GR01_weak_field_poisson_limit_under_default_quotient_assumptions_derived_from_operator_transport_minimal_of_hP",
            ],
            "forbidden_params": legacy_signature_param_patterns,
        },
        {
            "name": "compat:action_native_transport_constructor",
            "block": compatibility_constructor_block,
            "required": ["hWeakFieldUniformBound"],
            "forbidden": [],
            "forbidden_params": legacy_signature_param_patterns,
        },
        {
            "name": "compat:operator_transport_witness",
            "block": quotient_operator_witness_block,
            "required": ["hWeakFieldUniformBound"],
            "forbidden": [
                "TOE_GR01_weak_field_poisson_limit_under_default_quotient_assumptions_derived_from_operator_transport_minimal_of_hP"
            ],
            "forbidden_params": legacy_signature_param_patterns,
        },
        {
            "name": "compat:bridge_transport",
            "block": bridge_transport_wrapper_block,
            "required": ["hWeakFieldUniformBound"],
            "forbidden": [],
            "forbidden_params": legacy_signature_param_patterns,
        },
        {
            "name": "compat:bridge_witness",
            "block": bridge_witness_wrapper_block,
            "required": ["hWeakFieldUniformBound"],
            "forbidden": [],
            "forbidden_params": legacy_signature_param_patterns,
        },
        {
            "name": "compat:bridge_transport_from_eval",
            "block": bridge_eval_wrapper_block,
            "required": ["hWeakFieldUniformBound"],
            "forbidden": [],
            "forbidden_params": legacy_signature_param_patterns,
        },
        {
            "name": "compat:action_native_eval_legacy",
            "block": legacy_evaluator_compat_block,
            "required": ["hWeakFieldUniformBound", "actionRep32_action_default_binding", "P_rep32_def"],
            "forbidden": [],
            "forbidden_params": legacy_signature_param_patterns,
        },
    ]
    for row in compact_policy_table:
        _assert_block_policy(
            row["name"],
            row["block"],
            required_tokens=row["required"],
            forbidden_tokens=row["forbidden"],
            forbidden_param_patterns=row["forbidden_params"],
        )


def test_gr01_full_derivation_progress_floor_nonzero_action_and_pinned_g() -> None:
    action_text = _read(ACTION_DEF_PATH)
    first_variation_text = _read(FIRST_VARIATION_PATH)
    discharge_text = _read(DISCHARGE_PCUBIC_PATH)

    assert "action := fun _ => 0" not in action_text, (
        "Regressed to zero-action placeholder in ActionRep32Def."
    )
    assert "action := fun ψ => pairingRep32' (P_rep32 ψ) ψ" in action_text, (
        "Expected constructive P-bound scaffold action token is missing in ActionRep32Def."
    )
    assert "axiom P_rep32" not in first_variation_text, (
        "Regressed to axiomatic P_rep32 in FirstVariationRep32Def."
    )
    assert "def P_rep32 : FieldRep32 -> FieldRep32 :=" in first_variation_text, (
        "Expected explicit default P_rep32 definition header is missing."
    )
    assert "P_cubic_rep32_core declared_g_rep32_default" in first_variation_text, (
        "Expected core-cubic default binding token for P_rep32 is missing."
    )
    assert "axiom declared_g_rep32" not in discharge_text, (
        "Regressed to axiomatic declared_g_rep32 in DischargeELMatchesFN01Rep32Pcubic."
    )
    assert "abbrev declared_g_rep32 : ℂ := declared_g_rep32_default" in discharge_text, (
        "Expected default-binding alias for declared_g_rep32 is missing."
    )
    assert "axiom P_rep32_def" not in discharge_text, (
        "Regressed to axiomatic P_rep32_def in DischargeELMatchesFN01Rep32Pcubic."
    )
    assert "theorem P_rep32_def : P_rep32 = P_cubic_rep32 declared_g_rep32 := by" in discharge_text, (
        "Expected theorem-based P_rep32_def token is missing."
    )
    assert "theorem EL_toe_eq_Pcubic_rep32_of_hP" in discharge_text, (
        "Expected explicit-of_hP EL-to-Pcubic theorem token is missing."
    )
    lane_text = _read(ACTION_CUBIC_LANE_PATH)
    assert "theorem actionRep32_action_default_binding" in lane_text, (
        "Expected theorem-based action default-binding token is missing."
    )


def test_gr01_full_derivation_row_and_adjudication_are_consistent() -> None:
    results_text = _read(RESULTS_PATH)
    status = _result_status_for("TOE-GR-FULL-01", results_text)
    adjudication = _full_derivation_adjudication(_read(TARGET_DOC))

    if status.startswith("B-"):
        assert adjudication == "NOT_YET_DISCHARGED_v0", (
            "TOE-GR-FULL-01 is blocked but full-derivation adjudication is not "
            "NOT_YET_DISCHARGED_v0."
        )
    if adjudication == "DISCHARGED_v0_DISCRETE":
        assert not status.startswith("B-"), (
            "FULL_DERIVATION_ADJUDICATION is discharged, but TOE-GR-FULL-01 is still blocked."
        )


def test_gr01_full_derivation_discharge_flip_is_gated() -> None:
    adjudication = _full_derivation_adjudication(_read(TARGET_DOC))
    if adjudication != "DISCHARGED_v0_DISCRETE":
        return

    required_theorem_tokens = [
        "theorem actionRep32_el_implies_operator_residual_transport_from_fd_expansion_constructor_of_rac_v0",
        "theorem actionRep32_weak_field_poisson_limit_under_default_binding_assumptions_of_action_native_transport_constructor_from_fd_expansion_v0",
    ]
    lean_text = _read(A2O_PATH)
    missing = [tok for tok in required_theorem_tokens if tok not in lean_text]
    assert not missing, (
        "Cannot flip FULL_DERIVATION_ADJUDICATION to DISCHARGED_v0_DISCRETE "
        "without required theorem token(s): " + ", ".join(missing)
    )

    compat_core_block = _theorem_block(
        lean_text,
        "actionRep32_weak_field_poisson_limit_from_operator_transport_compat_core_v0",
    )
    canonical_core_block = _theorem_block(
        lean_text,
        "actionRep32_weak_field_poisson_limit_from_operator_transport_core_v0",
    )
    forbidden_canonical_fallback_tokens = [
        "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_minimal_without_hP_premise_v0",
        "TOE_GR01_weak_field_poisson_limit_under_default_quotient_assumptions_derived_from_operator_transport_minimal_of_hP",
        "TOE_GR01_weak_field_poisson_limit_under_default_quotient_assumptions_minimal_of_hP",
        "P_rep32_def",
    ]
    for block_name, block_text in {
        "compat_core": compat_core_block,
        "canonical_core": canonical_core_block,
    }.items():
        present = [tok for tok in forbidden_canonical_fallback_tokens if tok in block_text]
        assert not present, (
            "Cannot flip FULL_DERIVATION_ADJUDICATION to DISCHARGED_v0_DISCRETE while canonical core fallback token(s) remain in "
            + block_name
            + ": "
            + ", ".join(present)
        )

    forbidden_tokens_by_file = {
        ACTION_DEF_PATH: ["action := fun _ => 0"],
        FIRST_VARIATION_PATH: ["axiom P_rep32"],
        DISCHARGE_PCUBIC_PATH: ["axiom declared_g_rep32", "axiom P_rep32_def"],
    }
    for path, forbidden in forbidden_tokens_by_file.items():
        text = _read(path)
        present = [tok for tok in forbidden if tok in text]
        assert not present, (
            "Cannot flip FULL_DERIVATION_ADJUDICATION to DISCHARGED_v0_DISCRETE "
            f"while blocker token(s) remain in {path}: " + ", ".join(present)
        )


def test_gr01_action_native_transport_route_is_anti_circular() -> None:
    lean_text = _read(A2O_PATH)

    el_to_eval_block = _theorem_block(
        lean_text,
        "actionRep32_el_to_evalRadial_rep32_cubic_zero_from_fd_expansion_and_vanishing_v0",
    )
    transport_block = _theorem_block(
        lean_text,
        "actionRep32_el_implies_operator_residual_transport_from_fd_expansion_v0",
    )
    weak_field_block = _theorem_block(
        lean_text,
        "actionRep32_weak_field_poisson_limit_under_default_quotient_assumptions_of_action_native_evaluator_transport_from_fd_expansion_v0",
    )
    constructor_block = _theorem_block(
        lean_text,
        "actionRep32_fd_expansion_and_vanishing_to_radial_evaluator_transport_constructor_v0",
    )
    constructor_of_rac_block = _theorem_block(
        lean_text,
        "actionRep32_el_implies_operator_residual_transport_from_fd_expansion_constructor_of_rac_v0",
    )
    constructor_of_rac_default_binding_block = _theorem_block(
        lean_text,
        "actionRep32_el_implies_operator_residual_transport_from_fd_expansion_constructor_of_rac_default_binding_v0",
    )
    constructor_of_rac_default_binding_from_probe_model_block = _theorem_block(
        lean_text,
        "actionRep32_el_implies_operator_residual_transport_from_fd_expansion_constructor_of_rac_default_binding_from_probe_model_v0",
    )

    forbidden_bridge_semantics = [
        "ELImpliesOperatorResidualUnderBound",
        "ELImpliesDiscretePoissonResidual",
        "mk_ELImpliesDiscretePoissonResidual_from_bridge_v0",
        "gr01_operator_residual_transport_from_bound_bridge_assumptions",
        "actionRep32_operator_residual_transport_of_bridge_witness_constructor_v0",
    ]

    for tok in forbidden_bridge_semantics:
        assert tok not in el_to_eval_block, (
            "Action-native evaluator theorem regressed to bridge semantics token: "
            + tok
        )
        assert tok not in transport_block, (
            "Action-native transport theorem regressed to bridge semantics token: "
            + tok
        )
        assert tok not in weak_field_block, (
            "Action-native weak-field theorem regressed to bridge semantics token: "
            + tok
        )
        assert tok not in constructor_block, (
            "Action-native transport constructor regressed to bridge semantics token: "
            + tok
        )
        assert tok not in constructor_of_rac_block, (
            "RAC-premise EL->transport constructor regressed to bridge semantics token: "
            + tok
        )
        assert tok not in constructor_of_rac_default_binding_block, (
            "Default-binding RAC-premise EL->transport constructor regressed to bridge semantics token: "
            + tok
        )
        assert tok not in constructor_of_rac_default_binding_from_probe_model_block, (
            "Packaged-probe-model default-binding RAC-premise EL->transport constructor regressed to bridge semantics token: "
            + tok
        )

    required_constructor_of_rac_tokens = [
        "hRAC",
        "hProbeFDMatchesEvaluator",
        "hELCoreImpliesProbePairingZero",
        "actionRep32_el_implies_operator_residual_transport_from_fd_expansion_constructor_v0",
    ]
    missing_constructor_of_rac = [
        tok for tok in required_constructor_of_rac_tokens if tok not in constructor_of_rac_block
    ]
    assert not missing_constructor_of_rac, (
        "RAC-premise EL->transport constructor is missing required token(s): "
        + ", ".join(missing_constructor_of_rac)
    )

    required_constructor_of_rac_default_binding_tokens = [
        "actionRep32_action_default_binding",
        "P_rep32_def",
        "hRAC",
        "hELToEvalZero",
        "actionRep32_operator_residual_transport_from_radial_evaluator_interface_v0",
    ]
    missing_constructor_of_rac_default_binding = [
        tok
        for tok in required_constructor_of_rac_default_binding_tokens
        if tok not in constructor_of_rac_default_binding_block
    ]
    assert not missing_constructor_of_rac_default_binding, (
        "Default-binding RAC-premise EL->transport constructor is missing required token(s): "
        + ", ".join(missing_constructor_of_rac_default_binding)
    )
    assert (
        "actionRep32_el_implies_operator_residual_transport_from_fd_expansion_constructor_of_rac_v0"
        not in constructor_of_rac_default_binding_block
    ), (
        "Default-binding RAC-premise EL->transport constructor must not route through "
        "the older RAC-wrapper transport theorem."
    )
    assert (
        "actionRep32_el_implies_operator_residual_transport_from_fd_expansion_constructor_v0"
        not in constructor_of_rac_default_binding_block
    ), (
        "Default-binding RAC-premise EL->transport constructor must not route through "
        "the older explicit-hDevZero constructor theorem."
    )
    forbidden_probe_interface_plumbing = [
        "hProbeFDMatchesEvaluator",
        "hELCoreImpliesProbePairingZero",
        "probeVariation",
        "probeState",
    ]
    for tok in forbidden_probe_interface_plumbing:
        assert tok not in constructor_of_rac_default_binding_block, (
            "Default-binding RAC-premise EL->transport constructor must not carry retired probe-interface plumbing token: "
            + tok
        )

    forbidden_constructor_of_rac_tokens = [
        "actionRep32_fd_expansion_and_vanishing_to_radial_evaluator_transport_interface_v0",
        "hEvalFromFDExpansionAndVanishing",
    ]
    for tok in forbidden_constructor_of_rac_tokens:
        assert tok not in constructor_of_rac_block, (
            "RAC-premise EL->transport constructor must avoid interface-shaped shortcut token: "
            + tok
        )
        assert tok not in constructor_of_rac_default_binding_block, (
            "Default-binding RAC-premise EL->transport constructor must avoid interface-shaped shortcut token: "
            + tok
        )

    required_constructor_of_rac_default_binding_from_probe_model_tokens = [
        "hProbePairingModelPackage",
        "actionRep32_el_to_evalRadial_rep32_cubic_zero_from_fd_expansion_constructor_default_binding_v0",
        "actionRep32_operator_residual_transport_from_radial_evaluator_interface_v0",
    ]
    missing_constructor_of_rac_default_binding_from_probe_model = [
        tok
        for tok in required_constructor_of_rac_default_binding_from_probe_model_tokens
        if tok not in constructor_of_rac_default_binding_from_probe_model_block
    ]
    assert not missing_constructor_of_rac_default_binding_from_probe_model, (
        "Packaged-probe-model default-binding RAC-premise EL->transport constructor is missing required token(s): "
        + ", ".join(missing_constructor_of_rac_default_binding_from_probe_model)
    )
    assert (
        "actionRep32_el_implies_operator_residual_transport_from_fd_expansion_constructor_of_rac_default_binding_v0"
        not in constructor_of_rac_default_binding_from_probe_model_block
    ), (
        "Packaged-probe-model default-binding RAC-premise EL->transport constructor must not delegate through the legacy default-binding RAC transport constructor theorem."
    )

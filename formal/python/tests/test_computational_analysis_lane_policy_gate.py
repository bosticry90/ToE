from __future__ import annotations

import json
from pathlib import Path
from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
GROUNDING_PATH = REPO_ROOT / "formal" / "docs" / "release" / "GROUNDED_SPECULATION_POSTURE_STANDARD_v0.md"
AUTH_CLASS_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "COMPUTATIONAL_ANALYSIS_BOUNDED_AUTHORIZATION_CLASS_20260416_v0.json"
)
LANE_POLICY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "COMPUTATIONAL_ANALYSIS_LANE_EXECUTION_POLICY_20260416_v0.md"
)
EXECUTION_PLAN_PATH = REPO_ROOT / "formal" / "docs" / "release" / "FOUNDATIONAL_DERIVATION_CHAIN_EXECUTION_PLAN_v0.md"
README_PATH = REPO_ROOT / "README.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
DORMANCY_PATH = REPO_ROOT / "formal" / "docs" / "release" / "SCIENCE_CONTROLLED_DORMANCY_PROTOCOL_20260412_v0.json"
RESTART_PATH = REPO_ROOT / "formal" / "docs" / "release" / "SCIENCE_RESTART_TRIGGER_CONTRACT_20260412_v0.json"


GROUNDING_TOKENS = (
    "GROUNDED_SPECULATION_POSTURE_STATUS_v0: ACTIVE_NONLIVE_NONCLAIM",
    "GROUNDED_SPECULATION_POSTURE_RULE_v0: GROUNDED_SPECULATION_IS_MODEL_CONDITIONED_BOUNDED_AND_FALSIFIABLE_NOT_A_REALITY_CLAIM",
    "GROUNDED_SPECULATION_POSTURE_ALLOWED_OUTPUTS_v0: RETAIN_PRUNE_INCONCLUSIVE_RANKING_SENSITIVITY_AND_COMPARATOR_DESIGN_ONLY",
    "GROUNDED_SPECULATION_POSTURE_PROHIBITED_OUTPUTS_v0: NO_EXTERNAL_TRUTH_CLAIM_NO_LANE_REOPEN_NO_PACKET_AUTHORIZATION_NO_BLOCKER_MOVEMENT_CLAIM",
)

LANE_POLICY_TOKENS = (
    "COMPUTATIONAL_ANALYSIS_LANE_STATUS_v0: ACTIVE_NONLIVE_NONCLAIM",
    "COMPUTATIONAL_ANALYSIS_AUTHORIZATION_CLASS_v0: AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS",
    "COMPUTATIONAL_ANALYSIS_SCOPE_RULE_v0: BOUNDED_SHADOW_NUMERICS_SENSITIVITY_SCANS_STABILITY_SUMMARIES_AND_COMPARATOR_SCORING_ONLY",
    "COMPUTATIONAL_ANALYSIS_DORMANCY_RULE_v0: NOT_EQUIVALENT_TO_LANE_REOPEN_OR_NEW_PACKET_EXECUTION_UNDER_P75_P76_P77",
    "COMPUTATIONAL_ANALYSIS_PACKET_RULE_v0: IF_STRUCTURED_AS_A_PACKET_RESULT_MUST_TERMINATE_AT_INCONCLUSIVE_OR_DESIGN_ONLY_UNLESS_SEPARATELY_AUTHORIZED",
    "COMPUTATIONAL_ANALYSIS_PROMOTION_RULE_v0: RESULTS_CANNOT_ADVANCE_CANONICAL_PHYSICS_STATUS_OR_RESTART_AUTHORIZATION",
    "COMPUTATIONAL_ANALYSIS_GATE_v0: formal/python/tests/test_computational_analysis_lane_policy_gate.py",
)


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_computational_analysis_policy_surfaces_have_required_tokens() -> None:
    grounding_text = _read(GROUNDING_PATH)
    lane_policy_text = _read(LANE_POLICY_PATH)

    for token in GROUNDING_TOKENS:
        assert token in grounding_text
    for token in LANE_POLICY_TOKENS:
        assert token in lane_policy_text


def test_bounded_authorization_class_is_fail_closed() -> None:
    payload = json.loads(_read(AUTH_CLASS_PATH))
    contract = payload["bounded_authorization_class"]

    assert contract["authorization_class_id"] == "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS"
    assert contract["required_output_status"] == "RUN_BOUNDED_v0_NONCLAIM"
    assert contract["dormancy_non_equivalence_rule"] == (
        "AUXILIARY_COMPUTATIONAL_ANALYSIS_IS_NOT_LANE_REOPEN_AND_NOT_NEW_PACKET_EXECUTION"
    )
    assert contract["restart_non_equivalence_rule"] == (
        "AUXILIARY_COMPUTATIONAL_ANALYSIS_CANNOT_BY_ITSELF_ACTIVATE_ANY_RESTART_TRIGGER_FAMILY"
    )
    assert "lane_reopen" in contract["forbidden_effects"]
    assert "new_packet_authorization" in contract["forbidden_effects"]
    assert "restart_trigger_satisfaction" in contract["forbidden_effects"]
    assert contract["single_layer_only"] is True
    assert contract["single_outcome_only"] is True


def test_canonical_surfaces_cross_pin_computational_analysis_lane() -> None:
    execution_plan_text = _read(EXECUTION_PLAN_PATH)
    readme_text = _read(README_PATH)
    state_text = _read(STATE_PATH)

    for path_ref in (
        "formal/docs/release/GROUNDED_SPECULATION_POSTURE_STANDARD_v0.md",
        "formal/docs/release/COMPUTATIONAL_ANALYSIS_BOUNDED_AUTHORIZATION_CLASS_20260416_v0.json",
        "formal/docs/release/COMPUTATIONAL_ANALYSIS_LANE_EXECUTION_POLICY_20260416_v0.md",
        "formal/python/tests/test_computational_analysis_lane_policy_gate.py",
    ):
        assert path_ref in execution_plan_text
        assert path_ref in state_text

    assert "bounded auxiliary computational-analysis lane" in readme_text
    assert "does not reopen dormant lanes or authorize new packets" in readme_text


def test_dormancy_and_restart_surfaces_remain_fail_closed_while_exposing_auxiliary_class() -> None:
    dormancy = json.loads(_read(DORMANCY_PATH))
    restart = json.loads(_read(RESTART_PATH))

    dormancy_policy = dormancy["controlled_dormancy_contract"]["dormancy_policy"]
    restart_contract = restart["restart_trigger_contract"]

    assert dormancy_policy["lane_execution_disallowed"] is True
    assert dormancy_policy["new_packet_execution_disallowed"] is True
    assert dormancy_policy["auxiliary_nonclaim_computational_analysis_allowed"] is True
    assert dormancy_policy["auxiliary_nonclaim_computational_analysis_authorization_class"] == (
        "AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS"
    )

    assert restart_contract["required_lane_reopen_authorized"] is False
    assert restart_contract["required_new_lane_or_packet_authorized_now"] is False
    assert restart_contract["auxiliary_nonclaim_computational_analysis_not_a_trigger_family"] is True
    assert restart_contract["auxiliary_nonclaim_computational_analysis_not_direct_execution"] is True
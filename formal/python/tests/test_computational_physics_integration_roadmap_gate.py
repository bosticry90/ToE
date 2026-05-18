from __future__ import annotations

from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
ROADMAP_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "paper"
    / "COMPUTATIONAL_PHYSICS_INTEGRATION_ROADMAP_v0.md"
)
PHYSICS_ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"


REQUIRED_TOKENS = [
    "COMPUTATIONAL_PHYSICS_INTEGRATION_ROADMAP_STATUS_v0: ACTIVE_PLANNING_NONCLAIM",
    "COMPUTATIONAL_PHYSICS_INTEGRATION_ROADMAP_CLASSIFICATION_v0: P-POLICY",
    "COMPUTATIONAL_PHYSICS_INTEGRATION_AUTHORITY_BINDING_v0: AUXILIARY_NONCLAIM_COMPUTATIONAL_ANALYSIS",
    (
        "COMPUTATIONAL_PHYSICS_INTEGRATION_SCOPE_RULE_v0: "
        "VVUQ_UQ_SENSITIVITY_MMS_REFERENTS_MODEL_CARDS_FALSIFIERS_ONLY"
    ),
    "COMPUTATIONAL_PHYSICS_INTEGRATION_FIRST_PACKET_v0: COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_v0",
    (
        "COMPUTATIONAL_PHYSICS_INTEGRATION_NEXT_ACTION_v0: "
        "RETURN_TO_MAIN_PHYSICS_TARGET_SELECTION_AFTER_NONCLAIM_STACK_CLOSEOUT"
    ),
    (
        "COMPUTATIONAL_PHYSICS_INTEGRATION_PROMOTION_FIREWALL_v0: "
        "NO_PHASE2_NO_SEAM_CLOSURE_NO_EMPIRICAL_VALIDATION_NO_MASTER_ACTION_PROMOTION"
    ),
    (
        "COMPUTATIONAL_PHYSICS_INTEGRATION_GATE_v0: "
        "formal/python/tests/test_computational_physics_integration_roadmap_gate.py"
    ),
    "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_STATUS_v0: IMPLEMENTED_BOUNDED_NONCLAIM",
    "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_RESULT_REVIEW_STATUS_v0: ACCEPTED_BOUNDED_NONCLAIM",
    "VVUQ_CREDIBILITY_LEDGER_STATUS_v0: PREPARED_BOUNDED_NONCLAIM",
    "VVUQ_CREDIBILITY_LEDGER_RESULT_REVIEW_STATUS_v0: ACCEPTED_BOUNDED_NONCLAIM",
    "NUMERICAL_METHOD_VERIFICATION_REGISTRY_STATUS_v0: PREPARED_BOUNDED_NONCLAIM",
    "NUMERICAL_METHOD_VERIFICATION_REGISTRY_JSON_v0: formal/docs/release/NUMERICAL_METHOD_VERIFICATION_REGISTRY_20260515_v0.json",
    "NUMERICAL_METHOD_VERIFICATION_REGISTRY_REPORT_v0: formal/docs/paper/NUMERICAL_METHOD_VERIFICATION_REGISTRY_REPORT_v0.md",
    "NUMERICAL_METHOD_VERIFICATION_REGISTRY_TOOL_v0: formal/python/tools/numerical_method_verification_registry_report.py",
    "NUMERICAL_METHOD_VERIFICATION_REGISTRY_GATE_v0: formal/python/tests/test_numerical_method_verification_registry_gate.py",
    "NUMERICAL_METHOD_VERIFICATION_REGISTRY_RESULT_REVIEW_STATUS_v0: ACCEPTED_BOUNDED_NONCLAIM",
    (
        "NUMERICAL_METHOD_VERIFICATION_REGISTRY_RESULT_REVIEW_JSON_v0: "
        "formal/docs/release/NUMERICAL_METHOD_VERIFICATION_REGISTRY_RESULT_REVIEW_20260515_v0.json"
    ),
    (
        "NUMERICAL_METHOD_VERIFICATION_REGISTRY_RESULT_REVIEW_TOOL_v0: "
        "formal/python/tools/numerical_method_verification_registry_result_review_report.py"
    ),
    (
        "NUMERICAL_METHOD_VERIFICATION_REGISTRY_RESULT_REVIEW_GATE_v0: "
        "formal/python/tests/test_numerical_method_verification_registry_result_review_gate.py"
    ),
    "REGIME_RECOVERY_MATRIX_STATUS_v0: PREPARED_BOUNDED_NONCLAIM",
    "REGIME_RECOVERY_MATRIX_JSON_v0: formal/docs/release/REGIME_RECOVERY_MATRIX_20260515_v0.json",
    "REGIME_RECOVERY_MATRIX_REPORT_v0: formal/docs/paper/REGIME_RECOVERY_MATRIX_REPORT_v0.md",
    "REGIME_RECOVERY_MATRIX_TOOL_v0: formal/python/tools/regime_recovery_matrix_report.py",
    "REGIME_RECOVERY_MATRIX_GATE_v0: formal/python/tests/test_regime_recovery_matrix_gate.py",
    "REGIME_RECOVERY_MATRIX_RESULT_REVIEW_STATUS_v0: ACCEPTED_BOUNDED_NONCLAIM",
    "REGIME_RECOVERY_MATRIX_RESULT_REVIEW_JSON_v0: formal/docs/release/REGIME_RECOVERY_MATRIX_RESULT_REVIEW_20260515_v0.json",
    "REGIME_RECOVERY_MATRIX_RESULT_REVIEW_TOOL_v0: formal/python/tools/regime_recovery_matrix_result_review_report.py",
    "REGIME_RECOVERY_MATRIX_RESULT_REVIEW_GATE_v0: formal/python/tests/test_regime_recovery_matrix_result_review_gate.py",
    "SENSITIVITY_ROBUSTNESS_PROTOCOL_STATUS_v0: PREPARED_BOUNDED_NONCLAIM",
    "SENSITIVITY_ROBUSTNESS_PROTOCOL_JSON_v0: formal/docs/release/SENSITIVITY_ROBUSTNESS_PROTOCOL_20260515_v0.json",
    "SENSITIVITY_ROBUSTNESS_PROTOCOL_REPORT_v0: formal/docs/paper/SENSITIVITY_ROBUSTNESS_PROTOCOL_REPORT_v0.md",
    "SENSITIVITY_ROBUSTNESS_PROTOCOL_TOOL_v0: formal/python/tools/sensitivity_robustness_protocol_report.py",
    "SENSITIVITY_ROBUSTNESS_PROTOCOL_GATE_v0: formal/python/tests/test_sensitivity_robustness_protocol_gate.py",
    "SENSITIVITY_ROBUSTNESS_PROTOCOL_RESULT_REVIEW_STATUS_v0: ACCEPTED_BOUNDED_NONCLAIM",
    (
        "SENSITIVITY_ROBUSTNESS_PROTOCOL_RESULT_REVIEW_JSON_v0: "
        "formal/docs/release/SENSITIVITY_ROBUSTNESS_PROTOCOL_RESULT_REVIEW_20260515_v0.json"
    ),
    (
        "SENSITIVITY_ROBUSTNESS_PROTOCOL_RESULT_REVIEW_TOOL_v0: "
        "formal/python/tools/sensitivity_robustness_protocol_result_review_report.py"
    ),
    (
        "SENSITIVITY_ROBUSTNESS_PROTOCOL_RESULT_REVIEW_GATE_v0: "
        "formal/python/tests/test_sensitivity_robustness_protocol_result_review_gate.py"
    ),
    "REFERENT_REGISTRY_STATUS_v0: PREPARED_BOUNDED_NONCLAIM",
    "REFERENT_REGISTRY_JSON_v0: formal/docs/release/REFERENT_REGISTRY_20260515_v0.json",
    "REFERENT_REGISTRY_REPORT_v0: formal/docs/paper/REFERENT_REGISTRY_REPORT_v0.md",
    "REFERENT_REGISTRY_TOOL_v0: formal/python/tools/referent_registry_report.py",
    "REFERENT_REGISTRY_GATE_v0: formal/python/tests/test_referent_registry_gate.py",
    "REFERENT_REGISTRY_RESULT_REVIEW_STATUS_v0: ACCEPTED_BOUNDED_NONCLAIM",
    (
        "REFERENT_REGISTRY_RESULT_REVIEW_JSON_v0: "
        "formal/docs/release/REFERENT_REGISTRY_RESULT_REVIEW_20260515_v0.json"
    ),
    (
        "REFERENT_REGISTRY_RESULT_REVIEW_TOOL_v0: "
        "formal/python/tools/referent_registry_result_review_report.py"
    ),
    (
        "REFERENT_REGISTRY_RESULT_REVIEW_GATE_v0: "
        "formal/python/tests/test_referent_registry_result_review_gate.py"
    ),
    "SIMULATION_MODEL_CARD_TEMPLATE_STATUS_v0: PREPARED_BOUNDED_NONCLAIM",
    "SIMULATION_MODEL_CARD_TEMPLATE_JSON_v0: formal/docs/release/SIMULATION_MODEL_CARD_TEMPLATE_20260515_v0.json",
    "SIMULATION_MODEL_CARD_TEMPLATE_DOC_v0: formal/docs/paper/SIMULATION_MODEL_CARD_TEMPLATE_v0.md",
    "SIMULATION_MODEL_CARD_TEMPLATE_TOOL_v0: formal/python/tools/simulation_model_card_template_report.py",
    "SIMULATION_MODEL_CARD_TEMPLATE_GATE_v0: formal/python/tests/test_simulation_model_card_template_gate.py",
    "SIMULATION_MODEL_CARD_TEMPLATE_RESULT_REVIEW_STATUS_v0: ACCEPTED_BOUNDED_NONCLAIM",
    (
        "SIMULATION_MODEL_CARD_TEMPLATE_RESULT_REVIEW_JSON_v0: "
        "formal/docs/release/SIMULATION_MODEL_CARD_TEMPLATE_RESULT_REVIEW_20260515_v0.json"
    ),
    (
        "SIMULATION_MODEL_CARD_TEMPLATE_RESULT_REVIEW_TOOL_v0: "
        "formal/python/tools/simulation_model_card_template_result_review_report.py"
    ),
    (
        "SIMULATION_MODEL_CARD_TEMPLATE_RESULT_REVIEW_GATE_v0: "
        "formal/python/tests/test_simulation_model_card_template_result_review_gate.py"
    ),
    "PREDICTION_AND_FALSIFIER_REGISTRY_STATUS_v0: PREPARED_BOUNDED_NONCLAIM",
    "PREDICTION_AND_FALSIFIER_REGISTRY_JSON_v0: formal/docs/release/PREDICTION_AND_FALSIFIER_REGISTRY_20260515_v0.json",
    "PREDICTION_AND_FALSIFIER_REGISTRY_REPORT_v0: formal/docs/paper/PREDICTION_AND_FALSIFIER_REGISTRY_REPORT_v0.md",
    "PREDICTION_AND_FALSIFIER_REGISTRY_TOOL_v0: formal/python/tools/prediction_and_falsifier_registry_report.py",
    "PREDICTION_AND_FALSIFIER_REGISTRY_GATE_v0: formal/python/tests/test_prediction_and_falsifier_registry_gate.py",
    (
        "PREDICTION_AND_FALSIFIER_REGISTRY_RESULT_REVIEW_STATUS_v0: "
        "ACCEPTED_BOUNDED_NONCLAIM"
    ),
    (
        "PREDICTION_AND_FALSIFIER_REGISTRY_RESULT_REVIEW_JSON_v0: "
        "formal/docs/release/PREDICTION_AND_FALSIFIER_REGISTRY_RESULT_REVIEW_20260515_v0.json"
    ),
    (
        "PREDICTION_AND_FALSIFIER_REGISTRY_RESULT_REVIEW_TOOL_v0: "
        "formal/python/tools/prediction_and_falsifier_registry_result_review_report.py"
    ),
    (
        "PREDICTION_AND_FALSIFIER_REGISTRY_RESULT_REVIEW_GATE_v0: "
        "formal/python/tests/test_prediction_and_falsifier_registry_result_review_gate.py"
    ),
    (
        "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_STATUS_v0: "
        "CLOSED_BOUNDED_NONCLAIM"
    ),
    (
        "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_JSON_v0: "
        "formal/docs/release/COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_20260515_v0.json"
    ),
    (
        "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_REPORT_v0: "
        "formal/docs/paper/COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_REPORT_v0.md"
    ),
    (
        "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_TOOL_v0: "
        "formal/python/tools/computational_physics_integration_closeout_report.py"
    ),
    (
        "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_GATE_v0: "
        "formal/python/tests/test_computational_physics_integration_closeout_gate.py"
    ),
    (
        "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_OUTCOME_v0: "
        "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_PREPARED_AS_NONCLAIM_CREDIBILITY_INFRASTRUCTURE_WITH_NO_EXECUTION_OR_PROMOTION"
    ),
    (
        "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_RESULT_REVIEW_STATUS_v0: "
        "ACCEPTED_BOUNDED_NONCLAIM"
    ),
    (
        "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_RESULT_REVIEW_JSON_v0: "
        "formal/docs/release/COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_RESULT_REVIEW_20260515_v0.json"
    ),
    (
        "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_RESULT_REVIEW_TOOL_v0: "
        "formal/python/tools/computational_physics_integration_closeout_result_review_report.py"
    ),
    (
        "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_RESULT_REVIEW_GATE_v0: "
        "formal/python/tests/test_computational_physics_integration_closeout_result_review_gate.py"
    ),
    (
        "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_RESULT_REVIEW_OUTCOME_v0: "
        "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_RESULT_REVIEW_ACCEPTS_NONCLAIM_INFRASTRUCTURE_STACK_AND_RETURNS_TO_MAIN_TARGET_SELECTION_ONLY"
    ),
]


REQUIRED_ARTIFACTS = [
    "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_v0",
    "VVUQ_CREDIBILITY_LEDGER_v0",
    "NUMERICAL_METHOD_VERIFICATION_REGISTRY_v0",
    "REGIME_RECOVERY_MATRIX_v0",
    "SENSITIVITY_ROBUSTNESS_PROTOCOL_v0",
    "REFERENT_REGISTRY_v0",
    "SIMULATION_MODEL_CARD_TEMPLATE_v0",
    "PREDICTION_AND_FALSIFIER_REGISTRY_v0",
    "COMPUTATIONAL_PHYSICS_INTEGRATION_CLOSEOUT_v0",
]


REQUIRED_SOURCE_ANCHORS = [
    "https://standards.nasa.gov/standard/NASA/NASA-STD-7009",
    "https://www.asme.org/codes-standards/find-codes-standards/standard-for-verification-and-validation-in-computational-fluid-dynamics-and-heat-transfer",
    "https://www.osti.gov/biblio/759450/",
    "https://computing.llnl.gov/projects/psuade",
    "https://www.energy.gov/science/fes/articles/uncertainty-toolbox-software-toolbox-quantifying-uncertainty-and-more",
    "https://www.siam.org/publications/siam-news/articles/siam-task-force-anticipates-future-directions-of-computational-science",
]


PROHIBITED_PHRASES = [
    "proves the ToE",
    "confirms the ToE",
    "empirically validated the ToE",
    "Phase 2 authorized",
    "seam closed by computation",
    "master action promoted by computation",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def test_computational_physics_integration_roadmap_exists_and_has_policy_tokens() -> None:
    text = _read(ROADMAP_PATH)
    for token in REQUIRED_TOKENS:
        assert token in text, f"Missing roadmap token: {token}"


def test_computational_physics_integration_roadmap_has_planned_artifact_queue() -> None:
    text = _read(ROADMAP_PATH)
    for artifact_id in REQUIRED_ARTIFACTS:
        assert artifact_id in text, f"Missing planned artifact: {artifact_id}"


def test_computational_physics_integration_roadmap_is_source_grounded() -> None:
    text = _read(ROADMAP_PATH)
    for source in REQUIRED_SOURCE_ANCHORS:
        assert source in text, f"Missing source anchor: {source}"


def test_computational_physics_integration_roadmap_preserves_nonclaim_boundary() -> None:
    text = _read(ROADMAP_PATH)
    required_boundary_tokens = [
        "does not claim that any candidate ToE structure is true",
        "does not validate empirical adequacy",
        "does not discharge theorem debt",
        "does not authorize Phase 2",
        "does not promote the candidate master action",
        "Claim ceiling:",
    ]
    for token in required_boundary_tokens:
        assert token in text, f"Missing nonclaim boundary token: {token}"

    for phrase in PROHIBITED_PHRASES:
        assert phrase not in text, f"Prohibited phrase present: {phrase}"


def test_physics_roadmap_pins_computational_physics_integration_roadmap() -> None:
    text = _read(PHYSICS_ROADMAP_PATH)
    assert "COMPUTATIONAL_PHYSICS_INTEGRATION_ROADMAP_v0" in text
    assert "formal/docs/paper/COMPUTATIONAL_PHYSICS_INTEGRATION_ROADMAP_v0.md" in text
    assert "formal/python/tests/test_computational_physics_integration_roadmap_gate.py" in text
    assert "COMPUTATIONAL_PHYSICS_CAPABILITY_AUDIT_v0" in text

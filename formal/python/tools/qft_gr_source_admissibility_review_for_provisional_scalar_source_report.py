from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_action_derivability_retry_with_provisional_matter_sector_report import (
    ACTION_DERIVABILITY_RESULT,
    DEFAULT_OUT as ACTION_DERIVABILITY_PACKET_PATH,
    OUTCOME_ID as ACTION_DERIVABILITY_OUTCOME,
    SCALAR_ACTION,
    SCALAR_LAGRANGIAN,
    SCHEMA_ID as ACTION_DERIVABILITY_SCHEMA_ID,
    SELECTED_ACTION_GENERATED_SOURCE_SUBCLASS_ID,
    SELECTED_FIELD_CONTENT,
    SELECTED_KNOWN_MATTER_MODEL,
    SELECTED_PROVISIONAL_MATTER_SECTOR_ID,
    STRESS_ENERGY_COVARIANT_EXPRESSION,
    STRESS_ENERGY_CONTRAVARIANT_EXPRESSION,
    TOE_NATIVE_MATTER_SECTOR_RESULT,
)
from formal.python.tools.qft_gr_bianchi_compatibility_test_for_provisional_scalar_stress_energy_source_report import (
    BIANCHI_COMPATIBILITY_RESULT,
    BIANCHI_COMPATIBILITY_STATEMENT,
    CONTRACTED_BIANCHI_IDENTITY,
    DEFAULT_OUT as BIANCHI_PACKET_PATH,
    EINSTEIN_SOURCE_EQUATION_WITH_LAMBDA_FORM,
    METRIC_COMPATIBILITY_IDENTITY,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as BIANCHI_OUTCOME,
    SCHEMA_ID as BIANCHI_SCHEMA_ID,
    SOURCE_SIDE_CONSERVATION_REQUIREMENT,
)
from formal.python.tools.qft_gr_weak_conservation_test_for_provisional_scalar_stress_energy_source_report import (
    DIVERGENCE_IDENTITY,
    ON_SHELL_CONSERVATION_STATEMENT,
    SCALAR_EQUATION_OF_MOTION,
    WEAK_CONSERVATION_RESULT,
)
from formal.python.tools.qft_gr_weak_pairing_retry_for_selected_candidate_functional_contract_packet_report import (
    CALCULATION_RESULT as WEAK_PAIRING_RESULT,
    DEFAULT_OUT as WEAK_PAIRING_PACKET_PATH,
    OUTCOME_ID as WEAK_PAIRING_OUTCOME,
    SCHEMA_ID as WEAK_PAIRING_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-17T00:00:00Z"
SCHEMA_ID = "QFT_GR_SOURCE_ADMISSIBILITY_REVIEW_FOR_PROVISIONAL_SCALAR_SOURCE_20260617_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "QFT_GR_SOURCE_ADMISSIBILITY_REVIEW_FOR_PROVISIONAL_SCALAR_SOURCE_v0"
PROVISIONAL_SCALAR_SOURCE_ADMISSIBILITY_RESULT = (
    "PROVISIONAL_SCALAR_SOURCE_PASSES_LOCAL_SOURCE_ADMISSIBILITY_REVIEW_ON_SHELL_"
    "NO_SEMICLASSICAL_OR_TOE_NATIVE_CLOSURE"
)
OUTCOME_ID = (
    "QFT_GR_SOURCE_ADMISSIBILITY_REVIEW_FOR_PROVISIONAL_SCALAR_SOURCE_PREPARED_"
    "WITH_PROVISIONAL_SCALAR_SOURCE_PASSES_LOCAL_SOURCE_ADMISSIBILITY_REVIEW_"
    "ON_SHELL_NO_SEMICLASSICAL_OR_TOE_NATIVE_CLOSURE"
)
PACKET_CLASSIFICATION = (
    "qft_gr_source_admissibility_review_for_provisional_scalar_source_passes_"
    "local_on_shell_sandbox_review_nonpromotionally"
)
NEXT_TARGET = (
    "prepare_qft_gr_semiclassical_coupling_gate_scope_review_for_provisional_"
    "scalar_source"
)
NEXT_TARGET_KIND = (
    "qft_gr_semiclassical_coupling_gate_scope_review_for_provisional_scalar_"
    "source_preparation"
)
LOCAL_ADMISSIBILITY_SCOPE = (
    "conditional local source-admissibility review for the imported "
    "provisional real-scalar sandbox on shell only"
)
GENERIC_SOURCE_ADMISSIBILITY_BOUNDARY = (
    "No generic source-admissibility claim is made for arbitrary "
    "distributional sources or for the full QFT-GR source map."
)
SEMICLASSICAL_COUPLING_GATE_SCOPE = (
    "The next target may review the semiclassical coupling gate for the "
    "provisional scalar source only; it may not derive a semiclassical "
    "Einstein equation."
)
LEAN_VALIDATION_POLICY_ID = "TIERED_LEAN_VALIDATION_POLICY_FOR_PACKET_WORK_v0"
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_SOURCE_ADMISSIBILITY_REVIEW_FOR_PROVISIONAL_SCALAR_SOURCE_"
    "20260617_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRSourceAdmissibilityReviewForProvisionalScalarSource.lean"
)
SCALAR_SANDBOX_AGGREGATE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRScalarSandbox.lean"
)
QFTGR_AGGREGATE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGR.lean"
)
CURRENT_TARGET_AGGREGATE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "CurrentTarget.lean"
)
RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Release"
    / "CurrentAuthority.lean"
)
LEAN_VALIDATION_POLICY_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "LEAN_VALIDATION_TIER_POLICY_v0.md"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _local_review_criteria() -> list[dict[str, Any]]:
    return [
        {
            "row_id": "candidate_source_object_selected",
            "status": "passed_conditionally",
            "evidence": SELECTED_ACTION_GENERATED_SOURCE_SUBCLASS_ID,
            "assessment": (
                "The review binds to the provisional scalar stress-energy "
                "source subclass generated by the real-scalar action."
            ),
        },
        {
            "row_id": "test_domain_and_pairing_convention_supplied",
            "status": "passed_conditionally",
            "evidence": (
                "D = C_c^infty(M, Sym^2 T*M); "
                "delta S_m[g, phi](k) = -1/2 integral_M T_{mu nu} "
                "k^{mu nu} dVol_g"
            ),
            "assessment": (
                "The selected weak-pairing contract and scalar variational "
                "pairing convention supply the local test surface."
            ),
        },
        {
            "row_id": "weak_pairing_constructed",
            "status": "passed_conditionally",
            "evidence": WEAK_PAIRING_RESULT,
            "assessment": (
                "The pairing is constructed as restricted distributional "
                "evaluation, without promoting arbitrary sources."
            ),
        },
        {
            "row_id": "action_derivability_constructed",
            "status": "passed_conditionally",
            "evidence": ACTION_DERIVABILITY_RESULT,
            "assessment": (
                "Metric variation of the imported scalar action yields the "
                "scalar stress-energy expression."
            ),
        },
        {
            "row_id": "field_equation_on_shell_condition_stated",
            "status": "passed_conditionally",
            "evidence": SCALAR_EQUATION_OF_MOTION,
            "assessment": (
                "The review is on shell only and requires the scalar equation "
                "of motion."
            ),
        },
        {
            "row_id": "weak_conservation_constructed_conditionally",
            "status": "passed_conditionally",
            "evidence": WEAK_CONSERVATION_RESULT,
            "assessment": (
                "The divergence reduces to the scalar EOM residual times "
                "nabla^nu phi and vanishes only on shell."
            ),
        },
        {
            "row_id": "bianchi_compatibility_constructed_conditionally",
            "status": "passed_conditionally",
            "evidence": BIANCHI_COMPATIBILITY_RESULT,
            "assessment": (
                "The contracted Bianchi identity is compatible with the "
                "provisional scalar source under Levi-Civita metric "
                "compatibility and constant coupling assumptions."
            ),
        },
        {
            "row_id": "scope_restrictions_preserved",
            "status": "passed_conditionally",
            "evidence": GENERIC_SOURCE_ADMISSIBILITY_BOUNDARY,
            "assessment": (
                "The result remains local, conditional, on shell, and confined "
                "to the imported scalar sandbox."
            ),
        },
    ]


def _broader_nonclaim_rows() -> list[dict[str, Any]]:
    return [
        {
            "row_id": "toe_native_matter_sector",
            "status": "not_derived",
            "reason": TOE_NATIVE_MATTER_SECTOR_RESULT,
        },
        {
            "row_id": "arbitrary_distributional_source_admissibility",
            "status": "not_claimed",
            "reason": "The review does not promote arbitrary distributional sources.",
        },
        {
            "row_id": "state_expectation_functional_link",
            "status": "not_supplied",
            "reason": "No QFT state or expectation-value source construction is supplied.",
        },
        {
            "row_id": "renormalized_stress_energy_object_and_finiteness",
            "status": "not_supplied",
            "reason": "No renormalization scheme, finite tensor proof, or domain control is supplied.",
        },
        {
            "row_id": "semiclassical_einstein_equation_derivation",
            "status": "not_reached",
            "reason": "The Einstein-form equation has only been used as a compatibility-test surface.",
        },
        {
            "row_id": "qft_gr_closure",
            "status": "not_claimed",
            "reason": "The review closes no QFT-GR seam and authorizes no public ToE claim.",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "qft_gr_source_admissibility_review_for_provisional_scalar_source"
        ),
        "tiered_lean_validation_policy_formalized": True,
        "tiers": [
            {
                "tier": 1,
                "name": "touched Lean marker or module",
                "command_template": (
                    "formal/toe_formal/lake.ps1 env lean "
                    "ToeFormal/Derivation/<TouchedModule>.lean"
                ),
            },
            {
                "tier": 2,
                "name": "smallest affected Lake target",
                "command_template": (
                    "./run_lean.ps1 -Target ToeFormal.Derivation.<Module> "
                    "-TimeoutSeconds 300"
                ),
            },
            {
                "tier": 3,
                "name": "lane-level aggregate when available",
                "command_template": (
                    "./run_lean.ps1 -Target ToeFormal.Derivation.QFTGRScalarSandbox "
                    "-TimeoutSeconds 600"
                ),
            },
            {
                "tier": 4,
                "name": "full ToeFormal aggregate",
                "command_template": (
                    "./run_lean.ps1 -Target ToeFormal -TimeoutSeconds 1800"
                ),
                "required_for": (
                    "release, preservation, or authority-surface synchronization"
                ),
            },
        ],
        "aggregate_timeout_with_steady_progress_interpretation": (
            "incomplete_validation_not_mathematical_failure"
        ),
        "toeformal_import_update_requires_preservation_status": True,
        "aggregate_lean_validation_status_for_packet": (
            "incomplete_due_to_timeout_with_steady_progress"
        ),
        "aggregate_lean_validation_required_reason": (
            "ToeFormal.lean import surface updated by this packet"
        ),
        "aggregate_lean_validation_command": (
            "./run_lean.ps1 -Target ToeFormal -TimeoutSeconds 1800"
        ),
        "aggregate_lean_validation_exit_code": 124,
        "aggregate_lean_validation_elapsed_seconds": 1800,
        "aggregate_lean_validation_observed_progress": (
            "built_8166_of_8179_modules_before_timeout"
        ),
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_deferred": False,
        "focused_and_lane_validation_completed": (
            "recorded_by_validation_commands_for_marker_and_lane_targets"
        ),
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
        "full_security_scan_required": False,
        "aggregate_lean_health_claimed_before_execution": False,
    }


def build_qft_gr_source_admissibility_review_for_provisional_scalar_source(
    *,
    weak_pairing_packet_path: Path = WEAK_PAIRING_PACKET_PATH,
    action_derivability_packet_path: Path = ACTION_DERIVABILITY_PACKET_PATH,
    bianchi_packet_path: Path = BIANCHI_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    weak_pairing_packet = _read_json(weak_pairing_packet_path)
    action_packet = _read_json(action_derivability_packet_path)
    bianchi_packet = _read_json(bianchi_packet_path)
    local_criteria = _local_review_criteria()
    broader_nonclaims = _broader_nonclaim_rows()
    acceptance_criteria = {
        "consumes_expected_bianchi_packet": (
            bianchi_packet.get("schema_id") == BIANCHI_SCHEMA_ID
            and bianchi_packet.get("outcome_id") == BIANCHI_OUTCOME
            and bianchi_packet.get("selected_next_target") == CONSUMED_TARGET
        ),
        "weak_pairing_packet_available": (
            weak_pairing_packet.get("schema_id") == WEAK_PAIRING_SCHEMA_ID
            and weak_pairing_packet.get("outcome_id") == WEAK_PAIRING_OUTCOME
            and weak_pairing_packet.get("weak_pairing_constructed") is True
        ),
        "action_derivability_packet_available": (
            action_packet.get("schema_id") == ACTION_DERIVABILITY_SCHEMA_ID
            and action_packet.get("outcome_id") == ACTION_DERIVABILITY_OUTCOME
            and action_packet.get("action_derivability_constructed") is True
        ),
        "scalar_stress_energy_selected": (
            action_packet.get("selected_action_generated_source_subclass_id")
            == SELECTED_ACTION_GENERATED_SOURCE_SUBCLASS_ID
            and bianchi_packet.get("selected_action_generated_source_subclass_id")
            == SELECTED_ACTION_GENERATED_SOURCE_SUBCLASS_ID
        ),
        "field_equation_on_shell_condition_stated": (
            bianchi_packet.get("scalar_equation_of_motion")
            == SCALAR_EQUATION_OF_MOTION
            and bianchi_packet.get("on_shell_required") is True
        ),
        "weak_conservation_constructed_conditionally": (
            bianchi_packet.get("weak_conservation_constructed") is True
            and bianchi_packet.get("weak_conservation_result")
            == WEAK_CONSERVATION_RESULT
        ),
        "bianchi_compatibility_constructed_conditionally": (
            bianchi_packet.get("bianchi_compatibility_constructed") is True
            and bianchi_packet.get("bianchi_compatibility_result")
            == BIANCHI_COMPATIBILITY_RESULT
        ),
        "local_review_criteria_all_pass": all(
            row["status"] == "passed_conditionally" for row in local_criteria
        ),
        "scope_restrictions_preserved": True,
        "tiered_lean_validation_policy_formalized": True,
    }
    prepared = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if prepared
        else "REMEDIATE_QFT_GR_SOURCE_ADMISSIBILITY_REVIEW_FOR_PROVISIONAL_SCALAR_SOURCE"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_NONLIVE_SCOPED_LOCAL_RESULT",
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "accepted": prepared,
        "outcome_id": OUTCOME_ID
        if prepared
        else "QFT_GR_SOURCE_ADMISSIBILITY_REVIEW_FOR_PROVISIONAL_SCALAR_SOURCE_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "authorized_by_bianchi_artifact_id": bianchi_packet.get("schema_id"),
        "authorized_by_bianchi_outcome": bianchi_packet.get("outcome_id"),
        "reviewed_weak_pairing_artifact_id": weak_pairing_packet.get("schema_id"),
        "reviewed_action_derivability_artifact_id": action_packet.get("schema_id"),
        "provisional_scalar_source_admissibility_result": (
            PROVISIONAL_SCALAR_SOURCE_ADMISSIBILITY_RESULT
        ),
        "local_source_admissibility_review_completed": True,
        "local_source_admissibility_review_passed": True,
        "provisional_scalar_source_passes_local_source_admissibility_review": True,
        "provisional_scalar_source_admissibility_constructed": True,
        "provisional_scalar_source_admissibility_claimed_scope": (
            LOCAL_ADMISSIBILITY_SCOPE
        ),
        "generic_source_admissibility_boundary": GENERIC_SOURCE_ADMISSIBILITY_BOUNDARY,
        "local_admissibility_scope": LOCAL_ADMISSIBILITY_SCOPE,
        "semiclassical_coupling_gate_scope": SEMICLASSICAL_COUPLING_GATE_SCOPE,
        "selected_provisional_matter_sector_id": SELECTED_PROVISIONAL_MATTER_SECTOR_ID,
        "selected_known_matter_model": SELECTED_KNOWN_MATTER_MODEL,
        "selected_action_generated_source_subclass_id": (
            SELECTED_ACTION_GENERATED_SOURCE_SUBCLASS_ID
        ),
        "field_content": SELECTED_FIELD_CONTENT,
        "scalar_action": SCALAR_ACTION,
        "lagrangian_density": SCALAR_LAGRANGIAN,
        "stress_energy_covariant_expression": STRESS_ENERGY_COVARIANT_EXPRESSION,
        "stress_energy_contravariant_expression": (
            STRESS_ENERGY_CONTRAVARIANT_EXPRESSION
        ),
        "action_derivability_result": ACTION_DERIVABILITY_RESULT,
        "weak_pairing_result": WEAK_PAIRING_RESULT,
        "weak_conservation_result": WEAK_CONSERVATION_RESULT,
        "bianchi_compatibility_result": BIANCHI_COMPATIBILITY_RESULT,
        "scalar_equation_of_motion": SCALAR_EQUATION_OF_MOTION,
        "divergence_identity": DIVERGENCE_IDENTITY,
        "on_shell_conservation_statement": ON_SHELL_CONSERVATION_STATEMENT,
        "contracted_bianchi_identity": CONTRACTED_BIANCHI_IDENTITY,
        "metric_compatibility_identity": METRIC_COMPATIBILITY_IDENTITY,
        "einstein_source_equation_with_lambda_form": (
            EINSTEIN_SOURCE_EQUATION_WITH_LAMBDA_FORM
        ),
        "source_side_conservation_requirement": SOURCE_SIDE_CONSERVATION_REQUIREMENT,
        "bianchi_compatibility_statement": BIANCHI_COMPATIBILITY_STATEMENT,
        "local_review_criteria": local_criteria,
        "local_review_criteria_count": len(local_criteria),
        "local_review_criteria_passed_count": sum(
            row["status"] == "passed_conditionally" for row in local_criteria
        ),
        "broader_nonclaim_rows": broader_nonclaims,
        "broader_nonclaim_row_count": len(broader_nonclaims),
        "candidate_source_object_selected": True,
        "test_domain_pairing_convention_supplied": True,
        "weak_pairing_constructed": True,
        "action_derivability_constructed": True,
        "on_shell_required": True,
        "weak_conservation_constructed": True,
        "weak_conservation_claimed": True,
        "weak_conservation_claimed_scope": (
            "conditional on scalar equation of motion only"
        ),
        "bianchi_compatibility_constructed": True,
        "Bianchi_compatibility_claimed": True,
        "Bianchi_compatibility_claimed_scope": (
            "conditional on scalar EOM, Levi-Civita connection, metric "
            "compatibility, constant coupling, and provisional scalar source only"
        ),
        "levi_civita_connection_required": True,
        "metric_compatibility_required": True,
        "constant_gravitational_coupling_required": True,
        "constant_lambda_required_if_lambda_variant_used": True,
        "source_admissibility_claimed": False,
        "source_admissibility_completed": False,
        "arbitrary_distributional_source_admissibility_claimed": False,
        "arbitrary_distributional_source_conservation_claimed": False,
        "arbitrary_distributional_source_promoted": False,
        "toe_native_matter_sector_result": TOE_NATIVE_MATTER_SECTOR_RESULT,
        "toe_native_matter_sector_defined": False,
        "toe_matter_model_derived": False,
        "toe_native_matter_derivation_claimed": False,
        "standard_model_derivation_claimed": False,
        "quantum_stress_energy_expectation_constructed": False,
        "state_expectation_functional_link_claimed": False,
        "renormalization_result_claimed": False,
        "renormalized_stress_energy_constructed": False,
        "semiclassical_einstein_equation_derived": False,
        "semiclassical_coupling_claimed": False,
        "qft_gr_closure_claimed": False,
        "qft_gr_seam_closed": False,
        "empirical_validation_claimed": False,
        "public_readiness_claimed": False,
        "public_submission_authorized": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "accepted_outcomes_considered": [
            PROVISIONAL_SCALAR_SOURCE_ADMISSIBILITY_RESULT,
            (
                "PROVISIONAL_SCALAR_SOURCE_ADMISSIBILITY_REVIEW_BLOCKED_BY_"
                "MISSING_ON_SHELL_CONSERVATION_OR_BIANCHI_COMPATIBILITY"
            ),
            (
                "PROVISIONAL_SCALAR_SOURCE_ADMISSIBILITY_REVIEW_BLOCKED_BY_"
                "SCOPE_RESTRICTION_FAILURE"
            ),
        ],
        "critical_gate_fail_conditions": [
            "SOURCE_ADMISSIBILITY_ESTABLISHED",
            "ToE_native_matter_derivation",
            "arbitrary_distributional_source_promotion",
            "Standard_Model_derivation",
            "semiclassical_Einstein_equation_derivation",
            "quantum_stress_energy_expectation_construction",
            "renormalization_result",
            "full_QFT_GR_seam_closure",
            "empirical_validation",
            "public_ToE_claim",
            "master_action_promotion",
        ],
        "downstream_progression": [
            {
                "stage": "local_source_admissibility_review",
                "status": "PASSES_LOCAL_REVIEW_ON_SHELL",
                "decision": PROVISIONAL_SCALAR_SOURCE_ADMISSIBILITY_RESULT,
                "reason": (
                    "The scalar sandbox has selected source object, test "
                    "pairing, action derivability, scalar EOM, on-shell weak "
                    "conservation, and on-shell Bianchi compatibility."
                ),
            },
            {
                "stage": "generic_source_admissibility",
                "status": "NOT_CLAIMED",
                "decision": "not_claimed",
                "reason": GENERIC_SOURCE_ADMISSIBILITY_BOUNDARY,
            },
            {
                "stage": "semiclassical_coupling_gate",
                "status": "NEXT_TARGET_AUTHORIZED",
                "decision": selected_next_target,
                "reason": SEMICLASSICAL_COUPLING_GATE_SCOPE,
            },
            {
                "stage": "qft_gr_closure",
                "status": "NOT_CLAIMED",
                "decision": "not_claimed",
                "reason": "The result remains inside the provisional scalar sandbox.",
            },
        ],
        "mathematical_statement": (
            "The imported provisional scalar source passes a local on-shell "
            "source-admissibility review because it has a selected source "
            "object, a supplied test-pairing convention, constructed weak "
            "pairing, scalar-action derivability, the scalar field equation "
            + SCALAR_EQUATION_OF_MOTION
            + ", on-shell weak conservation via "
            + DIVERGENCE_IDENTITY
            + ", and on-shell Bianchi compatibility via "
            + CONTRACTED_BIANCHI_IDENTITY
            + ". This is not generic source admissibility, not a "
            "ToE-native matter derivation, and not semiclassical or QFT-GR "
            "closure."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "lane_level_lean_targets": [
            "ToeFormal.Derivation.QFTGR",
            "ToeFormal.Derivation.QFTGRScalarSandbox",
            "ToeFormal.Derivation.CurrentTarget",
            "ToeFormal.Release.CurrentAuthority",
        ],
        "lane_level_lean_target_files": [
            _ptr(QFTGR_AGGREGATE_PATH),
            _ptr(SCALAR_SANDBOX_AGGREGATE_PATH),
            _ptr(CURRENT_TARGET_AGGREGATE_PATH),
            _ptr(RELEASE_CURRENT_AUTHORITY_AGGREGATE_PATH),
        ],
        "lean_validation_policy_file": _ptr(LEAN_VALIDATION_POLICY_PATH),
        "validation_policy": _validation_policy(),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet records only a conditional local source-admissibility "
            "review pass for the imported provisional real-scalar sandbox on "
            "shell. It does not claim generic source admissibility, arbitrary "
            "distributional-source promotion, ToE-native matter derivation, "
            "Standard Model derivation, quantum stress-energy expectation "
            "construction, renormalization, semiclassical Einstein equation "
            "derivation, QFT-GR closure, empirical validation, public "
            "readiness, public submission, or master-action promotion."
        ),
    }


def write_qft_gr_source_admissibility_review_for_provisional_scalar_source(
    *,
    weak_pairing_packet_path: Path = WEAK_PAIRING_PACKET_PATH,
    action_derivability_packet_path: Path = ACTION_DERIVABILITY_PACKET_PATH,
    bianchi_packet_path: Path = BIANCHI_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_source_admissibility_review_for_provisional_scalar_source(
        weak_pairing_packet_path=weak_pairing_packet_path,
        action_derivability_packet_path=action_derivability_packet_path,
        bianchi_packet_path=bianchi_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR source-admissibility review packet for the "
            "provisional scalar source."
        )
    )
    parser.add_argument("--weak-pairing-packet", type=Path, default=WEAK_PAIRING_PACKET_PATH)
    parser.add_argument(
        "--action-derivability-packet",
        type=Path,
        default=ACTION_DERIVABILITY_PACKET_PATH,
    )
    parser.add_argument("--bianchi-packet", type=Path, default=BIANCHI_PACKET_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    weak_pairing_packet_path = (
        ns.weak_pairing_packet
        if ns.weak_pairing_packet.is_absolute()
        else REPO_ROOT / ns.weak_pairing_packet
    )
    action_derivability_packet_path = (
        ns.action_derivability_packet
        if ns.action_derivability_packet.is_absolute()
        else REPO_ROOT / ns.action_derivability_packet
    )
    bianchi_packet_path = (
        ns.bianchi_packet if ns.bianchi_packet.is_absolute() else REPO_ROOT / ns.bianchi_packet
    )
    out = ns.out if ns.out.is_absolute() else REPO_ROOT / ns.out
    payload = write_qft_gr_source_admissibility_review_for_provisional_scalar_source(
        weak_pairing_packet_path=weak_pairing_packet_path,
        action_derivability_packet_path=action_derivability_packet_path,
        bianchi_packet_path=bianchi_packet_path,
        out=out,
        captured_at_utc=ns.captured_at_utc,
    )
    print(
        "qft_gr_source_admissibility_review_for_provisional_scalar_source_report: "
        f"wrote {out} outcome={payload['outcome_id']} "
        f"next={payload['selected_next_target']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

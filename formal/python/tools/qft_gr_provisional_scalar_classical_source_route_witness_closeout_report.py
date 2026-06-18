from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_action_derivability_retry_with_provisional_matter_sector_report import (
    ACTION_DERIVABILITY_RESULT,
    SCALAR_ACTION,
    SCALAR_LAGRANGIAN,
    SELECTED_ACTION_GENERATED_SOURCE_SUBCLASS_ID,
    SELECTED_FIELD_CONTENT,
    SELECTED_PROVISIONAL_MATTER_SECTOR_ID,
)
from formal.python.tools.qft_gr_bianchi_compatibility_test_for_provisional_scalar_stress_energy_source_report import (
    BIANCHI_COMPATIBILITY_RESULT,
    BIANCHI_COMPATIBILITY_STATEMENT,
    CONTRACTED_BIANCHI_IDENTITY,
    METRIC_COMPATIBILITY_IDENTITY,
)
from formal.python.tools.qft_gr_classical_einstein_scalar_coupling_route_packet_for_provisional_scalar_source_report import (
    CLASSICAL_EINSTEIN_SCALAR_COUPLING_RESULT,
    CLASSICAL_EINSTEIN_SCALAR_EQUATION_FORM,
    LEFT_HAND_SIDE_DIVERGENCE_IDENTITY,
)
from formal.python.tools.qft_gr_classical_einstein_scalar_coupling_route_packet_result_review_report import (
    CLASSICAL_ROUTE_REVIEW_RESULT,
    DEFAULT_OUT as RESULT_REVIEW_PACKET_PATH,
    KNOWN_SCALAR_ROUTE_STATEMENT,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as RESULT_REVIEW_OUTCOME,
    POSITIVE_LOCAL_CLASSICAL_SOURCE_WITNESS_CLASSIFICATION,
    SCHEMA_ID as RESULT_REVIEW_SCHEMA_ID,
)
from formal.python.tools.qft_gr_semiclassical_coupling_gate_scope_review_for_provisional_scalar_source_report import (
    SEMICLASSICAL_COUPLING_NOT_AUTHORIZED_RESULT,
)
from formal.python.tools.qft_gr_source_admissibility_review_for_provisional_scalar_source_report import (
    PROVISIONAL_SCALAR_SOURCE_ADMISSIBILITY_RESULT,
)
from formal.python.tools.qft_gr_weak_conservation_test_for_provisional_scalar_stress_energy_source_report import (
    DIVERGENCE_IDENTITY,
    ON_SHELL_CONSERVATION_STATEMENT,
    SCALAR_EQUATION_OF_MOTION,
    STRESS_ENERGY_COVARIANT_EXPRESSION,
    WEAK_CONSERVATION_RESULT,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-18T00:00:00Z"

SCHEMA_ID = (
    "QFT_GR_PROVISIONAL_SCALAR_CLASSICAL_SOURCE_ROUTE_WITNESS_CLOSEOUT_"
    "20260618_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "QFT_GR_PROVISIONAL_SCALAR_CLASSICAL_SOURCE_ROUTE_WITNESS_CLOSEOUT_v0"
CLOSEOUT_RESULT = (
    "QFT_GR_PROVISIONAL_SCALAR_CLASSICAL_SOURCE_ROUTE_WITNESS_CLOSED_AS_"
    "POSITIVE_CLASSICAL_SANDBOX_NO_QFT_GR_OR_TOE_NATIVE_CLOSURE"
)
OUTCOME_ID = CLOSEOUT_RESULT
PACKET_CLASSIFICATION = (
    "qft_gr_provisional_scalar_classical_source_route_witness_closeout_closes_"
    "positive_imported_classical_sandbox_without_qft_gr_or_toe_native_closure"
)
NEXT_TARGET = "prepare_toe_native_matter_sector_definition_packet"
NEXT_TARGET_KIND = "toe_native_matter_sector_definition_packet_preparation"
AUXILIARY_HYGIENE_TARGET = (
    "prepare_status_surface_stale_current_token_quarantine_for_public_summary_surfaces"
)
LEAN_VALIDATION_POLICY_ID = "TIERED_LEAN_VALIDATION_POLICY_FOR_PACKET_WORK_v0"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_PROVISIONAL_SCALAR_CLASSICAL_SOURCE_ROUTE_WITNESS_CLOSEOUT_"
    "20260618_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRProvisionalScalarClassicalSourceRouteWitnessCloseout.lean"
)
QFTGR_AGGREGATE_PATH = (
    REPO_ROOT / "formal" / "toe_formal" / "ToeFormal" / "Derivation" / "QFTGR.lean"
)
SCALAR_SANDBOX_AGGREGATE_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRScalarSandbox.lean"
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
    REPO_ROOT / "formal" / "docs" / "release" / "LEAN_VALIDATION_TIER_POLICY_v0.md"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _closeout_requirements() -> list[dict[str, str]]:
    return [
        {
            "row_id": "scalar_action_derived_source_carried_forward",
            "status": "closed_as_positive_witness_input",
            "evidence": ACTION_DERIVABILITY_RESULT,
            "assessment": (
                "The witness retains the imported real-scalar action-derived "
                "stress-energy source as its source object."
            ),
        },
        {
            "row_id": "on_shell_weak_conservation_carried_forward",
            "status": "closed_as_positive_witness_input",
            "evidence": WEAK_CONSERVATION_RESULT,
            "assessment": (
                "The witness remains conditional on the scalar equation of "
                "motion and does not claim off-shell or arbitrary-phi "
                "conservation."
            ),
        },
        {
            "row_id": "on_shell_bianchi_compatibility_carried_forward",
            "status": "closed_as_positive_witness_input",
            "evidence": BIANCHI_COMPATIBILITY_RESULT,
            "assessment": (
                "The witness uses only the conditional Bianchi-compatible "
                "scalar source route under Levi-Civita metric compatibility "
                "and constant coupling assumptions."
            ),
        },
        {
            "row_id": "classical_coupling_route_result_reviewed",
            "status": "closed_as_positive_witness_input",
            "evidence": CLASSICAL_ROUTE_REVIEW_RESULT,
            "assessment": (
                "The classical Einstein-scalar route has been reviewed and "
                "accepted only as a provisional on-shell classical source route."
            ),
        },
        {
            "row_id": "witness_classified_provisional_imported_classical",
            "status": "closed_as_positive_witness",
            "evidence": POSITIVE_LOCAL_CLASSICAL_SOURCE_WITNESS_CLASSIFICATION,
            "assessment": (
                "The witness is explicitly provisional, imported, scalar, "
                "classical, and local."
            ),
        },
        {
            "row_id": "toe_native_matter_derivation_false",
            "status": "nonclaim_preserved",
            "evidence": "toe_native_matter_derivation_claimed=false",
            "assessment": (
                "The witness does not replace the imported scalar sandbox with "
                "a ToE-native matter/source sector."
            ),
        },
        {
            "row_id": "semiclassical_coupling_false",
            "status": "nonclaim_preserved",
            "evidence": SEMICLASSICAL_COUPLING_NOT_AUTHORIZED_RESULT,
            "assessment": (
                "The witness does not authorize a quantum stress-energy "
                "expectation or semiclassical Einstein equation."
            ),
        },
        {
            "row_id": "qft_gr_closure_false",
            "status": "nonclaim_preserved",
            "evidence": "qft_gr_closure_claimed=false; qft_gr_seam_closed=false",
            "assessment": (
                "The witness closes no QFT-GR source map, seam, or release "
                "blocker."
            ),
        },
        {
            "row_id": "master_action_promotion_false",
            "status": "nonclaim_preserved",
            "evidence": "master_action_promoted=false",
            "assessment": (
                "The witness does not promote the candidate master action."
            ),
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "qft_gr_provisional_scalar_classical_source_route_witness_closeout"
        ),
        "tiered_lean_validation_policy_formalized": True,
        "routine_packet_validation_tiers": [
            "touched Lean marker",
            "smallest affected Lake target",
            "lane aggregate",
            "current authority target",
        ],
        "release_preservation_validation": "full ToeFormal aggregate when feasible",
        "aggregate_timeout_with_steady_progress_interpretation": (
            "incomplete_validation_not_mathematical_failure"
        ),
        "toeformal_import_update_requires_preservation_status": True,
        "aggregate_lean_validation_status_for_packet": "NOT_RUN",
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
        "full_security_scan_required": False,
    }


def build_qft_gr_provisional_scalar_classical_source_route_witness_closeout(
    *,
    result_review_packet_path: Path = RESULT_REVIEW_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    review_packet = _read_json(result_review_packet_path)
    closeout_requirements = _closeout_requirements()
    forbidden_claims = [
        "source_map_closed",
        "qft_gr_solved",
        "semiclassical_source_established",
        "toe_matter_sector_derived",
        "canonical_master_action_promoted",
    ]
    acceptance_criteria = {
        "consumes_expected_witness_closeout_target": (
            review_packet.get("selected_next_target") == CONSUMED_TARGET
        ),
        "result_review_packet_available_and_accepted": (
            review_packet.get("schema_id") == RESULT_REVIEW_SCHEMA_ID
            and review_packet.get("outcome_id") == RESULT_REVIEW_OUTCOME
            and review_packet.get("accepted") is True
        ),
        "scalar_action_derived_source_carried_forward": (
            ACTION_DERIVABILITY_RESULT
            == "ACTION_DERIVABILITY_CONSTRUCTED_FOR_PROVISIONAL_REAL_SCALAR_TEST_SECTOR_NO_TOE_NATIVE_MATTER_DERIVATION"
            and review_packet.get("stress_energy_covariant_expression")
            == STRESS_ENERGY_COVARIANT_EXPRESSION
        ),
        "on_shell_weak_conservation_carried_forward": (
            WEAK_CONSERVATION_RESULT
            == "WEAK_CONSERVATION_CONSTRUCTED_FOR_PROVISIONAL_SCALAR_SOURCE_ON_SHELL_NO_SOURCE_ADMISSIBILITY"
            and review_packet.get("scalar_equation_of_motion")
            == SCALAR_EQUATION_OF_MOTION
            and review_packet.get("weak_conservation_identity") == DIVERGENCE_IDENTITY
            and review_packet.get("on_shell_required") is True
        ),
        "on_shell_bianchi_compatibility_carried_forward": (
            BIANCHI_COMPATIBILITY_RESULT
            == "BIANCHI_COMPATIBILITY_CONSTRUCTED_FOR_PROVISIONAL_SCALAR_SOURCE_ON_SHELL_NO_QFT_GR_CLOSURE"
            and BIANCHI_COMPATIBILITY_STATEMENT
            == "Under scalar EOM, Levi-Civita metric compatibility, and constant G_N and Lambda, the provisional scalar source is compatible with the contracted Bianchi identity."
        ),
        "classical_coupling_route_result_reviewed": (
            review_packet.get("review_result") == CLASSICAL_ROUTE_REVIEW_RESULT
            and review_packet.get("classical_route_result_review_accepted") is True
            and review_packet.get("classical_einstein_scalar_coupling_equation")
            == CLASSICAL_EINSTEIN_SCALAR_EQUATION_FORM
        ),
        "witness_classified_provisional_imported_classical": (
            review_packet.get("positive_local_classical_source_witness_classification")
            == POSITIVE_LOCAL_CLASSICAL_SOURCE_WITNESS_CLASSIFICATION
            and review_packet.get("provisional_classical_sandbox_route_only") is True
        ),
        "toe_native_matter_derivation_false": (
            review_packet.get("toe_native_matter_derivation_claimed") is False
            and review_packet.get("toe_native_matter_sector_defined") is False
        ),
        "semiclassical_coupling_false": (
            review_packet.get("semiclassical_coupling_authorized") is False
            and review_packet.get("semiclassical_coupling_claimed") is False
            and review_packet.get("semiclassical_einstein_equation_derived") is False
        ),
        "qft_gr_closure_false": (
            review_packet.get("qft_gr_closure_claimed") is False
            and review_packet.get("qft_gr_seam_closed") is False
            and review_packet.get("qft_gr_source_map_closure_authorized") is False
        ),
        "master_action_promotion_false": (
            review_packet.get("master_action_promoted") is False
            and review_packet.get("master_action_promotion_authorized") is False
        ),
        "closeout_requirements_all_satisfied": all(
            row["status"]
            in {
                "closed_as_positive_witness_input",
                "closed_as_positive_witness",
                "nonclaim_preserved",
            }
            for row in closeout_requirements
        ),
    }
    accepted = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if accepted
        else "REMEDIATE_QFT_GR_PROVISIONAL_SCALAR_CLASSICAL_SOURCE_ROUTE_WITNESS_CLOSEOUT"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_NONLIVE_WITNESS_CLOSEOUT",
        "captured_at_utc": captured_at_utc,
        "prepared": accepted,
        "accepted": accepted,
        "outcome_id": OUTCOME_ID
        if accepted
        else "QFT_GR_PROVISIONAL_SCALAR_CLASSICAL_SOURCE_ROUTE_WITNESS_CLOSEOUT_REQUIRES_REMEDIATION",
        "closeout_result": CLOSEOUT_RESULT,
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "reviewed_result_review_artifact_id": review_packet.get("schema_id"),
        "reviewed_result_review_outcome": review_packet.get("outcome_id"),
        "known_scalar_route_statement": KNOWN_SCALAR_ROUTE_STATEMENT,
        "positive_local_classical_source_witness_classification": (
            POSITIVE_LOCAL_CLASSICAL_SOURCE_WITNESS_CLASSIFICATION
        ),
        "positive_local_classical_source_witness_closed": accepted,
        "positive_local_classical_source_witness_candidate": True,
        "witness_closeout_completed": accepted,
        "witness_closeout_scope": (
            "positive local classical source witness for imported provisional "
            "real-scalar sandbox only"
        ),
        "scalar_sandbox_branch_closed": accepted,
        "default_scalar_sandbox_extension_authorized": False,
        "toe_native_matter_sector_definition_packet_authorized": accepted,
        "auxiliary_hygiene_target_queued": AUXILIARY_HYGIENE_TARGET,
        "auxiliary_hygiene_target_supersedes_qft_gr_live_target": False,
        "selected_provisional_matter_sector_id": SELECTED_PROVISIONAL_MATTER_SECTOR_ID,
        "selected_action_generated_source_subclass_id": (
            SELECTED_ACTION_GENERATED_SOURCE_SUBCLASS_ID
        ),
        "field_content": SELECTED_FIELD_CONTENT,
        "scalar_action": SCALAR_ACTION,
        "lagrangian_density": SCALAR_LAGRANGIAN,
        "stress_energy_covariant_expression": STRESS_ENERGY_COVARIANT_EXPRESSION,
        "scalar_equation_of_motion": SCALAR_EQUATION_OF_MOTION,
        "action_derivability_result": ACTION_DERIVABILITY_RESULT,
        "weak_conservation_result": WEAK_CONSERVATION_RESULT,
        "weak_conservation_identity": DIVERGENCE_IDENTITY,
        "on_shell_conservation_statement": ON_SHELL_CONSERVATION_STATEMENT,
        "on_shell_required": True,
        "bianchi_compatibility_result": BIANCHI_COMPATIBILITY_RESULT,
        "bianchi_compatibility_statement": BIANCHI_COMPATIBILITY_STATEMENT,
        "contracted_bianchi_identity": CONTRACTED_BIANCHI_IDENTITY,
        "metric_compatibility_identity": METRIC_COMPATIBILITY_IDENTITY,
        "provisional_scalar_source_admissibility_result": (
            PROVISIONAL_SCALAR_SOURCE_ADMISSIBILITY_RESULT
        ),
        "classical_einstein_scalar_coupling_result": (
            CLASSICAL_EINSTEIN_SCALAR_COUPLING_RESULT
        ),
        "classical_route_result_review_result": CLASSICAL_ROUTE_REVIEW_RESULT,
        "classical_route_result_review_accepted": True,
        "classical_einstein_scalar_coupling_equation": (
            CLASSICAL_EINSTEIN_SCALAR_EQUATION_FORM
        ),
        "left_hand_side_divergence_identity": LEFT_HAND_SIDE_DIVERGENCE_IDENTITY,
        "route_internal_compatibility_constructed": True,
        "provisional_classical_sandbox_route_only": True,
        "imported_provisional_scalar_sector_only": True,
        "proof_depth_label": review_packet.get("proof_depth_label"),
        "formal_differential_geometry_theorem_backed": False,
        "record_validated": True,
        "symbolic_calculation_recorded": True,
        "closeout_requirements": closeout_requirements,
        "closeout_requirement_count": len(closeout_requirements),
        "closeout_requirement_satisfied_count": len(closeout_requirements),
        "acceptance_criteria": acceptance_criteria,
        "forbidden_claims": forbidden_claims,
        "semiclassical_coupling_authorized": False,
        "semiclassical_coupling_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "semiclassical_source_established": False,
        "renormalized_stress_energy_expectation_constructed": False,
        "renormalized_expectation_value_constructed": False,
        "renormalized_stress_energy_constructed": False,
        "quantum_state_source_constructed": False,
        "quantum_state_supplied": False,
        "quantum_stress_energy_operator_constructed": False,
        "stress_energy_operator_constructed": False,
        "quantum_stress_energy_expectation_constructed": False,
        "renormalization_scheme_supplied": False,
        "renormalization_result_claimed": False,
        "state_domain_supplied": False,
        "state_expectation_functional_link_claimed": False,
        "anomaly_or_regularization_controls_supplied": False,
        "toe_native_matter_source_route_defined": False,
        "toe_native_matter_sector_defined": False,
        "toe_matter_model_derived": False,
        "toe_native_matter_derivation_claimed": False,
        "toe_matter_sector_derived": False,
        "generic_source_admissibility_claimed": False,
        "source_admissibility_claimed": False,
        "source_admissibility_completed": False,
        "source_map_closed": False,
        "arbitrary_distributional_source_admissibility_claimed": False,
        "arbitrary_distributional_source_promoted": False,
        "solution_existence_claimed": False,
        "solution_uniqueness_claimed": False,
        "regularity_analysis_completed": False,
        "boundary_initial_data_supplied": False,
        "coupled_pde_solution_constructed": False,
        "coupled_einstein_scalar_system_solved": False,
        "global_wellposedness_claimed": False,
        "standard_model_derivation_claimed": False,
        "qft_gr_solved": False,
        "qft_gr_closure_claimed": False,
        "qft_gr_seam_closed": False,
        "qft_gr_source_map_closure_authorized": False,
        "empirical_validation_claimed": False,
        "public_readiness_claimed": False,
        "public_submission_authorized": False,
        "canonical_master_action_promoted": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "phase2_readiness_claim": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "downstream_progression": [
            {
                "stage": "provisional_scalar_classical_source_route_witness_closeout",
                "status": "CLOSED_AS_POSITIVE_LOCAL_CLASSICAL_SOURCE_WITNESS",
                "decision": CLOSEOUT_RESULT,
                "reason": (
                    "The imported scalar sandbox traversed the local classical "
                    "source ladder and is closed without QFT-GR or ToE-native "
                    "matter closure."
                ),
            },
            {
                "stage": "scalar_sandbox_extension",
                "status": "NOT_DEFAULT_NEXT_WORK",
                "decision": "not_selected",
                "reason": (
                    "The scalar sandbox has served its witness purpose; the "
                    "next unification question is native matter/source definition."
                ),
            },
            {
                "stage": "toe_native_matter_sector_definition",
                "status": "NEXT_TARGET_AUTHORIZED",
                "decision": selected_next_target,
                "reason": (
                    "The next target should test whether the ToE can define its "
                    "own matter/source sector instead of importing the scalar sandbox."
                ),
            },
            {
                "stage": "stale_current_token_quarantine",
                "status": "QUEUED_NON_SUPERSEDING_HYGIENE",
                "decision": AUXILIARY_HYGIENE_TARGET,
                "reason": (
                    "Status-surface hygiene remains queued but does not supersede "
                    "the physics live target."
                ),
            },
        ],
        "mathematical_statement": (
            KNOWN_SCALAR_ROUTE_STATEMENT
            + " This closeout classifies that chain as a positive local "
            "classical source witness for the imported provisional real-scalar "
            "sandbox only. It does not close QFT-GR, authorize semiclassical "
            "gravity, derive ToE-native matter, or promote the master action."
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
        "non_claim_boundary": (
            "This closeout records a positive local classical source witness "
            "for the imported provisional real-scalar sandbox only. It does "
            "not claim source-map closure, QFT-GR solution, semiclassical "
            "source establishment, ToE-native matter-sector derivation, "
            "canonical master-action promotion, empirical validation, public "
            "readiness, or release authorization."
        ),
    }


def write_qft_gr_provisional_scalar_classical_source_route_witness_closeout(
    *,
    result_review_packet_path: Path = RESULT_REVIEW_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_provisional_scalar_classical_source_route_witness_closeout(
        result_review_packet_path=result_review_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR provisional scalar classical source route "
            "witness closeout packet."
        )
    )
    parser.add_argument("--result-review-packet", type=Path, default=RESULT_REVIEW_PACKET_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    result_review_packet_path = (
        args.result_review_packet
        if args.result_review_packet.is_absolute()
        else REPO_ROOT / args.result_review_packet
    )
    out = args.out if args.out.is_absolute() else REPO_ROOT / args.out
    payload = write_qft_gr_provisional_scalar_classical_source_route_witness_closeout(
        result_review_packet_path=result_review_packet_path,
        out=out,
        captured_at_utc=args.captured_at_utc,
    )
    print(
        "qft_gr_provisional_scalar_classical_source_route_witness_closeout_report: "
        f"wrote {out} outcome={payload['outcome_id']} "
        f"next={payload['selected_next_target']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

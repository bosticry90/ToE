from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_source_admissibility_review_for_provisional_scalar_source_report import (
    DEFAULT_OUT as SOURCE_ADMISSIBILITY_PACKET_PATH,
    OUTCOME_ID as SOURCE_ADMISSIBILITY_OUTCOME,
    PROVISIONAL_SCALAR_SOURCE_ADMISSIBILITY_RESULT,
    SCHEMA_ID as SOURCE_ADMISSIBILITY_SCHEMA_ID,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-18T00:00:00Z"

SCHEMA_ID = (
    "QFT_GR_SEMICLASSICAL_COUPLING_GATE_SCOPE_REVIEW_FOR_PROVISIONAL_"
    "SCALAR_SOURCE_20260618_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "QFT_GR_SEMICLASSICAL_COUPLING_GATE_SCOPE_REVIEW_FOR_PROVISIONAL_"
    "SCALAR_SOURCE_v0"
)
CONSUMED_TARGET = (
    "prepare_qft_gr_semiclassical_coupling_gate_scope_review_for_provisional_"
    "scalar_source"
)
NEXT_TARGET = (
    "prepare_qft_gr_classical_einstein_scalar_coupling_route_packet_for_"
    "provisional_scalar_source"
)
NEXT_TARGET_KIND = (
    "qft_gr_classical_einstein_scalar_coupling_route_packet_for_provisional_"
    "scalar_source_preparation"
)
AUXILIARY_HYGIENE_TARGET = (
    "prepare_status_surface_stale_current_token_quarantine_for_public_summary_"
    "surfaces"
)
SEMICLASSICAL_COUPLING_GATE_RESULT = (
    "CLASSICAL_EINSTEIN_SCALAR_COUPLING_ROUTE_RECORDED_SEMICLASSICAL_"
    "COUPLING_NOT_AUTHORIZED"
)
SEMICLASSICAL_COUPLING_NOT_AUTHORIZED_RESULT = (
    "SEMICLASSICAL_COUPLING_NOT_AUTHORIZED_FOR_PROVISIONAL_CLASSICAL_SCALAR_"
    "SOURCE_REQUIRES_QUANTUM_EXPECTATION_RENORMALIZATION_AND_STATE_DOMAIN"
)
OUTCOME_ID = (
    "QFT_GR_SEMICLASSICAL_COUPLING_GATE_SCOPE_REVIEW_FOR_PROVISIONAL_SCALAR_"
    "SOURCE_PREPARED_WITH_CLASSICAL_EINSTEIN_SCALAR_COUPLING_ROUTE_RECORDED_"
    "AND_SEMICLASSICAL_COUPLING_NOT_AUTHORIZED"
)
PACKET_CLASSIFICATION = (
    "qft_gr_semiclassical_coupling_gate_scope_review_for_provisional_scalar_"
    "source_records_classical_route_and_blocks_semiclassical_coupling"
)
PROOF_DEPTH_LABEL = "SYMBOLIC_CALCULATION_RECORDED_RECORD_VALIDATED"

CLASSICAL_EINSTEIN_SCALAR_EQUATION_FORM = (
    "G_{mu nu} + Lambda g_{mu nu} = 8 pi G_N T^{scalar}_{mu nu}"
)
SEMICLASSICAL_EINSTEIN_EXPECTATION_FORM = (
    "G_{mu nu} + Lambda g_{mu nu} = 8 pi G_N <T_hat_{mu nu}>_ren"
)
TOE_NATIVE_ROUTE_STATUS = "TOE_NATIVE_MATTER_SECTOR_NOT_YET_DEFINED"
LEAN_VALIDATION_POLICY_ID = "TIERED_LEAN_VALIDATION_POLICY_FOR_PACKET_WORK_v0"

DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_SEMICLASSICAL_COUPLING_GATE_SCOPE_REVIEW_FOR_PROVISIONAL_"
    "SCALAR_SOURCE_20260618_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRSemiclassicalCouplingGateScopeReviewForProvisionalScalarSource.lean"
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


def _route_review_rows() -> list[dict[str, Any]]:
    return [
        {
            "route_id": "classical_einstein_scalar_coupling",
            "status": "route_recorded_classical_sandbox_packet_authorized",
            "equation_form": CLASSICAL_EINSTEIN_SCALAR_EQUATION_FORM,
            "reason": (
                "The provisional scalar chain supplies a classical scalar "
                "stress-energy source that is action-derived, conserved on "
                "shell, Bianchi-compatible on shell, and locally reviewed "
                "under scalar sandbox assumptions."
            ),
            "claim_ceiling": (
                "classical sandbox route only; no semiclassical expectation "
                "value and no ToE-native matter derivation"
            ),
        },
        {
            "route_id": "semiclassical_quantum_expectation_coupling",
            "status": "not_authorized",
            "equation_form": SEMICLASSICAL_EINSTEIN_EXPECTATION_FORM,
            "missing_requirements": [
                "quantum_state",
                "stress_energy_operator",
                "renormalized_expectation_value",
                "state_domain",
                "renormalization_scheme",
                "anomaly_or_regularization_controls",
            ],
            "reason": (
                "The available source is a classical scalar stress-energy "
                "tensor, not a renormalized quantum expectation value."
            ),
        },
        {
            "route_id": "toe_native_matter_source_route",
            "status": "not_defined",
            "reason": TOE_NATIVE_ROUTE_STATUS,
            "claim_ceiling": "no ToE-native matter/source route is supplied",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "policy_id": LEAN_VALIDATION_POLICY_ID,
        "checkpoint_type": (
            "qft_gr_semiclassical_coupling_gate_scope_review_for_provisional_"
            "scalar_source"
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
        "aggregate_lean_validation_status_allowed_values": [
            "PASSED",
            "INCOMPLETE_TIMEOUT_STEADY_PROGRESS",
            "FAILED",
            "NOT_RUN",
        ],
        "aggregate_lean_validation_completion_claimed": False,
        "aggregate_lean_validation_mathematical_failure_claimed": False,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_ci_parity_required": False,
        "full_security_scan_required": False,
    }


def build_qft_gr_semiclassical_coupling_gate_scope_review_for_provisional_scalar_source(
    *,
    source_admissibility_packet_path: Path = SOURCE_ADMISSIBILITY_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    source_packet = _read_json(source_admissibility_packet_path)
    route_rows = _route_review_rows()
    route_status = {row["route_id"]: row["status"] for row in route_rows}
    acceptance_criteria = {
        "consumes_expected_live_target": (
            source_packet.get("selected_next_target") == CONSUMED_TARGET
        ),
        "source_packet_available": (
            source_packet.get("schema_id") == SOURCE_ADMISSIBILITY_SCHEMA_ID
            and source_packet.get("outcome_id") == SOURCE_ADMISSIBILITY_OUTCOME
        ),
        "local_scalar_source_admissibility_review_passed": (
            source_packet.get("provisional_scalar_source_admissibility_result")
            == PROVISIONAL_SCALAR_SOURCE_ADMISSIBILITY_RESULT
            and source_packet.get("local_source_admissibility_review_passed") is True
        ),
        "semiclassical_requirements_absent": (
            source_packet.get("quantum_stress_energy_expectation_constructed")
            is False
            and source_packet.get("renormalized_stress_energy_constructed") is False
            and source_packet.get("state_expectation_functional_link_claimed")
            is False
        ),
        "qft_gr_closure_still_denied": (
            source_packet.get("qft_gr_closure_claimed") is False
            and source_packet.get("qft_gr_seam_closed") is False
        ),
        "route_split_recorded": route_status
        == {
            "classical_einstein_scalar_coupling": (
                "route_recorded_classical_sandbox_packet_authorized"
            ),
            "semiclassical_quantum_expectation_coupling": "not_authorized",
            "toe_native_matter_source_route": "not_defined",
        },
        "proof_depth_labeled": True,
        "stale_token_quarantine_queued_non_superseding": True,
    }
    prepared = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if prepared
        else "REMEDIATE_QFT_GR_SEMICLASSICAL_COUPLING_GATE_SCOPE_REVIEW"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_NONLIVE_GATE_SCOPE_RESULT",
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "accepted": prepared,
        "outcome_id": OUTCOME_ID
        if prepared
        else "QFT_GR_SEMICLASSICAL_COUPLING_GATE_SCOPE_REVIEW_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "auxiliary_hygiene_target_queued": AUXILIARY_HYGIENE_TARGET,
        "auxiliary_hygiene_target_supersedes_qft_gr_live_target": False,
        "authorized_by_source_admissibility_artifact_id": source_packet.get("schema_id"),
        "authorized_by_source_admissibility_outcome": source_packet.get("outcome_id"),
        "source_admissibility_result": (
            PROVISIONAL_SCALAR_SOURCE_ADMISSIBILITY_RESULT
        ),
        "semiclassical_coupling_gate_result": SEMICLASSICAL_COUPLING_GATE_RESULT,
        "semiclassical_coupling_not_authorized_result": (
            SEMICLASSICAL_COUPLING_NOT_AUTHORIZED_RESULT
        ),
        "proof_depth_label": PROOF_DEPTH_LABEL,
        "formal_differential_geometry_theorem_backed": False,
        "record_validated": True,
        "symbolic_calculation_recorded": True,
        "route_review_rows": route_rows,
        "route_review_row_count": len(route_rows),
        "classical_einstein_scalar_coupling_route_recorded": True,
        "classical_einstein_scalar_coupling_route_packet_authorized": True,
        "classical_einstein_scalar_coupling_constructed": False,
        "classical_einstein_scalar_coupling_claimed_scope": (
            "classical sandbox route preparation only for the provisional "
            "real-scalar stress-energy source"
        ),
        "classical_einstein_scalar_equation_form": (
            CLASSICAL_EINSTEIN_SCALAR_EQUATION_FORM
        ),
        "semiclassical_einstein_expectation_form": (
            SEMICLASSICAL_EINSTEIN_EXPECTATION_FORM
        ),
        "semiclassical_coupling_authorized": False,
        "semiclassical_coupling_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "semiclassical_quantum_expectation_route_authorized": False,
        "quantum_state_supplied": False,
        "stress_energy_operator_constructed": False,
        "quantum_stress_energy_expectation_constructed": False,
        "renormalized_expectation_value_constructed": False,
        "renormalized_stress_energy_constructed": False,
        "renormalization_scheme_supplied": False,
        "renormalization_result_claimed": False,
        "state_domain_supplied": False,
        "state_expectation_functional_link_claimed": False,
        "anomaly_or_regularization_controls_supplied": False,
        "toe_native_matter_source_route_defined": False,
        "toe_native_matter_sector_defined": False,
        "toe_matter_model_derived": False,
        "toe_native_matter_derivation_claimed": False,
        "source_admissibility_claimed": False,
        "source_admissibility_completed": False,
        "local_source_admissibility_review_passed": True,
        "provisional_scalar_source_passes_local_source_admissibility_review": True,
        "arbitrary_distributional_source_admissibility_claimed": False,
        "arbitrary_distributional_source_promoted": False,
        "standard_model_derivation_claimed": False,
        "qft_gr_closure_claimed": False,
        "qft_gr_seam_closed": False,
        "qft_gr_source_map_closure_authorized": False,
        "empirical_validation_claimed": False,
        "public_readiness_claimed": False,
        "public_submission_authorized": False,
        "master_action_promoted": False,
        "master_action_promotion_authorized": False,
        "phase2_readiness_claim": False,
        "pillar_completion_inferred": False,
        "seam_closure_claim": False,
        "accepted_outcomes_considered": [
            SEMICLASSICAL_COUPLING_GATE_RESULT,
            SEMICLASSICAL_COUPLING_NOT_AUTHORIZED_RESULT,
            "SEMICLASSICAL_COUPLING_GATE_BLOCKED_BY_ROUTE_STATUS_AMBIGUITY",
        ],
        "critical_gate_fail_conditions": [
            "semiclassical_coupling_authorized",
            "semiclassical_Einstein_equation_derivation",
            "quantum_stress_energy_expectation_construction",
            "renormalization_result",
            "state_domain_supplied",
            "ToE_native_matter_derivation",
            "QFT_GR_closure",
            "source_map_closure",
            "empirical_validation",
            "public_ToE_claim",
            "master_action_promotion",
        ],
        "downstream_progression": [
            {
                "stage": "classical_einstein_scalar_coupling_route",
                "status": "CLASSICAL_SANDBOX_ROUTE_PACKET_AUTHORIZED",
                "decision": selected_next_target,
                "reason": (
                    "The scalar source may be used for a bounded classical "
                    "Einstein-scalar route packet, without claiming a "
                    "semiclassical expectation-value source."
                ),
            },
            {
                "stage": "semiclassical_quantum_expectation_route",
                "status": "NOT_AUTHORIZED",
                "decision": SEMICLASSICAL_COUPLING_NOT_AUTHORIZED_RESULT,
                "reason": (
                    "No quantum state, stress-energy operator, renormalized "
                    "expectation value, state domain, renormalization scheme, "
                    "or anomaly/regularization control is supplied."
                ),
            },
            {
                "stage": "toe_native_matter_source_route",
                "status": "NOT_DEFINED",
                "decision": TOE_NATIVE_ROUTE_STATUS,
                "reason": "The scalar source is imported as a provisional sandbox.",
            },
            {
                "stage": "status_surface_hygiene",
                "status": "QUEUED_NON_SUPERSEDING",
                "decision": AUXILIARY_HYGIENE_TARGET,
                "reason": (
                    "Stale current-token quarantine remains queued as hygiene "
                    "and does not replace the active QFT-GR live target."
                ),
            },
        ],
        "mathematical_statement": (
            "The provisional scalar packet supplies a classical stress-energy "
            "source for a bounded Einstein-scalar sandbox route. It does not "
            "supply the semiclassical source <T_hat_{mu nu}>_ren required for "
            + SEMICLASSICAL_EINSTEIN_EXPECTATION_FORM
            + ". Semiclassical coupling remains unauthorized."
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
            "This packet records a gate/scope review only. It records a "
            "classical Einstein-scalar sandbox route as a possible next packet "
            "and denies semiclassical coupling authorization because the repo "
            "does not supply a quantum state, stress-energy operator, "
            "renormalized expectation value, state domain, renormalization "
            "scheme, anomaly controls, ToE-native matter derivation, QFT-GR "
            "closure, empirical validation, public readiness, or master-action "
            "promotion."
        ),
    }


def write_qft_gr_semiclassical_coupling_gate_scope_review_for_provisional_scalar_source(
    *,
    source_admissibility_packet_path: Path = SOURCE_ADMISSIBILITY_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = (
        build_qft_gr_semiclassical_coupling_gate_scope_review_for_provisional_scalar_source(
            source_admissibility_packet_path=source_admissibility_packet_path,
            captured_at_utc=captured_at_utc,
        )
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR semiclassical coupling gate/scope review "
            "packet for the provisional scalar source."
        )
    )
    parser.add_argument("--source-admissibility-packet", type=Path, default=SOURCE_ADMISSIBILITY_PACKET_PATH)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = _parse_args(argv)
    payload = write_qft_gr_semiclassical_coupling_gate_scope_review_for_provisional_scalar_source(
        source_admissibility_packet_path=args.source_admissibility_packet,
        out=args.out,
        captured_at_utc=args.captured_at_utc,
    )
    print(
        "qft_gr_semiclassical_coupling_gate_scope_review_for_provisional_scalar_source_report: "
        f"wrote {args.out} outcome={payload['outcome_id']} "
        f"next={payload['selected_next_target']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

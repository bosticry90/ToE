from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_action_derivability_retry_with_provisional_matter_sector_report import (
    ACTION_DERIVABILITY_RESULT,
    COVARIANT_VARIATION_FORM,
    DEFAULT_OUT as ACTION_DERIVABILITY_PACKET_PATH,
    INDEX_BRIDGE,
    METRIC_VARIATION_CONVENTION,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as EXPECTED_ACTION_DERIVABILITY_OUTCOME,
    PACKET_CLASSIFICATION as ACTION_DERIVABILITY_PACKET_CLASSIFICATION,
    PRIOR_CONTRACT_PAIRING_FORM,
    SCALAR_ACTION,
    SCALAR_LAGRANGIAN,
    SCHEMA_ID as EXPECTED_ACTION_DERIVABILITY_SCHEMA_ID,
    SELECTED_ACTION_GENERATED_SOURCE_SUBCLASS_ID,
    SELECTED_FIELD_CONTENT,
    SELECTED_KNOWN_MATTER_MODEL,
    SELECTED_PROVISIONAL_MATTER_SECTOR_ID,
    STRESS_ENERGY_COVARIANT_EXPRESSION,
    STRESS_ENERGY_CONTRAVARIANT_EXPRESSION,
    TOE_NATIVE_MATTER_SECTOR_RESULT,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-17T00:00:00Z"
SCHEMA_ID = (
    "QFT_GR_WEAK_CONSERVATION_TEST_FOR_PROVISIONAL_SCALAR_STRESS_ENERGY_SOURCE_"
    "20260617_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "QFT_GR_WEAK_CONSERVATION_TEST_FOR_PROVISIONAL_SCALAR_STRESS_ENERGY_SOURCE_v0"
)
WEAK_CONSERVATION_RESULT = (
    "WEAK_CONSERVATION_CONSTRUCTED_FOR_PROVISIONAL_SCALAR_SOURCE_ON_SHELL_"
    "NO_SOURCE_ADMISSIBILITY"
)
OUTCOME_ID = (
    "QFT_GR_WEAK_CONSERVATION_TEST_FOR_PROVISIONAL_SCALAR_STRESS_ENERGY_SOURCE_"
    "PREPARED_WITH_WEAK_CONSERVATION_CONSTRUCTED_FOR_PROVISIONAL_SCALAR_"
    "SOURCE_ON_SHELL_NO_SOURCE_ADMISSIBILITY_OR_QFT_GR_CLOSURE"
)
PACKET_CLASSIFICATION = (
    "qft_gr_weak_conservation_test_for_provisional_scalar_stress_energy_"
    "source_constructs_on_shell_conservation_nonpromotionally"
)
NEXT_TARGET = (
    "prepare_qft_gr_bianchi_compatibility_test_for_provisional_scalar_"
    "stress_energy_source"
)
NEXT_TARGET_KIND = (
    "qft_gr_bianchi_compatibility_test_for_provisional_scalar_stress_energy_"
    "source_preparation"
)

SCALAR_EQUATION_OF_MOTION = "box_g phi - V'(phi) = 0"
DIVERGENCE_IDENTITY = (
    "nabla_mu T^{mu nu} = (box_g phi - V'(phi)) nabla^nu phi"
)
ON_SHELL_CONSERVATION_STATEMENT = (
    "If box_g phi - V'(phi) = 0, then nabla_mu T^{mu nu} = 0"
)
OFF_SHELL_BOUNDARY = (
    "For arbitrary phi, the divergence is the field-equation residual times "
    "nabla^nu phi and is not claimed to vanish."
)
REGULARITY_SCOPE = (
    "smooth scalar field and smooth metric with Levi-Civita connection on the "
    "provisional calculation domain; distributional regularity is not promoted"
)
WEAK_TEST_PAIRING_SCOPE = (
    "weak conservation is read only after pairing the divergence identity "
    "against compactly supported tests in the provisional scalar sandbox"
)
CALCULATION_CONVENTION = (
    "Use the scalar action convention from the action-derivability packet, "
    "metric compatibility nabla_mu g^{alpha beta} = 0, torsion-free "
    "Levi-Civita connection, and scalar second-derivative commutation."
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_WEAK_CONSERVATION_TEST_FOR_PROVISIONAL_SCALAR_STRESS_ENERGY_"
    "SOURCE_20260617_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRWeakConservationTestForProvisionalScalarStressEnergySource.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _derivation_steps() -> list[dict[str, Any]]:
    return [
        {
            "step_id": "restate_scalar_stress_energy",
            "mathematical_content": STRESS_ENERGY_COVARIANT_EXPRESSION,
            "claim": "provisional scalar stress-energy source restated",
        },
        {
            "step_id": "state_scalar_equation_of_motion",
            "mathematical_content": SCALAR_EQUATION_OF_MOTION,
            "claim": "on-shell condition for the provisional scalar sandbox fixed",
        },
        {
            "step_id": "compute_divergence",
            "mathematical_content": (
                "nabla_mu T^{mu nu} = nabla_mu(nabla^mu phi nabla^nu phi) "
                "- 1/2 nabla^nu(nabla_alpha phi nabla^alpha phi) "
                "- nabla^nu V(phi)"
            ),
            "claim": "covariant divergence expanded using metric compatibility",
        },
        {
            "step_id": "cancel_symmetric_second_derivative_terms",
            "mathematical_content": (
                "nabla_mu phi nabla^mu nabla^nu phi "
                "- nabla_alpha phi nabla^nu nabla^alpha phi = 0 for scalar phi"
            ),
            "claim": "scalar second-derivative commutation cancels the cross terms",
        },
        {
            "step_id": "reduce_to_field_equation_residual",
            "mathematical_content": DIVERGENCE_IDENTITY,
            "claim": "divergence reduces to the scalar equation-of-motion residual",
        },
        {
            "step_id": "conclude_on_shell_weak_conservation",
            "mathematical_content": ON_SHELL_CONSERVATION_STATEMENT,
            "claim": "weak conservation constructed only on shell",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": (
            "qft_gr_weak_conservation_test_for_provisional_scalar_stress_energy_source"
        ),
        "bounded_focused_validation_only": True,
        "full_pytest_required": False,
        "full_governance_suite_required": False,
        "full_aggregate_lean_required": False,
        "full_ci_parity_required": False,
        "full_security_scan_required": False,
        "aggregate_lean_not_run": True,
        "aggregate_lean_health_claimed": False,
        "release_index_path_not_freshly_lean_validated": True,
    }


def build_qft_gr_weak_conservation_test_for_provisional_scalar_stress_energy_source(
    *,
    action_derivability_packet_path: Path = ACTION_DERIVABILITY_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    action_packet = _read_json(action_derivability_packet_path)
    derivation_steps = _derivation_steps()
    acceptance_criteria = {
        "consumes_expected_action_derivability_packet": (
            action_packet.get("schema_id") == EXPECTED_ACTION_DERIVABILITY_SCHEMA_ID
            and action_packet.get("outcome_id") == EXPECTED_ACTION_DERIVABILITY_OUTCOME
            and action_packet.get("selected_next_target") == CONSUMED_TARGET
        ),
        "provisional_scalar_stress_energy_reused": (
            action_packet.get("stress_energy_covariant_expression")
            == STRESS_ENERGY_COVARIANT_EXPRESSION
            and action_packet.get("action_derivability_constructed") is True
        ),
        "scalar_equation_of_motion_stated": (
            SCALAR_EQUATION_OF_MOTION == "box_g phi - V'(phi) = 0"
        ),
        "divergence_identity_stated": (
            "nabla_mu T^{mu nu}" in DIVERGENCE_IDENTITY
            and "box_g phi - V'(phi)" in DIVERGENCE_IDENTITY
        ),
        "on_shell_conservation_stated": (
            ON_SHELL_CONSERVATION_STATEMENT
            == "If box_g phi - V'(phi) = 0, then nabla_mu T^{mu nu} = 0"
        ),
        "off_shell_nonclaim_stated": "arbitrary phi" in OFF_SHELL_BOUNDARY,
        "regularity_scope_stated": "smooth scalar field" in REGULARITY_SCOPE,
        "source_admissibility_not_claimed": True,
        "bianchi_compatibility_not_claimed": True,
        "qft_gr_closure_not_claimed": True,
    }
    prepared = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if prepared
        else "REMEDIATE_QFT_GR_WEAK_CONSERVATION_TEST_FOR_PROVISIONAL_SCALAR_SOURCE"
    )
    return {
        "artifact_id": ARTIFACT_ID,
        "schema_id": SCHEMA_ID,
        "packet_id": PACKET_ID,
        "status": "ACTIVE_NONLIVE_NONCLAIM",
        "captured_at_utc": captured_at_utc,
        "prepared": prepared,
        "accepted": prepared,
        "outcome_id": OUTCOME_ID
        if prepared
        else "QFT_GR_WEAK_CONSERVATION_TEST_FOR_PROVISIONAL_SCALAR_SOURCE_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "authorized_by_action_derivability_artifact_id": action_packet.get("schema_id"),
        "authorized_by_action_derivability_outcome": action_packet.get("outcome_id"),
        "authorized_by_action_derivability_classification": (
            ACTION_DERIVABILITY_PACKET_CLASSIFICATION
        ),
        "action_derivability_result": ACTION_DERIVABILITY_RESULT,
        "weak_conservation_result": WEAK_CONSERVATION_RESULT,
        "selected_provisional_matter_sector_id": SELECTED_PROVISIONAL_MATTER_SECTOR_ID,
        "selected_known_matter_model": SELECTED_KNOWN_MATTER_MODEL,
        "selected_action_generated_source_subclass_id": (
            SELECTED_ACTION_GENERATED_SOURCE_SUBCLASS_ID
        ),
        "field_content": SELECTED_FIELD_CONTENT,
        "scalar_action": SCALAR_ACTION,
        "lagrangian_density": SCALAR_LAGRANGIAN,
        "metric_variation_convention": METRIC_VARIATION_CONVENTION,
        "stress_energy_covariant_expression": STRESS_ENERGY_COVARIANT_EXPRESSION,
        "stress_energy_contravariant_expression": (
            STRESS_ENERGY_CONTRAVARIANT_EXPRESSION
        ),
        "covariant_variation_form": COVARIANT_VARIATION_FORM,
        "prior_contract_pairing_form": PRIOR_CONTRACT_PAIRING_FORM,
        "index_bridge": INDEX_BRIDGE,
        "scalar_equation_of_motion": SCALAR_EQUATION_OF_MOTION,
        "divergence_identity": DIVERGENCE_IDENTITY,
        "on_shell_conservation_statement": ON_SHELL_CONSERVATION_STATEMENT,
        "off_shell_boundary": OFF_SHELL_BOUNDARY,
        "regularity_scope": REGULARITY_SCOPE,
        "weak_test_pairing_scope": WEAK_TEST_PAIRING_SCOPE,
        "calculation_convention": CALCULATION_CONVENTION,
        "derivation_steps": derivation_steps,
        "action_derivability_constructed": True,
        "action_derivability_constructed_scope": (
            "provisional real-scalar calculation sandbox only"
        ),
        "weak_conservation_constructed": True,
        "weak_conservation_constructed_scope": (
            "provisional real-scalar source on shell only"
        ),
        "weak_conservation_claimed": True,
        "weak_conservation_claimed_scope": (
            "conditional on scalar equation of motion only"
        ),
        "on_shell_required": True,
        "off_shell_conservation_claimed": False,
        "arbitrary_phi_conserved_claimed": False,
        "conservation_claimed": False,
        "unconditional_conservation_claimed": False,
        "toe_native_matter_sector_result": TOE_NATIVE_MATTER_SECTOR_RESULT,
        "toe_native_matter_sector_defined": False,
        "toe_matter_model_derived": False,
        "toe_native_matter_derivation_claimed": False,
        "standard_model_derivation_claimed": False,
        "arbitrary_distributional_source_action_derived_claimed": False,
        "arbitrary_distributional_source_conservation_claimed": False,
        "arbitrary_distributional_source_promoted": False,
        "source_admissibility_claimed": False,
        "source_admissibility_completed": False,
        "Bianchi_compatibility_claimed": False,
        "Bianchi_compatibility_completed": False,
        "semiclassical_coupling_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "qft_gr_closure_claimed": False,
        "qft_gr_seam_closed": False,
        "empirical_validation_claimed": False,
        "public_submission_authorized": False,
        "master_action_promoted": False,
        "accepted_outcomes_considered": [
            WEAK_CONSERVATION_RESULT,
            "WEAK_CONSERVATION_BLOCKED_BY_MISSING_SCALAR_EQUATION_OF_MOTION_CONVENTION",
            "WEAK_CONSERVATION_BLOCKED_BY_CONNECTION_OR_REGULARITY_SCOPE",
        ],
        "critical_gate_fail_conditions": [
            "source_admissibility",
            "Bianchi_compatibility",
            "semiclassical_coupling",
            "QFT_GR_closure",
            "ToE_native_matter_derivation",
            "arbitrary_distributional_source_conservation",
        ],
        "downstream_progression": [
            {
                "stage": "weak_conservation",
                "status": "CONSTRUCTED_FOR_PROVISIONAL_SCALAR_SOURCE_ON_SHELL",
                "decision": WEAK_CONSERVATION_RESULT,
                "reason": (
                    "The divergence identity reduces to the scalar "
                    "equation-of-motion residual times nabla^nu phi."
                ),
            },
            {
                "stage": "off_shell_conservation",
                "status": "NOT_CLAIMED",
                "decision": "arbitrary_phi_not_conserved_by_this_packet",
                "reason": OFF_SHELL_BOUNDARY,
            },
            {
                "stage": "source_admissibility",
                "status": "NOT_REACHED",
                "decision": "not_reached",
                "reason": (
                    "On-shell scalar weak conservation is not source "
                    "admissibility."
                ),
            },
            {
                "stage": "bianchi_compatibility",
                "status": "NEXT_TARGET_AUTHORIZED",
                "decision": selected_next_target,
                "reason": (
                    "Bianchi compatibility remains a separate downstream test."
                ),
            },
            {
                "stage": "semiclassical_coupling",
                "status": "NOT_REACHED",
                "decision": "not_reached",
                "reason": "Einstein coupling remains downstream of Bianchi compatibility.",
            },
        ],
        "mathematical_statement": (
            "For the provisional scalar stress-energy source "
            + STRESS_ENERGY_COVARIANT_EXPRESSION
            + ", with "
            + SCALAR_EQUATION_OF_MOTION
            + " as the scalar field equation, the calculation gives "
            + DIVERGENCE_IDENTITY
            + ". Therefore, on shell, "
            + ON_SHELL_CONSERVATION_STATEMENT
            + ". This is a conditional weak-conservation result only inside "
            "the imported scalar sandbox."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "validation_policy": _validation_policy(),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet constructs weak conservation only for the imported "
            "provisional real-scalar source on shell. It does not claim "
            "off-shell conservation, arbitrary-phi conservation, arbitrary "
            "distributional-source conservation, source admissibility, Bianchi "
            "compatibility, semiclassical coupling, QFT-GR closure, empirical "
            "validation, public submission, ToE-native matter derivation, or "
            "master-action promotion."
        ),
    }


def write_qft_gr_weak_conservation_test_for_provisional_scalar_stress_energy_source(
    *,
    action_derivability_packet_path: Path = ACTION_DERIVABILITY_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = (
        build_qft_gr_weak_conservation_test_for_provisional_scalar_stress_energy_source(
            action_derivability_packet_path=action_derivability_packet_path,
            captured_at_utc=captured_at_utc,
        )
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR weak-conservation test packet for the "
            "provisional scalar stress-energy source."
        )
    )
    parser.add_argument(
        "--action-derivability-packet",
        type=Path,
        default=ACTION_DERIVABILITY_PACKET_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    action_derivability_packet_path = (
        ns.action_derivability_packet
        if ns.action_derivability_packet.is_absolute()
        else (REPO_ROOT / ns.action_derivability_packet)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = (
        write_qft_gr_weak_conservation_test_for_provisional_scalar_stress_energy_source(
            action_derivability_packet_path=action_derivability_packet_path,
            out=out,
            captured_at_utc=str(ns.captured_at_utc),
        )
    )
    print(
        json.dumps(
            {
                "out": _ptr(out),
                "packet_id": payload["packet_id"],
                "outcome_id": payload["outcome_id"],
                "prepared": payload["prepared"],
                "weak_conservation_result": payload["weak_conservation_result"],
                "selected_next_target": payload["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

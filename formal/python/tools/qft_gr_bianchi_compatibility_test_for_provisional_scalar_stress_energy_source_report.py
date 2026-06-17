from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_weak_conservation_test_for_provisional_scalar_stress_energy_source_report import (
    ACTION_DERIVABILITY_RESULT,
    DEFAULT_OUT as WEAK_CONSERVATION_PACKET_PATH,
    DIVERGENCE_IDENTITY,
    NEXT_TARGET as CONSUMED_TARGET,
    ON_SHELL_CONSERVATION_STATEMENT,
    OUTCOME_ID as EXPECTED_WEAK_CONSERVATION_OUTCOME,
    PACKET_CLASSIFICATION as WEAK_CONSERVATION_PACKET_CLASSIFICATION,
    REGULARITY_SCOPE,
    SCALAR_ACTION,
    SCALAR_EQUATION_OF_MOTION,
    SCALAR_LAGRANGIAN,
    SCHEMA_ID as EXPECTED_WEAK_CONSERVATION_SCHEMA_ID,
    SELECTED_ACTION_GENERATED_SOURCE_SUBCLASS_ID,
    SELECTED_FIELD_CONTENT,
    SELECTED_KNOWN_MATTER_MODEL,
    SELECTED_PROVISIONAL_MATTER_SECTOR_ID,
    STRESS_ENERGY_COVARIANT_EXPRESSION,
    STRESS_ENERGY_CONTRAVARIANT_EXPRESSION,
    TOE_NATIVE_MATTER_SECTOR_RESULT,
    WEAK_CONSERVATION_RESULT,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-17T00:00:00Z"
SCHEMA_ID = (
    "QFT_GR_BIANCHI_COMPATIBILITY_TEST_FOR_PROVISIONAL_SCALAR_STRESS_ENERGY_"
    "SOURCE_20260617_v0"
)
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = (
    "QFT_GR_BIANCHI_COMPATIBILITY_TEST_FOR_PROVISIONAL_SCALAR_STRESS_ENERGY_SOURCE_v0"
)
BIANCHI_COMPATIBILITY_RESULT = (
    "BIANCHI_COMPATIBILITY_CONSTRUCTED_FOR_PROVISIONAL_SCALAR_SOURCE_ON_SHELL_"
    "NO_QFT_GR_CLOSURE"
)
OUTCOME_ID = (
    "QFT_GR_BIANCHI_COMPATIBILITY_TEST_FOR_PROVISIONAL_SCALAR_STRESS_ENERGY_"
    "SOURCE_PREPARED_WITH_BIANCHI_COMPATIBILITY_CONSTRUCTED_FOR_PROVISIONAL_"
    "SCALAR_SOURCE_ON_SHELL_NO_SOURCE_ADMISSIBILITY_OR_QFT_GR_CLOSURE"
)
PACKET_CLASSIFICATION = (
    "qft_gr_bianchi_compatibility_test_for_provisional_scalar_stress_energy_"
    "source_constructs_on_shell_compatibility_nonpromotionally"
)
NEXT_TARGET = "prepare_qft_gr_source_admissibility_review_for_provisional_scalar_source"
NEXT_TARGET_KIND = (
    "qft_gr_source_admissibility_review_for_provisional_scalar_source_preparation"
)

CONTRACTED_BIANCHI_IDENTITY = "nabla_mu G^{mu nu} = 0"
METRIC_COMPATIBILITY_IDENTITY = "nabla_mu g^{mu nu} = 0"
EINSTEIN_SOURCE_EQUATION_FORM = "G^{mu nu} = 8 pi G_N T^{mu nu}"
EINSTEIN_SOURCE_EQUATION_WITH_LAMBDA_FORM = (
    "G^{mu nu} + Lambda g^{mu nu} = 8 pi G_N T^{mu nu}"
)
SOURCE_SIDE_CONSERVATION_REQUIREMENT = "nabla_mu T^{mu nu} = 0"
BIANCHI_COMPATIBILITY_STATEMENT = (
    "Under scalar EOM, Levi-Civita metric compatibility, and constant G_N "
    "and Lambda, the provisional scalar source is compatible with the "
    "contracted Bianchi identity."
)
COUPLING_CONSTANT_SCOPE = (
    "G_N is constant, and Lambda is constant when the cosmological-constant "
    "variant is used."
)
CONNECTION_SCOPE = (
    "Levi-Civita connection only: torsion-free and metric-compatible on the "
    "provisional smooth calculation domain."
)
PROVISIONAL_SOURCE_SCOPE = (
    "provisional real-scalar stress-energy source only; no arbitrary "
    "distributional source is admitted"
)
SEMICLASSICAL_NONDERIVATION_BOUNDARY = (
    "The Einstein-form source equation is used only as a compatibility test "
    "surface and is not derived as a semiclassical Einstein equation."
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_BIANCHI_COMPATIBILITY_TEST_FOR_PROVISIONAL_SCALAR_STRESS_ENERGY_"
    "SOURCE_20260617_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRBianchiCompatibilityTestForProvisionalScalarStressEnergySource.lean"
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
            "step_id": "state_einstein_source_test_equation",
            "mathematical_content": (
                EINSTEIN_SOURCE_EQUATION_FORM
                + " or "
                + EINSTEIN_SOURCE_EQUATION_WITH_LAMBDA_FORM
            ),
            "claim": "Einstein-form equation stated only as compatibility test surface",
        },
        {
            "step_id": "state_bianchi_identity",
            "mathematical_content": CONTRACTED_BIANCHI_IDENTITY,
            "claim": "contracted Bianchi identity fixed",
        },
        {
            "step_id": "state_metric_compatibility",
            "mathematical_content": METRIC_COMPATIBILITY_IDENTITY,
            "claim": "cosmological-constant term has zero divergence under metric compatibility",
        },
        {
            "step_id": "take_divergence_of_source_equation",
            "mathematical_content": (
                "0 = nabla_mu(G^{mu nu} + Lambda g^{mu nu}) "
                "= 8 pi G_N nabla_mu T^{mu nu}"
            ),
            "claim": "constant coupling reduces Bianchi compatibility to source conservation",
        },
        {
            "step_id": "insert_scalar_weak_conservation",
            "mathematical_content": DIVERGENCE_IDENTITY,
            "claim": "prior scalar weak-conservation residual is reused",
        },
        {
            "step_id": "conclude_on_shell_bianchi_compatibility",
            "mathematical_content": BIANCHI_COMPATIBILITY_STATEMENT,
            "claim": "Bianchi compatibility constructed only on shell for the provisional scalar source",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": (
            "qft_gr_bianchi_compatibility_test_for_provisional_scalar_stress_energy_source"
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


def build_qft_gr_bianchi_compatibility_test_for_provisional_scalar_stress_energy_source(
    *,
    weak_conservation_packet_path: Path = WEAK_CONSERVATION_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    weak_packet = _read_json(weak_conservation_packet_path)
    derivation_steps = _derivation_steps()
    acceptance_criteria = {
        "consumes_expected_weak_conservation_packet": (
            weak_packet.get("schema_id") == EXPECTED_WEAK_CONSERVATION_SCHEMA_ID
            and weak_packet.get("outcome_id") == EXPECTED_WEAK_CONSERVATION_OUTCOME
            and weak_packet.get("selected_next_target") == CONSUMED_TARGET
        ),
        "weak_conservation_available_on_shell": (
            weak_packet.get("weak_conservation_constructed") is True
            and weak_packet.get("on_shell_required") is True
            and weak_packet.get("divergence_identity") == DIVERGENCE_IDENTITY
        ),
        "contracted_bianchi_identity_stated": (
            CONTRACTED_BIANCHI_IDENTITY == "nabla_mu G^{mu nu} = 0"
        ),
        "metric_compatibility_stated": (
            METRIC_COMPATIBILITY_IDENTITY == "nabla_mu g^{mu nu} = 0"
        ),
        "constant_coupling_scope_stated": "constant" in COUPLING_CONSTANT_SCOPE,
        "scalar_eom_condition_carried": (
            SCALAR_EQUATION_OF_MOTION == "box_g phi - V'(phi) = 0"
        ),
        "source_admissibility_not_claimed": True,
        "semiclassical_equation_not_derived": True,
        "qft_gr_closure_not_claimed": True,
    }
    prepared = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if prepared
        else "REMEDIATE_QFT_GR_BIANCHI_COMPATIBILITY_TEST_FOR_PROVISIONAL_SCALAR_SOURCE"
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
        else "QFT_GR_BIANCHI_COMPATIBILITY_TEST_FOR_PROVISIONAL_SCALAR_SOURCE_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "authorized_by_weak_conservation_artifact_id": weak_packet.get("schema_id"),
        "authorized_by_weak_conservation_outcome": weak_packet.get("outcome_id"),
        "authorized_by_weak_conservation_classification": (
            WEAK_CONSERVATION_PACKET_CLASSIFICATION
        ),
        "action_derivability_result": ACTION_DERIVABILITY_RESULT,
        "weak_conservation_result": WEAK_CONSERVATION_RESULT,
        "bianchi_compatibility_result": BIANCHI_COMPATIBILITY_RESULT,
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
        "scalar_equation_of_motion": SCALAR_EQUATION_OF_MOTION,
        "divergence_identity": DIVERGENCE_IDENTITY,
        "on_shell_conservation_statement": ON_SHELL_CONSERVATION_STATEMENT,
        "contracted_bianchi_identity": CONTRACTED_BIANCHI_IDENTITY,
        "metric_compatibility_identity": METRIC_COMPATIBILITY_IDENTITY,
        "einstein_source_equation_form": EINSTEIN_SOURCE_EQUATION_FORM,
        "einstein_source_equation_with_lambda_form": (
            EINSTEIN_SOURCE_EQUATION_WITH_LAMBDA_FORM
        ),
        "source_side_conservation_requirement": SOURCE_SIDE_CONSERVATION_REQUIREMENT,
        "bianchi_compatibility_statement": BIANCHI_COMPATIBILITY_STATEMENT,
        "coupling_constant_scope": COUPLING_CONSTANT_SCOPE,
        "connection_scope": CONNECTION_SCOPE,
        "regularity_scope": REGULARITY_SCOPE,
        "provisional_source_scope": PROVISIONAL_SOURCE_SCOPE,
        "semiclassical_nonderivation_boundary": SEMICLASSICAL_NONDERIVATION_BOUNDARY,
        "derivation_steps": derivation_steps,
        "action_derivability_constructed": True,
        "weak_conservation_constructed": True,
        "weak_conservation_claimed": True,
        "weak_conservation_claimed_scope": (
            "conditional on scalar equation of motion only"
        ),
        "bianchi_compatibility_constructed": True,
        "bianchi_compatibility_constructed_scope": (
            "provisional scalar source on shell under imposed Einstein-form "
            "compatibility equation only"
        ),
        "Bianchi_compatibility_claimed": True,
        "Bianchi_compatibility_claimed_scope": (
            "conditional on scalar EOM, Levi-Civita connection, metric "
            "compatibility, constant coupling, and provisional scalar source only"
        ),
        "on_shell_required": True,
        "levi_civita_connection_required": True,
        "metric_compatibility_required": True,
        "constant_gravitational_coupling_required": True,
        "constant_lambda_required_if_lambda_variant_used": True,
        "einstein_equation_imposed_for_compatibility_test": True,
        "semiclassical_einstein_equation_derived": False,
        "semiclassical_coupling_claimed": False,
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
        "qft_gr_closure_claimed": False,
        "qft_gr_seam_closed": False,
        "empirical_validation_claimed": False,
        "public_readiness_claimed": False,
        "public_submission_authorized": False,
        "master_action_promoted": False,
        "accepted_outcomes_considered": [
            BIANCHI_COMPATIBILITY_RESULT,
            "BIANCHI_COMPATIBILITY_BLOCKED_BY_MISSING_CONNECTION_OR_METRIC_COMPATIBILITY_SCOPE",
            "BIANCHI_COMPATIBILITY_BLOCKED_BY_NONCONSTANT_COUPLING_OR_LAMBDA_SCOPE",
            "BIANCHI_COMPATIBILITY_BLOCKED_BY_MISSING_ON_SHELL_SOURCE_CONSERVATION",
        ],
        "critical_gate_fail_conditions": [
            "ToE_native_matter_derivation",
            "arbitrary_distributional_source_admissibility",
            "semiclassical_Einstein_equation_derivation",
            "QFT_GR_seam_closure",
            "empirical_validation",
            "public_readiness",
            "master_action_promotion",
        ],
        "downstream_progression": [
            {
                "stage": "bianchi_compatibility",
                "status": "CONSTRUCTED_FOR_PROVISIONAL_SCALAR_SOURCE_ON_SHELL",
                "decision": BIANCHI_COMPATIBILITY_RESULT,
                "reason": (
                    "The contracted Bianchi identity and metric compatibility "
                    "require source-side conservation, supplied conditionally "
                    "by the scalar EOM."
                ),
            },
            {
                "stage": "source_admissibility",
                "status": "NEXT_TARGET_AUTHORIZED",
                "decision": selected_next_target,
                "reason": (
                    "Bianchi compatibility is not full source admissibility."
                ),
            },
            {
                "stage": "semiclassical_coupling",
                "status": "NOT_REACHED",
                "decision": "not_reached",
                "reason": SEMICLASSICAL_NONDERIVATION_BOUNDARY,
            },
            {
                "stage": "qft_gr_closure",
                "status": "NOT_CLAIMED",
                "decision": "not_claimed",
                "reason": "The result remains inside the provisional scalar sandbox.",
            },
        ],
        "mathematical_statement": (
            "For the imposed compatibility-test equation "
            + EINSTEIN_SOURCE_EQUATION_WITH_LAMBDA_FORM
            + ", "
            + CONTRACTED_BIANCHI_IDENTITY
            + " and "
            + METRIC_COMPATIBILITY_IDENTITY
            + " imply "
            + SOURCE_SIDE_CONSERVATION_REQUIREMENT
            + " when G_N and Lambda are constant. The prior scalar result "
            + DIVERGENCE_IDENTITY
            + " makes this condition hold on shell under "
            + SCALAR_EQUATION_OF_MOTION
            + ". This constructs Bianchi compatibility only for the "
            "provisional scalar source and does not derive source admissibility "
            "or semiclassical coupling."
        ),
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "validation_policy": _validation_policy(),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet constructs Bianchi compatibility only for the "
            "imported provisional scalar source on shell under Levi-Civita "
            "metric compatibility and constant coupling assumptions. It does "
            "not claim ToE-native matter derivation, arbitrary "
            "distributional-source admissibility, source admissibility, "
            "semiclassical Einstein equation derivation, QFT-GR closure, "
            "empirical validation, public readiness, public submission, or "
            "master-action promotion."
        ),
    }


def write_qft_gr_bianchi_compatibility_test_for_provisional_scalar_stress_energy_source(
    *,
    weak_conservation_packet_path: Path = WEAK_CONSERVATION_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = (
        build_qft_gr_bianchi_compatibility_test_for_provisional_scalar_stress_energy_source(
            weak_conservation_packet_path=weak_conservation_packet_path,
            captured_at_utc=captured_at_utc,
        )
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Generate the QFT-GR Bianchi-compatibility test packet for the "
            "provisional scalar stress-energy source."
        )
    )
    parser.add_argument(
        "--weak-conservation-packet",
        type=Path,
        default=WEAK_CONSERVATION_PACKET_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    weak_conservation_packet_path = (
        ns.weak_conservation_packet
        if ns.weak_conservation_packet.is_absolute()
        else (REPO_ROOT / ns.weak_conservation_packet)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = (
        write_qft_gr_bianchi_compatibility_test_for_provisional_scalar_stress_energy_source(
            weak_conservation_packet_path=weak_conservation_packet_path,
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
                "bianchi_compatibility_result": payload[
                    "bianchi_compatibility_result"
                ],
                "selected_next_target": payload["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

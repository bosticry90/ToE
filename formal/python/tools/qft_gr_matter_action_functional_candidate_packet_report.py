from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_action_derivability_test_for_distributional_symmetric_tensor_candidate_packet_report import (
    ACTION_DERIVABILITY_RESULT as PRIOR_ACTION_DERIVABILITY_RESULT,
    DEFAULT_OUT as ACTION_DERIVABILITY_PACKET_PATH,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as EXPECTED_ACTION_DERIVABILITY_OUTCOME,
    SCHEMA_ID as EXPECTED_ACTION_DERIVABILITY_SCHEMA_ID,
    SELECTED_FUNCTIONAL_CONTRACT,
    SELECTED_REPLACEMENT_CANDIDATE_ID,
    TEST_SPACE,
    WEAK_VARIATIONAL_OBLIGATION,
    WELL_DEFINED_PAIRING_SCOPE,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-16T00:00:00Z"
SCHEMA_ID = "QFT_GR_MATTER_ACTION_FUNCTIONAL_CANDIDATE_PACKET_20260616_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "QFT_GR_MATTER_ACTION_FUNCTIONAL_CANDIDATE_PACKET_v0"
MATTER_ACTION_RESULT = (
    "MATTER_ACTION_FUNCTIONAL_BLOCKED_BY_MISSING_FIELD_CONTENT_AND_LAGRANGIAN"
)
OUTCOME_ID = (
    "QFT_GR_MATTER_ACTION_FUNCTIONAL_CANDIDATE_PACKET_PREPARED_WITH_MATTER_"
    "ACTION_FUNCTIONAL_BLOCKED_BY_MISSING_FIELD_CONTENT_AND_LAGRANGIAN_AND_NO_"
    "ACTION_DERIVABILITY_OR_SOURCE_ADMISSIBILITY"
)
PACKET_CLASSIFICATION = (
    "qft_gr_matter_action_functional_candidate_packet_records_missing_field_"
    "content_and_lagrangian_for_pairable_distributional_source_candidate"
)
TRUE_MATTER_ACTION_FORM = (
    "S_m[g, psi] = integral_M L_m(g, psi, nabla psi, ...) dVol_g"
)
EFFECTIVE_ACTION_FORM = "W[g] with <T_{mu nu}> = -2 / sqrt(-g) * delta W / delta g^{mu nu}"
FORMAL_VARIATIONAL_PRIMITIVE_FORM = "delta S_T[g_0](h) = -1/2 T(h)"
NEXT_TARGET = "prepare_qft_gr_matter_field_content_and_lagrangian_candidate_packet"
NEXT_TARGET_KIND = "qft_gr_matter_field_content_and_lagrangian_candidate_packet_preparation"
AUTHORIZED_BY_ACTION_DERIVABILITY_COMMIT = (
    "ff26d8ffabdf390efca2a89ec9561bca8f03c235"
)
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_MATTER_ACTION_FUNCTIONAL_CANDIDATE_PACKET_20260616_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRMatterActionFunctionalCandidatePacket.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _route_assessments() -> list[dict[str, Any]]:
    return [
        {
            "route_id": "true_matter_action_route",
            "route_kind": "matter_action_functional",
            "candidate_form": TRUE_MATTER_ACTION_FORM,
            "required_variation": WEAK_VARIATIONAL_OBLIGATION,
            "selection_status": "blocked_not_selected",
            "selection_licensed": False,
            "matter_action_admissibility_claimed": False,
            "blocked_by": [
                "matter_field_content_not_supplied",
                "lagrangian_density_not_supplied",
                "field_variation_policy_not_supplied",
                "metric_variation_rule_not_supplied",
                "variational_domain_not_supplied",
            ],
            "reason": (
                "The true matter-action route requires fields psi, a "
                "Lagrangian density L_m, an off-shell/on-shell or held-fixed "
                "field policy, and a metric-variation domain. None is licensed "
                "by the prior action-derivability packet."
            ),
        },
        {
            "route_id": "effective_qft_action_route",
            "route_kind": "effective_action_or_generating_functional",
            "candidate_form": EFFECTIVE_ACTION_FORM,
            "required_variation": "delta W / delta g^{mu nu}",
            "selection_status": "recorded_not_licensed",
            "selection_licensed": False,
            "matter_action_admissibility_claimed": False,
            "blocked_by": [
                "qft_state_data_not_supplied",
                "renormalization_prescription_not_supplied",
                "effective_action_domain_not_supplied",
                "anomaly_handling_not_supplied",
                "expectation_value_output_contract_not_supplied",
            ],
            "reason": (
                "The effective/QFT route is relevant but would import state, "
                "renormalization, domain, and anomaly data before those data "
                "are licensed."
            ),
        },
        {
            "route_id": "formal_variational_primitive_route",
            "route_kind": "formal_background_linear_primitive",
            "candidate_form": FORMAL_VARIATIONAL_PRIMITIVE_FORM,
            "required_variation": WEAK_VARIATIONAL_OBLIGATION,
            "selection_status": "recorded_not_selected",
            "selection_licensed": False,
            "matter_action_admissibility_claimed": False,
            "blocked_by": [
                "background_dependence_not_resolved",
                "non_dynamical_primitive_not_matter_action",
                "covariance_not_supplied",
                "field_content_not_supplied",
            ],
            "reason": (
                "A formal first-variation primitive could mirror -1/2 T(h), "
                "but that would not be a licensed matter action functional and "
                "would not authorize source admissibility."
            ),
        },
    ]


def _required_action_data() -> list[dict[str, Any]]:
    return [
        {
            "field_id": "matter_field_content",
            "required": "fields psi and bundle/domain data",
            "status": "missing",
        },
        {
            "field_id": "lagrangian_density",
            "required": "L_m(g, psi, nabla psi, ...)",
            "status": "missing",
        },
        {
            "field_id": "metric_variation_rule",
            "required": WEAK_VARIATIONAL_OBLIGATION,
            "status": "missing",
        },
        {
            "field_id": "variational_domain",
            "required": f"h in {TEST_SPACE} plus field-variation policy",
            "status": "missing",
        },
        {
            "field_id": "sign_and_normalization_convention",
            "required": "delta S_m[g, psi](h) = -1/2 <T, h>",
            "status": "target_convention_stated_not_derived",
        },
        {
            "field_id": "distributional_compatibility",
            "required": "variation output may be distribution-valued and match T",
            "status": "not_reached",
        },
        {
            "field_id": "covariance_or_diffeomorphism_behavior",
            "required": "action covariance sufficient for downstream conservation checks",
            "status": "not_reached",
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": "qft_gr_matter_action_functional_candidate_packet",
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


def build_qft_gr_matter_action_functional_candidate_packet(
    *,
    action_derivability_packet_path: Path = ACTION_DERIVABILITY_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    action_packet = _read_json(action_derivability_packet_path)
    route_assessments = _route_assessments()
    required_data = _required_action_data()
    true_route = route_assessments[0]
    effective_route = route_assessments[1]
    formal_route = route_assessments[2]
    acceptance_criteria = {
        "consumes_expected_action_derivability_packet": (
            action_packet.get("schema_id") == EXPECTED_ACTION_DERIVABILITY_SCHEMA_ID
            and action_packet.get("outcome_id") == EXPECTED_ACTION_DERIVABILITY_OUTCOME
            and action_packet.get("selected_next_target") == CONSUMED_TARGET
        ),
        "prior_action_derivability_blocked": (
            action_packet.get("action_derivability_result")
            == PRIOR_ACTION_DERIVABILITY_RESULT
            and action_packet.get("matter_action_functional_supplied") is False
        ),
        "true_matter_action_route_tested_and_blocked": (
            true_route["selection_status"] == "blocked_not_selected"
            and "matter_field_content_not_supplied" in true_route["blocked_by"]
            and "lagrangian_density_not_supplied" in true_route["blocked_by"]
        ),
        "effective_action_route_recorded_not_licensed": (
            effective_route["selection_status"] == "recorded_not_licensed"
            and "renormalization_prescription_not_supplied"
            in effective_route["blocked_by"]
        ),
        "formal_primitive_not_promoted_to_matter_action": (
            formal_route["selection_status"] == "recorded_not_selected"
            and formal_route["matter_action_admissibility_claimed"] is False
        ),
        "no_action_candidate_selected": all(
            row["selection_licensed"] is False for row in route_assessments
        ),
        "required_field_content_and_lagrangian_missing": {
            row["field_id"]: row["status"] for row in required_data
        }.get("matter_field_content")
        == "missing"
        and {
            row["field_id"]: row["status"] for row in required_data
        }.get("lagrangian_density")
        == "missing",
        "next_target_is_field_content_and_lagrangian_packet": NEXT_TARGET
        == "prepare_qft_gr_matter_field_content_and_lagrangian_candidate_packet",
        "non_promotion_boundary_preserved": True,
    }
    prepared = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET
        if prepared
        else "REMEDIATE_QFT_GR_MATTER_ACTION_FUNCTIONAL_CANDIDATE_PACKET"
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
        else "QFT_GR_MATTER_ACTION_FUNCTIONAL_CANDIDATE_PACKET_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "authorized_by_action_derivability_artifact_id": action_packet.get(
            "schema_id"
        ),
        "authorized_by_action_derivability_commit": AUTHORIZED_BY_ACTION_DERIVABILITY_COMMIT,
        "candidate_id": SELECTED_REPLACEMENT_CANDIDATE_ID,
        "functional_contract": SELECTED_FUNCTIONAL_CONTRACT,
        "weak_pairing_scope": WELL_DEFINED_PAIRING_SCOPE,
        "weak_variational_obligation": WEAK_VARIATIONAL_OBLIGATION,
        "matter_action_result": MATTER_ACTION_RESULT,
        "matter_action_functional_candidate_selected": False,
        "true_matter_action_route_selected": False,
        "effective_qft_action_route_selected": False,
        "formal_variational_primitive_selected": False,
        "formal_variational_primitive_constructed": False,
        "action_derivability_retry_authorized": False,
        "field_content_and_lagrangian_packet_required": True,
        "true_matter_action_form": TRUE_MATTER_ACTION_FORM,
        "effective_action_form": EFFECTIVE_ACTION_FORM,
        "formal_variational_primitive_form": FORMAL_VARIATIONAL_PRIMITIVE_FORM,
        "route_assessments": route_assessments,
        "required_action_data": required_data,
        "missing_action_data": [
            row["field_id"]
            for row in required_data
            if row["status"] in {"missing", "target_convention_stated_not_derived"}
        ],
        "mathematical_statement": (
            "A true matter action route would require S_m[g, psi] with "
            "field content psi and Lagrangian density L_m such that "
            "delta S_m[g, psi](h) = -1/2 <T, h>. The current pairable "
            "distributional tensor supplies T but not psi, L_m, or a licensed "
            "metric-variation rule, so no matter action functional candidate "
            "is selected."
        ),
        "downstream_progression": [
            {
                "stage": "matter_action_functional_candidate",
                "status": "BLOCKED",
                "decision": MATTER_ACTION_RESULT,
                "reason": "Field content and Lagrangian density are not supplied.",
            },
            {
                "stage": "action_derivability_retry",
                "status": "NOT_AUTHORIZED",
                "decision": "not_reached",
                "reason": "No matter action functional candidate was selected.",
            },
            {
                "stage": "matter_field_content_and_lagrangian_candidate",
                "status": "NEXT_TARGET_AUTHORIZED",
                "decision": selected_next_target,
                "reason": "Field content and Lagrangian data are required before matter-action construction can be retried.",
            },
            {
                "stage": "weak_conservation",
                "status": "NOT_REACHED",
                "decision": "not_reached",
                "reason": "Weak conservation is downstream of action derivability or a non-action route decision.",
            },
            {
                "stage": "bianchi_compatibility",
                "status": "NOT_REACHED",
                "decision": "not_reached",
                "reason": "Bianchi compatibility is downstream of conservation.",
            },
            {
                "stage": "semiclassical_source_admissibility",
                "status": "NOT_REACHED",
                "decision": "not_reached",
                "reason": "Semiclassical coupling is downstream of source admissibility checks.",
            },
        ],
        "source_admissibility_claimed": False,
        "action_derivability_claimed": False,
        "matter_action_admissibility_claimed": False,
        "weak_conservation_claimed": False,
        "conservation_claimed": False,
        "Bianchi_compatibility_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "qft_gr_closure_claimed": False,
        "qft_gr_seam_closed": False,
        "empirical_validation_claimed": False,
        "public_submission_authorized": False,
        "master_action_promoted": False,
        "acceptable_result_outcomes": [
            "MATTER_ACTION_FUNCTIONAL_CANDIDATE_CONSTRUCTED_ACTION_DERIVABILITY_RETRY_AUTHORIZED",
            "FORMAL_VARIATIONAL_PRIMITIVE_CONSTRUCTED_NO_MATTER_ACTION_ADMISSIBILITY",
            MATTER_ACTION_RESULT,
            "EFFECTIVE_ACTION_ROUTE_RECORDED_BUT_NOT_LICENSED",
            "NON_ACTION_SOURCE_ROUTE_DECISION_REQUIRED",
        ],
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "validation_policy": _validation_policy(),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet evaluates true matter-action, effective/QFT action, "
            "and formal variational primitive routes. It records that no "
            "matter action functional candidate is selected because field "
            "content and a Lagrangian are missing. It does not claim action "
            "derivability, matter-action admissibility, source admissibility, "
            "weak conservation, Bianchi compatibility, semiclassical coupling, "
            "QFT-GR closure, empirical validation, public submission, or "
            "master-action promotion."
        ),
    }


def write_qft_gr_matter_action_functional_candidate_packet(
    *,
    action_derivability_packet_path: Path = ACTION_DERIVABILITY_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_matter_action_functional_candidate_packet(
        action_derivability_packet_path=action_derivability_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QFT-GR matter action functional candidate packet JSON."
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
    payload = write_qft_gr_matter_action_functional_candidate_packet(
        action_derivability_packet_path=action_derivability_packet_path,
        out=out,
        captured_at_utc=str(ns.captured_at_utc),
    )
    print(
        json.dumps(
            {
                "out": _ptr(out),
                "packet_id": payload["packet_id"],
                "outcome_id": payload["outcome_id"],
                "prepared": payload["prepared"],
                "matter_action_result": payload["matter_action_result"],
                "selected_next_target": payload["selected_next_target"],
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

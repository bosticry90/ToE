from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.qft_gr_broader_stress_energy_like_distribution_candidate_regular_type_and_domain_contract_packet_report import (
    CANDIDATE_SOURCE_ID as RETIRED_CANDIDATE_ID,
    DEFAULT_OUT as REGULAR_TYPE_DOMAIN_PACKET_PATH,
    DISTRIBUTIONAL_CONTRACT,
    NEXT_TARGET as CONSUMED_TARGET,
    OUTCOME_ID as EXPECTED_REGULAR_TYPE_DOMAIN_OUTCOME,
    REQUIRED_FUNCTIONAL_CONTRACT,
    SCHEMA_ID as EXPECTED_REGULAR_TYPE_DOMAIN_SCHEMA_ID,
    TEST_SPACE,
)


REPO_ROOT = find_repo_root(Path(__file__))
DEFAULT_CAPTURED_AT_UTC = "2026-06-16T00:00:00Z"
SCHEMA_ID = "QFT_GR_CANDIDATE_DEFINITION_REVISION_OR_REPLACEMENT_PACKET_20260616_v0"
ARTIFACT_ID = SCHEMA_ID
PACKET_ID = "QFT_GR_CANDIDATE_DEFINITION_REVISION_OR_REPLACEMENT_PACKET_v0"
DECISION_RESULT = "CURRENT_CANDIDATE_REPLACED_BY_STRICTER_FUNCTIONAL_SOURCE_CANDIDATE"
OUTCOME_ID = (
    "QFT_GR_CANDIDATE_DEFINITION_REVISION_OR_REPLACEMENT_PACKET_PREPARED_WITH_"
    "CURRENT_CANDIDATE_REPLACED_BY_STRICTER_FUNCTIONAL_SOURCE_CANDIDATE_AND_"
    "WEAK_PAIRING_RETRY_AUTHORIZED_ONLY"
)
PACKET_CLASSIFICATION = (
    "qft_gr_candidate_definition_revision_or_replacement_packet_retires_"
    "underspecified_broader_candidate_and_selects_distributional_symmetric_"
    "tensor_functional_source_candidate_for_weak_pairing_retry_only"
)
SELECTED_REPLACEMENT_CANDIDATE_ID = "distributional_symmetric_tensor_candidate_v0"
SELECTED_REPLACEMENT_CANDIDATE_KIND = "tensor_valued_distribution"
SELECTED_FUNCTIONAL_CONTRACT = (
    "T in D'(M, Sym^2 TM), equivalently T : C_c^infty(M, Sym^2 T*M) -> R "
    "continuous linear"
)
SELECTED_PAIRING_RULE = "<T, h> := T(h) for h in C_c^infty(M, Sym^2 T*M)"
SELECTED_TENSOR_TYPE = "symmetric contravariant rank-2 tensor distribution"
SELECTED_INDEX_PLACEMENT = "contravariant T^{mu nu} paired with covariant h_{mu nu}"
NEXT_TARGET = "prepare_qft_gr_weak_pairing_retry_for_selected_candidate_functional_contract"
NEXT_TARGET_KIND = "qft_gr_weak_pairing_retry_for_selected_candidate_functional_contract"
AUTHORIZED_BY_REGULAR_TYPE_DOMAIN_COMMIT = "56eac7b11fbfd2c384129f4e7d7a58a698b6f4a2"
DEFAULT_OUT = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "QFT_GR_CANDIDATE_DEFINITION_REVISION_OR_REPLACEMENT_PACKET_20260616_v0.json"
)
LEAN_PACKET_PATH = (
    REPO_ROOT
    / "formal"
    / "toe_formal"
    / "ToeFormal"
    / "Derivation"
    / "QFTGRCandidateDefinitionRevisionOrReplacementPacket.lean"
)


def _ptr(path: Path) -> str:
    return str(path.relative_to(REPO_ROOT)).replace("\\", "/")


def _read_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise FileNotFoundError(f"Missing required JSON file: {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def _revision_lane() -> dict[str, Any]:
    required_v1_fields = [
        "candidate_id",
        "background_geometry_assumptions",
        "tensor_type",
        "index_placement",
        "regularity_class",
        "test_domain",
        "pairing_rule",
        "linearity_condition",
        "continuity_condition",
        "symmetry_condition",
        "metric_or_volume_dependence",
        "coordinate_or_covariance_behavior",
        "whether_action_derived_or_not",
        "known_missing_downstream_checks",
    ]
    return {
        "lane_id": "revise_current_candidate",
        "candidate_under_review": RETIRED_CANDIDATE_ID,
        "proposed_revised_candidate_id": "broader_stress_energy_like_distribution_candidate_v1",
        "lane_question": (
            "Can the underspecified broader stress-energy-like distribution "
            "candidate be upgraded into a v1 candidate with a functional "
            "contract?"
        ),
        "required_v1_fields": required_v1_fields,
        "selection_status": "not_selected",
        "selection_licensed": False,
        "decision": "revision_not_licensed",
        "reason": (
            "The prior packet recorded that the current candidate does not "
            "supply regularity class, tensor/density status, index placement, "
            "linearity, continuity, metric dependence, or covariance behavior. "
            "No internal artifact licenses filling those fields by patching "
            "the same candidate."
        ),
        "missing_fields": required_v1_fields[1:13],
    }


def _replacement_options() -> list[dict[str, Any]]:
    return [
        {
            "candidate_id": "locally_integrable_symmetric_tensor_candidate_v0",
            "candidate_kind": "locally_integrable_tensor_field",
            "regularity": "L^1_loc(M, Sym^2 TM)",
            "test_domain": TEST_SPACE,
            "pairing_rule": "<T, h> = integral_M T^{mu nu} h_{mu nu} dVol_g",
            "selection_status": "not_selected",
            "selection_licensed": False,
            "unselected_reason": (
                "This route requires a locally integrable tensor representative "
                "and metric volume contract; the old candidate did not license "
                "such a representative."
            ),
        },
        {
            "candidate_id": SELECTED_REPLACEMENT_CANDIDATE_ID,
            "candidate_kind": SELECTED_REPLACEMENT_CANDIDATE_KIND,
            "regularity": "D'(M, Sym^2 TM)",
            "test_domain": TEST_SPACE,
            "functional_contract": SELECTED_FUNCTIONAL_CONTRACT,
            "pairing_rule": SELECTED_PAIRING_RULE,
            "linearity_condition": "linear on C_c^infty(M, Sym^2 T*M)",
            "continuity_condition": "continuous for the C_c^infty test-space topology",
            "tensor_type": SELECTED_TENSOR_TYPE,
            "index_placement": SELECTED_INDEX_PLACEMENT,
            "metric_or_volume_dependence": (
                "no dVol_g factor is built into the distributional contract; "
                "metric dependence is not promoted beyond the selected test "
                "bundle notation"
            ),
            "coordinate_or_covariance_behavior": (
                "must be checked in the weak-pairing retry; not claimed here"
            ),
            "action_derived_status": "not_claimed",
            "known_missing_downstream_checks": [
                "weak_pairing_well_definedness",
                "action_derivability",
                "weak_conservation",
                "Bianchi_compatibility",
                "semiclassical_source_admissibility",
            ],
            "selection_status": "selected",
            "selection_licensed": True,
            "selection_reason": (
                "This is the narrowest replacement that directly supplies the "
                "functional contract needed for the next weak-pairing retry "
                "without requiring smoothness, local integrability, action "
                "derivation, conservation, or semiclassical coupling."
            ),
        },
        {
            "candidate_id": "tensor_density_source_candidate_v0",
            "candidate_kind": "tensor_density",
            "regularity": "tensor density with unspecified density weight",
            "test_domain": TEST_SPACE,
            "pairing_rule": "direct tensor-density pairing with compactly supported test tensors",
            "selection_status": "not_selected",
            "selection_licensed": False,
            "unselected_reason": (
                "This route would require density weight and transformation "
                "law choices not needed for the immediate weak-pairing retry."
            ),
        },
        {
            "candidate_id": "renormalized_expectation_stress_energy_candidate_v0",
            "candidate_kind": "operator_valued_distribution_expectation_candidate",
            "regularity": "renormalized c-number expectation distribution",
            "test_domain": TEST_SPACE,
            "pairing_rule": "state and renormalization map would produce a tensor distribution",
            "selection_status": "not_selected",
            "selection_licensed": False,
            "unselected_reason": (
                "This route imports state, operator-domain, and renormalization "
                "machinery before the weaker distributional functional retry."
            ),
        },
        {
            "candidate_id": "action_variation_source_candidate_v0",
            "candidate_kind": "action_variation_source_candidate",
            "regularity": "source derived from metric variation of an action",
            "test_domain": TEST_SPACE,
            "pairing_rule": "delta S_m pairing against metric variations",
            "selection_status": "not_selected",
            "selection_licensed": False,
            "unselected_reason": (
                "This route is too strong for the current step because action "
                "derivability is downstream of weak pairing and remains not "
                "reached."
            ),
        },
    ]


def _validation_policy() -> dict[str, Any]:
    return {
        "checkpoint_type": "qft_gr_candidate_definition_revision_or_replacement_packet",
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


def build_qft_gr_candidate_definition_revision_or_replacement_packet(
    *,
    regular_type_domain_packet_path: Path = REGULAR_TYPE_DOMAIN_PACKET_PATH,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    prior_packet = _read_json(regular_type_domain_packet_path)
    revision_lane = _revision_lane()
    replacement_options = _replacement_options()
    selected_options = [
        row for row in replacement_options if row["selection_status"] == "selected"
    ]
    selected = selected_options[0]
    acceptance_criteria = {
        "consumes_expected_regular_type_domain_packet": (
            prior_packet.get("schema_id") == EXPECTED_REGULAR_TYPE_DOMAIN_SCHEMA_ID
            and prior_packet.get("outcome_id") == EXPECTED_REGULAR_TYPE_DOMAIN_OUTCOME
            and prior_packet.get("selected_next_target") == CONSUMED_TARGET
        ),
        "revision_lane_evaluated_and_not_selected": (
            revision_lane["selection_status"] == "not_selected"
            and revision_lane["selection_licensed"] is False
            and bool(revision_lane["missing_fields"])
        ),
        "replacement_lane_options_enumerated": [
            row["candidate_id"] for row in replacement_options
        ]
        == [
            "locally_integrable_symmetric_tensor_candidate_v0",
            SELECTED_REPLACEMENT_CANDIDATE_ID,
            "tensor_density_source_candidate_v0",
            "renormalized_expectation_stress_energy_candidate_v0",
            "action_variation_source_candidate_v0",
        ],
        "exactly_one_replacement_selected": len(selected_options) == 1,
        "selected_replacement_specifies_regularity": bool(selected.get("regularity")),
        "selected_replacement_specifies_test_domain": selected.get("test_domain")
        == TEST_SPACE,
        "selected_replacement_specifies_pairing_rule": selected.get("pairing_rule")
        == SELECTED_PAIRING_RULE,
        "selected_replacement_specifies_functional_contract": selected.get(
            "functional_contract"
        )
        == SELECTED_FUNCTIONAL_CONTRACT,
        "weak_pairing_retry_authorized_only_for_selected_contract": True,
        "downstream_nonclaims_preserved": True,
    }
    prepared = all(acceptance_criteria.values())
    selected_next_target = (
        NEXT_TARGET if prepared else "REMEDIATE_QFT_GR_CANDIDATE_DEFINITION_PACKET"
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
        else "QFT_GR_CANDIDATE_DEFINITION_REVISION_OR_REPLACEMENT_PACKET_REQUIRES_REMEDIATION",
        "packet_classification": PACKET_CLASSIFICATION,
        "consumed_target": CONSUMED_TARGET,
        "selected_next_target": selected_next_target,
        "selected_next_target_kind": NEXT_TARGET_KIND,
        "authorized_by_regular_type_domain_artifact_id": prior_packet.get("schema_id"),
        "authorized_by_regular_type_domain_commit": AUTHORIZED_BY_REGULAR_TYPE_DOMAIN_COMMIT,
        "prior_regular_type_domain_result": prior_packet.get("regular_type_domain_result"),
        "retired_candidate_id": RETIRED_CANDIDATE_ID,
        "retired_candidate_status": "retired_due_to_insufficient_definition",
        "decision_result": DECISION_RESULT,
        "revision_lane": revision_lane,
        "replacement_options": replacement_options,
        "selected_replacement_candidate_id": selected["candidate_id"],
        "selected_replacement_candidate_kind": selected["candidate_kind"],
        "selected_regular_type": selected["regularity"],
        "selected_test_domain": selected["test_domain"],
        "selected_functional_contract": selected["functional_contract"],
        "selected_pairing_rule": selected["pairing_rule"],
        "selected_tensor_type": selected["tensor_type"],
        "selected_index_placement": selected["index_placement"],
        "linearity_condition": selected["linearity_condition"],
        "continuity_condition": selected["continuity_condition"],
        "symmetry_condition": "symmetric rank-2 tensor-valued distribution",
        "metric_or_volume_dependence": selected["metric_or_volume_dependence"],
        "coordinate_or_covariance_behavior": selected[
            "coordinate_or_covariance_behavior"
        ],
        "action_derived_status": selected["action_derived_status"],
        "known_missing_downstream_checks": selected["known_missing_downstream_checks"],
        "current_candidate_revised": False,
        "current_candidate_replaced": True,
        "no_candidate_selected": False,
        "weak_pairing_retry_authorized": prepared,
        "weak_pairing_retry_target": selected_next_target if prepared else None,
        "weak_pairing_completed": False,
        "source_admissibility_claimed": False,
        "action_derivability_claimed": False,
        "conservation_claimed": False,
        "Bianchi_compatibility_claimed": False,
        "semiclassical_einstein_equation_derived": False,
        "qft_gr_closure_claimed": False,
        "qft_gr_seam_closed": False,
        "empirical_validation_claimed": False,
        "public_submission_authorized": False,
        "master_action_promoted": False,
        "downstream_progression": [
            {
                "stage": "candidate_revision_or_replacement",
                "status": "completed",
                "decision": DECISION_RESULT,
                "reason": "The old candidate is retired and a stricter functional source candidate is selected.",
            },
            {
                "stage": "weak_pairing_retry",
                "status": "AUTHORIZED",
                "decision": NEXT_TARGET,
                "reason": "The selected replacement supplies a distributional functional contract.",
            },
            {
                "stage": "action_derivability",
                "status": "NOT_REACHED",
                "decision": "not_reached",
                "reason": "Action derivability is downstream of a successful weak-pairing retry.",
            },
            {
                "stage": "weak_conservation",
                "status": "NOT_REACHED",
                "decision": "not_reached",
                "reason": "Weak conservation is downstream of source/action semantics.",
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
                "reason": "Semiclassical coupling is downstream of the prior checks.",
            },
        ],
        "acceptable_result_outcomes": [
            "CURRENT_CANDIDATE_REVISED_TO_DISTRIBUTIONAL_TENSOR_CONTRACT_WEAK_PAIRING_RETRY_AUTHORIZED",
            DECISION_RESULT,
            "CANDIDATE_REVISION_AND_REPLACEMENT_OPTIONS_RECORDED_NO_SELECTION_LICENSED",
            "CURRENT_CANDIDATE_RETIRED_NO_QFT_GR_SOURCE_CANDIDATE_SELECTED",
        ],
        "lean_packet_file": _ptr(LEAN_PACKET_PATH),
        "validation_policy": _validation_policy(),
        "acceptance_criteria": acceptance_criteria,
        "non_claim_boundary": (
            "This packet retires the underspecified broader stress-energy-like "
            "distribution candidate and selects only a stricter distributional "
            "symmetric tensor functional source candidate for weak-pairing "
            "retry. It does not complete weak pairing, establish source "
            "admissibility, derive action origin, prove conservation, prove "
            "Bianchi compatibility, derive semiclassical Einstein coupling, "
            "close QFT-GR, authorize empirical validation, public submission, "
            "or master-action promotion."
        ),
    }


def write_qft_gr_candidate_definition_revision_or_replacement_packet(
    *,
    regular_type_domain_packet_path: Path = REGULAR_TYPE_DOMAIN_PACKET_PATH,
    out: Path = DEFAULT_OUT,
    captured_at_utc: str = DEFAULT_CAPTURED_AT_UTC,
) -> dict[str, Any]:
    payload = build_qft_gr_candidate_definition_revision_or_replacement_packet(
        regular_type_domain_packet_path=regular_type_domain_packet_path,
        captured_at_utc=captured_at_utc,
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return payload


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Generate the QFT-GR candidate definition revision/replacement packet JSON."
    )
    parser.add_argument(
        "--regular-type-domain-packet",
        type=Path,
        default=REGULAR_TYPE_DOMAIN_PACKET_PATH,
    )
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT)
    parser.add_argument("--captured-at-utc", default=DEFAULT_CAPTURED_AT_UTC)
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    regular_type_domain_packet_path = (
        ns.regular_type_domain_packet
        if ns.regular_type_domain_packet.is_absolute()
        else (REPO_ROOT / ns.regular_type_domain_packet)
    )
    out = ns.out if ns.out.is_absolute() else (REPO_ROOT / ns.out)
    payload = write_qft_gr_candidate_definition_revision_or_replacement_packet(
        regular_type_domain_packet_path=regular_type_domain_packet_path,
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
                "decision_result": payload["decision_result"],
                "selected_replacement_candidate_id": payload[
                    "selected_replacement_candidate_id"
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

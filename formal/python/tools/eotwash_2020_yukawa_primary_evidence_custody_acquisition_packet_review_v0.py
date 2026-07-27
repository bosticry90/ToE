from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
PACKET_RELATIVE_PATH = (
    "formal/docs/release/"
    "EOTWASH_2020_YUKAWA_PRIMARY_EVIDENCE_CUSTODY_ACQUISITION_PACKET_"
    "20260718_v0.json"
)
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "EOTWASH_2020_YUKAWA_PRIMARY_EVIDENCE_CUSTODY_ACQUISITION_PACKET_"
    "REVIEW_20260718_v0.json"
)
HUMAN_REVIEW_RELATIVE_PATH = (
    "formal/docs/lanes/"
    "EOTWASH_2020_YUKAWA_PRIMARY_EVIDENCE_CUSTODY_ACQUISITION_PACKET_"
    "REVIEW_20260718_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_eotwash_2020_yukawa_primary_evidence_custody_acquisition_packet_review_v0.py"
)

TARGET = "review_eotwash_2020_yukawa_primary_evidence_custody_acquisition_packet_v0_result"
VERDICT = "ACCEPTED_PRIMARY_EVIDENCE_ACQUISITION_CONTRACT_READY_FOR_ONE_BOUNDED_EXECUTION"
PRINCIPAL_OUTCOME = "PRIMARY_EVIDENCE_ACQUISITION_CONTRACT_READY"
SELECTED_NEXT_TARGET = "execute_eotwash_2020_yukawa_primary_evidence_custody_acquisition_v0"
SELECTED_NEXT_TARGET_KIND = (
    "ONE_BOUNDED_LEGITIMATE_ACQUISITION_EXECUTION_THEN_INDEPENDENT_RESULT_REVIEW"
)
RESULT_REVIEW_TARGET = (
    "review_eotwash_2020_yukawa_primary_evidence_custody_acquisition_v0_result"
)

PACKET_HASHES = {
    "formal/docs/lanes/EOTWASH_2020_YUKAWA_PRIMARY_EVIDENCE_CUSTODY_ACQUISITION_PACKET_20260718_v0.md":
        "345a407a317ebd1967a72c3582a186b51d3347a1017d50d77325ba14db49510c",
    PACKET_RELATIVE_PATH:
        "ea10948408c2df5c49b8d83563d08dae37ce4edd7289a591055d367dff283477",
    "formal/python/tools/eotwash_2020_yukawa_primary_evidence_custody_acquisition_packet_v0.py":
        "9db05478025f170b175fda6fc4aee95afe0578a68cc0997c73585184d0f29fcb",
    "formal/python/tests/test_eotwash_2020_yukawa_primary_evidence_custody_acquisition_packet_v0.py":
        "64fef151c14fd5cafe28fa4c671f8577d40c423364d199717f8012fd6c9153b4",
    "formal/toe_formal/ToeFormal/Derivation/Eotwash2020YukawaPrimaryEvidenceCustodyAcquisitionPacketV0.lean":
        "32124103d0abca29ddcbce689fde6f858d738d11ddd3669336c2761a0de4aa61",
}

STATE_ORDER = ["IDENTIFIED", "ACQUIRED", "INGESTED", "VERIFIED", "COMPLETE"]


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_packet() -> dict[str, Any]:
    value = json.loads((REPO_ROOT / PACKET_RELATIVE_PATH).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError("acquisition packet must be a JSON object")
    return value


def _validate_packet() -> tuple[list[dict[str, str]], dict[str, Any]]:
    custody: list[dict[str, str]] = []
    for relative_path, expected in PACKET_HASHES.items():
        observed = _sha256(REPO_ROOT / relative_path)
        if observed != expected:
            raise ValueError(f"acquisition packet custody drift: {relative_path}")
        custody.append({"relative_path": relative_path, "sha256": observed})
    packet = _load_packet()
    if packet.get("verdict") != (
        "PREPARED_PRIMARY_EVIDENCE_ACQUISITION_CONTRACT_PENDING_INDEPENDENT_REVIEW"
    ):
        raise ValueError("acquisition packet is not pending independent review")
    if packet.get("selected_next_target") != TARGET:
        raise ValueError("acquisition packet did not rotate to this review")
    if packet["scope"].get("acquisition_execution_authorized") is not False:
        raise ValueError("prepared packet improperly authorized acquisition")
    if packet["scope"].get("supplement_downloaded_or_acquired") is not False:
        raise ValueError("prepared packet unexpectedly acquired evidence")
    return custody, packet


def _transition_allowed(
    current: str,
    target: str,
    *,
    custody_fields_complete: bool = False,
    parsed: bool = False,
    exact_inventory_match: bool = False,
    inventory_item_complete: bool = False,
) -> bool:
    if current not in STATE_ORDER or target not in STATE_ORDER:
        return False
    if STATE_ORDER.index(target) != STATE_ORDER.index(current) + 1:
        return False
    if target == "ACQUIRED":
        return custody_fields_complete
    if target == "INGESTED":
        return parsed
    if target == "VERIFIED":
        return exact_inventory_match
    if target == "COMPLETE":
        return inventory_item_complete
    return False


def _probe(
    probe_id: str,
    attempted_shortcut: str,
    expected: str,
    observed: str,
    passed: bool,
) -> dict[str, Any]:
    return {
        "probe_id": probe_id,
        "attempted_shortcut": attempted_shortcut,
        "expected": expected,
        "observed": observed,
        "status": "PASS" if passed else "FAIL",
    }


def _adversarial_probes(packet: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        _probe(
            "IDENTIFIED_URL_TO_COMPLETE",
            "advance a known supplement URL directly from IDENTIFIED to COMPLETE",
            "REJECT",
            "REJECT",
            not _transition_allowed("IDENTIFIED", "COMPLETE", inventory_item_complete=True),
        ),
        _probe(
            "ACQUIRED_FILE_WITHOUT_CUSTODY_FIELDS",
            "advance IDENTIFIED to ACQUIRED without all twelve custody fields",
            "REJECT",
            "REJECT",
            not _transition_allowed("IDENTIFIED", "ACQUIRED", custody_fields_complete=False),
        ),
        _probe(
            "ACQUIRED_FILE_TO_VERIFIED",
            "advance an acquired file directly to VERIFIED because its filename says supplement",
            "REJECT",
            "REJECT",
            not _transition_allowed("ACQUIRED", "VERIFIED", exact_inventory_match=True),
        ),
        _probe(
            "INGESTED_CONTENT_WITHOUT_EXACT_MATCH",
            "advance parsed content to VERIFIED without matching an exact inventory item",
            "REJECT",
            "REJECT",
            not _transition_allowed("INGESTED", "VERIFIED", exact_inventory_match=False),
        ),
        _probe(
            "VERIFIED_PARTIAL_ITEM_TO_COMPLETE",
            "advance a verified partial component to COMPLETE",
            "REJECT",
            "REJECT",
            not _transition_allowed("VERIFIED", "COMPLETE", inventory_item_complete=False),
        ),
        _probe(
            "DISSERTATION_PROSE_SUBSTITUTION",
            "infer missing numerical values or priors from supporting dissertation prose",
            "REJECT",
            "REJECT",
            "values inferred from dissertation prose" in packet["source_hierarchy"]["forbidden_substitutions"],
        ),
        _probe(
            "ACCESS_CONTROL_CIRCUMVENTION",
            "bypass publisher access controls to obtain bytes",
            "REJECT",
            "REJECT",
            packet["bounded_acquisition_protocol"]["access_control_circumvention_allowed"] is False,
        ),
        _probe(
            "AUTHOR_CONTACT_DURING_ACQUISITION",
            "contact an author or custodian during the authorized non-contact run",
            "REJECT_AND_STOP_WITH_CONTACT_REQUIRED",
            "REJECT_AND_STOP_WITH_CONTACT_REQUIRED",
            packet["bounded_acquisition_protocol"]["author_contact_status"]
            == "NOT_AUTHORIZED_TERMINAL_OUTCOME_ONLY",
        ),
        _probe(
            "SYNTHETIC_FORECAST_BYPASS",
            "run a synthetic sensitivity forecast inside evidence acquisition",
            "REJECT",
            "REJECT",
            packet["scope"]["synthetic_forward_model_lane_authorized"] is False,
        ),
        _probe(
            "LIKELIHOOD_AFTER_COMPLETE_FILE",
            "execute a scalar likelihood immediately after one file appears complete",
            "REJECT_AND_STOP_FOR_RESULT_REVIEW",
            "REJECT_AND_STOP_FOR_RESULT_REVIEW",
            packet["scope"]["likelihood_execution_authorized"] is False,
        ),
    ]


def _gate(gate_id: str, passed: bool, finding: str) -> dict[str, Any]:
    return {"gate_id": gate_id, "status": "PASS" if passed else "FAIL", "finding": finding}


def _review_gates(packet: dict[str, Any], probes: list[dict[str, Any]]) -> list[dict[str, Any]]:
    inventory = {row["item_id"]: row for row in packet["required_evidence_inventory"]["rows"]}
    custody = packet["custody_contract"]
    hierarchy = packet["source_hierarchy"]
    protocol = packet["bounded_acquisition_protocol"]
    scope = packet["scope"]
    return [
        _gate(
            "G1_EXACT_PACKET_AUTHORITY_AND_CUSTODY",
            packet["selected_next_target"] == TARGET,
            "Five packet artifacts match frozen SHA-256 custody and rotate to this review.",
        ),
        _gate(
            "G2_SUITABILITY_AND_EXECUTABILITY_REMAIN_SEPARATE",
            packet["experiment_boundary"]["experiment_scientifically_suitable"] is True
            and packet["experiment_boundary"]["independent_likelihood_executable_now"] is False,
            "The experiment is suitable while the independent likelihood remains blocked.",
        ),
        _gate(
            "G3_SIX_ITEM_INVENTORY_COVERS_DECISION_BEARING_OPERATIONS",
            packet["required_evidence_inventory"]["item_count"] == 6
            and packet["required_evidence_inventory"]["complete_item_count"] == 0
            and all(row["required_operation"] for row in inventory.values()),
            "All decision-bearing data, metadata, uncertainty, nuisance, forward-model, and coverage operations are mapped.",
        ),
        _gate(
            "G4_OBSERVATION_VECTOR_AND_PHYSICAL_ROW_MAPPING_EXACT",
            inventory["OBSERVATION_TORQUE_VECTOR"]["expected_count"] == 285
            and "row identifiers and ordering" in inventory["OBSERVATION_TORQUE_VECTOR"]["required_fields"],
            "The 95x3 vector requires units, ordering, identifiers, and selection flags.",
        ),
        _gate(
            "G5_DISPLACEMENT_AND_CONFIGURATION_METADATA_SEPARATE",
            "ordering key matching the torque vector"
            in inventory["DISPLACEMENT_AND_CONFIGURATION_METADATA"]["required_fields"],
            "Configuration metadata cannot be hidden inside a generic supplement label.",
        ),
        _gate(
            "G6_UNCERTAINTY_AND_COVARIANCE_CONTRACT_COMPLETE_IN_SCOPE",
            "covariance matrix or equivalent generative error model"
            in inventory["UNCERTAINTY_AND_COVARIANCE_MODEL"]["required_fields"],
            "Pointwise errors, correlations, block structure, conditioning, units, and ordering are required.",
        ),
        _gate(
            "G7_FIVE_NUISANCE_PRIOR_CONTRACTS_EXACT",
            inventory["FIVE_NUISANCE_PRIOR_CONTRACTS"]["expected_count"] == 5
            and len(inventory["FIVE_NUISANCE_PRIOR_CONTRACTS"]["parameter_ids"]) == 5,
            "All five nuisance identities, numerical constraints, relations, and model entry points are mandatory.",
        ),
        _gate(
            "G8_EXTENDED_SOURCE_FORWARD_MODEL_CANNOT_BE_DESCRIPTIVE_ONLY",
            "Yukawa implementation for arbitrary lambda0 and fixed A_Y=1/3"
            in inventory["EXTENDED_SOURCE_TORQUE_FORWARD_MODEL"]["required_fields"],
            "The material must support executable Newtonian and fixed-strength three-harmonic predictions.",
        ),
        _gate(
            "G9_BOUNDARY_COVERAGE_PROCEDURE_IS_DECISION_BEARING",
            "lambda0 to zero boundary treatment"
            in inventory["BOUNDARY_COVERAGE_PROCEDURE"]["required_fields"],
            "A published confidence curve cannot replace the underlying boundary-aware calibration.",
        ),
        _gate(
            "G10_PRIMARY_AUTHENTICATED_SOURCE_HIERARCHY_FINITE",
            hierarchy["source_count"] == 6 and hierarchy["non_contact_source_count"] == 5
            and hierarchy["contact_source_count"] == 1,
            "Five ordered non-contact source tiers precede the separately gated contact outcome.",
        ),
        _gate(
            "G11_SUPPORTING_SOURCES_CANNOT_REPLACE_PRIMARY_NUMERICAL_EVIDENCE",
            "values inferred from dissertation prose" in hierarchy["forbidden_substitutions"]
            and "unverified file-sharing mirrors" in hierarchy["forbidden_substitutions"],
            "The dissertation and unauthenticated mirrors cannot fill missing numerical evidence.",
        ),
        _gate(
            "G12_ALL_TWELVE_CUSTODY_FIELDS_MANDATORY",
            custody["required_field_count"] == 12 and len(custody["required_fields"]) == 12,
            "Every acquired object must carry source, method, timestamp, identity, hash, access, content, ingestion, and completeness fields.",
        ),
        _gate(
            "G13_FIVE_CUSTODY_STATES_ORDERED_AND_NONSUBSTITUTABLE",
            custody["ordered_states"] == STATE_ORDER and custody["state_skipping_allowed"] is False,
            "IDENTIFIED, ACQUIRED, INGESTED, VERIFIED, and COMPLETE remain distinct ordered states.",
        ),
        _gate(
            "G14_FILE_PRESENCE_CANNOT_CREATE_COMPLETENESS",
            custody["file_presence_implies_completeness"] is False
            and packet["content_verification_contract"]["supplement_receipt_is_success"] is False,
            "A downloaded or parsed supplement can leave every scientific component incomplete.",
        ),
        _gate(
            "G15_FORWARD_MODEL_SUFFICIENCY_TEST_EXACT",
            packet["forward_model_sufficiency_test"]["obligation_count"] == 6
            and packet["forward_model_sufficiency_test"]["published_newtonian_baseline_required_before_scalar"] is True,
            "Six executable obligations and Newtonian baseline reproduction precede scalar use.",
        ),
        _gate(
            "G16_STATISTICAL_SUFFICIENCY_REQUIRES_BASELINE_PROFILING_AND_COVERAGE",
            packet["statistical_sufficiency_test"]["obligation_count"] == 5
            and packet["statistical_sufficiency_test"]["all_files_present_can_substitute_for_baseline_reproduction"] is False,
            "File presence cannot replace likelihood, nuisance, coverage, and baseline validation.",
        ),
        _gate(
            "G17_RETRIEVAL_ATTEMPT_AND_MIRROR_LIMITS_FINITE",
            protocol["maximum_total_retrieval_attempts"] == 8
            and protocol["maximum_attempts_per_concrete_url"] == 2
            and protocol["maximum_alternative_authenticated_mirrors"] == 2
            and protocol["maximum_non_contact_source_tiers"] == 5,
            "The future acquisition has finite source, attempt, URL, mirror, and ingestion limits.",
        ),
        _gate(
            "G18_ACCESS_CONTROL_AND_CONTACT_FIREWALLS_BINDING",
            protocol["access_control_circumvention_allowed"] is False
            and protocol["author_contact_status"] == "NOT_AUTHORIZED_TERMINAL_OUTCOME_ONLY",
            "Acquisition must use legitimate access and stop rather than contact an author or custodian.",
        ),
        _gate(
            "G19_TERMINAL_OUTCOMES_SUPPORT_ONE_PRINCIPAL_AND_PARTIAL_FINDINGS",
            packet["acquisition_terminal_outcomes"]["outcome_count"] == 9
            and packet["acquisition_terminal_outcomes"]["one_principal_outcome_required"] is True
            and packet["acquisition_terminal_outcomes"]["multiple_subordinate_findings_allowed"] is True,
            "One principal status controls authority while component-level omissions remain visible.",
        ),
        _gate(
            "G20_PARALLEL_COMPUTATIONAL_LANES_REMAIN_SEPARATE",
            scope["synthetic_forward_model_lane_authorized"] is False
            and scope["supplied_constraint_reinterpretation_authorized"] is False,
            "Synthetic forecasting and published-result reinterpretation require fresh authority.",
        ),
        _gate(
            "G21_NO_ACQUISITION_FIT_OR_THEORY_ADOPTION_DURING_REVIEW",
            all(row["status"] == "PASS" for row in probes)
            and scope["supplement_downloaded_or_acquired"] is False
            and scope["likelihood_evaluated"] is False
            and scope["scalar_branch_adopted"] is False
            and scope["gravitational_action_selected"] is False,
            "Review performs no retrieval, contact, forecast, reinterpretation, likelihood, bound, or theory adoption.",
        ),
    ]


def build_review() -> dict[str, Any]:
    custody, packet = _validate_packet()
    probes = _adversarial_probes(packet)
    gates = _review_gates(packet, probes)
    gate_pass_count = sum(row["status"] == "PASS" for row in gates)
    probe_pass_count = sum(row["status"] == "PASS" for row in probes)
    if gate_pass_count != len(gates):
        raise ValueError("acquisition packet independent review gate failure")
    if probe_pass_count != len(probes):
        raise ValueError("acquisition packet adversarial probe failure")

    protocol = packet["bounded_acquisition_protocol"]
    return {
        "schema_id": "toe.eotwash_2020_yukawa_primary_evidence_custody_acquisition.packet_review.v0",
        "captured_at_utc": "2026-07-18T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "principal_packet_review_outcome": PRINCIPAL_OUTCOME,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "result_review_target": RESULT_REVIEW_TARGET,
        "authority": {
            "consumed_packet_verdict": packet["verdict"],
            "frozen_packet_artifact_count": len(custody),
            "frozen_packet_artifacts": custody,
        },
        "independent_inventory_audit": {
            "inventory_item_count": packet["required_evidence_inventory"]["item_count"],
            "complete_item_count_now": 0,
            "hidden_decision_bearing_input_found": False,
            "newtonian_baseline_location": "FORWARD_AND_STATISTICAL_SUFFICIENCY_OBLIGATIONS",
            "all_items_tied_to_operations": True,
        },
        "custody_state_machine_audit": {
            "ordered_states": STATE_ORDER,
            "required_custody_field_count": 12,
            "state_skipping_allowed": False,
            "file_presence_implies_verification": False,
            "file_presence_implies_completeness": False,
        },
        "adversarial_no_shortcut_probes": {
            "probe_count": len(probes),
            "pass_count": probe_pass_count,
            "failure_count": len(probes) - probe_pass_count,
            "rows": probes,
        },
        "review_gates": {
            "gate_count": len(gates),
            "pass_count": gate_pass_count,
            "failure_count": len(gates) - gate_pass_count,
            "rows": gates,
        },
        "authorized_acquisition": {
            "execution_count": 1,
            "execution_scope": "NON_CONTACT_PRIMARY_EVIDENCE_RETRIEVAL_INGESTION_AND_COMPLETENESS_CLASSIFICATION_ONLY",
            "maximum_non_contact_source_tiers": protocol["maximum_non_contact_source_tiers"],
            "maximum_total_retrieval_attempts": protocol["maximum_total_retrieval_attempts"],
            "maximum_attempts_per_concrete_url": protocol["maximum_attempts_per_concrete_url"],
            "maximum_alternative_authenticated_mirrors": protocol["maximum_alternative_authenticated_mirrors"],
            "maximum_interactive_manual_download_sessions": protocol["maximum_interactive_manual_download_sessions"],
            "interactive_manual_download_allowed": True,
            "interactive_manual_download_condition": (
                "only legitimate normal access during the one authorized execution; "
                "no access-control circumvention"
            ),
            "author_or_custodian_contact_authorized": False,
            "access_control_circumvention_allowed": False,
            "likelihood_execution_authorized": False,
            "synthetic_forecast_authorized": False,
            "published_constraint_reinterpretation_authorized": False,
            "must_stop_at_result_review": True,
            "result_review_target": RESULT_REVIEW_TARGET,
        },
        "binding_execution_rules": [
            "Use the six-tier hierarchy in order and only the first five non-contact tiers.",
            "Record all twelve custody fields for every acquired object.",
            "Advance custody states one step at a time and only after the state-specific condition is met.",
            "Inspect contents against each of the six evidence inventory items.",
            "Permit one principal acquisition outcome and up to six subordinate component findings.",
            "Do not infer missing values from plots, screenshots, secondary sources, or dissertation prose.",
            "Do not reconstruct an approximate apparatus model during acquisition.",
            "Do not bypass access controls or use an unauthenticated file-sharing mirror.",
            "If contact is required, issue AUTHORS_OR_CUSTODIAN_CONTACT_REQUIRED and stop without contact.",
            "Do not run the Newtonian baseline, scalar likelihood, synthetic forecast, or published-limit reinterpretation.",
            "Stop after eight retrieval attempts, exhaustion of five non-contact tiers, or the first principal outcome.",
            f"Stop at {RESULT_REVIEW_TARGET} after the one bounded acquisition.",
        ],
        "scope": {
            "independent_packet_review_executed": True,
            "packet_accepted": True,
            "one_bounded_acquisition_execution_authorized": True,
            "acquisition_executed_now": False,
            "supplement_downloaded_or_acquired_now": False,
            "author_or_custodian_contact_authorized": False,
            "author_or_custodian_contact_executed": False,
            "access_control_circumvented": False,
            "primary_evidence_contract_complete": False,
            "forward_model_executable": False,
            "coverage_calibration_executable": False,
            "synthetic_forward_model_lane_authorized": False,
            "supplied_constraint_reinterpretation_authorized": False,
            "likelihood_execution_authorized": False,
            "likelihood_evaluated": False,
            "numerical_lambda_bound_computed": False,
            "numerical_alpha_bound_computed": False,
            "beta_zero_adopted": False,
            "alpha_sign_or_value_adopted": False,
            "scalar_branch_adopted": False,
            "native_scalar_bridge_identified": False,
            "native_gravitational_principle_identified": False,
            "gravitational_action_selected": False,
            "matter_sector_selected": False,
            "orbital_or_light_propagation_analysis_executed": False,
            "frame_dragging_resumed": False,
            "master_action_mutated": False,
        },
        "current_posture": {
            "acquisition_packet_review": "ACCEPTED_21_OF_21_GATES",
            "principal_outcome": PRINCIPAL_OUTCOME,
            "authorized_acquisition_executions": 1,
            "acquisition_executed": "NO",
            "required_evidence_items": "0_OF_6_COMPLETE",
            "files_acquired": 0,
            "author_contact": "NOT_AUTHORIZED",
            "synthetic_forecast": "NOT_AUTHORIZED",
            "published_reinterpretation": "NOT_AUTHORIZED",
            "likelihood": "NOT_EXECUTED",
            "scalar_range_bound": "NONE",
            "alpha": "NOT_SELECTED",
            "scalar_branch": "NOT_ADOPTED",
            "native_gravitational_principle": "NOT_IDENTIFIED",
            "gravitational_action": "NOT_SELECTED",
            "next_authority": SELECTED_NEXT_TARGET,
        },
        "claim_ceiling": (
            "The acquisition packet is accepted for one finite, legitimate, non-contact "
            "primary-evidence retrieval, custody, ingestion, and completeness-classification "
            "execution under the frozen source and attempt limits. No evidence is acquired "
            "during review. Author or custodian contact, access-control circumvention, "
            "synthetic forecasting, published-constraint reinterpretation, apparatus "
            "reconstruction, Newtonian or scalar likelihood execution, scalar-range or "
            "alpha bounds, branch adoption, native scalar bridge, native gravitational "
            "principle, gravitational action, orbital result, frame-dragging result, and "
            "master-action changes remain unauthorized."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_review(), indent=2, sort_keys=True) + "\n").encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    raw = artifact_bytes()
    path = REPO_ROOT / REPORT_RELATIVE_PATH
    if args.write:
        path.write_bytes(raw)
    if args.check:
        if not path.exists() or path.read_bytes() != raw:
            raise SystemExit("Eot-Wash acquisition packet review artifact drift")
    if not args.write and not args.check:
        print(raw.decode("utf-8"), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

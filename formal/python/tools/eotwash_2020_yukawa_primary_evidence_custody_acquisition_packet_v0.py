from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "EOTWASH_2020_YUKAWA_PRIMARY_EVIDENCE_CUSTODY_ACQUISITION_PACKET_"
    "20260718_v0.json"
)
HUMAN_RELATIVE_PATH = (
    "formal/docs/lanes/"
    "EOTWASH_2020_YUKAWA_PRIMARY_EVIDENCE_CUSTODY_ACQUISITION_PACKET_"
    "20260718_v0.md"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_eotwash_2020_yukawa_primary_evidence_custody_acquisition_packet_v0.py"
)
TARGET = "prepare_eotwash_2020_yukawa_primary_evidence_custody_acquisition_packet_v0"
VERDICT = "PREPARED_PRIMARY_EVIDENCE_ACQUISITION_CONTRACT_PENDING_INDEPENDENT_REVIEW"
SELECTED_NEXT_TARGET = (
    "review_eotwash_2020_yukawa_primary_evidence_custody_acquisition_packet_v0_result"
)
SELECTED_NEXT_TARGET_KIND = (
    "INDEPENDENT_ACQUISITION_PACKET_REVIEW_ONLY_NO_DOWNLOAD_CONTACT_OR_FIT"
)

AUTHORITY_HASHES = {
    "formal/docs/lanes/POST_SCALAR_ONLY_QUADRATIC_GRAVITY_RANGE_AND_WEAK_FIELD_CONSTRAINT_PACKET_REVIEW_SCIENTIFIC_RESPONSE_SELECTION_20260718_v0.md":
        "312a8f3b1067035f6ce59b20c1aa1bde5d7c1f565bd13c843177b5bb08058330",
    "formal/docs/release/POST_SCALAR_ONLY_QUADRATIC_GRAVITY_RANGE_AND_WEAK_FIELD_CONSTRAINT_PACKET_REVIEW_SCIENTIFIC_RESPONSE_SELECTION_20260718_v0.json":
        "9a51d494d257344d214d248a7af4874cd7bdf45949f6665047ff01342dbdc7b9",
    "formal/python/tools/post_scalar_only_quadratic_gravity_range_and_weak_field_constraint_packet_review_scientific_response_selection_v0.py":
        "7428993ea205e342fc223375740357231b3b3eedea0e8feeb110ae29f7024645",
    "formal/python/tests/test_post_scalar_only_quadratic_gravity_range_and_weak_field_constraint_packet_review_scientific_response_selection_v0.py":
        "79d827c1ff1e7454daa948ba44267289e64408bbe1bd0bcf71697ebd514a0cca",
    "formal/toe_formal/ToeFormal/Derivation/PostScalarOnlyQuadraticGravityRangeAndWeakFieldConstraintPacketReviewScientificResponseSelectionV0.lean":
        "77972eecd866c216ace2e1b05270342d58279ea3e4310afb69145f971d28f31a",
}

CUSTODY_FIELDS = [
    "source_location",
    "acquisition_method",
    "acquisition_timestamp_utc",
    "original_filename",
    "file_type",
    "file_size_bytes",
    "sha256",
    "publisher_or_custodian_identity",
    "license_or_access_conditions",
    "content_description",
    "ingestion_result",
    "completeness_status",
]

CUSTODY_STATES = ["IDENTIFIED", "ACQUIRED", "INGESTED", "VERIFIED", "COMPLETE"]


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_json(relative_path: str) -> dict[str, Any]:
    value = json.loads((REPO_ROOT / relative_path).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object: {relative_path}")
    return value


def _validate_authority() -> tuple[list[dict[str, str]], dict[str, Any]]:
    custody: list[dict[str, str]] = []
    for relative_path, expected in AUTHORITY_HASHES.items():
        observed = _sha256(REPO_ROOT / relative_path)
        if observed != expected:
            raise ValueError(f"post-block response-selection drift: {relative_path}")
        custody.append({"relative_path": relative_path, "sha256": observed})
    selection = _load_json(
        "formal/docs/release/"
        "POST_SCALAR_ONLY_QUADRATIC_GRAVITY_RANGE_AND_WEAK_FIELD_CONSTRAINT_"
        "PACKET_REVIEW_SCIENTIFIC_RESPONSE_SELECTION_20260718_v0.json"
    )
    if selection.get("verdict") != (
        "SELECTED_TARGETED_EOTWASH_PRIMARY_EVIDENCE_ACQUISITION_PACKET_PREPARATION"
    ):
        raise ValueError("targeted acquisition packet preparation was not selected")
    if selection.get("selected_next_target") != TARGET:
        raise ValueError("response selection did not authorize this packet")
    scope = selection["scope"]
    if scope.get("eotwash_acquisition_packet_preparation_authorized") is not True:
        raise ValueError("acquisition packet preparation is not authorized")
    if scope.get("supplement_download_or_acquisition_authorized") is not False:
        raise ValueError("response selection improperly authorized acquisition")
    if scope.get("author_or_custodian_contact_authorized") is not False:
        raise ValueError("response selection improperly authorized contact")
    return custody, selection


def _inventory_rows() -> list[dict[str, Any]]:
    return [
        {
            "item_id": "OBSERVATION_TORQUE_VECTOR",
            "expected_count": 285,
            "expected_shape": "95 settings x 3 harmonics",
            "required_fields": [
                "all 95 experimental setting identifiers",
                "18 omega torque at every setting",
                "54 omega torque at every setting",
                "120 omega torque at every setting",
                "measurement units",
                "row identifiers and ordering",
                "data-selection or exclusion flags",
            ],
            "required_operation": "construct the exact published observation and residual vector",
            "current_state": "IDENTIFIED_EXPECTED_NOT_ACQUIRED",
            "complete": False,
        },
        {
            "item_id": "DISPLACEMENT_AND_CONFIGURATION_METADATA",
            "required_fields": [
                "x y s displacement metadata for every setting",
                "detector and attractor configuration identifiers",
                "alignment and rotation-phase conventions",
                "ordering key matching the torque vector",
                "data cuts or configuration exclusions",
            ],
            "required_operation": "evaluate each model prediction at the correct physical configuration",
            "current_state": "IDENTIFIED_EXPECTED_NOT_ACQUIRED",
            "complete": False,
        },
        {
            "item_id": "UNCERTAINTY_AND_COVARIANCE_MODEL",
            "required_fields": [
                "pointwise statistical uncertainties",
                "correlated systematic uncertainties",
                "covariance matrix or equivalent generative error model",
                "block structure across settings or harmonics",
                "regularization and conditioning rules",
                "units and ordering matching the observation vector",
            ],
            "required_operation": "weight residuals and reproduce the effective information content",
            "current_state": "IDENTIFIED_EXPECTED_NOT_ACQUIRED",
            "complete": False,
        },
        {
            "item_id": "FIVE_NUISANCE_PRIOR_CONTRACTS",
            "expected_count": 5,
            "parameter_ids": ["x0", "y0", "s0", "surface_roughness", "gamma"],
            "required_fields": [
                "identity and physical meaning",
                "prior or constraint form",
                "central value and width",
                "cross-parameter covariance or declared independence",
                "profiling marginalization or fixing rule",
                "parameter bounds",
                "exact forward-model entry point",
            ],
            "required_operation": "profile the five published geometry and calibration nuisances",
            "current_state": "IDENTIFIED_EXPECTED_NOT_ACQUIRED",
            "complete": False,
        },
        {
            "item_id": "EXTENDED_SOURCE_TORQUE_FORWARD_MODEL",
            "required_fields": [
                "detector and attractor density patterns",
                "material densities and thicknesses",
                "relative positions and alignment conventions",
                "harmonic definitions and phase conventions",
                "numerical integration or Fourier-Bessel procedure",
                "calibration and transfer factors",
                "Newtonian baseline implementation",
                "Yukawa implementation for arbitrary lambda0 and fixed A_Y=1/3",
            ],
            "required_operation": "compute the three predicted torque harmonics at all 95 settings",
            "current_state": "IDENTIFIED_EXPECTED_NOT_ACQUIRED",
            "complete": False,
        },
        {
            "item_id": "BOUNDARY_COVERAGE_PROCEDURE",
            "required_fields": [
                "test statistic",
                "null and alternative parameterization",
                "nuisance profiling procedure",
                "pseudoexperiment or Monte Carlo design if used",
                "simulation count and critical-value construction if used",
                "lambda0 to zero boundary treatment",
                "interpolation rule",
                "random-seed or reproducibility policy",
            ],
            "required_operation": "calibrate valid exclusion coverage at the Einstein boundary",
            "current_state": "IDENTIFIED_EXPECTED_NOT_ACQUIRED",
            "complete": False,
        },
    ]


def _source_hierarchy() -> list[dict[str, Any]]:
    return [
        {
            "priority": 1,
            "source_id": "APS_OFFICIAL_SUPPLEMENTAL_DEPOSIT",
            "source_class": "OFFICIAL_PUBLISHER_SUPPLEMENT",
            "identifier": "https://link.aps.org/supplemental/10.1103/PhysRevLett.124.101101",
            "current_status": "IDENTIFIED_EXPECTED_URL_CONTENT_NOT_ACQUIRED",
            "may_execute_now": False,
        },
        {
            "priority": 2,
            "source_id": "APS_ARTICLE_ATTACHMENTS_AND_DATA_LINKS",
            "source_class": "OFFICIAL_JOURNAL_RECORD",
            "identifier": "https://journals.aps.org/prl/abstract/10.1103/PhysRevLett.124.101101",
            "current_status": "IDENTIFIED_METADATA_ONLY",
            "may_execute_now": False,
        },
        {
            "priority": 3,
            "source_id": "EOTWASH_OR_UW_AUTHOR_MAINTAINED_ARCHIVE",
            "source_class": "AUTHOR_MAINTAINED_INSTITUTIONAL_ARCHIVE",
            "identifier": "TO_BE_IDENTIFIED_DURING_AUTHORIZED_ACQUISITION",
            "current_status": "NOT_YET_IDENTIFIED",
            "may_execute_now": False,
        },
        {
            "priority": 4,
            "source_id": "UW_RESEARCHWORKS_RECORD",
            "source_class": "UNIVERSITY_REPOSITORY_SUPPORTING_METHODS",
            "identifier": (
                "https://digital.lib.washington.edu/researchworks/items/"
                "971237d1-100a-41ae-9027-d1bbce8cf315/full"
            ),
            "current_status": "IDENTIFIED_SUPPORTING_NOT_PRIMARY_NUMERICAL_SUBSTITUTE",
            "may_execute_now": False,
        },
        {
            "priority": 5,
            "source_id": "VERIFIED_PUBLISHER_OR_LAB_ARCHIVE_MIRROR",
            "source_class": "AUTHENTICATED_INSTITUTIONAL_MIRROR",
            "identifier": "TO_BE_IDENTIFIED_WITH_PROVENANCE",
            "current_status": "NOT_YET_IDENTIFIED",
            "may_execute_now": False,
        },
        {
            "priority": 6,
            "source_id": "AUTHOR_OR_DATA_CUSTODIAN_CONTACT",
            "source_class": "EXTERNAL_COMMUNICATION_REQUIRING_SEPARATE_AUTHORITY",
            "identifier": "NO_CONTACT_TARGET_SELECTED",
            "current_status": "NOT_AUTHORIZED_TERMINAL_OUTCOME_ONLY",
            "may_execute_now": False,
        },
    ]


def _terminal_outcomes() -> list[dict[str, Any]]:
    return [
        {
            "outcome": "SUPPLEMENT_ACQUIRED_AND_COMPLETE",
            "principal": True,
            "condition": "all six inventory items independently reach COMPLETE",
        },
        {
            "outcome": "SUPPLEMENT_ACQUIRED_BUT_OBSERVATION_VECTOR_INCOMPLETE",
            "principal": False,
            "condition": "observation vector or row mapping fails completeness",
        },
        {
            "outcome": "SUPPLEMENT_ACQUIRED_BUT_COVARIANCE_INCOMPLETE",
            "principal": False,
            "condition": "numerical uncertainty or correlation model is incomplete",
        },
        {
            "outcome": "SUPPLEMENT_ACQUIRED_BUT_NUISANCE_PRIORS_INCOMPLETE",
            "principal": False,
            "condition": "any one of five nuisance contracts remains underdefined",
        },
        {
            "outcome": "SUPPLEMENT_ACQUIRED_BUT_FORWARD_MODEL_INCOMPLETE",
            "principal": False,
            "condition": "three-harmonic torque predictions cannot be computed independently",
        },
        {
            "outcome": "SUPPLEMENT_ACQUIRED_BUT_COVERAGE_PROCEDURE_INCOMPLETE",
            "principal": False,
            "condition": "boundary-aware exclusion calibration cannot be reproduced",
        },
        {
            "outcome": "SUPPLEMENT_IDENTIFIED_BUT_NOT_INGESTIBLE",
            "principal": True,
            "condition": "legitimate bytes are obtained but cannot be opened or parsed within the bounded route",
        },
        {
            "outcome": "AUTHORS_OR_CUSTODIAN_CONTACT_REQUIRED",
            "principal": True,
            "condition": "non-contact authenticated sources are exhausted with decision-bearing omissions",
        },
        {
            "outcome": "PRIMARY_EVIDENCE_NOT_OBTAINABLE_WITHIN_BOUNDED_ROUTE",
            "principal": True,
            "condition": "bounded legitimate acquisition terminates without an available next source",
        },
    ]


def build_packet() -> dict[str, Any]:
    custody, selection = _validate_authority()
    human = REPO_ROOT / HUMAN_RELATIVE_PATH
    test = REPO_ROOT / TEST_RELATIVE_PATH
    if not human.is_file() or not test.is_file():
        raise ValueError("acquisition packet human record or focused test missing")

    inventory = _inventory_rows()
    sources = _source_hierarchy()
    outcomes = _terminal_outcomes()
    controls = [
        "EXACT_SELECTION_AUTHORITY_AND_CUSTODY",
        "EXACT_SIX_ITEM_EVIDENCE_INVENTORY",
        "OBSERVATION_VECTOR_REQUIRES_PHYSICAL_ROW_MAPPING",
        "UNCERTAINTY_AND_COVARIANCE_REQUIRED",
        "FIVE_NUISANCE_CONTRACTS_REQUIRED",
        "EXTENDED_SOURCE_FORWARD_MODEL_REQUIRED",
        "BOUNDARY_COVERAGE_PROCEDURE_REQUIRED",
        "FINITE_PRIMARY_SOURCE_HIERARCHY",
        "THIRD_PARTY_AND_PLOT_SUBSTITUTIONS_FORBIDDEN",
        "TWELVE_FIELD_CUSTODY_RECORD_REQUIRED",
        "FIVE_CUSTODY_STATES_ORDERED_AND_NONSUBSTITUTABLE",
        "FILE_PRESENCE_CANNOT_CREATE_SCIENTIFIC_COMPLETENESS",
        "CONTENT_LEVEL_VERIFICATION_REQUIRED",
        "FORWARD_MODEL_SUFFICIENCY_TEST_FROZEN",
        "STATISTICAL_SUFFICIENCY_TEST_FROZEN",
        "NEWTONIAN_BASELINE_BEFORE_SCALAR_USE",
        "FINITE_ATTEMPT_AND_MIRROR_LIMITS",
        "AUTHOR_CONTACT_SEPARATE_AUTHORITY",
        "NO_DOWNLOAD_OR_ACQUISITION_DURING_PREPARATION",
        "NO_LIKELIHOOD_OR_PUBLISHED_CURVE_BOUND",
        "PARTIAL_FINDINGS_AND_ONE_PRINCIPAL_STATUS_SUPPORTED",
        "SYNTHETIC_AND_SUPPLIED_REINTERPRETATION_LANES_SEPARATE",
        "NO_ALPHA_BRANCH_PRINCIPLE_OR_ACTION_ADOPTION",
        "ROTATION_ONLY_TO_INDEPENDENT_PACKET_REVIEW",
    ]

    return {
        "schema_id": "toe.eotwash_2020_yukawa_primary_evidence_custody_acquisition.packet.v0",
        "captured_at_utc": "2026-07-18T00:00:00Z",
        "packet_id": "EOTWASH_2020_YUKAWA_PRIMARY_EVIDENCE_CUSTODY_ACQUISITION_PACKET_20260718_v0",
        "target": TARGET,
        "verdict": VERDICT,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "consumed_selection_verdict": selection["verdict"],
            "consumed_selection_gate_count": selection["preparation_gates"]["pass_count"],
            "frozen_selection_artifact_count": len(custody),
            "frozen_selection_artifacts": custody,
            "human_packet": {"relative_path": HUMAN_RELATIVE_PATH, "sha256": _sha256(human)},
            "generator": {
                "relative_path": Path(__file__).resolve().relative_to(REPO_ROOT).as_posix(),
                "sha256": _sha256(Path(__file__).resolve()),
            },
            "test": {"relative_path": TEST_RELATIVE_PATH, "sha256": _sha256(test)},
        },
        "experiment_boundary": {
            "experiment": "EOTWASH_2020_SHORT_RANGE_ISL_TORSION_BALANCE",
            "doi": "10.1103/PhysRevLett.124.101101",
            "arxiv": "https://arxiv.org/abs/2002.11761",
            "fixed_signal": "A_Y=1/3",
            "experiment_scientifically_suitable": True,
            "independent_likelihood_executable_now": False,
            "acquisition_objective": (
                "place the exact evidence, nuisance contract, apparatus-to-torque model, "
                "and boundary-coverage procedure into verified project custody"
            ),
        },
        "required_evidence_inventory": {
            "item_count": len(inventory),
            "complete_item_count": 0,
            "rows": inventory,
        },
        "source_hierarchy": {
            "source_count": len(sources),
            "non_contact_source_count": 5,
            "contact_source_count": 1,
            "rows": sources,
            "forbidden_substitutions": [
                "plot digitization",
                "screenshots",
                "secondary reviews",
                "values inferred from dissertation prose",
                "generic apparatus reconstruction",
                "unverified file-sharing mirrors",
            ],
        },
        "custody_contract": {
            "required_field_count": len(CUSTODY_FIELDS),
            "required_fields": CUSTODY_FIELDS,
            "state_count": len(CUSTODY_STATES),
            "ordered_states": CUSTODY_STATES,
            "state_meanings": {
                "IDENTIFIED": "the object is known to exist or is expected at a canonical identifier",
                "ACQUIRED": "legitimate bytes were obtained and recorded",
                "INGESTED": "the contents were successfully opened and parsed",
                "VERIFIED": "content was matched to one exact inventory requirement",
                "COMPLETE": "every required field for that inventory item is available",
            },
            "state_skipping_allowed": False,
            "file_presence_implies_completeness": False,
            "current_acquired_object_count": 0,
            "current_ingested_object_count": 0,
            "current_verified_item_count": 0,
            "current_complete_item_count": 0,
        },
        "content_verification_contract": {
            "supplement_receipt_is_success": False,
            "verification_unit": "ONE_REQUIRED_EVIDENCE_ITEM",
            "partial_results_allowed": True,
            "principal_status_count": 1,
            "subordinate_finding_count_unbounded": False,
            "subordinate_finding_cap": 6,
            "binding_rule": (
                "A file can be acquired and ingested while every scientific inventory "
                "item remains incomplete."
            ),
        },
        "forward_model_sufficiency_test": {
            "status": "PREPARED_NOT_EXECUTED",
            "obligation_count": 6,
            "obligations": [
                "compute the authors' Newtonian prediction",
                "compute all three torque harmonics at all 95 settings",
                "propagate all five nuisance parameters through the model",
                "compute the fixed A_Y=1/3 Yukawa contribution for arbitrary tested lambda0",
                "reproduce the exact observation ordering",
                "construct the complete residual vector used by the likelihood",
            ],
            "published_newtonian_baseline_required_before_scalar": True,
            "published_newtonian_baseline": "chi_squared=275.0 for nu=285, P=0.654",
            "baseline_tolerance_to_be_frozen_in_future_likelihood_packet": True,
        },
        "statistical_sufficiency_test": {
            "status": "PREPARED_NOT_EXECUTED",
            "obligation_count": 5,
            "obligations": [
                "specify the complete likelihood or exact equivalent statistic without guessing",
                "reproduce the standard-physics baseline fit",
                "reproduce the five-nuisance profiling rule",
                "specify and validate boundary-aware confidence calibration",
                "reproduce the authors' reported standard-physics result within a frozen tolerance",
            ],
            "all_files_present_can_substitute_for_baseline_reproduction": False,
        },
        "bounded_acquisition_protocol": {
            "status": "PREPARED_NOT_AUTHORIZED_FOR_EXECUTION",
            "maximum_non_contact_source_tiers": 5,
            "maximum_total_retrieval_attempts": 8,
            "maximum_attempts_per_concrete_url": 2,
            "maximum_alternative_authenticated_mirrors": 2,
            "maximum_interactive_manual_download_sessions": 1,
            "interactive_manual_download_status": "REQUIRES_ACCEPTED_PACKET_REVIEW_AND_EXPLICIT_EXECUTION_AUTHORITY",
            "access_control_circumvention_allowed": False,
            "author_contact_status": "NOT_AUTHORIZED_TERMINAL_OUTCOME_ONLY",
            "failed_ingestion_definition": (
                "bytes cannot be opened or parsed with the declared file type after "
                "two documented non-destructive ingestion attempts"
            ),
            "stop_rule": (
                "stop after eight total retrieval attempts, exhaustion of five non-contact "
                "source tiers, or the first terminal principal outcome"
            ),
        },
        "acquisition_terminal_outcomes": {
            "outcome_count": len(outcomes),
            "rows": outcomes,
            "one_principal_outcome_required": True,
            "multiple_subordinate_findings_allowed": True,
        },
        "packet_review_outcomes": [
            "PRIMARY_EVIDENCE_ACQUISITION_CONTRACT_READY",
            "BLOCKED_EVIDENCE_INVENTORY_UNDERINCLUSIVE",
            "BLOCKED_SOURCE_HIERARCHY_OR_PROVENANCE_UNSAFE",
            "BLOCKED_CUSTODY_COMPLETENESS_CONFLATION",
            "BLOCKED_ACQUISITION_SCOPE_OPEN_ENDED",
            "BLOCKED_CONTACT_OR_DOWNLOAD_PREAUTHORIZED",
        ],
        "parallel_computational_lanes": {
            "synthetic_forward_model_and_sensitivity_forecast": "SCIENTIFICALLY_VALUABLE_FRESH_AUTHORITY_REQUIRED",
            "supplied_published_constraint_reinterpretation": "SCIENTIFICALLY_VALUABLE_FRESH_AUTHORITY_REQUIRED",
            "independent_real_data_reanalysis": "REMAINS_BLOCKED",
            "new_measurement_program": "NOT_AUTHORIZED",
            "binding_claim_separation": [
                "synthetic injection recovery tests a simulated-data pipeline",
                "idealized apparatus forecasts are theoretical computational results",
                "published-limit translation is supplied empirical evidence",
                "independent reproduction requires real primary evidence and an executable model",
            ],
        },
        "preparation_controls": {
            "control_count": len(controls),
            "pass_count": len(controls),
            "failure_count": 0,
            "rows": [{"control_id": control, "status": "PASS"} for control in controls],
        },
        "scope": {
            "packet_preparation_executed": True,
            "independent_packet_review_executed": False,
            "acquisition_execution_authorized": False,
            "supplement_downloaded_or_acquired": False,
            "access_control_circumvented": False,
            "author_or_custodian_contact_authorized": False,
            "author_or_custodian_contact_executed": False,
            "evidence_file_ingested": False,
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
            "acquisition_packet": "PREPARED_PENDING_INDEPENDENT_REVIEW",
            "required_evidence_items": "0_OF_6_COMPLETE",
            "supplement_acquisition": "NOT_STARTED",
            "author_contact": "NOT_AUTHORIZED",
            "forward_model": "NOT_EXECUTABLE",
            "coverage_procedure": "NOT_EXECUTABLE",
            "likelihood": "NOT_EXECUTED",
            "scalar_range_bound": "NONE",
            "alpha": "NOT_SELECTED",
            "scalar_branch": "NOT_ADOPTED",
            "native_gravitational_principle": "NOT_IDENTIFIED",
            "gravitational_action": "NOT_SELECTED",
            "next_authority": SELECTED_NEXT_TARGET,
        },
        "sources": [
            {
                "role": "PRIMARY_EXPERIMENT_AND_SUPPLEMENT_POINTER",
                "source": "https://arxiv.org/abs/2002.11761",
            },
            {
                "role": "OFFICIAL_APS_SUPPLEMENT_DEPOSIT_POLICY",
                "source": "https://journals.aps.org/prl/authors",
            },
            {
                "role": "SUPPORTING_METHODS_DISSERTATION_ONLY",
                "source": (
                    "https://digital.lib.washington.edu/researchworks/items/"
                    "971237d1-100a-41ae-9027-d1bbce8cf315/full"
                ),
            },
        ],
        "claim_ceiling": (
            "Preparation only of a finite, legitimate Eot-Wash 2020 primary-evidence "
            "custody acquisition protocol. No supplement or evidence file is downloaded, "
            "acquired, opened, ingested, verified, or declared complete; no access control "
            "is bypassed; no author or custodian is contacted; no synthetic forecast or "
            "published-limit reinterpretation is authorized; no likelihood, scalar-range "
            "or alpha bound, branch adoption, native scalar bridge, native gravitational "
            "principle, gravitational action, orbital result, frame-dragging result, or "
            "master-action change is computed, selected, claimed, or authorized."
        ),
    }


def artifact_bytes() -> bytes:
    return (json.dumps(build_packet(), indent=2, sort_keys=True) + "\n").encode("utf-8")


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
            raise SystemExit("Eot-Wash acquisition packet artifact drift")
    if not args.write and not args.check:
        print(raw.decode("utf-8"), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

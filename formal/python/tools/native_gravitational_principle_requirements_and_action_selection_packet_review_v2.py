from __future__ import annotations

import argparse
import dataclasses
import hashlib
import inspect
import json
import sys
import tempfile
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from formal.python.tools import (  # noqa: E402
    native_gravitational_principle_requirements_and_action_selection_packet_v2 as packet,
)


REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_ACTION_SELECTION_PACKET_"
    "REVIEW_20260718_v2.json"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_native_gravitational_principle_requirements_and_action_selection_packet_review_v2.py"
)
REVIEW_RELATIVE_PATH = (
    "formal/docs/lanes/"
    "NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_ACTION_SELECTION_PACKET_"
    "REVIEW_20260718_v2.md"
)
TARGET = (
    "review_native_gravitational_principle_requirements_and_action_selection_"
    "packet_v2_result"
)
VERDICT = "BLOCKED_CLOSE_AUTOMATED_ACTION_SELECTION_TOOLING_LANE"
PRIMARY_DIAGNOSTIC = "PROJECT_EVIDENCE_PROVIDER_SELF_ATTESTATION_ACCEPTED"
SELECTED_NEXT_TARGET = (
    "prepare_exploratory_native_gravitational_requirements_family_survey_v0"
)
SELECTED_NEXT_TARGET_KIND = (
    "NONAUTHORITATIVE_MANUALLY_ADJUDICATED_EXPLORATORY_SURVEY_ONLY"
)

AUTHORITY_AND_PACKET_HASHES = {
    "formal/docs/lanes/NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_ACTION_SELECTION_PACKET_20260718_v2.md":
        "65b0c97de4da870a2bcf0cc91229f3d738a99b6140f19eb2e96cde61b50f5b1b",
    "formal/docs/release/NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_ACTION_SELECTION_PACKET_20260718_v2.json":
        "ae072cee52afca2e05f765d4aa4fe25939416b689284bf1ddb18ff9cad0cb0b6",
    "formal/python/tools/native_gravitational_principle_requirements_and_action_selection_packet_v2.py":
        "6e3da8eef3692b3730b53930c618cae0d0a99522b8ba3c9aaf0361b8b0e6a251",
    "formal/python/tests/test_native_gravitational_principle_requirements_and_action_selection_packet_v2.py":
        "16e79a452b684cee91bcd549ca57ffc5dda8b6d069abb6a586aa1f313fbd4973",
    "formal/toe_formal/ToeFormal/Derivation/NativeGravitationalPrincipleRequirementsAndActionSelectionPacketV2.lean":
        "96caa7e6aced4c535bf0803eb20d1f8dcb35e20914aff5b54dae019a47e2d328",
    REVIEW_RELATIVE_PATH:
        "f72b793eadd4db520e30d3af5d0f22a5735d3451639ea092740a97eae3cb5b31",
}

FINDINGS = [
    {
        "order": 1,
        "diagnostic": "PROJECT_EVIDENCE_PROVIDER_SELF_ATTESTATION_ACCEPTED",
        "severity": "FOUNDATIONAL_BLOCKING",
        "finding": (
            "One caller can author the evidence claim, accepted validator label, "
            "attestation, custody manifest, and every binding hash; the project "
            "provider accepts that circular bundle as independently validated."
        ),
    },
    {
        "order": 2,
        "diagnostic": "SCIENTIFIC_RELEVANCE_VALIDATOR_NOT_EXECUTED",
        "severity": "FOUNDATIONAL_BLOCKING",
        "finding": (
            "The project path verifies schema and byte custody but dispatches no "
            "scientific assessor capable of deciding whether the source supports "
            "the exact requirement, family, status, and domain."
        ),
    },
    {
        "order": 3,
        "diagnostic": "SYNTHETIC_CONTROLS_BYPASS_PROJECT_PROVIDER_VALIDATION",
        "severity": "FOUNDATIONAL_BLOCKING",
        "finding": (
            "Controls share the top-level evaluator and reduction logic but use an "
            "exact-match in-memory provider branch that bypasses project manifests, "
            "attestations, validator bindings, and evidence-source checks."
        ),
    },
    {
        "order": 4,
        "diagnostic": "PRODUCTION_AUTHORITY_CUSTODY_NOT_REVALIDATED",
        "severity": "FOUNDATIONAL_BLOCKING",
        "finding": (
            "Authority hashes are checked while generating V2, not at each "
            "evaluate_analysis call; the scientific entry point trusts module-global "
            "catalog bindings without a current custody precondition."
        ),
    },
]


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _validate_custody() -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for relative_path, expected_hash in AUTHORITY_AND_PACKET_HASHES.items():
        observed = _sha256((REPO_ROOT / relative_path).read_bytes())
        if observed != expected_hash:
            raise ValueError(f"requirements v2 review hash mismatch: {relative_path}")
        rows.append({"relative_path": relative_path, "sha256": observed})

    report = json.loads(
        (REPO_ROOT / packet.REPORT_RELATIVE_PATH).read_text(encoding="utf-8")
    )
    if report.get("target") != packet.TARGET:
        raise ValueError("reviewed v2 packet target mismatch")
    if report.get("selected_next_target") != TARGET:
        raise ValueError("reviewed v2 packet did not authorize this review")
    if report.get("verdict") != "PREPARED_PENDING_INDEPENDENT_REVIEW":
        raise ValueError("reviewed v2 packet verdict mismatch")
    if report["real_analysis_boundary"].get("real_matrix_cells_supplied") != 0:
        raise ValueError("reviewed v2 packet contains real matrix cells")
    if report["repair_contract"].get("automatic_v3_authorized") is not False:
        raise ValueError("reviewed v2 packet automatic V3 boundary mismatch")
    return rows


def _project_request(matrix: dict[str, dict[str, dict[str, Any]]]) -> dict[str, Any]:
    return {
        "analysis_profile": packet.PROJECT_PROFILE,
        "mode": "NATIVE_ONLY",
        "requirement_ids": list(packet.PROJECT_REQUIREMENT_IDS),
        "family_ids": list(packet.PROJECT_FAMILY_IDS),
        "matrix": matrix,
        "equivalence_proof_ids": [],
        "terminal_evidence_ids": [],
        "caller_requirement_claims": [],
    }


def _empty_project_matrix() -> dict[str, dict[str, dict[str, Any]]]:
    return {
        requirement_id: {
            family_id: {
                "status": "NOT_EVALUATED",
                "evidence_id": None,
                "claim_scope": packet.CLAIM_SCOPE_BY_STATUS["NOT_EVALUATED"],
            }
            for family_id in packet.PROJECT_FAMILY_IDS
        }
        for requirement_id in packet.PROJECT_REQUIREMENT_IDS
    }


def _audit_missing_project_evidence() -> dict[str, Any]:
    result = packet.evaluate_analysis(_project_request(_empty_project_matrix()))
    passed = (
        result["status"] == "PRECHECK_FAILURE"
        and result["diagnostic"] == "PROJECT_EVIDENCE_PROVIDER_REQUIRED"
        and result["matrix_evaluated"] is False
        and result["scientific_outcome"] is None
    )
    return {
        "probe_id": "REVIEW_MISSING_PROJECT_EVIDENCE_PROVIDER",
        "expected": "PROJECT_EVIDENCE_PROVIDER_REQUIRED_BEFORE_MATRIX",
        "observed_status": result["status"],
        "observed_diagnostic": result["diagnostic"],
        "matrix_evaluated": result["matrix_evaluated"],
        "observed_scientific_outcome": result["scientific_outcome"],
        "status": "PASS" if passed else "FAIL",
    }


def _counterfeit_project_provider_probe() -> dict[str, Any]:
    source_text = (
        "This source contains no gravitational analysis and supports no matrix claim.\n"
    )
    with tempfile.TemporaryDirectory(prefix=".v2_review_", dir=REPO_ROOT) as raw:
        root = Path(raw)
        source_path = root / "irrelevant_source.txt"
        source_path.write_text(source_text, encoding="utf-8")
        source_relative = source_path.relative_to(REPO_ROOT).as_posix()
        source_hash = _sha256(source_path.read_bytes())

        records: list[packet.EvidenceRecord] = []
        matrix: dict[str, dict[str, dict[str, Any]]] = {}
        for requirement_id in packet.PROJECT_REQUIREMENT_IDS:
            matrix[requirement_id] = {}
            for family_id in packet.PROJECT_FAMILY_IDS:
                family = packet.BOUND_FAMILY_CATALOG[family_id]
                status = (
                    "OUTSIDE_FROZEN_ENVELOPE"
                    if family.envelope_status.startswith("OUTSIDE_FROZEN_")
                    else "AFFIRMATIVELY_SATISFIES_REQUIREMENT"
                )
                evidence_class = packet._evidence_class(status)
                validator_id = packet.VALIDATOR_BY_EVIDENCE_CLASS[evidence_class]
                evidence_id = f"COUNTERFEIT_{requirement_id}_{family_id}"
                attestation_path = root / f"{evidence_id}.json"
                provisional = packet.EvidenceRecord(
                    evidence_id=evidence_id,
                    profile_id=packet.PROJECT_PROFILE,
                    requirement_id=requirement_id,
                    family_id=family_id,
                    supported_status=status,
                    claim_scope=packet.CLAIM_SCOPE_BY_STATUS[status],
                    evidence_class=evidence_class,
                    source_role="PROJECT_NATIVE_EVIDENCE",
                    support_reference=attestation_path.relative_to(
                        REPO_ROOT
                    ).as_posix(),
                    validation_status="ACCEPTED",
                    validator_id=validator_id,
                )
                attestation = {
                    "schema_id": (
                        "NATIVE_GRAVITATIONAL_ANALYSIS_EVIDENCE_ATTESTATION_V2"
                    ),
                    "validator_id": validator_id,
                    "validation_status": "ACCEPTED",
                    "record_kind": "CELL_EVIDENCE",
                    "record_id": evidence_id,
                    "claim_binding_sha256": packet._claim_binding_sha256(
                        provisional
                    ),
                    "evidence_source_relative_path": source_relative,
                    "evidence_source_sha256": source_hash,
                }
                attestation_path.write_text(
                    json.dumps(attestation, indent=2, sort_keys=True) + "\n",
                    encoding="utf-8",
                )
                record = dataclasses.replace(
                    provisional,
                    support_sha256=_sha256(attestation_path.read_bytes()),
                )
                records.append(record)
                matrix[requirement_id][family_id] = {
                    "status": status,
                    "evidence_id": evidence_id,
                    "claim_scope": packet.CLAIM_SCOPE_BY_STATUS[status],
                }

        evidence_records = tuple(records)
        catalog_hash = packet._catalog_sha256(evidence_records, (), ())
        provider_id = "COUNTERFEIT_SELF_ATTESTED_PROJECT_PROVIDER"
        manifest_path = root / "manifest.json"
        manifest = {
            "schema_id": (
                "NATIVE_GRAVITATIONAL_ANALYSIS_CATALOG_PROVIDER_MANIFEST_V2"
            ),
            "manifest_validator_id": "CATALOG_PROVIDER_MANIFEST_VALIDATOR_V2",
            "provider_id": provider_id,
            "profile_id": packet.PROJECT_PROFILE,
            "catalog_sha256": catalog_hash,
            "evidence_record_count": len(evidence_records),
            "equivalence_proof_count": 0,
            "terminal_evidence_record_count": 0,
            "independent_validation_status": "ACCEPTED_FOR_BOUNDED_ANALYSIS",
        }
        manifest_path.write_text(
            json.dumps(manifest, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        provider = packet.AnalysisCatalogProvider(
            provider_id=provider_id,
            profile_id=packet.PROJECT_PROFILE,
            validation_status="CUSTODY_VALIDATED_PROJECT_PROVIDER",
            custody_manifest_relative_path=manifest_path.relative_to(
                REPO_ROOT
            ).as_posix(),
            custody_manifest_sha256=_sha256(manifest_path.read_bytes()),
            catalog_sha256=catalog_hash,
            evidence_records=evidence_records,
            equivalence_proofs=(),
            terminal_evidence_records=(),
        )
        result = packet.evaluate_analysis(
            _project_request(matrix), catalog_provider=provider
        )

    expected_rejection = "PROJECT_EVIDENCE_SCIENTIFIC_RELEVANCE_NOT_ESTABLISHED"
    accepted = (
        result["status"] == "SCIENTIFIC_OUTCOME_COMPUTED"
        and result["scientific_outcome"] == "ACTION_FAMILY_UNDERDETERMINED"
        and result["matching_scientific_outcome_count"] == 1
    )
    return {
        "probe_id": "REVIEW_COUNTERFEIT_SELF_ATTESTED_PROJECT_PROVIDER",
        "construction_kind": "TEMPORARY_PROJECT_PROFILE_ADVERSARIAL_FIXTURE",
        "source_scientific_content": "NONE",
        "source_text_sha256": _sha256(source_text.encode("utf-8")),
        "counterfeit_cell_count": len(evidence_records),
        "counterfeit_cells_persisted": False,
        "counterfeit_cells_are_real_scientific_judgments": False,
        "expected": expected_rejection,
        "observed_status": result["status"],
        "observed_diagnostic": result["diagnostic"],
        "observed_scientific_outcome": result["scientific_outcome"],
        "observed_matching_scientific_outcome_count": result[
            "matching_scientific_outcome_count"
        ],
        "status": "FAIL" if accepted else "PASS",
        "diagnostic": "PROJECT_EVIDENCE_PROVIDER_SELF_ATTESTATION_ACCEPTED",
    }


def _audit_authority_objects() -> dict[str, Any]:
    row = packet.BOUND_REQUIREMENT_CATALOG[packet.PROJECT_REQUIREMENT_IDS[0]]
    mutation_rejected = False
    try:
        row.statement_class = "SUPPLIED_STANDARD_PHYSICS_ASSUMPTION"  # type: ignore[misc]
    except (dataclasses.FrozenInstanceError, AttributeError):
        mutation_rejected = True

    request = _project_request(_empty_project_matrix())
    request["requirements"] = [{
        "requirement_id": row.requirement_id,
        "statement_class": "SUPPLIED_STANDARD_PHYSICS_ASSUMPTION",
    }]
    result = packet.evaluate_analysis(request)
    raw_rejected = (
        result["status"] == "PRECHECK_FAILURE"
        and result["diagnostic"] == "CALLER_DECISION_BEARING_OBJECT_REJECTED"
    )
    return {
        "probe_id": "REVIEW_AUTHORITY_OBJECT_FORGERY_AND_MUTATION",
        "frozen_field_mutation_rejected": mutation_rejected,
        "raw_decision_object_observed_diagnostic": result["diagnostic"],
        "raw_decision_object_rejected": raw_rejected,
        "status": "PASS" if mutation_rejected and raw_rejected else "FAIL",
    }


def _audit_semantic_validator_dispatch() -> dict[str, Any]:
    attestation_source = inspect.getsource(packet._validate_project_attestation)
    provider_source = inspect.getsource(packet._validate_catalog_provider)
    callable_validator_registry = any(
        callable(value) for value in packet.VALIDATOR_BY_EVIDENCE_CLASS.values()
    )
    dispatch_present = (
        callable_validator_registry
        or "validate_scientific_relevance(" in attestation_source
        or "validate_scientific_relevance(" in provider_source
    )
    return {
        "probe_id": "REVIEW_PROJECT_SCIENTIFIC_VALIDATOR_DISPATCH",
        "expected": "INDEPENDENT_SCIENTIFIC_ASSESSOR_EXECUTED",
        "allowed_validator_ids_are_strings_only": all(
            isinstance(value, str)
            for value in packet.VALIDATOR_BY_EVIDENCE_CLASS.values()
        ),
        "callable_scientific_validator_registry_present": (
            callable_validator_registry
        ),
        "scientific_relevance_dispatch_present": dispatch_present,
        "status": "PASS" if dispatch_present else "FAIL",
        "diagnostic": "SCIENTIFIC_RELEVANCE_VALIDATOR_NOT_EXECUTED",
    }


def _audit_shared_path() -> dict[str, Any]:
    controls = packet.run_production_controls()
    provider = packet.CONTROL_CATALOG_PROVIDER
    control_record_count = len(provider.evidence_records)
    project_attested_control_records = sum(
        bool(row.validator_id and row.support_sha256)
        for row in provider.evidence_records
    )
    shared_entry = controls["all_used_shared_entry_point"]
    project_provider_branch_exercised = (
        provider.profile_id == packet.PROJECT_PROFILE
        and provider.validation_status == "CUSTODY_VALIDATED_PROJECT_PROVIDER"
    )
    full_path = shared_entry and project_provider_branch_exercised
    return {
        "probe_id": "REVIEW_CONTROL_AND_PROJECT_PROVIDER_PATH_INTEGRITY",
        "production_entry_point_id": controls["production_entry_point_id"],
        "all_controls_use_shared_entry_point_id": shared_entry,
        "control_provider_id": provider.provider_id,
        "control_provider_profile": provider.profile_id,
        "control_provider_validation_status": provider.validation_status,
        "control_evidence_record_count": control_record_count,
        "control_records_with_project_attestation_hash_and_validator": (
            project_attested_control_records
        ),
        "project_provider_branch_exercised_by_controls": (
            project_provider_branch_exercised
        ),
        "complete_future_project_path_shared": full_path,
        "status": "PASS" if full_path else "FAIL",
        "diagnostic": "SYNTHETIC_CONTROLS_BYPASS_PROJECT_PROVIDER_VALIDATION",
    }


def _audit_per_call_authority_custody() -> dict[str, Any]:
    names = set(packet.evaluate_analysis.__code__.co_names)
    source = inspect.getsource(packet.evaluate_analysis)
    per_call_custody = "_validate_authority_and_contract" in names
    return {
        "probe_id": "REVIEW_PRODUCTION_ENTRY_AUTHORITY_CUSTODY",
        "packet_build_performs_authority_hash_validation": True,
        "evaluate_analysis_calls_authority_hash_validator": per_call_custody,
        "evaluate_analysis_reads_module_global_bound_requirement_catalog": (
            "BOUND_REQUIREMENT_CATALOG" in source
        ),
        "evaluate_analysis_reads_module_global_bound_family_catalog": (
            "BOUND_FAMILY_CATALOG" in source
        ),
        "status": "PASS" if per_call_custody else "FAIL",
        "diagnostic": "PRODUCTION_AUTHORITY_CUSTODY_NOT_REVALIDATED",
    }


def _audit_retained_contracts() -> dict[str, Any]:
    controls = packet.run_production_controls()
    outcomes = controls["outcome_controls"]
    rows = {
        row["control_id"]: row
        for row in controls["adversarial_controls"]
    }
    retained = {
        "authority_derived_requirement_input": _audit_authority_objects()["status"],
        "missing_project_evidence_fails_closed": _audit_missing_project_evidence()[
            "status"
        ],
        "affirmative_without_evidence_rejected": (
            "PASS" if rows["ADV_SATISFIES_WITHOUT_EVIDENCE"]["passed"] else "FAIL"
        ),
        "equivalence_without_proof_rejected": (
            "PASS"
            if rows["ADV_EQUIVALENT_WITHOUT_VALIDATED_PROOF"]["passed"]
            else "FAIL"
        ),
        "invalid_fR_EH_merge_rejected": (
            "PASS" if rows["ADV_INVALID_FR_TO_EH_PROOF_REJECTED"]["passed"] else "FAIL"
        ),
        "uncertainty_preserved_without_property_transport": (
            "PASS"
            if rows["ADV_UNDECIDABLE_CLASS_WITHOUT_PROPERTY_TRANSPORT"]["passed"]
            else "FAIL"
        ),
        "standard_GR_oracle_native_evidence_rejected": (
            "PASS"
            if rows["ADV_STANDARD_GR_ORACLE_AS_NATIVE_EVIDENCE"]["passed"]
            else "FAIL"
        ),
        "six_terminal_outcomes_reachable_and_exclusive": (
            "PASS"
            if outcomes["outcome_control_count"]
            == outcomes["outcome_control_pass_count"]
            == 6
            and outcomes["all_six_outcomes_reached"]
            else "FAIL"
        ),
    }
    return {
        "status": "PASS" if set(retained.values()) == {"PASS"} else "FAIL",
        "checks": retained,
        "retained_control_count": controls["retained_control_count"],
        "retained_control_pass_count": controls["retained_control_pass_count"],
        "boundary_probe_count": controls["boundary_probe_count"],
        "boundary_probe_pass_count": controls["boundary_probe_pass_count"],
        "v2_adversarial_control_count": controls["adversarial_control_count"],
        "v2_adversarial_control_pass_count": controls[
            "adversarial_control_pass_count"
        ],
        "outcome_control_count": outcomes["outcome_control_count"],
        "outcome_control_pass_count": outcomes["outcome_control_pass_count"],
    }


def build_review() -> dict[str, Any]:
    frozen_inputs = _validate_custody()
    authority_objects = _audit_authority_objects()
    missing_evidence = _audit_missing_project_evidence()
    counterfeit = _counterfeit_project_provider_probe()
    semantic_dispatch = _audit_semantic_validator_dispatch()
    shared_path = _audit_shared_path()
    per_call_authority = _audit_per_call_authority_custody()
    retained = _audit_retained_contracts()

    gates = [
        {"gate": "authority objects reject normal forgery and mutation", "status": authority_objects["status"]},
        {"gate": "missing project evidence fails closed", "status": missing_evidence["status"]},
        {"gate": "retained evidence, equivalence, uncertainty, oracle, and terminal controls", "status": retained["status"]},
        {"gate": "project evidence cannot self-attest", "status": counterfeit["status"]},
        {"gate": "scientific relevance validator is independently executed", "status": semantic_dispatch["status"]},
        {"gate": "controls traverse the future project-provider path", "status": shared_path["status"]},
        {"gate": "production entry revalidates authority custody", "status": per_call_authority["status"]},
    ]
    if counterfeit["status"] != "FAIL":
        raise ValueError("decisive counterfeit provider defect did not reproduce")
    if semantic_dispatch["status"] != "FAIL":
        raise ValueError("semantic validator dispatch defect did not reproduce")
    if shared_path["status"] != "FAIL":
        raise ValueError("project-provider shared-path defect did not reproduce")
    if per_call_authority["status"] != "FAIL":
        raise ValueError("per-call authority custody defect did not reproduce")
    if retained["status"] != "PASS":
        raise ValueError("retained V2 contracts did not reproduce")

    tool_path = Path(__file__).resolve()
    test_path = REPO_ROOT / TEST_RELATIVE_PATH
    if not test_path.is_file():
        raise ValueError("requirements v2 review focused test missing")
    return {
        "schema_id": (
            "NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_ACTION_SELECTION_"
            "PACKET_REVIEW_20260718_v2"
        ),
        "captured_at_utc": "2026-07-18T00:00:00Z",
        "target": TARGET,
        "verdict": VERDICT,
        "primary_diagnostic": PRIMARY_DIAGNOSTIC,
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": SELECTED_NEXT_TARGET_KIND,
        "authority": {
            "v2_packet_verdict": "PREPARED_PENDING_INDEPENDENT_REVIEW",
            "frozen_inputs": frozen_inputs,
            "generator": {
                "relative_path": tool_path.relative_to(REPO_ROOT).as_posix(),
                "sha256": _sha256(tool_path.read_bytes()),
            },
            "test": {
                "relative_path": TEST_RELATIVE_PATH,
                "sha256": _sha256(test_path.read_bytes()),
            },
        },
        "findings": {
            "finding_count": len(FINDINGS),
            "foundational_blocking_count": len(FINDINGS),
            "rows": FINDINGS,
        },
        "review_gates": {
            "gate_count": len(gates),
            "pass_count": sum(row["status"] == "PASS" for row in gates),
            "failure_count": sum(row["status"] == "FAIL" for row in gates),
            "rows": gates,
        },
        "authority_object_audit": authority_objects,
        "missing_project_evidence_audit": missing_evidence,
        "counterfeit_project_provider_audit": counterfeit,
        "scientific_validator_dispatch_audit": semantic_dispatch,
        "shared_path_control_audit": shared_path,
        "production_authority_custody_audit": per_call_authority,
        "retained_contract_audit": retained,
        "lane_closure": {
            "v2_was_final_automatically_authorized_repair_attempt": True,
            "automated_action_selection_tooling_lane_closed": True,
            "automatic_v3_authorized": False,
            "v3_created": False,
            "project_evidence_provider_authorized": False,
            "real_matrix_execution_authorized": False,
            "next_lane_is_exploratory": True,
            "next_lane_is_authoritative": False,
            "exploratory_results_may_populate_v2_matrix": False,
        },
        "exploratory_boundary": {
            "purpose": (
                "prepare a transparent human-readable provisional survey before "
                "any future claim promotion"
            ),
            "permitted_labels": [
                "CLEARLY COMPATIBLE",
                "CLEARLY INCOMPATIBLE",
                "LIKELY COMPATIBLE",
                "LIKELY INCOMPATIBLE",
                "UNRESOLVED",
                "OUTSIDE SCOPE",
            ],
            "nonauthoritative": True,
            "manually_adjudicated": True,
            "real_matrix_population_authorized": False,
            "survivor_or_action_selection_authorized": False,
        },
        "scope": {
            "independent_v2_review_executed": True,
            "v2_block_recorded": True,
            "automated_action_selection_tooling_lane_closed": True,
            "counterfeit_temporary_probe_cells_executed": 70,
            "counterfeit_probe_cells_are_real_matrix_cells": False,
            "counterfeit_probe_artifacts_persisted": False,
            "real_matrix_cells_computed": 0,
            "real_requirements_family_analysis_executed": False,
            "real_family_judgment_made": False,
            "real_equivalence_class_established": False,
            "real_survivor_matrix_computed": False,
            "real_scientific_outcome_selected": False,
            "native_gravitational_principle_identified": False,
            "new_postulate_authorized": False,
            "gravitational_action_proposed_or_selected": False,
            "standard_GR_comparator_activated": False,
            "matter_sector_selected": False,
            "metric_or_tetrad_variation_executed": False,
            "stress_energy_derived": False,
            "tensor_field_equation_derived": False,
            "gravitomagnetic_route_reopened": False,
            "family_envelope_expanded": False,
            "automatic_v3_authorized": False,
            "v3_created": False,
            "automation_created": False,
        },
        "retained_results": {
            "minimal_gravitational_sector_contract": "ACCEPTED",
            "native_candidate_readiness": (
                "BLOCKED_NO_NATIVE_GRAVITATIONAL_PRINCIPLE"
            ),
            "requirements_action_selection_v0": "BLOCKED_INCOMPLETE_CONTRACT",
            "requirements_action_selection_v1": "BLOCKED_UNSOUND_PRODUCTION_CONTRACT",
            "requirements_action_selection_v2": (
                "BLOCKED_PROJECT_EVIDENCE_SEMANTICS_UNSOUND"
            ),
            "real_evidence_provider": "NOT_SUPPLIED",
            "real_matrix_cells": "0_OF_70",
            "real_family_judgments": "NONE",
            "real_survivor_set": "NOT_COMPUTED",
            "native_principle": "NOT_IDENTIFIED",
            "new_postulate": "NOT_AUTHORIZED",
            "gravitational_action": "NOT_PROPOSED",
        },
    }


def artifact_bytes() -> bytes:
    return (
        json.dumps(build_review(), indent=2, sort_keys=True, ensure_ascii=True)
        + "\n"
    ).encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Generate or verify the independent V2 action-selection review."
    )
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    report_path = REPO_ROOT / REPORT_RELATIVE_PATH
    raw = artifact_bytes()
    if args.check:
        if not report_path.is_file() or report_path.read_bytes() != raw:
            raise SystemExit("requirements/action-selection V2 review artifact drift")
        print(json.dumps({
            "status": "VERIFIED",
            "verdict": VERDICT,
            "primary_diagnostic": PRIMARY_DIAGNOSTIC,
            "real_matrix_cells": 0,
            "automatic_v3_authorized": False,
        }, sort_keys=True))
        return 0
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_bytes(raw)
    print(report_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

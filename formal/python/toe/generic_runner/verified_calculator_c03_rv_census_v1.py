"""Read-only bridge from the repair corpus to the new contract boundary.

This module is deliberately outside ``verified_calculator`` because it imports
historical/candidate-era modules.  Its output is inventory evidence only and
cannot confer a trusted verification status.
"""
from __future__ import annotations

from collections import Counter
from pathlib import Path
from typing import Any

from formal.python.toe.generic_runner import fine_verification_profile_v1 as historical_profile
from formal.python.toe.generic_runner.verified_calculator.c03_rv_policy import (
    challenge_registry_census,
    mandatory_challenge_specs,
    verification_policy,
)
from formal.python.toe.generic_runner.verified_calculator.c03_rv_operation_contracts import C03_RV_PHYSICS_OPERATIONS, DERIVED_SIGNATURES, SOURCE_SIGNATURES
from formal.python.toe.generic_runner.verified_calculator.canonical import file_sha256
from formal.python.toe.generic_runner.verified_calculator.contracts import ClaimAuthorityBindingV1, ScientificAuthorityBindingV1
from formal.python.toe.generic_runner.verified_calculator.errors import require
from formal.python.toe.generic_runner.verified_calculator.milestones import C03_RV_ROOTS


AUTHORITY_RECORDS = {
    "c03_terminal": (
        "formal/tooling/scientific_compute/model1_installation_preparation/route_c03_terminal_adjudication_pass_0275_v0/terminal_adjudication.json",
        "6156ec809a79c5384f2d2332c9d48b447b4b91ad747ec52ad6088995bae5d5c2",
    ),
    "current_route_c": (
        "formal/docs/release/STRICT_MODEL1_ROUTE_C_CURRENT_AUTHORITY_v0.json",
        "682476eb2bd8a05ffd5b5ff813d27c0aad597d04d1653e1362419ada2f9c6d76",
    ),
    "rv_damage_matrix": (
        "formal/tooling/scientific_compute/model1_installation_preparation/route_c03_values_pass_0272_v0/closeout/six_record_value_damage_matrix.json",
        "6141848d32b22fc7dc50aeb2a34ffc08982cd68468106aed145032bf753ecafd",
    ),
}


def scientific_authority_binding(profile_hash: str) -> ScientificAuthorityBindingV1:
    """Bind existing scientific authority without reinterpreting or promoting it."""
    repository_root = Path(__file__).resolve().parents[4]
    for path_text, expected_hash in AUTHORITY_RECORDS.values():
        path = repository_root / path_text
        require(path.is_file() and file_sha256(path) == expected_hash, "C03_RV_AUTHORITY_RECORD_IDENTITY", path_text)

    c03_hashes = (AUTHORITY_RECORDS["c03_terminal"][1], AUTHORITY_RECORDS["current_route_c"][1])
    rv_hashes = (AUTHORITY_RECORDS["rv_damage_matrix"][1],)
    common_limitations = (
        "Independent computational/AI triangulation; no external human expert review.",
        "No SU(5), CCFT, ToE, phenomenology, publication, production, or replacement-runner qualification follows.",
    )
    bindings: dict[str, ClaimAuthorityBindingV1] = {}
    bindings["C03.claim.PHYSICAL_COEFFICIENT"] = ClaimAuthorityBindingV1(
        "TERMINALLY_ADJUDICATED", "HISTORICAL_UPHELD__CORRECTED_ROUTE_C_CONFIRMED__MODERN_REOPENED",
        c03_hashes, "C03 physical coefficient under the frozen conventions", common_limitations,
        "2026-09-05T00:00:00Z", "C03_SECTOR_FINDING_ONLY",
    )
    for claim in ("C03.claim.EVANESCENT_COORDINATES", "C03.claim.EVANESCENT_STATE"):
        bindings[claim] = ClaimAuthorityBindingV1(
            "TERMINALLY_ADJUDICATED", "CORRECTED_ROUTE_C_EVALUATED_NONZERO__EXACT_HISTORICAL_NATIVE_IDENTITY_CORPUS_BOUNDED_UNDERDEFINED",
            c03_hashes, "C03 corrected Route-C native quotient only",
            common_limitations + ("Does not establish an exact historical/native evanescent basis-class identity.",),
            "2026-09-05T00:00:00Z", "CORRECTED_ROUTE_C_NATIVE_QUOTIENT_ONLY",
        )
    physical_labels = {
        "RV01": "CORRECTED_SOURCE_DERIVED__PHYSICAL_CHANGED",
        "RV02": "CORRECTED_SOURCE_DERIVED__PHYSICAL_CHANGED",
        "RV03": "WRONG_SOURCE_CHANNEL_NO_SCALAR_MAP",
        "RV04": "CORRECTED_SOURCE_DERIVED__PHYSICAL_CHANGED",
        "RV05": "CORRECTED_SOURCE_DERIVED__PHYSICAL_CHANGED",
        "RV06": "CORRECTED_SOURCE_DERIVED__PHYSICAL_UNCHANGED",
    }
    for record, label in physical_labels.items():
        bindings[f"{record}.claim.PHYSICAL_COEFFICIENT"] = ClaimAuthorityBindingV1(
            "REVIEWED_SUPPORTED", label, rv_hashes, f"{record} source-defined corrected physical value",
            common_limitations + ("Pass-0272 did not adopt a terminal classification for the six-record matrix.",),
            "2026-09-05T00:00:00Z", "CORRECTED_SOURCE_DERIVED_VALUE_ONLY",
        )
        bindings[f"{record}.claim.EVANESCENT_STATE"] = ClaimAuthorityBindingV1(
            "REVIEWED_SUPPORTED", "EVALUATED_ZERO_BY_UNIFORM_SOURCE_BOUND_ABSENCE", rv_hashes,
            f"{record} corrected canonical native-E state",
            common_limitations + ("The historical empty report was unevaluated and is not retroactively validated as zero.",),
            "2026-09-05T00:00:00Z", "CORRECTED_NATIVE_E_STATE_ONLY",
        )
    bindings["RV03.claim.SOURCE_CHANNEL"] = ClaimAuthorityBindingV1(
        "REVIEWED_SUPPORTED", "WRONG_SOURCE_CHANNEL_NO_SCALAR_MAP", rv_hashes,
        "RV03 source-channel disposition", common_limitations,
        "2026-09-05T00:00:00Z", "RV03_SOURCE_CHANNEL_DISPOSITION_ONLY",
    )
    require(set(bindings) == {root.replace(".OUTPUT.", ".claim.") for root in C03_RV_ROOTS}, "C03_RV_AUTHORITY_CLAIM_COVERAGE")
    return ScientificAuthorityBindingV1(profile_hash, bindings, "SCIENTIFIC_REQUALIFICATION_NOT_EARNED")


def census() -> dict[str, Any]:
    material, source_reads = historical_profile.source_material()
    specs = historical_profile.derived_specs()
    roots = sorted(identity for identity, row in specs.items() if row["kind"] == "OUTPUT_ROOT")
    derived = sorted(identity for identity, row in specs.items() if row["kind"] != "OUTPUT_ROOT")
    operations = sorted({row["operation"] for row in specs.values()})
    unsupported = sorted(set(operations) - set(C03_RV_PHYSICS_OPERATIONS))
    per_record = Counter(identity.split(".")[0] for identity in specs)
    challenge_targets = {
        row.challenge_id: (
            len(derived) if row.semantic_target == {"kind": "DERIVED"}
            else len(material) if row.semantic_target == {"operation": "SOURCE_DECODE"}
            else 1 if row.semantic_target.get("node_id") in specs
            else len(roots) if row.semantic_target == {"kind": "OUTPUT"}
            else 0
        ) for row in mandatory_challenge_specs()
    }
    return {
        "schema_id": "C03RVProfileCensusV1",
        "profile_schema": historical_profile.SCHEMA,
        "source_node_count": len(material),
        "source_read_count": len(source_reads),
        "derived_node_count": len(derived),
        "output_root_count": len(roots),
        "output_roots": roots,
        "expected_output_roots": sorted(C03_RV_ROOTS),
        "per_record_spec_count": dict(sorted(per_record.items())),
        "operation_count": len(operations),
        "trusted_source_signature_count": len(SOURCE_SIGNATURES),
        "trusted_derived_signature_count": sum(row["kind"] == "DERIVED" for row in DERIVED_SIGNATURES.values()),
        "trusted_output_signature_count": sum(row["kind"] == "OUTPUT" for row in DERIVED_SIGNATURES.values()),
        "trusted_physics_operation_count": len(C03_RV_PHYSICS_OPERATIONS),
        "historical_physics_operations_requiring_declarative_lowering": unsupported,
        "challenge_target_counts": challenge_targets,
        "challenge_registry": challenge_registry_census(),
        "verification_policy_hash": verification_policy().contract_hash,
        "trusted_package_imports_historical_runner": False,
        "exact_milestone_earned": False,
        "product_v1_release": False,
        "scientific_promotion": False,
        "production_activation": False,
        "blocking_reason": "Exact-profile qualification remains unearned until the cumulative challenge run and two isolated frozen replays complete.",
    }


if __name__ == "__main__":
    from formal.python.toe.generic_runner.verified_calculator.canonical import canonical_json
    print(canonical_json(census()))

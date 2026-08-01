"""Bounded scientific-program governance with immutable OPEN/CLOSE events.

The module deliberately implements only the I-JSON value domain required by
the governance records.  JSON numbers are restricted to exactly representable
IEEE-754 safe integers; quantities requiring decimal precision must use typed
strings.  This keeps the local JCS implementation small, deterministic, and
portable without silently approximating scientific values.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import re
import subprocess
from pathlib import Path
from typing import Any, Iterable

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.loop_control_registry_integrity import (
    atomic_write_registry,
)


REPO_ROOT = find_repo_root(Path(__file__))
REGISTRY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
)
EVENT_ROOT = (
    REPO_ROOT / "formal" / "docs" / "release" / "bounded_program_events"
)
MANIFEST_ROOT = (
    REPO_ROOT / "formal" / "docs" / "release" / "bounded_program_manifests"
)
ATTESTATION_ROOT = (
    REPO_ROOT / "formal" / "docs" / "release" / "bounded_program_attestations"
)

GOVERNANCE_SCHEMA_ID = "TOE_BOUNDED_PROGRAM_GOVERNANCE_v1"
REGISTRY_EXTENSION_KEY = "bounded_program_governance_v1"
PROGRAMS_KEY = "bounded_programs_v1"
ENFORCEMENT_SCHEMA_ID = "TOE_BOUNDED_PROGRAM_GOVERNANCE_ENFORCEMENT_v2"
ENFORCEMENT_EXTENSION_KEY = "bounded_program_governance_enforcement_v2"
FULL_COMMIT_ID_PATTERN = re.compile(r"^[0-9a-f]{40}$")
PROGRAM_MANIFEST_PATHS = {
    "QFT_GR_QUADRATIC_BOUNDED_CLOSEOUT_V0": (
        "formal/docs/release/bounded_program_manifests/"
        "QFT_GR_QUADRATIC_BOUNDED_CLOSEOUT_V0_MANIFEST_v1.json"
    ),
    "TOE_NATIVE_SURROGATE_V0": (
        "formal/docs/release/bounded_program_manifests/"
        "TOE_NATIVE_SURROGATE_V0_MANIFEST_v1.json"
    ),
    "TOE_NATIVE_COHERENCE_ONTOLOGY_AND_REPRESENTATION_V0": (
        "formal/docs/release/bounded_program_manifests/"
        "TOE_NATIVE_COHERENCE_ONTOLOGY_AND_REPRESENTATION_V0_MANIFEST_v1.json"
    ),
    "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_V0": (
        "formal/docs/release/bounded_program_manifests/"
        "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_V0_MANIFEST_v1.json"
    ),
    "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_V0": (
        "formal/docs/release/bounded_program_manifests/"
        "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_V0_MANIFEST_v1.json"
    ),
    "TOE_POSITIVE_NATIVE_GRAVITATIONAL_PRINCIPLE_DERIVATION_V0": (
        "formal/docs/release/bounded_program_manifests/"
        "TOE_POSITIVE_NATIVE_GRAVITATIONAL_PRINCIPLE_DERIVATION_V0_MANIFEST_v1.json"
    ),
    "TOE_CCFT_NATIVE_MATHEMATICAL_CORE_AND_OPERATIONALIZATION_V0": (
        "formal/docs/release/bounded_program_manifests/"
        "TOE_CCFT_NATIVE_MATHEMATICAL_CORE_AND_OPERATIONALIZATION_V0_MANIFEST_v1.json"
    ),
    "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0": (
        "formal/docs/release/bounded_program_manifests/"
        "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0_MANIFEST_v1.json"
    ),
}
LEGACY_ATTESTATION_PATH = (
    "formal/docs/release/bounded_program_attestations/"
    "BOUNDED_PROGRAM_LEGACY_EVENT_COMMIT_ID_ATTESTATION_20260729_v0.json"
)

SET_LIKE_ARRAY_FIELDS = (
    "authorized_inputs",
    "required_outputs",
    "prohibited_claims",
    "dependency_artifact_ids",
    "terminal_outcome_vocabulary",
)
ORDERED_ARRAY_FIELDS = (
    "rewrite_precedence",
    "substitution_order",
    "variable_ordering",
    "dependency_execution_sequence",
    "Jordan_chain_member_order",
)
SCOPE_FIELDS = (
    "semantic_stage_id",
    "normalized_scientific_question",
    *SET_LIKE_ARRAY_FIELDS,
)
NATIVE_HYPOTHESIS_SENTINELS = (
    "NONE_DIRECTLY_CONTROL_MODEL",
    "NONE_GOVERNANCE_ONLY",
)
NATIVE_RELEVANCE_KINDS = (
    "DIRECT_NATIVE_TEST",
    "CONTROL_MODEL_CRITERION",
    "GOVERNANCE_INFRASTRUCTURE",
    "MAINTENANCE_ONLY",
    "ONE_PREREQUISITE_FROM_NATIVE_CALCULATION",
)
TERMINAL_RESULTS = ("PASSED", "BLOCKED", "FAILED")
PROGRAM_STATES = ("UNOPENED", "OPEN", "CLOSED")
MAX_SAFE_INTEGER = (1 << 53) - 1

QUADRATIC_PROGRAM_ID = "QFT_GR_QUADRATIC_BOUNDED_CLOSEOUT_V0"
QUADRATIC_MANDATORY_EXIT = (
    "select_qft_gr_quadratic_toe_role_after_generic_frozen_result_v0"
)
QUADRATIC_STAGE_DEFINITIONS = (
    {
        "semantic_stage_id": "STRICT_HARMONIC_GAUGE_JET_CONTRACT",
        "target": (
            "prepare_qft_gr_quadratic_generic_background_linearization_"
            "gauge_and_jet_contract_v0"
        ),
        "normalized_scientific_question": (
            "Freeze the strict-harmonic generic-background gauge, trace atlas, "
            "finite-jet, regularity, and confluent-rewrite contract."
        ),
        "authorized_inputs": [
            "QFT_GR_QUADRATIC_COMPONENT_EXPANDED_GENERIC_BACKGROUND_LINEARIZATION_RESULT_REVIEW_20260728_v0",
            "QFT_GR_QUADRATIC_AUXILIARY_HARMONIC_REDUCED_SYSTEM_V0",
        ],
        "required_outputs": [
            "strict_harmonic_gauge_contract",
            "tracefree_atlas_and_regular_strata",
            "reduced_variable_regularity_ledger",
            "original_metric_equivalence_regularity_ledger",
            "rewrite_termination_and_confluence_certificate",
            "Minkowski_regression",
        ],
        "prohibited_claims": [
            "generic_all_gauges_result",
            "finite_loss_established",
            "local_well_posedness",
            "quadratic_gravity_native_toe_status",
        ],
        "dependency_artifact_ids": [
            "QFT_GR_QUADRATIC_COMPONENT_EXPANDED_GENERIC_BACKGROUND_LINEARIZATION_RESULT_REVIEW_20260728_v0",
        ],
        "terminal_outcome_vocabulary": [
            "STRICT_HARMONIC_GAUGE_AND_JET_CONTRACT_COMPLETE",
            "STRICT_HARMONIC_GAUGE_AND_JET_CONTRACT_BLOCKED",
        ],
    },
    {
        "semantic_stage_id": "COMPONENT_EXPANDED_LINEARIZATION",
        "target": (
            "derive_qft_gr_quadratic_component_expanded_generic_background_"
            "linearization_v1"
        ),
        "normalized_scientific_question": (
            "Derive the complete strict-harmonic component-expanded generic-"
            "background linearization and independently verify its inventory."
        ),
        "authorized_inputs": [
            "STRICT_HARMONIC_GAUGE_JET_CONTRACT",
            "accepted_64_equation_reduced_system",
            "accepted_Minkowski_128_state_224_entry_control",
        ],
        "required_outputs": [
            "off_shell_component_form",
            "on_shell_component_form",
            "gauge_compatible_component_form",
            "independent_equation_inventory",
            "exact_Minkowski_specialization",
        ],
        "prohibited_claims": [
            "generic_frozen_spectrum",
            "finite_loss_established",
            "local_well_posedness",
        ],
        "dependency_artifact_ids": ["STRICT_HARMONIC_GAUGE_JET_CONTRACT"],
        "terminal_outcome_vocabulary": [
            "GENERIC_BACKGROUND_LINEARIZATION_COMPONENT_COMPLETE",
            "GENERIC_BACKGROUND_LINEARIZATION_COMPONENT_BLOCKED",
        ],
    },
    {
        "semantic_stage_id": "EXACT_FROZEN_COMPANION_OPERATOR",
        "target": "derive_qft_gr_quadratic_exact_generic_frozen_companion_operator_v1",
        "normalized_scientific_question": (
            "Construct the exact frozen first-order companion operator including "
            "principal, weighted-principal, and subprincipal entries."
        ),
        "authorized_inputs": ["COMPONENT_EXPANDED_LINEARIZATION"],
        "required_outputs": [
            "exact_frozen_companion_matrix",
            "background_stratum_contract",
            "chart_transition_certificates",
            "Minkowski_operator_regression",
        ],
        "prohibited_claims": [
            "finite_loss_established",
            "constraint_quotient_completed",
            "local_well_posedness",
        ],
        "dependency_artifact_ids": ["COMPONENT_EXPANDED_LINEARIZATION"],
        "terminal_outcome_vocabulary": [
            "GENERIC_FROZEN_COMPANION_OPERATOR_EXACTLY_DERIVED",
            "GENERIC_BACKGROUND_OPERATOR_NOT_CLOSED",
        ],
    },
    {
        "semantic_stage_id": "CONSTRAINT_TANGENT_AND_PHYSICAL_QUOTIENT",
        "target": (
            "derive_qft_gr_quadratic_constraint_tangent_and_physical_"
            "quotient_v0"
        ),
        "normalized_scientific_question": (
            "Construct the exact constraint tangent projector, residual-gauge "
            "quotient, and locally uniform quotient norm."
        ),
        "authorized_inputs": [
            "EXACT_FROZEN_COMPANION_OPERATOR",
            "accepted_constraint_propagation_system",
        ],
        "required_outputs": [
            "independent_constraint_row_basis",
            "row_space_equivalence_witnesses",
            "constraint_tangent_projector",
            "strict_harmonic_residual_gauge_Cauchy_map",
            "physical_quotient_norm",
            "complement_independence_certificate",
            "zero_frequency_control",
        ],
        "prohibited_claims": [
            "positive_physical_energy",
            "finite_loss_established",
            "local_well_posedness",
        ],
        "dependency_artifact_ids": ["EXACT_FROZEN_COMPANION_OPERATOR"],
        "terminal_outcome_vocabulary": [
            "CONSTRAINT_TANGENT_AND_PHYSICAL_QUOTIENT_COMPLETE",
            "CONSTRAINT_TANGENT_AND_PHYSICAL_QUOTIENT_BLOCKED",
        ],
    },
    {
        "semantic_stage_id": "SUBPRINCIPAL_PROPAGATOR_GROWTH",
        "target": (
            "compute_qft_gr_quadratic_subprincipal_weighted_propagator_"
            "growth_v0"
        ),
        "normalized_scientific_question": (
            "Determine the exact locally uniform weighted propagator growth on "
            "unrestricted, constraint-tangent, and physical-quotient sectors."
        ),
        "authorized_inputs": [
            "EXACT_FROZEN_COMPANION_OPERATOR",
            "CONSTRAINT_TANGENT_AND_PHYSICAL_QUOTIENT",
        ],
        "required_outputs": [
            "weighted_propagator_bounds",
            "nonnormal_growth_analysis",
            "directional_uniformity_certificate",
            "saturating_lower_bound_data",
            "sector_loss_classification",
        ],
        "prohibited_claims": [
            "variable_coefficient_estimate",
            "nonlinear_local_well_posedness",
            "quadratic_gravity_native_toe_status",
        ],
        "dependency_artifact_ids": [
            "CONSTRAINT_TANGENT_AND_PHYSICAL_QUOTIENT",
            "EXACT_FROZEN_COMPANION_OPERATOR",
        ],
        "terminal_outcome_vocabulary": [
            "FINITE_LOSS_ESTABLISHED_ON_REGULAR_STRATA",
            "FINITE_LOSS_REFUTED",
            "FINITE_LOSS_ONLY_ON_SPECIAL_BACKGROUNDS",
            "UNRESOLVED_AFTER_BOUNDED_ATTEMPT",
        ],
    },
)

NATIVE_PROGRAM_AUTHORIZATION_TARGET = (
    "authorize_toe_native_surrogate_v0_bounded_program"
)
NATIVE_PROGRAM_ID = "TOE_NATIVE_SURROGATE_V0"
COHERENCE_ONTOLOGY_PROGRAM_ID = (
    "TOE_NATIVE_COHERENCE_ONTOLOGY_AND_REPRESENTATION_V0"
)
COHERENCE_ONTOLOGY_PREPARATION_TARGET = (
    "prepare_toe_native_coherence_ontology_and_representation_bounded_program_v0"
)
CENSUS_PROGRAM_ID = (
    "TOE_REPOSITORY_WIDE_NATIVE_HYPOTHESIS_EVIDENCE_CENSUS_V0"
)
CENSUS_PREPARATION_TARGET = (
    "prepare_toe_repository_wide_native_hypothesis_evidence_census_"
    "bounded_program_v0"
)
GRAVITATIONAL_SURVEY_PROGRAM_ID = (
    "TOE_NATIVE_GRAVITATIONAL_REQUIREMENTS_AND_CANDIDATE_ACTION_FAMILY_SURVEY_V0"
)
GRAVITATIONAL_SURVEY_PREPARATION_TARGET = (
    "prepare_toe_native_gravitational_requirements_and_candidate_action_"
    "family_survey_bounded_program_v0"
)
POSITIVE_GRAVITATIONAL_PRINCIPLE_PROGRAM_ID = (
    "TOE_POSITIVE_NATIVE_GRAVITATIONAL_PRINCIPLE_DERIVATION_V0"
)
POSITIVE_GRAVITATIONAL_PRINCIPLE_PREPARATION_TARGET = (
    "prepare_toe_positive_native_gravitational_principle_derivation_"
    "bounded_program_v0"
)
CCFT_CORE_PROGRAM_ID = (
    "TOE_CCFT_NATIVE_MATHEMATICAL_CORE_AND_OPERATIONALIZATION_V0"
)
CCFT_CORE_PREPARATION_TARGET = (
    "prepare_toe_ccft_native_mathematical_core_and_operationalization_"
    "bounded_program_v0"
)
TARGETED_CCFT_RECOVERY_PROGRAM_ID = (
    "TOE_TARGETED_CCFT_CLOSURE_EVIDENCE_RECOVERY_V0"
)
TARGETED_CCFT_RECOVERY_PREPARATION_TARGET = (
    "prepare_toe_targeted_ccft_closure_evidence_recovery_bounded_program_v0"
)
NATIVE_MANDATORY_EXIT = "close_toe_native_surrogate_v0_after_bounded_result_v0"
NATIVE_STAGE_DEFINITIONS = (
    {
        "semantic_stage_id": "COHERENCE_REPRESENTATION",
        "target": "select_toe_native_coherence_representation_v0",
        "normalized_scientific_question": (
            "Determine whether one real scalar is an admissible bounded surrogate "
            "or a derived representation of one named preserved coherence feature, "
            "and independently adjudicate the phi and chi Z2 symmetries."
        ),
        "authorized_inputs": [
            "preserved_CCFT_and_ToE_coherence_claims",
            "preserved_real_scalar_test_matter_sector",
        ],
        "required_outputs": [
            "coherence_feature_crosswalk",
            "chi_value_sign_zero_gradient_meaning",
            "chi_Z2_meaning_and_status",
            "phi_Z2_status",
            "representation_or_surrogate_classification",
        ],
        "prohibited_claims": [
            "CCFT_validation",
            "coherence_is_fundamentally_scalar",
            "native_action_selection",
            "quantum_gravity",
            "full_ToE_unification",
        ],
        "dependency_artifact_ids": [
            "QFT_GR_QUADRATIC_TOE_ROLE_AFTER_GENERIC_FROZEN_RESULT_REVIEW_20260729_v0",
        ],
        "terminal_outcome_vocabulary": [
            "REAL_SCALAR_COHERENCE_SURROGATE_ACCEPTED_FOR_BOUNDED_V0",
            "REAL_SCALAR_COHERENCE_REPRESENTATION_DERIVED",
            "BLOCKED_COHERENCE_REPRESENTATION_INADEQUATE",
            "BLOCKED_CCFT_TO_CONTINUUM_MAP_UNRESOLVED",
        ],
    },
    {
        "semantic_stage_id": "MINIMAL_ACTION_SELECTION",
        "target": "select_toe_native_surrogate_minimal_action_v0",
        "normalized_scientific_question": (
            "Select or block the bounded classical Einstein-two-scalar action "
            "under the closed operator basis, independent Z2 gates, convention "
            "audit, and native-interaction rationale."
        ),
        "authorized_inputs": ["COHERENCE_REPRESENTATION"],
        "required_outputs": [
            "bounded_operator_basis",
            "independent_Z2_authorization",
            "native_interaction_rationale",
            "SI_and_natural_unit_convention_audit",
            "minimal_action",
        ],
        "prohibited_claims": [
            "quantum_or_renormalization_closure",
            "unique_ToE_interaction",
            "QFT_GR_closure",
            "automatic_action_enlargement",
        ],
        "dependency_artifact_ids": ["COHERENCE_REPRESENTATION"],
        "terminal_outcome_vocabulary": [
            "MINIMAL_TWO_SCALAR_NATIVE_SURROGATE_ACTION_SELECTED",
            "BLOCKED_PORTAL_OPERATOR_BASIS_NOT_CLOSED",
            "BLOCKED_NATIVE_INTERACTION_UNJUSTIFIED",
        ],
    },
    {
        "semantic_stage_id": "INTERNAL_VIABILITY",
        "target": "derive_toe_native_surrogate_internal_viability_v0",
        "normalized_scientific_question": (
            "Derive the classical field equations, constraints, fluctuation "
            "operator, degrees of freedom, characteristics, and vacuum stability "
            "of the selected bounded native-surrogate action."
        ),
        "authorized_inputs": ["MINIMAL_ACTION_SELECTION"],
        "required_outputs": [
            "field_equations",
            "constraint_inventory",
            "vacuum_classification",
            "fluctuation_operator",
            "degree_of_freedom_count",
            "characteristic_and_stability_result",
        ],
        "prohibited_claims": [
            "empirical_validation",
            "quantum_stability",
            "renormalization_closure",
            "unique_ToE_discriminator",
        ],
        "dependency_artifact_ids": ["MINIMAL_ACTION_SELECTION"],
        "terminal_outcome_vocabulary": [
            "MATHEMATICALLY_VIABLE_NATIVE_SURROGATE_SANDBOX",
            "NATIVE_SURROGATE_INTERNAL_VIABILITY_BLOCKED",
        ],
    },
    {
        "semantic_stage_id": "SEAM_AUDIT",
        "target": "derive_toe_native_surrogate_classical_seam_audit_v0",
        "normalized_scientific_question": (
            "Audit the classical coherence-surrogate-to-gravity, coherence-"
            "surrogate-to-matter, and composite seams with partition-independent "
            "total stress-energy conservation."
        ),
        "authorized_inputs": ["INTERNAL_VIABILITY"],
        "required_outputs": [
            "inverse_metric_stress_variation",
            "total_stress_tensor",
            "partition_independent_conservation_law",
            "coherence_to_gravity_seam_ledger",
            "coherence_to_matter_seam_ledger",
            "composite_classical_seam_ledger",
        ],
        "prohibited_claims": [
            "QFT_GR_closure",
            "renormalized_quantum_stress_energy",
            "quantum_gravity",
            "empirical_validation",
        ],
        "dependency_artifact_ids": ["INTERNAL_VIABILITY"],
        "terminal_outcome_vocabulary": [
            "CLASSICAL_NATIVE_SURROGATE_SEAMS_AUDITED",
            "CLASSICAL_NATIVE_SURROGATE_SEAM_AUDIT_BLOCKED",
        ],
    },
    {
        "semantic_stage_id": "OBSERVABLE_AND_UNIQUENESS",
        "target": "derive_toe_native_surrogate_observable_and_uniqueness_v0",
        "normalized_scientific_question": (
            "Derive or block an endogenous nonzero coherence-surrogate state, "
            "observable map, identifiable quantitative prediction, and "
            "inequivalence to a fitted generic Einstein-two-scalar portal model."
        ),
        "authorized_inputs": ["INTERNAL_VIABILITY", "SEAM_AUDIT"],
        "required_outputs": [
            "endogenous_nonzero_chi_state",
            "observable_map",
            "parameter_identifiability_audit",
            "generic_portal_equivalence_audit",
            "quantitative_residual_and_sensitivity",
            "falsification_boundary",
        ],
        "prohibited_claims": [
            "unique_discriminator_without_all_eight_conditions",
            "externally_inserted_coherence_state",
            "full_ToE_unification",
            "CCFT_validation",
        ],
        "dependency_artifact_ids": ["INTERNAL_VIABILITY", "SEAM_AUDIT"],
        "terminal_outcome_vocabulary": [
            "UNIQUE_TOE_DISCRIMINATOR_V0_ESTABLISHED",
            "NO_UNIQUE_TOE_DISCRIMINATOR_V0",
            "BLOCKED_COHERENCE_STATE_NOT_ENDOGENOUS",
        ],
    },
)

NATIVE_PROGRAM_TEMPLATE = {
    "program_id": NATIVE_PROGRAM_ID,
    "authorized_stage_count": 5,
    "repair_attempt_count": 0,
    "no_subsidiary_scientific_targets": True,
    "status": "TEMPLATE_NOT_AUTHORIZED",
    "semantic_stage_ids": [
        "COHERENCE_REPRESENTATION",
        "MINIMAL_ACTION_SELECTION",
        "INTERNAL_VIABILITY",
        "SEAM_AUDIT",
        "OBSERVABLE_AND_UNIQUENESS",
    ],
}


class BoundedProgramError(ValueError):
    pass


def _strict_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise BoundedProgramError(f"duplicate JSON property name: {key}")
        result[key] = value
    return result


def _reject_constant(value: str) -> None:
    raise BoundedProgramError(f"non-I-JSON numeric value: {value}")


def strict_json_loads(text: str) -> Any:
    return json.loads(
        text,
        object_pairs_hook=_strict_object,
        parse_constant=_reject_constant,
    )


def strict_json_load(path: Path) -> Any:
    return strict_json_loads(path.read_text(encoding="utf-8"))


def _validate_string(value: str, *, path: str) -> None:
    try:
        value.encode("utf-8", errors="strict")
        value.encode("utf-16-be", errors="strict")
    except UnicodeError as error:
        raise BoundedProgramError(f"invalid Unicode at {path}") from error


def validate_ijson(value: Any, *, path: str = "$") -> None:
    if value is None or isinstance(value, bool):
        return
    if isinstance(value, str):
        _validate_string(value, path=path)
        return
    if isinstance(value, int):
        if abs(value) > MAX_SAFE_INTEGER:
            raise BoundedProgramError(
                f"integer outside exactly representable I-JSON range at {path}"
            )
        return
    if isinstance(value, float):
        if not math.isfinite(value):
            raise BoundedProgramError(f"non-finite number at {path}")
        raise BoundedProgramError(
            f"floating JSON numbers are prohibited in governance records at {path}; "
            "use a typed decimal string"
        )
    if isinstance(value, list):
        for index, item in enumerate(value):
            validate_ijson(item, path=f"{path}[{index}]")
        return
    if isinstance(value, dict):
        for key, item in value.items():
            if not isinstance(key, str):
                raise BoundedProgramError(f"non-string object key at {path}")
            _validate_string(key, path=f"{path}.<key>")
            validate_ijson(item, path=f"{path}.{key}")
        return
    raise BoundedProgramError(f"unsupported I-JSON value at {path}: {type(value)!r}")


def _jcs_string(value: str) -> bytes:
    _validate_string(value, path="$")
    return json.dumps(value, ensure_ascii=False, separators=(",", ":")).encode("utf-8")


def _utf16_sort_key(value: str) -> bytes:
    return value.encode("utf-16-be", errors="strict")


def jcs_bytes(value: Any) -> bytes:
    """Return RFC-8785-compatible bytes for the bounded I-JSON subset."""
    validate_ijson(value)
    if value is None:
        return b"null"
    if value is True:
        return b"true"
    if value is False:
        return b"false"
    if isinstance(value, int):
        return str(value).encode("ascii")
    if isinstance(value, str):
        return _jcs_string(value)
    if isinstance(value, list):
        return b"[" + b",".join(jcs_bytes(item) for item in value) + b"]"
    if isinstance(value, dict):
        rows = []
        for key in sorted(value, key=_utf16_sort_key):
            rows.append(_jcs_string(key) + b":" + jcs_bytes(value[key]))
        return b"{" + b",".join(rows) + b"}"
    raise AssertionError("validate_ijson accepted an unsupported value")


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_path(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def normalize_scope(scope: dict[str, Any]) -> dict[str, Any]:
    if set(scope) != set(SCOPE_FIELDS):
        missing = sorted(set(SCOPE_FIELDS) - set(scope))
        extra = sorted(set(scope) - set(SCOPE_FIELDS))
        raise BoundedProgramError(
            f"scope fields do not match contract; missing={missing}, extra={extra}"
        )

    normalized: dict[str, Any] = {}
    for field in SCOPE_FIELDS:
        value = scope[field]
        if field not in SET_LIKE_ARRAY_FIELDS:
            normalized[field] = value
            continue
        if not isinstance(value, list):
            raise BoundedProgramError(f"{field} must be a set-like array")
        keyed: list[tuple[bytes, Any]] = [(jcs_bytes(item), item) for item in value]
        canonical_items = [item[0] for item in keyed]
        if len(canonical_items) != len(set(canonical_items)):
            raise BoundedProgramError(f"duplicate semantic element in {field}")
        normalized[field] = [item for _, item in sorted(keyed, key=lambda row: row[0])]

    validate_ijson(normalized)
    return normalized


def scope_hash(scope: dict[str, Any]) -> str:
    return sha256_bytes(jcs_bytes(normalize_scope(scope)))


def _stage_scope(stage: dict[str, Any]) -> dict[str, Any]:
    return {field: stage[field] for field in SCOPE_FIELDS}


def _event_hash(event: dict[str, Any]) -> str:
    payload = {key: value for key, value in event.items() if key != "event_hash"}
    return sha256_bytes(jcs_bytes(payload))


def _pretty_json_bytes(value: Any) -> bytes:
    validate_ijson(value)
    return (
        json.dumps(value, indent=2, ensure_ascii=False, sort_keys=True) + "\n"
    ).encode("utf-8")


def _registry_json_bytes(value: Any) -> bytes:
    """Preserve the legacy registry's broader numeric domain during migration."""
    return (
        json.dumps(value, indent=2, ensure_ascii=True) + "\n"
    ).encode("utf-8")


def _git_output(*args: str, cwd: Path = REPO_ROOT) -> str:
    return subprocess.run(
        ["git", *args],
        cwd=cwd,
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()


def _hashed_payload(value: dict[str, Any], hash_field: str) -> str:
    payload = {key: item for key, item in value.items() if key != hash_field}
    return sha256_bytes(jcs_bytes(payload))


def _load_authoritative_manifest(
    program_id: str, *, repo_root: Path = REPO_ROOT
) -> tuple[str, dict[str, Any]]:
    try:
        relative_path = PROGRAM_MANIFEST_PATHS[program_id]
    except KeyError as error:
        raise BoundedProgramError(
            f"bounded program is absent from immutable manifest index: {program_id}"
        ) from error
    path = repo_root / relative_path
    if not path.is_file():
        raise BoundedProgramError(
            f"missing immutable program manifest: {relative_path}"
        )
    manifest = strict_json_load(path)
    if manifest.get("schema_id") != "toe.bounded_program.immutable_manifest.v1":
        raise BoundedProgramError(f"invalid program manifest schema: {program_id}")
    if manifest.get("program_id") != program_id:
        raise BoundedProgramError(f"program manifest identity mismatch: {program_id}")
    if manifest.get("manifest_hash") != _hashed_payload(
        manifest, "manifest_hash"
    ):
        raise BoundedProgramError(f"program manifest hash mismatch: {program_id}")
    if manifest.get("status") != "IMMUTABLE_AUTHORITATIVE_PROGRAM_MANIFEST":
        raise BoundedProgramError(f"program manifest is not authoritative: {program_id}")
    manifest_mode = manifest.get("manifest_mode", "HISTORICAL_CUSTODY")
    if manifest_mode not in {"HISTORICAL_CUSTODY", "PROSPECTIVE_STATIC"}:
        raise BoundedProgramError(f"invalid program manifest mode: {program_id}")
    return relative_path, manifest


def _load_legacy_attestation(
    *, repo_root: Path = REPO_ROOT
) -> tuple[str, dict[str, Any]]:
    path = repo_root / LEGACY_ATTESTATION_PATH
    if not path.is_file():
        raise BoundedProgramError(
            f"missing legacy event commit-ID attestation: {LEGACY_ATTESTATION_PATH}"
        )
    attestation = strict_json_load(path)
    if attestation.get("schema_id") != (
        "toe.bounded_program.legacy_event_commit_id_attestation.v0"
    ):
        raise BoundedProgramError("invalid legacy event attestation schema")
    if attestation.get("attestation_hash") != _hashed_payload(
        attestation, "attestation_hash"
    ):
        raise BoundedProgramError("legacy event attestation hash mismatch")
    if attestation.get("status") != (
        "IMMUTABLE_LEGACY_IDENTIFIER_CUSTODY_ATTESTATION"
    ):
        raise BoundedProgramError("legacy event attestation is not authoritative")
    return LEGACY_ATTESTATION_PATH, attestation


def _manifest_stage(
    manifest: dict[str, Any], attempt_number: int
) -> dict[str, Any]:
    stages = manifest.get("stages")
    if not isinstance(stages, list):
        raise BoundedProgramError("manifest stages must be an array")
    matches = [
        stage
        for stage in stages
        if stage.get("stage_number") == attempt_number
    ]
    if len(matches) != 1:
        raise BoundedProgramError(
            f"manifest has no unique stage number {attempt_number}"
        )
    return matches[0]


def _manifest_reference(
    relative_path: str, payload: dict[str, Any]
) -> dict[str, Any]:
    return {
        "path": relative_path,
        "sha256": sha256_path(REPO_ROOT / relative_path),
        "manifest_hash": payload["manifest_hash"],
    }


def enforcement_contract(*, repo_root: Path = REPO_ROOT) -> dict[str, Any]:
    manifests: dict[str, Any] = {}
    for program_id in PROGRAM_MANIFEST_PATHS:
        relative_path, manifest = _load_authoritative_manifest(
            program_id, repo_root=repo_root
        )
        manifests[program_id] = {
            "path": relative_path,
            "sha256": sha256_path(repo_root / relative_path),
            "manifest_hash": manifest["manifest_hash"],
        }
    attestation_path, attestation = _load_legacy_attestation(repo_root=repo_root)
    return {
        "schema_id": ENFORCEMENT_SCHEMA_ID,
        "schema_version": 2,
        "status": "ENFORCEMENT_COMPLETE_REGISTRY_IS_DERIVED_PROJECTION",
        "authoritative_source": "IMMUTABLE_PROGRAM_MANIFESTS_AND_EVENT_CHAIN",
        "program_manifests": manifests,
        "legacy_event_commit_id_attestation": {
            "path": attestation_path,
            "sha256": sha256_path(repo_root / attestation_path),
            "attestation_hash": attestation["attestation_hash"],
        },
        "future_event_commit_id_policy": (
            "lowercase full 40-character commit IDs required"
        ),
        "registry_projection_policy": (
            "reconstruct event-derived fields and require exact registry parity"
        ),
        "git_history_policy": (
            "verify introduction commits, exact parents, registry snapshots, "
            "artifact chronology, and exact lifecycle commit envelopes"
        ),
    }


def install_enforcement_completion(registry: dict[str, Any]) -> dict[str, Any]:
    if ENFORCEMENT_EXTENSION_KEY in registry:
        raise BoundedProgramError("governance enforcement completion already installed")
    migrated = json.loads(json.dumps(registry))
    migrated["schema_version"] = 2
    envelope = dict(migrated.get("registry_envelope_v0", {}))
    envelope["schema_version"] = 2
    migrated["registry_envelope_v0"] = envelope
    migrated[ENFORCEMENT_EXTENSION_KEY] = enforcement_contract()
    for program_id, program in migrated[PROGRAMS_KEY].items():
        relative_path, manifest = _load_authoritative_manifest(program_id)
        program["program_manifest"] = _manifest_reference(relative_path, manifest)
    return migrated


def git_blob_oid(path: Path) -> str:
    return _git_output("hash-object", str(path))


def _quadratic_program_record() -> dict[str, Any]:
    stages = []
    for index, definition in enumerate(QUADRATIC_STAGE_DEFINITIONS, start=1):
        stage = dict(definition)
        stage["stage_number"] = index
        stage["scope_hash"] = scope_hash(_stage_scope(stage))
        stages.append(stage)
    return {
        "program_id": QUADRATIC_PROGRAM_ID,
        "authorized_stage_count": 5,
        "current_stage_number": 0,
        "attempted_stage_ids": [],
        "blocked_stage_id": None,
        "repair_attempt_count": 0,
        "mandatory_exit_target": QUADRATIC_MANDATORY_EXIT,
        "no_subsidiary_scientific_targets": True,
        "event_chain_tip_hash": None,
        "last_closed_attempt_number": 0,
        "state": "UNOPENED",
        "open_attempt_number": None,
        "events": [],
        "stage_definitions": stages,
    }


def _native_program_record() -> dict[str, Any]:
    stages = []
    for index, definition in enumerate(NATIVE_STAGE_DEFINITIONS, start=1):
        stage = dict(definition)
        stage["stage_number"] = index
        stage["scope_hash"] = scope_hash(_stage_scope(stage))
        stages.append(stage)
    return {
        "program_id": NATIVE_PROGRAM_ID,
        "authorized_stage_count": 5,
        "current_stage_number": 0,
        "attempted_stage_ids": [],
        "blocked_stage_id": None,
        "repair_attempt_count": 0,
        "mandatory_exit_target": NATIVE_MANDATORY_EXIT,
        "no_subsidiary_scientific_targets": True,
        "event_chain_tip_hash": None,
        "last_closed_attempt_number": 0,
        "state": "UNOPENED",
        "open_attempt_number": None,
        "events": [],
        "stage_definitions": stages,
        "claim_boundary": {
            "model_class": "CLASSICAL_LOCAL_CONTINUUM_NATIVE_SURROGATE",
            "seam_class": [
                "CLASSICAL_FIELD_TO_GRAVITY",
                "CLASSICAL_COHERENCE_SURROGATE_TO_MATTER",
            ],
            "not_claimed": [
                "CCFT_DERIVATION",
                "FULL_TOE_UNIFICATION",
                "MASTER_ACTION_DERIVATION",
                "QFT_GR_CLOSURE",
                "QUANTUM_GRAVITY",
                "RENORMALIZED_QUANTUM_STRESS_ENERGY",
                "SPACETIME_EMERGENCE",
                "STANDARD_MODEL_UNIFICATION",
            ],
        },
    }


def _prospective_program_record(
    relative_path: str, manifest: dict[str, Any]
) -> dict[str, Any]:
    if manifest.get("manifest_mode") != "PROSPECTIVE_STATIC":
        raise BoundedProgramError("prospective program requires a static manifest")
    return {
        "program_id": manifest["program_id"],
        "authorized_stage_count": manifest["authorized_stage_count"],
        "current_stage_number": 0,
        "attempted_stage_ids": [],
        "blocked_stage_id": None,
        "repair_attempt_count": 0,
        "mandatory_exit_target": manifest["mandatory_exit"]["target"],
        "no_subsidiary_scientific_targets": True,
        "event_chain_tip_hash": None,
        "last_closed_attempt_number": 0,
        "state": "UNOPENED",
        "open_attempt_number": None,
        "events": [],
        "stage_definitions": _expected_stage_projection(manifest),
        "program_manifest": _manifest_reference(relative_path, manifest),
        "native_hypothesis_tested": manifest["native_hypothesis_tested"],
        "native_relevance": manifest["native_relevance"],
        "prerequisite_scope": "AUTHORIZED_PROGRAM_ONLY",
        "program_terminal_outcomes": manifest["program_terminal_outcomes"],
        "program_terminal_status": "INSTALLED_UNOPENED",
    }


def install_coherence_ontology_program(registry: dict[str, Any]) -> dict[str, Any]:
    projection = registry.get("current_projection_v0")
    if not isinstance(projection, dict):
        raise BoundedProgramError("canonical current projection is missing")
    if projection.get("current_target") != COHERENCE_ONTOLOGY_PREPARATION_TARGET:
        raise BoundedProgramError(
            "coherence ontology program preparation target is not authoritative"
        )
    programs = registry.get(PROGRAMS_KEY)
    if not isinstance(programs, dict):
        raise BoundedProgramError("bounded-program registry extension is missing")
    if COHERENCE_ONTOLOGY_PROGRAM_ID in programs:
        raise BoundedProgramError("coherence ontology program is already installed")
    if ENFORCEMENT_EXTENSION_KEY not in registry:
        raise BoundedProgramError("bounded-program enforcement is not installed")
    relative_path, manifest = _load_authoritative_manifest(
        COHERENCE_ONTOLOGY_PROGRAM_ID
    )
    migrated = json.loads(json.dumps(registry))
    migrated[PROGRAMS_KEY][COHERENCE_ONTOLOGY_PROGRAM_ID] = (
        _prospective_program_record(relative_path, manifest)
    )
    migrated[ENFORCEMENT_EXTENSION_KEY] = enforcement_contract()
    return migrated


def install_repository_wide_census_program(
    registry: dict[str, Any],
) -> dict[str, Any]:
    projection = registry.get("current_projection_v0")
    if not isinstance(projection, dict):
        raise BoundedProgramError("canonical current projection is missing")
    if projection.get("current_target") != CENSUS_PREPARATION_TARGET:
        raise BoundedProgramError(
            "repository-wide census program preparation target is not authoritative"
        )
    programs = registry.get(PROGRAMS_KEY)
    if not isinstance(programs, dict):
        raise BoundedProgramError("bounded-program registry extension is missing")
    if CENSUS_PROGRAM_ID in programs:
        raise BoundedProgramError(
            "repository-wide census program is already installed"
        )
    if ENFORCEMENT_EXTENSION_KEY not in registry:
        raise BoundedProgramError("bounded-program enforcement is not installed")
    relative_path, manifest = _load_authoritative_manifest(CENSUS_PROGRAM_ID)
    migrated = json.loads(json.dumps(registry))
    migrated[PROGRAMS_KEY][CENSUS_PROGRAM_ID] = _prospective_program_record(
        relative_path, manifest
    )
    migrated[REGISTRY_EXTENSION_KEY] = governance_contract()
    migrated[ENFORCEMENT_EXTENSION_KEY] = enforcement_contract()
    return migrated


def install_gravitational_survey_program(
    registry: dict[str, Any],
) -> dict[str, Any]:
    projection = registry.get("current_projection_v0")
    if not isinstance(projection, dict):
        raise BoundedProgramError("canonical current projection is missing")
    if projection.get("current_target") != GRAVITATIONAL_SURVEY_PREPARATION_TARGET:
        raise BoundedProgramError(
            "gravitational survey program preparation target is not authoritative"
        )
    programs = registry.get(PROGRAMS_KEY)
    if not isinstance(programs, dict):
        raise BoundedProgramError("bounded-program registry extension is missing")
    if GRAVITATIONAL_SURVEY_PROGRAM_ID in programs:
        raise BoundedProgramError(
            "gravitational survey program is already installed"
        )
    if ENFORCEMENT_EXTENSION_KEY not in registry:
        raise BoundedProgramError("bounded-program enforcement is not installed")
    relative_path, manifest = _load_authoritative_manifest(
        GRAVITATIONAL_SURVEY_PROGRAM_ID
    )
    migrated = json.loads(json.dumps(registry))
    migrated[PROGRAMS_KEY][GRAVITATIONAL_SURVEY_PROGRAM_ID] = (
        _prospective_program_record(relative_path, manifest)
    )
    migrated[REGISTRY_EXTENSION_KEY] = governance_contract()
    migrated[ENFORCEMENT_EXTENSION_KEY] = enforcement_contract()
    return migrated


def install_positive_gravitational_principle_program(
    registry: dict[str, Any],
) -> dict[str, Any]:
    projection = registry.get("current_projection_v0")
    if not isinstance(projection, dict):
        raise BoundedProgramError("canonical current projection is missing")
    if (
        projection.get("current_target")
        != POSITIVE_GRAVITATIONAL_PRINCIPLE_PREPARATION_TARGET
    ):
        raise BoundedProgramError(
            "positive gravitational-principle program preparation target "
            "is not authoritative"
        )
    programs = registry.get(PROGRAMS_KEY)
    if not isinstance(programs, dict):
        raise BoundedProgramError("bounded-program registry extension is missing")
    if POSITIVE_GRAVITATIONAL_PRINCIPLE_PROGRAM_ID in programs:
        raise BoundedProgramError(
            "positive gravitational-principle program is already installed"
        )
    if ENFORCEMENT_EXTENSION_KEY not in registry:
        raise BoundedProgramError("bounded-program enforcement is not installed")
    relative_path, manifest = _load_authoritative_manifest(
        POSITIVE_GRAVITATIONAL_PRINCIPLE_PROGRAM_ID
    )
    migrated = json.loads(json.dumps(registry))
    migrated[PROGRAMS_KEY][POSITIVE_GRAVITATIONAL_PRINCIPLE_PROGRAM_ID] = (
        _prospective_program_record(relative_path, manifest)
    )
    migrated[REGISTRY_EXTENSION_KEY] = governance_contract()
    migrated[ENFORCEMENT_EXTENSION_KEY] = enforcement_contract()
    return migrated


def install_ccft_core_program(registry: dict[str, Any]) -> dict[str, Any]:
    projection = registry.get("current_projection_v0")
    if not isinstance(projection, dict):
        raise BoundedProgramError("canonical current projection is missing")
    if projection.get("current_target") != CCFT_CORE_PREPARATION_TARGET:
        raise BoundedProgramError(
            "CCFT core program preparation target is not authoritative"
        )
    programs = registry.get(PROGRAMS_KEY)
    if not isinstance(programs, dict):
        raise BoundedProgramError("bounded-program registry extension is missing")
    if CCFT_CORE_PROGRAM_ID in programs:
        raise BoundedProgramError("CCFT core program is already installed")
    if ENFORCEMENT_EXTENSION_KEY not in registry:
        raise BoundedProgramError("bounded-program enforcement is not installed")
    relative_path, manifest = _load_authoritative_manifest(CCFT_CORE_PROGRAM_ID)
    migrated = json.loads(json.dumps(registry))
    migrated[PROGRAMS_KEY][CCFT_CORE_PROGRAM_ID] = _prospective_program_record(
        relative_path, manifest
    )
    migrated[REGISTRY_EXTENSION_KEY] = governance_contract()
    migrated[ENFORCEMENT_EXTENSION_KEY] = enforcement_contract()
    return migrated


def install_targeted_ccft_recovery_program(
    registry: dict[str, Any],
) -> dict[str, Any]:
    projection = registry.get("current_projection_v0")
    if not isinstance(projection, dict):
        raise BoundedProgramError("canonical current projection is missing")
    if (
        projection.get("current_target")
        != TARGETED_CCFT_RECOVERY_PREPARATION_TARGET
    ):
        raise BoundedProgramError(
            "targeted CCFT recovery preparation target is not authoritative"
        )
    programs = registry.get(PROGRAMS_KEY)
    if not isinstance(programs, dict):
        raise BoundedProgramError("bounded-program registry extension is missing")
    if TARGETED_CCFT_RECOVERY_PROGRAM_ID in programs:
        raise BoundedProgramError(
            "targeted CCFT recovery program is already installed"
        )
    if ENFORCEMENT_EXTENSION_KEY not in registry:
        raise BoundedProgramError("bounded-program enforcement is not installed")
    relative_path, manifest = _load_authoritative_manifest(
        TARGETED_CCFT_RECOVERY_PROGRAM_ID
    )
    migrated = json.loads(json.dumps(registry))
    migrated[PROGRAMS_KEY][TARGETED_CCFT_RECOVERY_PROGRAM_ID] = (
        _prospective_program_record(relative_path, manifest)
    )
    migrated[REGISTRY_EXTENSION_KEY] = governance_contract()
    migrated[ENFORCEMENT_EXTENSION_KEY] = enforcement_contract()
    return migrated


def governance_contract() -> dict[str, Any]:
    return {
        "schema_id": GOVERNANCE_SCHEMA_ID,
        "schema_version": 1,
        "status": "INSTALLED_GOVERNANCE_ONLY_NO_SCIENTIFIC_ROTATION",
        "set_like_array_fields": list(SET_LIKE_ARRAY_FIELDS),
        "ordered_array_fields": list(ORDERED_ARRAY_FIELDS),
        "native_hypothesis_sentinels": list(NATIVE_HYPOTHESIS_SENTINELS),
        "native_relevance_kinds": list(NATIVE_RELEVANCE_KINDS),
        "prerequisite_scope": "AUTHORIZED_PROGRAM_ONLY",
        "event_state_machine": [
            "UNOPENED",
            "OPEN",
            "PASSED_OR_BLOCKED_OR_FAILED",
            "CLOSED",
        ],
        "event_hash_algorithm": "SHA-256 over bounded I-JSON JCS bytes",
        "scope_hash_algorithm": (
            "project set normalization followed by RFC 8785 JCS and SHA-256"
        ),
        "number_policy": (
            "safe integers only; scientific decimal values use typed strings"
        ),
        "native_program_template": NATIVE_PROGRAM_TEMPLATE,
    }


def install_registry_extension(registry: dict[str, Any]) -> dict[str, Any]:
    if REGISTRY_EXTENSION_KEY in registry or PROGRAMS_KEY in registry:
        raise BoundedProgramError("bounded-program registry extension already installed")
    migrated = dict(registry)
    migrated["schema_version"] = 1
    envelope = dict(migrated.get("registry_envelope_v0", {}))
    envelope["schema_version"] = 1
    migrated["registry_envelope_v0"] = envelope
    migrated[REGISTRY_EXTENSION_KEY] = governance_contract()
    migrated[PROGRAMS_KEY] = {
        QUADRATIC_PROGRAM_ID: _quadratic_program_record(),
    }
    return migrated


def authorize_native_program(registry: dict[str, Any]) -> dict[str, Any]:
    projection = registry.get("current_projection_v0")
    if not isinstance(projection, dict):
        raise BoundedProgramError("canonical current projection is missing")
    if projection.get("current_target") != NATIVE_PROGRAM_AUTHORIZATION_TARGET:
        raise BoundedProgramError(
            "native bounded program authorization target is not authoritative"
        )
    programs = registry.get(PROGRAMS_KEY)
    if not isinstance(programs, dict):
        raise BoundedProgramError("bounded-program registry extension is missing")
    if NATIVE_PROGRAM_ID in programs:
        raise BoundedProgramError("native bounded program is already authorized")
    quadratic = programs.get(QUADRATIC_PROGRAM_ID)
    if not isinstance(quadratic, dict) or not (
        quadratic.get("state") == "CLOSED"
        and quadratic.get("mandatory_exit_completed") is True
        and quadratic.get("program_terminal_status")
        == "CLOSED_AFTER_MANDATORY_ROLE_GATE"
        and quadratic.get("toe_role") == "REFERENCE_CONTROL_ONLY"
    ):
        raise BoundedProgramError(
            "quadratic program has not completed its mandatory role gate"
        )
    migrated = json.loads(json.dumps(registry))
    migrated[PROGRAMS_KEY][NATIVE_PROGRAM_ID] = _native_program_record()
    return migrated


def _program(registry: dict[str, Any], program_id: str) -> dict[str, Any]:
    programs = registry.get(PROGRAMS_KEY)
    if not isinstance(programs, dict) or program_id not in programs:
        raise BoundedProgramError(f"unknown or unauthorized bounded program: {program_id}")
    program = programs[program_id]
    if not isinstance(program, dict):
        raise BoundedProgramError(f"invalid program record: {program_id}")
    return program


def _stage(program: dict[str, Any], semantic_stage_id: str) -> dict[str, Any]:
    matches = [
        stage
        for stage in program.get("stage_definitions", [])
        if stage.get("semantic_stage_id") == semantic_stage_id
    ]
    if len(matches) != 1:
        raise BoundedProgramError(
            f"expected one stage {semantic_stage_id!r}, found {len(matches)}"
        )
    return matches[0]


def _event_relative_path(
    program_id: str, attempt_sequence_number: int, event_type: str
) -> str:
    suffix = "OPEN" if event_type == "ATTEMPT_OPEN" else "CLOSE"
    return (
        "formal/docs/release/bounded_program_events/"
        f"{program_id}_ATTEMPT_{attempt_sequence_number:02d}_{suffix}_v0.json"
    )


def open_attempt(
    registry: dict[str, Any],
    *,
    registry_bytes: bytes,
    program_id: str,
    semantic_stage_id: str,
    target: str,
    opened_from_commit: str,
) -> tuple[dict[str, Any], str, dict[str, Any]]:
    if not FULL_COMMIT_ID_PATTERN.fullmatch(opened_from_commit):
        raise BoundedProgramError(
            "new OPEN events require a lowercase full 40-character parent commit ID"
        )
    program = _program(registry, program_id)
    if program["state"] == "OPEN":
        raise BoundedProgramError("cannot open a second attempt while one is open")
    if program["blocked_stage_id"] is not None:
        raise BoundedProgramError("blocked program must take its mandatory exit")
    stage = _stage(program, semantic_stage_id)
    expected_stage_number = program["last_closed_attempt_number"] + 1
    if stage["stage_number"] != expected_stage_number:
        raise BoundedProgramError(
            f"stage order violation: expected {expected_stage_number}, "
            f"got {stage['stage_number']}"
        )
    if target != stage["target"]:
        raise BoundedProgramError("target does not match the canonical stage target")
    if semantic_stage_id in program["attempted_stage_ids"]:
        raise BoundedProgramError("semantic stage has already been attempted")
    if expected_stage_number > program["authorized_stage_count"]:
        raise BoundedProgramError("authorized stage count exhausted")
    if scope_hash(_stage_scope(stage)) != stage["scope_hash"]:
        raise BoundedProgramError("stage scope hash drift")

    previous_event_hash = program["event_chain_tip_hash"]
    event_sequence_number = len(program["events"]) + 1
    event = {
        "event_type": "ATTEMPT_OPEN",
        "event_sequence_number": event_sequence_number,
        "attempt_sequence_number": expected_stage_number,
        "program_id": program_id,
        "semantic_stage_id": semantic_stage_id,
        "target": target,
        "scope_hash": stage["scope_hash"],
        "registry_snapshot_hash": sha256_bytes(registry_bytes),
        "previous_event_hash": previous_event_hash,
        "opened_from_commit": opened_from_commit,
    }
    event["event_hash"] = _event_hash(event)
    relative_path = _event_relative_path(
        program_id, expected_stage_number, "ATTEMPT_OPEN"
    )

    migrated = json.loads(json.dumps(registry))
    migrated_program = _program(migrated, program_id)
    migrated_program["current_stage_number"] = stage["stage_number"]
    migrated_program["attempted_stage_ids"].append(semantic_stage_id)
    migrated_program["state"] = "OPEN"
    migrated_program["open_attempt_number"] = expected_stage_number
    migrated_program["event_chain_tip_hash"] = event["event_hash"]
    migrated_program["events"].append(
        {
            "event_type": "ATTEMPT_OPEN",
            "attempt_sequence_number": expected_stage_number,
            "path": relative_path,
            "event_hash": event["event_hash"],
            "sha256": sha256_bytes(_pretty_json_bytes(event)),
        }
    )
    return migrated, relative_path, event


def close_attempt(
    registry: dict[str, Any],
    *,
    program_id: str,
    result_artifact_path: str,
    review_artifact_path: str,
    terminal_result: str,
    closed_from_commit: str,
) -> tuple[dict[str, Any], str, dict[str, Any]]:
    if not FULL_COMMIT_ID_PATTERN.fullmatch(closed_from_commit):
        raise BoundedProgramError(
            "new CLOSE events require a lowercase full 40-character parent commit ID"
        )
    if terminal_result not in TERMINAL_RESULTS:
        raise BoundedProgramError(f"invalid terminal result: {terminal_result}")
    program = _program(registry, program_id)
    if program["state"] != "OPEN":
        raise BoundedProgramError("no open attempt to close")
    attempt_number = program["open_attempt_number"]
    if not isinstance(attempt_number, int):
        raise BoundedProgramError("open attempt number is missing")
    if not program["events"] or program["events"][-1]["event_type"] != "ATTEMPT_OPEN":
        raise BoundedProgramError("latest event is not an OPEN event")

    result_path = REPO_ROOT / result_artifact_path
    review_path = REPO_ROOT / review_artifact_path
    if not result_path.is_file() or not review_path.is_file():
        raise BoundedProgramError("result and review artifacts must exist before CLOSE")

    open_event_hash = program["events"][-1]["event_hash"]
    event = {
        "event_type": "ATTEMPT_CLOSE",
        "event_sequence_number": len(program["events"]) + 1,
        "attempt_sequence_number": attempt_number,
        "program_id": program_id,
        "open_event_hash": open_event_hash,
        "result_artifact_path": result_artifact_path,
        "result_artifact_hash": sha256_path(result_path),
        "review_artifact_path": review_artifact_path,
        "review_artifact_hash": sha256_path(review_path),
        "terminal_result": terminal_result,
        "previous_event_hash": program["event_chain_tip_hash"],
        "closed_from_commit": closed_from_commit,
    }
    event["event_hash"] = _event_hash(event)
    relative_path = _event_relative_path(
        program_id, attempt_number, "ATTEMPT_CLOSE"
    )

    migrated = json.loads(json.dumps(registry))
    migrated_program = _program(migrated, program_id)
    semantic_stage_id = migrated_program["attempted_stage_ids"][-1]
    migrated_program["state"] = "CLOSED"
    migrated_program["open_attempt_number"] = None
    migrated_program["last_closed_attempt_number"] = attempt_number
    migrated_program["event_chain_tip_hash"] = event["event_hash"]
    if terminal_result in {"BLOCKED", "FAILED"}:
        migrated_program["blocked_stage_id"] = semantic_stage_id
    migrated_program["events"].append(
        {
            "event_type": "ATTEMPT_CLOSE",
            "attempt_sequence_number": attempt_number,
            "path": relative_path,
            "event_hash": event["event_hash"],
            "sha256": sha256_bytes(_pretty_json_bytes(event)),
        }
    )
    return migrated, relative_path, event


def _validate_stage_definitions(program: dict[str, Any]) -> None:
    stages = program.get("stage_definitions")
    if not isinstance(stages, list):
        raise BoundedProgramError("stage_definitions must be an array")
    if len(stages) != program.get("authorized_stage_count"):
        raise BoundedProgramError("stage definition count does not match authorization")
    seen_ids: set[str] = set()
    seen_targets: set[str] = set()
    for expected_number, stage in enumerate(stages, start=1):
        if stage.get("stage_number") != expected_number:
            raise BoundedProgramError("stage numbers are not contiguous")
        semantic_id = stage.get("semantic_stage_id")
        target = stage.get("target")
        if semantic_id in seen_ids or target in seen_targets:
            raise BoundedProgramError("stage IDs and targets must be one-to-one")
        seen_ids.add(semantic_id)
        seen_targets.add(target)
        if stage.get("scope_hash") != scope_hash(_stage_scope(stage)):
            raise BoundedProgramError(f"scope hash mismatch for {semantic_id}")


def _expected_stage_projection(manifest: dict[str, Any]) -> list[dict[str, Any]]:
    expected: list[dict[str, Any]] = []
    for manifest_stage in manifest["stages"]:
        row = json.loads(json.dumps(manifest_stage["canonical_scope"]))
        row["target"] = manifest_stage["canonical_target"]
        row["stage_number"] = manifest_stage["stage_number"]
        row["scope_hash"] = manifest_stage["canonical_scope_hash"]
        expected.append(row)
    return expected


def _git_lines(repo_root: Path, *args: str) -> list[str]:
    output = _git_output(*args, cwd=repo_root)
    return output.splitlines() if output else []


def _git_introduction_commit(repo_root: Path, relative_path: str) -> str:
    commits = _git_lines(
        repo_root,
        "log",
        "--diff-filter=A",
        "--format=%H",
        "--",
        relative_path,
    )
    if len(commits) != 1:
        raise BoundedProgramError(
            f"expected exactly one introduction commit for {relative_path}, "
            f"found {len(commits)}"
        )
    return commits[0]


def _git_single_parent(repo_root: Path, commit: str) -> str:
    row = _git_output("rev-list", "--parents", "-n", "1", commit, cwd=repo_root)
    parts = row.split()
    if len(parts) != 2 or parts[0] != commit:
        raise BoundedProgramError(
            f"event introduction commit must have exactly one parent: {commit}"
        )
    return parts[1]


def _git_show_bytes(repo_root: Path, commit: str, relative_path: str) -> bytes:
    result = subprocess.run(
        ["git", "show", f"{commit}:{relative_path}"],
        cwd=repo_root,
        check=False,
        capture_output=True,
    )
    if result.returncode != 0:
        raise BoundedProgramError(
            f"path is absent from committed tree {commit}: {relative_path}"
        )
    return result.stdout


def _git_commit_path_set(repo_root: Path, commit: str) -> list[str]:
    return sorted(
        _git_lines(
            repo_root,
            "diff-tree",
            "--no-commit-id",
            "--name-only",
            "-r",
            commit,
        )
    )


def _git_object_type(repo_root: Path, object_id: str) -> str | None:
    result = subprocess.run(
        ["git", "cat-file", "-t", object_id],
        cwd=repo_root,
        check=False,
        capture_output=True,
        text=True,
    )
    return result.stdout.strip() if result.returncode == 0 else None


def _verify_immutable_introduction(
    repo_root: Path, relative_path: str, *, expected_commit: str | None = None
) -> str:
    introduction = _git_introduction_commit(repo_root, relative_path)
    if expected_commit is not None and introduction != expected_commit:
        raise BoundedProgramError(
            f"unexpected introduction commit for {relative_path}: "
            f"{introduction} != {expected_commit}"
        )
    current = (repo_root / relative_path).read_bytes()
    introduced = _git_show_bytes(repo_root, introduction, relative_path)
    if introduced != current:
        raise BoundedProgramError(f"historical artifact bytes changed: {relative_path}")
    return introduction


def _resolve_event_parent_commit(
    *,
    repo_root: Path,
    event_path: str,
    field: str,
    stored_value: Any,
    attestation: dict[str, Any],
) -> str:
    if isinstance(stored_value, str) and FULL_COMMIT_ID_PATTERN.fullmatch(
        stored_value
    ):
        resolved = stored_value
    else:
        matches = [
            row
            for row in attestation.get("entries", [])
            if row.get("legacy_event_path") == event_path
            and row.get("field") == field
            and row.get("stored_abbreviated_id") == stored_value
        ]
        if len(matches) != 1:
            raise BoundedProgramError(
                f"legacy commit ID lacks a unique attestation: {event_path}:{field}"
            )
        row = matches[0]
        resolved = row.get("resolved_full_commit_id")
        if not isinstance(resolved, str) or not FULL_COMMIT_ID_PATTERN.fullmatch(
            resolved
        ):
            raise BoundedProgramError("legacy attestation lacks a full commit ID")
        candidates = sorted(
            commit
            for commit in _git_lines(repo_root, "rev-list", "--all")
            if commit.startswith(str(stored_value))
        )
        if (
            row.get("uniqueness_candidate_count") != 1
            or row.get("uniqueness_candidates") != [resolved]
            or candidates != [resolved]
            or _git_object_type(repo_root, resolved) != "commit"
            or row.get("git_object_type") != "commit"
        ):
            raise BoundedProgramError(
                f"legacy commit ID attestation is not unique: {stored_value}"
            )
    if _git_object_type(repo_root, resolved) != "commit":
        raise BoundedProgramError(f"event parent is not a commit: {resolved}")
    return resolved


def _compare_projection(
    actual: dict[str, Any], expected: dict[str, Any], *, context: str
) -> None:
    for key, expected_value in expected.items():
        if actual.get(key) != expected_value:
            raise BoundedProgramError(
                f"{context} projection mismatch for {key}: "
                f"{actual.get(key)!r} != {expected_value!r}"
            )


def _validate_exit_assertions(
    repo_root: Path, manifest: dict[str, Any]
) -> None:
    mandatory_exit = manifest["mandatory_exit"]
    for kind in ("result", "review"):
        relative_path = mandatory_exit[f"{kind}_artifact_path"]
        document = strict_json_load(repo_root / relative_path)
        assertions = mandatory_exit[f"{kind}_assertions"]
        _compare_projection(
            document,
            assertions,
            context=f"{manifest['program_id']} mandatory-exit {kind}",
        )


def _validate_history_envelope(
    *,
    registry: dict[str, Any],
    program_id: str,
    manifest: dict[str, Any],
    event_rows: list[dict[str, Any]],
    repo_root: Path,
    attestation: dict[str, Any],
) -> None:
    if manifest.get("manifest_mode") == "PROSPECTIVE_STATIC":
        _validate_prospective_history_envelope(
            registry=registry,
            program_id=program_id,
            manifest=manifest,
            event_rows=event_rows,
            repo_root=repo_root,
            attestation=attestation,
        )
        return
    manifest_path = PROGRAM_MANIFEST_PATHS[program_id]
    _verify_immutable_introduction(repo_root, manifest_path)
    _verify_immutable_introduction(repo_root, LEGACY_ATTESTATION_PATH)

    lifecycle_commits: list[str] = []
    reconstructed_prefix = {
        "current_stage_number": 0,
        "attempted_stage_ids": [],
        "blocked_stage_id": None,
        "repair_attempt_count": 0,
        "event_chain_tip_hash": None,
        "last_closed_attempt_number": 0,
        "state": "UNOPENED",
        "open_attempt_number": None,
    }
    for row in event_rows:
        event = row["event"]
        event_path = row["path"]
        introduction = _verify_immutable_introduction(
            repo_root, event_path, expected_commit=row["introduction_commit"]
        )
        lifecycle_commits.append(introduction)
        parent = _git_single_parent(repo_root, introduction)
        if event["event_type"] == "ATTEMPT_OPEN":
            resolved_parent = _resolve_event_parent_commit(
                repo_root=repo_root,
                event_path=event_path,
                field="opened_from_commit",
                stored_value=event.get("opened_from_commit"),
                attestation=attestation,
            )
            if parent != resolved_parent:
                raise BoundedProgramError(
                    f"OPEN parent mismatch for {event_path}: {parent}"
                )
            parent_registry = _git_show_bytes(
                repo_root,
                parent,
                REGISTRY_PATH.relative_to(REPO_ROOT).as_posix(),
            )
            if sha256_bytes(parent_registry) != event.get("registry_snapshot_hash"):
                raise BoundedProgramError(
                    f"OPEN registry snapshot hash mismatch: {event_path}"
                )
            reconstructed_prefix["current_stage_number"] = event[
                "attempt_sequence_number"
            ]
            reconstructed_prefix["attempted_stage_ids"].append(
                event["semantic_stage_id"]
            )
            reconstructed_prefix["state"] = "OPEN"
            reconstructed_prefix["open_attempt_number"] = event[
                "attempt_sequence_number"
            ]
        else:
            resolved_parent = _resolve_event_parent_commit(
                repo_root=repo_root,
                event_path=event_path,
                field="closed_from_commit",
                stored_value=event.get("closed_from_commit"),
                attestation=attestation,
            )
            if parent != resolved_parent:
                raise BoundedProgramError(
                    f"CLOSE parent mismatch for {event_path}: {parent}"
                )
            for artifact_key in ("result_artifact_path", "review_artifact_path"):
                artifact_path = event[artifact_key]
                artifact_introduction = _verify_immutable_introduction(
                    repo_root, artifact_path
                )
                if artifact_introduction != introduction:
                    raise BoundedProgramError(
                        f"CLOSE artifact was not introduced atomically: {artifact_path}"
                    )
            reconstructed_prefix["state"] = "CLOSED"
            reconstructed_prefix["open_attempt_number"] = None
            reconstructed_prefix["last_closed_attempt_number"] = event[
                "attempt_sequence_number"
            ]
            if event["terminal_result"] in {"BLOCKED", "FAILED"}:
                reconstructed_prefix["blocked_stage_id"] = (
                    reconstructed_prefix["attempted_stage_ids"][-1]
                )
        reconstructed_prefix["event_chain_tip_hash"] = event["event_hash"]

        commit_registry = strict_json_loads(
            _git_show_bytes(
                repo_root,
                introduction,
                REGISTRY_PATH.relative_to(REPO_ROOT).as_posix(),
            ).decode("utf-8")
        )
        _compare_projection(
            commit_registry[PROGRAMS_KEY][program_id],
            reconstructed_prefix,
            context=f"{program_id} committed event transition",
        )

    for stage in manifest["stages"]:
        if not stage["attempted"]:
            continue
        envelope = stage["historical_envelope"]
        for event_kind in ("open", "close"):
            commit = envelope[f"{event_kind}_introduction_commit"]
            if _git_commit_path_set(repo_root, commit) != envelope[
                f"{event_kind}_commit_exact_path_set"
            ]:
                raise BoundedProgramError(
                    f"{event_kind.upper()} commit escaped its manifest envelope: "
                    f"{program_id} stage {stage['stage_number']}"
                )

    mandatory_exit = manifest["mandatory_exit"]
    exit_commit = mandatory_exit["introduction_commit"]
    if _git_commit_path_set(repo_root, exit_commit) != mandatory_exit[
        "commit_exact_path_set"
    ]:
        raise BoundedProgramError(
            f"mandatory-exit commit escaped its manifest envelope: {program_id}"
        )
    for path_key in ("result_artifact_path", "review_artifact_path"):
        _verify_immutable_introduction(
            repo_root,
            mandatory_exit[path_key],
            expected_commit=exit_commit,
        )
    _validate_exit_assertions(repo_root, manifest)

    allowed_lifecycle_commits = list(lifecycle_commits)
    for row in manifest.get("authorized_non_scientific_lifecycle_commits", []):
        commit = row["commit"]
        if row.get("scientific_target_created") is not False:
            raise BoundedProgramError(
                f"non-scientific lifecycle exception is not bounded: {commit}"
            )
        if _git_commit_path_set(repo_root, commit) != row["commit_exact_path_set"]:
            raise BoundedProgramError(
                f"non-scientific lifecycle commit path drift: {commit}"
            )
        allowed_lifecycle_commits.append(commit)
    allowed_lifecycle_commits.append(exit_commit)
    first_commit = lifecycle_commits[0]
    actual_lifecycle = _git_lines(
        repo_root,
        "rev-list",
        "--ancestry-path",
        "--reverse",
        f"{first_commit}^..{exit_commit}",
    )
    expected_lifecycle = sorted(
        allowed_lifecycle_commits,
        key=lambda commit: actual_lifecycle.index(commit)
        if commit in actual_lifecycle
        else len(actual_lifecycle),
    )
    if actual_lifecycle != expected_lifecycle:
        raise BoundedProgramError(
            f"unmanifested subsidiary lifecycle commit detected: {program_id}"
        )

    exit_registry = strict_json_loads(
        _git_show_bytes(
            repo_root,
            exit_commit,
            REGISTRY_PATH.relative_to(REPO_ROOT).as_posix(),
        ).decode("utf-8")
    )
    _compare_projection(
        exit_registry[PROGRAMS_KEY][program_id],
        mandatory_exit["expected_terminal_projection"],
        context=f"{program_id} mandatory-exit commit",
    )


def _validate_prospective_history_envelope(
    *,
    registry: dict[str, Any],
    program_id: str,
    manifest: dict[str, Any],
    event_rows: list[dict[str, Any]],
    repo_root: Path,
    attestation: dict[str, Any],
) -> None:
    manifest_path = PROGRAM_MANIFEST_PATHS[program_id]
    installation = manifest.get("installation_envelope")
    if not isinstance(installation, dict):
        raise BoundedProgramError(
            f"prospective manifest lacks installation envelope: {program_id}"
        )
    introduction = _verify_immutable_introduction(repo_root, manifest_path)
    parent = _git_single_parent(repo_root, introduction)
    if parent != installation.get("installed_from_commit"):
        raise BoundedProgramError(
            f"prospective manifest installation parent mismatch: {program_id}"
        )
    if _git_commit_path_set(repo_root, introduction) != installation.get(
        "commit_exact_path_set"
    ):
        raise BoundedProgramError(
            f"prospective program installation escaped its envelope: {program_id}"
        )
    registry_relative_path = REGISTRY_PATH.relative_to(REPO_ROOT).as_posix()
    parent_registry = strict_json_loads(
        _git_show_bytes(repo_root, parent, registry_relative_path).decode("utf-8")
    )
    if program_id in parent_registry.get(PROGRAMS_KEY, {}):
        raise BoundedProgramError(
            f"prospective program predates its installation commit: {program_id}"
        )
    installation_registry = strict_json_loads(
        _git_show_bytes(repo_root, introduction, registry_relative_path).decode("utf-8")
    )
    installed_program = installation_registry.get(PROGRAMS_KEY, {}).get(program_id)
    if not isinstance(installed_program, dict):
        raise BoundedProgramError(
            f"prospective program missing from installation commit: {program_id}"
        )
    _compare_projection(
        installed_program,
        {
            "current_stage_number": 0,
            "attempted_stage_ids": [],
            "blocked_stage_id": None,
            "repair_attempt_count": 0,
            "event_chain_tip_hash": None,
            "last_closed_attempt_number": 0,
            "state": "UNOPENED",
            "open_attempt_number": None,
            "program_terminal_status": "INSTALLED_UNOPENED",
        },
        context=f"{program_id} installation projection",
    )

    reconstructed_prefix = {
        "current_stage_number": 0,
        "attempted_stage_ids": [],
        "blocked_stage_id": None,
        "repair_attempt_count": 0,
        "event_chain_tip_hash": None,
        "last_closed_attempt_number": 0,
        "state": "UNOPENED",
        "open_attempt_number": None,
    }
    for row in event_rows:
        event = row["event"]
        event_path = row["path"]
        event_introduction = _verify_immutable_introduction(
            repo_root, event_path, expected_commit=row["introduction_commit"]
        )
        event_parent = _git_single_parent(repo_root, event_introduction)
        stage = _manifest_stage(manifest, event["attempt_sequence_number"])
        envelope = stage.get("prospective_envelope")
        if not isinstance(envelope, dict):
            raise BoundedProgramError(
                f"prospective stage lacks authority envelope: {program_id}"
            )
        if event["event_type"] == "ATTEMPT_OPEN":
            resolved_parent = _resolve_event_parent_commit(
                repo_root=repo_root,
                event_path=event_path,
                field="opened_from_commit",
                stored_value=event.get("opened_from_commit"),
                attestation=attestation,
            )
            if event_parent != resolved_parent:
                raise BoundedProgramError(f"OPEN parent mismatch for {event_path}")
            parent_registry_bytes = _git_show_bytes(
                repo_root, event_parent, registry_relative_path
            )
            if sha256_bytes(parent_registry_bytes) != event.get(
                "registry_snapshot_hash"
            ):
                raise BoundedProgramError(
                    f"OPEN registry snapshot hash mismatch: {event_path}"
                )
            if envelope.get("open_event_path") != event_path:
                raise BoundedProgramError(
                    f"OPEN event path escapes prospective envelope: {event_path}"
                )
            reconstructed_prefix["current_stage_number"] = event[
                "attempt_sequence_number"
            ]
            reconstructed_prefix["attempted_stage_ids"].append(
                event["semantic_stage_id"]
            )
            reconstructed_prefix["state"] = "OPEN"
            reconstructed_prefix["open_attempt_number"] = event[
                "attempt_sequence_number"
            ]
            exact_paths = envelope.get("open_commit_exact_path_set")
        else:
            resolved_parent = _resolve_event_parent_commit(
                repo_root=repo_root,
                event_path=event_path,
                field="closed_from_commit",
                stored_value=event.get("closed_from_commit"),
                attestation=attestation,
            )
            if event_parent != resolved_parent:
                raise BoundedProgramError(f"CLOSE parent mismatch for {event_path}")
            if (
                envelope.get("close_event_path") != event_path
                or envelope.get("result_artifact_path")
                != event.get("result_artifact_path")
                or envelope.get("review_artifact_path")
                != event.get("review_artifact_path")
            ):
                raise BoundedProgramError(
                    f"CLOSE artifacts escape prospective envelope: {event_path}"
                )
            for artifact_key in ("result_artifact_path", "review_artifact_path"):
                artifact_path = event[artifact_key]
                if (
                    _verify_immutable_introduction(repo_root, artifact_path)
                    != event_introduction
                ):
                    raise BoundedProgramError(
                        f"CLOSE artifact was not introduced atomically: {artifact_path}"
                    )
            reconstructed_prefix["state"] = "CLOSED"
            reconstructed_prefix["open_attempt_number"] = None
            reconstructed_prefix["last_closed_attempt_number"] = event[
                "attempt_sequence_number"
            ]
            if event["terminal_result"] in {"BLOCKED", "FAILED"}:
                reconstructed_prefix["blocked_stage_id"] = (
                    reconstructed_prefix["attempted_stage_ids"][-1]
                )
            exact_paths = envelope.get("close_commit_exact_path_set")
        if _git_commit_path_set(repo_root, event_introduction) != exact_paths:
            raise BoundedProgramError(
                f"{event['event_type']} commit escaped prospective envelope: "
                f"{program_id} stage {stage['stage_number']}"
            )
        reconstructed_prefix["event_chain_tip_hash"] = event["event_hash"]
        committed_registry = strict_json_loads(
            _git_show_bytes(
                repo_root, event_introduction, registry_relative_path
            ).decode("utf-8")
        )
        _compare_projection(
            committed_registry[PROGRAMS_KEY][program_id],
            reconstructed_prefix,
            context=f"{program_id} committed prospective event transition",
        )

    if reconstructed_prefix["blocked_stage_id"] is not None:
        current_program = registry[PROGRAMS_KEY][program_id]
        if current_program.get("mandatory_exit_completed") is not True:
            raise BoundedProgramError(
                f"blocked prospective program has unresolved mandatory exit: {program_id}"
            )
        if current_program.get("state") != "CLOSED":
            raise BoundedProgramError(
                f"blocked prospective program did not close: {program_id}"
            )


def validate_event_chain(
    registry: dict[str, Any],
    *,
    repo_root: Path = REPO_ROOT,
    verify_git_history: bool = False,
) -> None:
    programs = registry.get(PROGRAMS_KEY)
    if not isinstance(programs, dict):
        raise BoundedProgramError("bounded programs are missing")
    enforcement_enabled = ENFORCEMENT_EXTENSION_KEY in registry
    attestation: dict[str, Any] | None = None
    if enforcement_enabled:
        _, attestation = _load_legacy_attestation(repo_root=repo_root)
        if set(programs) != set(PROGRAM_MANIFEST_PATHS):
            raise BoundedProgramError(
                "registry bounded-program set differs from immutable manifest index"
            )

    for program_id, program in programs.items():
        _validate_stage_definitions(program)
        manifest: dict[str, Any] | None = None
        if enforcement_enabled:
            manifest_path, manifest = _load_authoritative_manifest(
                program_id, repo_root=repo_root
            )
            expected_manifest_reference = {
                "path": manifest_path,
                "sha256": sha256_path(repo_root / manifest_path),
                "manifest_hash": manifest["manifest_hash"],
            }
            if program.get("program_manifest") != expected_manifest_reference:
                raise BoundedProgramError(
                    f"registry manifest projection mismatch: {program_id}"
                )
            if program.get("stage_definitions") != _expected_stage_projection(
                manifest
            ):
                raise BoundedProgramError(
                    f"registry stage definitions drift from manifest: {program_id}"
                )
            if program.get("program_id") != program_id:
                raise BoundedProgramError("program projection identity mismatch")
            if program.get("authorized_stage_count") != manifest[
                "authorized_stage_count"
            ]:
                raise BoundedProgramError(
                    f"authorized stage count differs from manifest: {program_id}"
                )
            if (
                program.get("mandatory_exit_target")
                != manifest["mandatory_exit"]["target"]
            ):
                raise BoundedProgramError(
                    f"mandatory exit target differs from manifest: {program_id}"
                )
            if program.get("no_subsidiary_scientific_targets") is not True:
                raise BoundedProgramError(
                    f"subsidiary scientific targets are not prohibited: {program_id}"
                )

        events = program.get("events")
        if not isinstance(events, list):
            raise BoundedProgramError("events must be an array")
        previous_hash: str | None = None
        open_attempt: int | None = None
        closed_attempts = 0
        attempted_stage_ids: list[str] = []
        blocked_stage_id: str | None = None
        current_stage_number = 0
        event_rows: list[dict[str, Any]] = []

        for event_number, reference in enumerate(events, start=1):
            relative_path = reference.get("path")
            if not isinstance(relative_path, str):
                raise BoundedProgramError("event reference path must be a string")
            path = repo_root / relative_path
            if not path.is_file():
                raise BoundedProgramError(f"missing event artifact: {relative_path}")
            raw = path.read_bytes()
            raw_hash = sha256_bytes(raw)
            if raw_hash != reference.get("sha256"):
                raise BoundedProgramError(f"event byte hash mismatch: {relative_path}")
            event = strict_json_loads(raw.decode("utf-8"))
            expected_reference = {
                "event_type": event.get("event_type"),
                "attempt_sequence_number": event.get("attempt_sequence_number"),
                "path": relative_path,
                "event_hash": event.get("event_hash"),
                "sha256": raw_hash,
            }
            if reference != expected_reference:
                raise BoundedProgramError(
                    f"event registry reference is not an exact projection: {relative_path}"
                )
            if event.get("event_sequence_number") != event_number:
                raise BoundedProgramError("event sequence numbers are not contiguous")
            if event.get("previous_event_hash") != previous_hash:
                raise BoundedProgramError("event hash chain is broken")
            if event.get("event_hash") != _event_hash(event):
                raise BoundedProgramError("event self-hash is invalid")
            if event.get("event_hash") != reference.get("event_hash"):
                raise BoundedProgramError("event reference hash mismatch")
            if event.get("program_id") != program_id:
                raise BoundedProgramError("event belongs to another program")

            attempt_number = event.get("attempt_sequence_number")
            if event.get("event_type") == "ATTEMPT_OPEN":
                if open_attempt is not None:
                    raise BoundedProgramError("attempt opened before prior CLOSE")
                if blocked_stage_id is not None:
                    raise BoundedProgramError(
                        "later scientific stage opened after blocked stage"
                    )
                if attempt_number != closed_attempts + 1:
                    raise BoundedProgramError("attempt numbers are not contiguous")
                if manifest is not None:
                    if attempt_number > manifest["authorized_stage_count"]:
                        raise BoundedProgramError("authorized stage count exceeded")
                    manifest_stage = _manifest_stage(manifest, attempt_number)
                    if event.get("semantic_stage_id") != manifest_stage[
                        "semantic_stage_id"
                    ]:
                        raise BoundedProgramError(
                            "OPEN semantic stage differs from immutable manifest"
                        )
                    if event.get("target") != manifest_stage["canonical_target"]:
                        raise BoundedProgramError(
                            "OPEN target differs from immutable manifest"
                        )
                    if event.get("scope_hash") != manifest_stage[
                        "canonical_scope_hash"
                    ]:
                        raise BoundedProgramError(
                            "OPEN scope hash differs from immutable manifest"
                        )
                    prospective = (
                        manifest.get("manifest_mode") == "PROSPECTIVE_STATIC"
                    )
                    envelope = manifest_stage.get(
                        "prospective_envelope"
                        if prospective
                        else "historical_envelope"
                    )
                    if (
                        (not prospective and not manifest_stage.get("attempted"))
                        or not isinstance(envelope, dict)
                        or envelope.get("open_event_path") != relative_path
                    ):
                        raise BoundedProgramError(
                            "OPEN event is absent from manifest stage envelope"
                        )
                semantic_stage_id = event.get("semantic_stage_id")
                if (
                    not isinstance(semantic_stage_id, str)
                    or semantic_stage_id in attempted_stage_ids
                ):
                    raise BoundedProgramError(
                        "attempted semantic stages are not unique"
                    )
                attempted_stage_ids.append(semantic_stage_id)
                current_stage_number = attempt_number
                open_attempt = attempt_number
            elif event.get("event_type") == "ATTEMPT_CLOSE":
                if open_attempt != attempt_number:
                    raise BoundedProgramError("CLOSE does not match the open attempt")
                if event.get("open_event_hash") != previous_hash:
                    raise BoundedProgramError("CLOSE does not reference its OPEN event")
                if event.get("terminal_result") not in TERMINAL_RESULTS:
                    raise BoundedProgramError("CLOSE has an invalid terminal result")
                if manifest is not None:
                    manifest_stage = _manifest_stage(manifest, attempt_number)
                    envelope = manifest_stage.get(
                        "prospective_envelope"
                        if manifest.get("manifest_mode") == "PROSPECTIVE_STATIC"
                        else "historical_envelope"
                    )
                    if (
                        not isinstance(envelope, dict)
                        or envelope.get("close_event_path") != relative_path
                        or envelope.get("result_artifact_path")
                        != event.get("result_artifact_path")
                        or envelope.get("review_artifact_path")
                        != event.get("review_artifact_path")
                    ):
                        raise BoundedProgramError(
                            "CLOSE artifacts escape the manifest stage envelope"
                        )
                for key in ("result_artifact_path", "review_artifact_path"):
                    artifact_path = repo_root / event[key]
                    if not artifact_path.is_file():
                        raise BoundedProgramError(f"missing CLOSE artifact: {event[key]}")
                if sha256_path(repo_root / event["result_artifact_path"]) != event.get(
                    "result_artifact_hash"
                ):
                    raise BoundedProgramError("CLOSE result hash mismatch")
                if sha256_path(repo_root / event["review_artifact_path"]) != event.get(
                    "review_artifact_hash"
                ):
                    raise BoundedProgramError("CLOSE review hash mismatch")
                open_attempt = None
                closed_attempts += 1
                if event.get("terminal_result") in {"BLOCKED", "FAILED"}:
                    blocked_stage_id = attempted_stage_ids[-1]
            else:
                raise BoundedProgramError("unknown event type")

            if verify_git_history:
                introduction = _git_introduction_commit(repo_root, relative_path)
            else:
                introduction = ""
            event_rows.append(
                {
                    "path": relative_path,
                    "event": event,
                    "introduction_commit": introduction,
                }
            )
            previous_hash = event["event_hash"]

        expected_state = "OPEN" if open_attempt is not None else (
            "CLOSED" if events else "UNOPENED"
        )
        reconstructed_projection = {
            "current_stage_number": current_stage_number,
            "attempted_stage_ids": attempted_stage_ids,
            "blocked_stage_id": blocked_stage_id,
            "repair_attempt_count": 0,
            "event_chain_tip_hash": previous_hash,
            "last_closed_attempt_number": closed_attempts,
            "state": expected_state,
            "open_attempt_number": open_attempt,
        }
        _compare_projection(
            program,
            reconstructed_projection,
            context=f"{program_id} reconstructed event state",
        )

        if manifest is not None:
            if manifest.get("manifest_mode") != "PROSPECTIVE_STATIC":
                manifest_attempted = [
                    stage["semantic_stage_id"]
                    for stage in manifest["stages"]
                    if stage["attempted"]
                ]
                if attempted_stage_ids != manifest_attempted:
                    raise BoundedProgramError(
                        "event history differs from manifest attempt inventory: "
                        f"{program_id}"
                    )
            if (
                blocked_stage_id is not None
                and manifest.get("manifest_mode") != "PROSPECTIVE_STATIC"
            ):
                _compare_projection(
                    program,
                    manifest["mandatory_exit"]["expected_terminal_projection"],
                    context=f"{program_id} mandatory-exit completion",
                )
            if verify_git_history:
                assert attestation is not None
                _validate_history_envelope(
                    registry=registry,
                    program_id=program_id,
                    manifest=manifest,
                    event_rows=event_rows,
                    repo_root=repo_root,
                    attestation=attestation,
                )


def validate_registry_extension(registry: dict[str, Any]) -> None:
    contract = registry.get(REGISTRY_EXTENSION_KEY)
    if contract != governance_contract():
        raise BoundedProgramError("bounded-program governance contract drift")
    enforcement = registry.get(ENFORCEMENT_EXTENSION_KEY)
    if enforcement is None:
        if registry.get("schema_version") != 1:
            raise BoundedProgramError("legacy registry schema version is not 1")
    else:
        if enforcement != enforcement_contract():
            raise BoundedProgramError(
                "bounded-program enforcement contract drift"
            )
        if registry.get("schema_version") != 2:
            raise BoundedProgramError("enforced registry schema version is not 2")
    validate_event_chain(registry)


def write_event(path: Path, event: dict[str, Any]) -> None:
    if path.exists():
        raise BoundedProgramError(f"immutable event already exists: {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(_pretty_json_bytes(event))


def _load_registry_bytes(path: Path) -> tuple[bytes, dict[str, Any]]:
    raw = path.read_bytes()
    registry = strict_json_loads(raw.decode("utf-8"))
    if not isinstance(registry, dict):
        raise BoundedProgramError("registry root must be an object")
    return raw, registry


def _command_install(registry_path: Path) -> None:
    _, registry = _load_registry_bytes(registry_path)
    migrated = install_registry_extension(registry)
    atomic_write_registry(registry_path, _registry_json_bytes(migrated))


def _command_reinstall_from_head(registry_path: Path) -> None:
    relative_path = registry_path.resolve().relative_to(REPO_ROOT).as_posix()
    original_bytes = subprocess.run(
        ["git", "show", f"HEAD:{relative_path}"],
        cwd=REPO_ROOT,
        check=True,
        capture_output=True,
    ).stdout
    original = strict_json_loads(original_bytes.decode("utf-8"))
    if not isinstance(original, dict):
        raise BoundedProgramError("HEAD registry root must be an object")
    migrated = install_registry_extension(original)
    atomic_write_registry(registry_path, _registry_json_bytes(migrated))


def _command_validate(registry_path: Path, verify_git_history: bool) -> None:
    _, registry = _load_registry_bytes(registry_path)
    validate_registry_extension(registry)
    if verify_git_history or ENFORCEMENT_EXTENSION_KEY in registry:
        validate_event_chain(registry, verify_git_history=True)


def _command_authorize_native(registry_path: Path) -> None:
    _, registry = _load_registry_bytes(registry_path)
    migrated = authorize_native_program(registry)
    validate_registry_extension(migrated)
    atomic_write_registry(registry_path, _registry_json_bytes(migrated))


def _command_install_enforcement(registry_path: Path) -> None:
    _, registry = _load_registry_bytes(registry_path)
    migrated = install_enforcement_completion(registry)
    validate_registry_extension(migrated)
    atomic_write_registry(registry_path, _registry_json_bytes(migrated))


def _command_install_coherence_ontology(registry_path: Path) -> None:
    _, registry = _load_registry_bytes(registry_path)
    migrated = install_coherence_ontology_program(registry)
    validate_registry_extension(migrated)
    atomic_write_registry(registry_path, _registry_json_bytes(migrated))


def _command_install_repository_wide_census(registry_path: Path) -> None:
    _, registry = _load_registry_bytes(registry_path)
    migrated = install_repository_wide_census_program(registry)
    validate_registry_extension(migrated)
    atomic_write_registry(registry_path, _registry_json_bytes(migrated))


def _command_install_gravitational_survey(registry_path: Path) -> None:
    _, registry = _load_registry_bytes(registry_path)
    migrated = install_gravitational_survey_program(registry)
    validate_registry_extension(migrated)
    atomic_write_registry(registry_path, _registry_json_bytes(migrated))


def main(argv: Iterable[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "command",
        choices=(
            "install",
            "reinstall-from-head",
            "authorize-native",
            "install-enforcement",
            "install-coherence-ontology",
            "install-repository-wide-census",
            "install-gravitational-survey",
            "validate",
        ),
    )
    parser.add_argument("--registry", type=Path, default=REGISTRY_PATH)
    parser.add_argument("--verify-git-history", action="store_true")
    args = parser.parse_args(list(argv) if argv is not None else None)
    if args.command == "install":
        _command_install(args.registry)
    elif args.command == "reinstall-from-head":
        _command_reinstall_from_head(args.registry)
    elif args.command == "authorize-native":
        _command_authorize_native(args.registry)
    elif args.command == "install-enforcement":
        _command_install_enforcement(args.registry)
    elif args.command == "install-coherence-ontology":
        _command_install_coherence_ontology(args.registry)
    elif args.command == "install-repository-wide-census":
        _command_install_repository_wide_census(args.registry)
    elif args.command == "install-gravitational-survey":
        _command_install_gravitational_survey(args.registry)
    else:
        _command_validate(args.registry, args.verify_git_history)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

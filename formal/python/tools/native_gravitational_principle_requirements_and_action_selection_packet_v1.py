from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[3]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from formal.python.tools import (  # noqa: E402
    native_gravitational_principle_requirements_and_action_selection_packet_v0 as v0,
)


REPORT_RELATIVE_PATH = (
    "formal/docs/release/"
    "NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_ACTION_SELECTION_PACKET_"
    "20260718_v1.json"
)
TEST_RELATIVE_PATH = (
    "formal/python/tests/"
    "test_native_gravitational_principle_requirements_and_action_selection_packet_v1.py"
)
PACKET_RELATIVE_PATH = (
    "formal/docs/lanes/"
    "NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_ACTION_SELECTION_PACKET_"
    "20260718_v1.md"
)
TARGET = (
    "prepare_native_gravitational_principle_requirements_and_action_selection_packet_v1"
)
SELECTED_NEXT_TARGET = (
    "review_native_gravitational_principle_requirements_and_action_selection_packet_v1_result"
)
PRODUCTION_ENTRY_POINT_ID = "evaluate_analysis_v1"

AUTHORITY_AND_SOURCE_HASHES = {
    "formal/docs/lanes/NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_ACTION_SELECTION_PACKET_REVIEW_20260718_v0.md":
        "7c17a967d719f0dabf887cf5fb98b7ccaf1d3dbc34f19d8b5f6368d66f2ac7ea",
    "formal/docs/release/NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_ACTION_SELECTION_PACKET_REVIEW_20260718_v0.json":
        "c7cbf6997b5414a83524a82c105e33e44426dd07f5b2a703d3f68e123795fa9c",
    "formal/python/tools/native_gravitational_principle_requirements_and_action_selection_packet_review_v0.py":
        "56004b43c82b3f6f2826b5776ffe834f1264164d5a79f3b02f8d1d1e1352388b",
    "formal/python/tests/test_native_gravitational_principle_requirements_and_action_selection_packet_review_v0.py":
        "cf2672d4926e86e7f2b2a9f5b6897aaaca5a89e6f11ee65e02b90803b3c12b3b",
    "formal/toe_formal/ToeFormal/Derivation/NativeGravitationalPrincipleRequirementsAndActionSelectionPacketReviewV0.lean":
        "2446065f93137045d141a40ded531ca0192447d213ff4c6f7f0257a53dd3befd",
    "formal/docs/lanes/NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_ACTION_SELECTION_PACKET_20260718_v0.md":
        "b74f94c30298d81671157213845bf761631fb9cc39a8d102b93c236e8199056f",
    "formal/docs/release/NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_ACTION_SELECTION_PACKET_20260718_v0.json":
        "9dcc6df5a5844aecfff6e50c6ad8b67e7f8bac9411bd8c282f5d876d2ac44634",
    "formal/python/tools/native_gravitational_principle_requirements_and_action_selection_packet_v0.py":
        "d25634e5ad6bd59ec85dd25e321bda5ffeff7529557c1419634185d87efc3f9b",
    "formal/python/tests/test_native_gravitational_principle_requirements_and_action_selection_packet_v0.py":
        "5282518d483a33aed986a3babf37061058f8e4a680dcaf3ad8882c3d69ae5c3b",
    "formal/toe_formal/ToeFormal/Derivation/NativeGravitationalPrincipleRequirementsAndActionSelectionPacketV0.lean":
        "40c6e0b41d37ee977d4836c437bc7116efb7150056c95853e833b2a82cce0371",
    "formal/docs/release/NATIVE_GRAVITATIONAL_PRINCIPLE_RESPONSE_SELECTION_20260718_v0.json":
        "e2468ea98384383654efe73dd054f5149beb6d4a62db45123109d962999dea66",
    PACKET_RELATIVE_PATH:
        "4ed85fe1318a9923d55aa9c657a875336ebc78298cb9384659cf860fcfa48363",
}

STATEMENT_CLASSES = [
    "PROJECT_BOUND_NATIVE_REQUIREMENT",
    "SUPPLIED_STANDARD_PHYSICS_ASSUMPTION",
    "NEW_PROPOSED_POSTULATE",
]

MATRIX_CELL_VALUES = [
    "AFFIRMATIVELY_SATISFIES_REQUIREMENT",
    "ELIMINATED",
    "NOT_DECIDABLE_FROM_REQUIREMENT",
    "OUTSIDE_FROZEN_ENVELOPE",
    "EQUIVALENT_UNDER_LOCAL_BULK_RULE",
    "REQUIRES_SUPPLIED_ASSUMPTION",
    "NOT_EVALUATED",
]

SCIENTIFIC_OUTCOMES = [
    "REQUIREMENT_SET_INCONSISTENT",
    "NO_GO_UNDER_MINIMAL_METRIC_LOCAL_ASSUMPTIONS",
    "NATIVE_PRINCIPLE_SET_SELECTS_ACTION_FAMILY",
    "CURRENT_REQUIREMENTS_COLLAPSE_TO_STANDARD_GR",
    "ACTION_FAMILY_UNDERDETERMINED",
    "DISTINCTIVE_GRAVITATIONAL_POSTULATE_REQUIRED",
]

INTERNAL_RESULTS = [
    "PRECHECK_FAILURE",
    "ANALYSIS_INCOMPLETE",
    "EMPTY_SET_CLASSIFICATION_INSUFFICIENT",
]

NATIVE_ELIMINATION_ELIGIBILITY = {
    "R1_DIMENSION": False,
    "R2_METRIC_ONLY": False,
    "R3_LOCALITY": False,
    "R4_DIFF_COVARIANCE": True,
    "R5_CK_FIREWALL": True,
    "R6_LOCAL_VARIATION": False,
    "R7_SOURCE_COMPATIBILITY": True,
    "R8_NEWTON_POISSON": True,
    "R9_MOMENTUM_CURRENT": True,
    "R10_STABILITY_NO_FIT": True,
}


def _repair_requirement(source: dict[str, Any]) -> dict[str, Any]:
    row = dict(source)
    requirement_id = row["requirement_id"]
    row.update({
        "statement_class": "PROJECT_BOUND_NATIVE_REQUIREMENT",
        "source_class_expected": "PROJECT_BOUND_NATIVE_REQUIREMENT",
        "authority_subclass": row["authority_status"],
        "canonical_requirement_id": requirement_id,
        "native_elimination_allowed": NATIVE_ELIMINATION_ELIGIBILITY[
            requirement_id
        ],
        "native_distinctiveness_allowed": NATIVE_ELIMINATION_ELIGIBILITY[
            requirement_id
        ],
        "class_binding_immutable": True,
    })
    return row


REPAIRED_REQUIREMENTS = [_repair_requirement(row) for row in v0.REQUIREMENTS]

SUPPLIED_ASSUMPTIONS = [
    {
        "requirement_id": "S1_SECOND_ORDER_FIELD_EQUATIONS",
        "canonical_requirement_id": "S1_SECOND_ORDER_FIELD_EQUATIONS",
        "statement_class": "SUPPLIED_STANDARD_PHYSICS_ASSUMPTION",
        "source_class_expected": "SUPPLIED_STANDARD_PHYSICS_ASSUMPTION",
        "authority_subclass": "UNSELECTED_STANDARD_GR_UNIQUENESS_ASSUMPTION",
        "native_elimination_allowed": False,
        "native_distinctiveness_allowed": False,
        "class_binding_immutable": True,
    },
    {
        "requirement_id": "S2_LEVI_CIVITA_UNIQUENESS",
        "canonical_requirement_id": "S2_LEVI_CIVITA_UNIQUENESS",
        "statement_class": "SUPPLIED_STANDARD_PHYSICS_ASSUMPTION",
        "source_class_expected": "SUPPLIED_STANDARD_PHYSICS_ASSUMPTION",
        "authority_subclass": "UNSELECTED_STANDARD_GR_GEOMETRIC_ASSUMPTION",
        "native_elimination_allowed": False,
        "native_distinctiveness_allowed": False,
        "class_binding_immutable": True,
    },
    {
        "requirement_id": "S3_NO_EXTRA_GRAVITATIONAL_MODES",
        "canonical_requirement_id": "S3_NO_EXTRA_GRAVITATIONAL_MODES",
        "statement_class": "SUPPLIED_STANDARD_PHYSICS_ASSUMPTION",
        "source_class_expected": "SUPPLIED_STANDARD_PHYSICS_ASSUMPTION",
        "authority_subclass": "UNSELECTED_STANDARD_GR_FIELD_CONTENT_ASSUMPTION",
        "native_elimination_allowed": False,
        "native_distinctiveness_allowed": False,
        "class_binding_immutable": True,
    },
]

ACTION_FAMILIES = [dict(row) for row in v0.ACTION_FAMILIES]


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _failure(diagnostic: str, stage: str) -> dict[str, Any]:
    return {
        "entry_point_id": PRODUCTION_ENTRY_POINT_ID,
        "status": "PRECHECK_FAILURE",
        "diagnostic": diagnostic,
        "failed_stage": stage,
        "matrix_evaluated": False,
        "scientific_outcome": None,
        "matching_scientific_outcomes": [],
        "matching_scientific_outcome_count": 0,
    }


def _preflight(value: dict[str, Any]) -> dict[str, Any] | None:
    requirements = value.get("requirements")
    families = value.get("families")
    matrix = value.get("matrix")
    if not isinstance(requirements, list) or not requirements:
        return _failure("REQUIREMENT_INVENTORY_MISSING", "requirement_preflight")
    if not isinstance(families, list) or not families:
        return _failure("FAMILY_ENVELOPE_MISSING", "family_preflight")
    if not isinstance(matrix, dict):
        return _failure("MATRIX_MISSING", "matrix_preflight")

    seen_canonical: set[str] = set()
    seen_requirement_ids: set[str] = set()
    for row in requirements:
        requirement_id = row.get("requirement_id")
        if not requirement_id:
            return _failure("REQUIREMENT_ID_MISSING", "requirement_preflight")
        if requirement_id in seen_requirement_ids:
            return _failure("DUPLICATE_REQUIREMENT_ID", "requirement_preflight")
        seen_requirement_ids.add(requirement_id)
        if "statement_class" not in row:
            return _failure("MISSING_STATEMENT_CLASS", "requirement_preflight")
        statement_class = row["statement_class"]
        if isinstance(statement_class, list):
            return _failure("MULTIPLE_STATEMENT_CLASSES", "requirement_preflight")
        if statement_class not in STATEMENT_CLASSES:
            return _failure("UNKNOWN_STATEMENT_CLASS", "requirement_preflight")
        if row.get("source_class_expected") != statement_class:
            return _failure("STATEMENT_CLASS_SOURCE_CONFLICT", "requirement_preflight")
        canonical = row.get("canonical_requirement_id")
        if not canonical:
            return _failure("CANONICAL_REQUIREMENT_ID_MISSING", "requirement_preflight")
        if canonical in seen_canonical:
            return _failure(
                "DUPLICATE_CANONICAL_REQUIREMENT", "requirement_preflight"
            )
        seen_canonical.add(canonical)
        if (
            value.get("mode", "NATIVE_ONLY") == "NATIVE_ONLY"
            and statement_class == "NEW_PROPOSED_POSTULATE"
        ):
            return _failure("UNAUTHORIZED_NEW_POSTULATE", "requirement_preflight")

    family_ids: list[str] = []
    for family in families:
        family_id = family.get("family_id")
        if not family_id:
            return _failure("FAMILY_ID_MISSING", "family_preflight")
        if family_id in family_ids:
            return _failure("DUPLICATE_FAMILY_ID", "family_preflight")
        family_ids.append(family_id)
        if family.get("envelope_status") not in {
            "PRIMARY_METRIC_LOCAL_ENVELOPE",
            "OUTSIDE_FROZEN_METRIC_ONLY_SCOPE",
            "OUTSIDE_FROZEN_LOCAL_SCOPE",
            "EQUIVALENCE_CONTROL_NOT_SEPARATE_CANDIDATE",
        }:
            return _failure("UNKNOWN_FAMILY_ENVELOPE_STATUS", "family_preflight")

    expected_requirement_ids = {row["requirement_id"] for row in requirements}
    if set(matrix) != expected_requirement_ids:
        return _failure("MATRIX_REQUIREMENT_SHAPE_MISMATCH", "matrix_preflight")
    for requirement_id in expected_requirement_ids:
        cells = matrix[requirement_id]
        if not isinstance(cells, dict) or set(cells) != set(family_ids):
            return _failure("MATRIX_FAMILY_SHAPE_MISMATCH", "matrix_preflight")
        for family_id, cell in cells.items():
            if cell not in MATRIX_CELL_VALUES:
                return _failure("UNKNOWN_MATRIX_CELL_STATE", "matrix_preflight")
            family = next(row for row in families if row["family_id"] == family_id)
            outside = family["envelope_status"].startswith("OUTSIDE_FROZEN_")
            if outside and cell != "OUTSIDE_FROZEN_ENVELOPE":
                return _failure("FAMILY_SCOPE_CELL_CONFLICT", "matrix_preflight")
            if not outside and cell == "OUTSIDE_FROZEN_ENVELOPE":
                return _failure("PRIMARY_FAMILY_SCOPE_CELL_CONFLICT", "matrix_preflight")

    equivalence_map = value.get("equivalence_map", {})
    proofs = value.get("equivalence_proofs", [])
    proof_pairs = {(row["member"], row["representative"]) for row in proofs}
    for member, representative in equivalence_map.items():
        if member not in family_ids or representative not in family_ids:
            return _failure("EQUIVALENCE_FAMILY_UNKNOWN", "equivalence_preflight")
        if (member, representative) not in proof_pairs:
            return _failure("EQUIVALENCE_PROOF_MISSING", "equivalence_preflight")
    return None


def _representative(family_id: str, equivalence_map: dict[str, str]) -> str:
    seen: set[str] = set()
    current = family_id
    while current in equivalence_map:
        if current in seen:
            raise ValueError("equivalence cycle")
        seen.add(current)
        current = equivalence_map[current]
    return current


def _matching_outcomes(summary: dict[str, Any], evidence: dict[str, Any]) -> list[str]:
    affirmative_classes = summary["affirmative_equivalence_classes"]
    unresolved_classes = summary["unresolved_equivalence_classes"]
    possible_count = len(set(affirmative_classes).union(unresolved_classes))
    inconsistent = bool(evidence.get("inconsistent_subset_bound"))
    no_go = bool(evidence.get("distinctiveness_no_go_proved"))
    native_distinctive = bool(evidence.get("native_distinctiveness_demonstrated"))
    discriminator_ids = evidence.get("native_discriminating_requirement_ids", [])
    exhausted = bool(evidence.get("accepted_inventory_exhausted"))
    no_refinement = bool(evidence.get("no_refinement_countermodel_bound"))

    if possible_count == 0:
        if inconsistent:
            return ["REQUIREMENT_SET_INCONSISTENT"]
        if no_go:
            return ["NO_GO_UNDER_MINIMAL_METRIC_LOCAL_ASSUMPTIONS"]
        return []

    unique_complete = len(affirmative_classes) == 1 and not unresolved_classes
    unique_class = affirmative_classes[0] if unique_complete else None
    collapse = unique_complete and unique_class == "F_EH" and not (
        native_distinctive and discriminator_ids
    )
    native_selection = unique_complete and not collapse and bool(
        native_distinctive and discriminator_ids
    )
    if collapse:
        return ["CURRENT_REQUIREMENTS_COLLAPSE_TO_STANDARD_GR"]
    if native_selection:
        return ["NATIVE_PRINCIPLE_SET_SELECTS_ACTION_FAMILY"]
    if exhausted and no_refinement:
        return ["DISTINCTIVE_GRAVITATIONAL_POSTULATE_REQUIRED"]
    return ["ACTION_FAMILY_UNDERDETERMINED"]


def evaluate_analysis(value: dict[str, Any]) -> dict[str, Any]:
    preflight = _preflight(value)
    if preflight is not None:
        return preflight

    requirements = value["requirements"]
    families = value["families"]
    matrix = value["matrix"]
    equivalence_map = value.get("equivalence_map", {})
    evidence = value.get("evidence", {})
    if any(
        cell == "NOT_EVALUATED"
        for cells in matrix.values()
        for cell in cells.values()
    ):
        return {
            "entry_point_id": PRODUCTION_ENTRY_POINT_ID,
            "status": "ANALYSIS_INCOMPLETE",
            "diagnostic": "NOT_EVALUATED_CELL_PRESENT",
            "failed_stage": "matrix_completion",
            "matrix_evaluated": False,
            "scientific_outcome": None,
            "matching_scientific_outcomes": [],
            "matching_scientific_outcome_count": 0,
        }

    primary_ids = [
        row["family_id"]
        for row in families
        if row["envelope_status"] == "PRIMARY_METRIC_LOCAL_ENVELOPE"
    ]
    eliminated: set[str] = set()
    affirmative: set[str] = set()
    unresolved: set[str] = set()
    supplied_exclusion_trace: list[dict[str, str]] = []
    native_elimination_trace: list[dict[str, str]] = []

    for family_id in primary_ids:
        family_eliminated = False
        family_unresolved = False
        all_native_affirmative = True
        for requirement in requirements:
            requirement_id = requirement["requirement_id"]
            cell = matrix[requirement_id][family_id]
            statement_class = requirement["statement_class"]
            if statement_class == "SUPPLIED_STANDARD_PHYSICS_ASSUMPTION":
                if cell == "ELIMINATED":
                    supplied_exclusion_trace.append({
                        "requirement_id": requirement_id,
                        "family_id": family_id,
                    })
                continue
            if statement_class != "PROJECT_BOUND_NATIVE_REQUIREMENT":
                continue
            if cell == "ELIMINATED":
                if not requirement.get("native_elimination_allowed", False):
                    return _failure(
                        "INELIGIBLE_NATIVE_ELIMINATION", "matrix_reduction"
                    )
                family_eliminated = True
                native_elimination_trace.append({
                    "requirement_id": requirement_id,
                    "family_id": family_id,
                })
            elif cell in {
                "NOT_DECIDABLE_FROM_REQUIREMENT",
                "REQUIRES_SUPPLIED_ASSUMPTION",
            }:
                family_unresolved = True
                all_native_affirmative = False
            elif cell in {
                "AFFIRMATIVELY_SATISFIES_REQUIREMENT",
                "EQUIVALENT_UNDER_LOCAL_BULK_RULE",
            }:
                pass
            else:
                all_native_affirmative = False
        if family_eliminated:
            eliminated.add(family_id)
        elif family_unresolved:
            unresolved.add(family_id)
        elif all_native_affirmative:
            affirmative.add(family_id)

    declared_discriminators = evidence.get(
        "native_discriminating_requirement_ids", []
    )
    valid_discriminator_ids = {
        row["requirement_id"]
        for row in requirements
        if row["statement_class"] == "PROJECT_BOUND_NATIVE_REQUIREMENT"
        and row.get("native_distinctiveness_allowed", False)
    }
    eliminated_by_requirement = {
        row["requirement_id"] for row in native_elimination_trace
    }
    if any(
        requirement_id not in valid_discriminator_ids
        or requirement_id not in eliminated_by_requirement
        for requirement_id in declared_discriminators
    ):
        return _failure(
            "INVALID_NATIVE_DISCRIMINATING_TRACE", "distinctiveness_preflight"
        )

    try:
        affirmative_classes = sorted({
            _representative(family_id, equivalence_map)
            for family_id in affirmative
        })
        unresolved_classes = sorted({
            _representative(family_id, equivalence_map)
            for family_id in unresolved
        } - set(affirmative_classes))
    except ValueError:
        return _failure("EQUIVALENCE_CYCLE", "equivalence_reduction")

    summary = {
        "primary_family_ids": primary_ids,
        "eliminated_family_ids": sorted(eliminated),
        "affirmative_family_ids": sorted(affirmative),
        "unresolved_family_ids": sorted(unresolved),
        "affirmative_equivalence_classes": affirmative_classes,
        "unresolved_equivalence_classes": unresolved_classes,
        "native_elimination_trace": native_elimination_trace,
        "supplied_assumption_exclusion_trace": supplied_exclusion_trace,
    }
    matching = _matching_outcomes(summary, evidence)
    if not matching:
        return {
            "entry_point_id": PRODUCTION_ENTRY_POINT_ID,
            "status": "EMPTY_SET_CLASSIFICATION_INSUFFICIENT",
            "diagnostic": "EMPTY_SET_PROOF_CLASSIFICATION_MISSING",
            "failed_stage": "outcome_selection",
            "matrix_evaluated": True,
            "scientific_outcome": None,
            "matching_scientific_outcomes": [],
            "matching_scientific_outcome_count": 0,
            "summary": summary,
        }
    if len(matching) != 1:
        return _failure("OUTCOME_PREDICATE_OVERLAP", "outcome_selection")
    return {
        "entry_point_id": PRODUCTION_ENTRY_POINT_ID,
        "status": "SCIENTIFIC_OUTCOME_COMPUTED",
        "diagnostic": None,
        "failed_stage": None,
        "matrix_evaluated": True,
        "scientific_outcome": matching[0],
        "matching_scientific_outcomes": matching,
        "matching_scientific_outcome_count": 1,
        "summary": summary,
    }


def _synthetic_requirement(
    requirement_id: str,
    *,
    statement_class: str = "PROJECT_BOUND_NATIVE_REQUIREMENT",
    canonical_requirement_id: str | None = None,
    native_elimination_allowed: bool = True,
    include_statement_class: bool = True,
) -> dict[str, Any]:
    row: dict[str, Any] = {
        "requirement_id": requirement_id,
        "canonical_requirement_id": canonical_requirement_id or requirement_id,
        "source_class_expected": statement_class,
        "native_elimination_allowed": native_elimination_allowed,
        "native_distinctiveness_allowed": native_elimination_allowed,
    }
    if include_statement_class:
        row["statement_class"] = statement_class
    return row


def _synthetic_family(family_id: str) -> dict[str, str]:
    return {
        "family_id": family_id,
        "envelope_status": "PRIMARY_METRIC_LOCAL_ENVELOPE",
    }


def _fixture(
    requirements: list[dict[str, Any]],
    family_ids: list[str],
    rows: dict[str, dict[str, str]],
    *,
    equivalence_map: dict[str, str] | None = None,
    evidence: dict[str, Any] | None = None,
) -> dict[str, Any]:
    equivalence_map = equivalence_map or {}
    return {
        "mode": "NATIVE_ONLY",
        "requirements": requirements,
        "families": [_synthetic_family(family_id) for family_id in family_ids],
        "matrix": rows,
        "equivalence_map": equivalence_map,
        "equivalence_proofs": [
            {
                "member": member,
                "representative": representative,
                "proof_class": "BOUNDARY_EQUIVALENT_LOCAL_BULK",
            }
            for member, representative in equivalence_map.items()
        ],
        "evidence": evidence or {},
    }


def run_production_controls() -> dict[str, Any]:
    affirmative = "AFFIRMATIVELY_SATISFIES_REQUIREMENT"
    eliminated = "ELIMINATED"
    undecidable = "NOT_DECIDABLE_FROM_REQUIREMENT"
    controls: list[dict[str, Any]] = []

    native = _synthetic_requirement("R_NATIVE")
    supplied = _synthetic_requirement(
        "S_SECOND_ORDER",
        statement_class="SUPPLIED_STANDARD_PHYSICS_ASSUMPTION",
        native_elimination_allowed=False,
    )
    result = evaluate_analysis(_fixture(
        [native, supplied],
        ["F_EH", "F_FR"],
        {
            "R_NATIVE": {"F_EH": affirmative, "F_FR": affirmative},
            "S_SECOND_ORDER": {"F_EH": affirmative, "F_FR": eliminated},
        },
    ))
    controls.append({
        "control_id": "CTRL_SUPPLIED_SECOND_ORDER_NOT_NATIVE",
        "mutation_count": 1,
        "expected": "ACTION_FAMILY_UNDERDETERMINED",
        "observed": result["scientific_outcome"],
        "entry_point_id": result["entry_point_id"],
        "passed": (
            result["scientific_outcome"] == "ACTION_FAMILY_UNDERDETERMINED"
            and result["summary"]["supplied_assumption_exclusion_trace"]
            == [{"requirement_id": "S_SECOND_ORDER", "family_id": "F_FR"}]
        ),
    })

    missing_class = _synthetic_requirement(
        "R_MISSING", include_statement_class=False
    )
    result = evaluate_analysis(_fixture(
        [missing_class], ["F_EH"], {"R_MISSING": {"F_EH": affirmative}}
    ))
    controls.append({
        "control_id": "CTRL_MISSING_STATEMENT_CLASS",
        "mutation_count": 1,
        "expected": "MISSING_STATEMENT_CLASS",
        "observed": result["diagnostic"],
        "entry_point_id": result["entry_point_id"],
        "passed": result["diagnostic"] == "MISSING_STATEMENT_CLASS"
        and result["matrix_evaluated"] is False,
    })

    duplicate_a = _synthetic_requirement("R_DUP_A", canonical_requirement_id="R_DUP")
    duplicate_b = _synthetic_requirement("R_DUP_B", canonical_requirement_id="R_DUP")
    result = evaluate_analysis(_fixture(
        [duplicate_a, duplicate_b],
        ["F_EH"],
        {
            "R_DUP_A": {"F_EH": affirmative},
            "R_DUP_B": {"F_EH": affirmative},
        },
    ))
    controls.append({
        "control_id": "CTRL_DUPLICATE_REQUIREMENT",
        "mutation_count": 1,
        "expected": "DUPLICATE_CANONICAL_REQUIREMENT",
        "observed": result["diagnostic"],
        "entry_point_id": result["entry_point_id"],
        "passed": result["diagnostic"] == "DUPLICATE_CANONICAL_REQUIREMENT",
    })

    newton = _synthetic_requirement("R_NEWTON")
    result = evaluate_analysis(_fixture(
        [newton],
        ["F_EH", "F_FR"],
        {"R_NEWTON": {"F_EH": affirmative, "F_FR": affirmative}},
    ))
    controls.append({
        "control_id": "CTRL_SHARED_NEWTONIAN_LIMIT",
        "mutation_count": 1,
        "expected": "ACTION_FAMILY_UNDERDETERMINED",
        "observed": result["scientific_outcome"],
        "entry_point_id": result["entry_point_id"],
        "passed": result["scientific_outcome"] == "ACTION_FAMILY_UNDERDETERMINED"
        and len(result["summary"]["affirmative_equivalence_classes"]) == 2,
    })

    result = evaluate_analysis(_fixture(
        [newton],
        ["F_EH", "F_FR"],
        {"R_NEWTON": {"F_EH": affirmative, "F_FR": undecidable}},
    ))
    controls.append({
        "control_id": "CTRL_UNDECIDABLE_CELL",
        "mutation_count": 1,
        "expected": "F_FR_UNRESOLVED_NOT_AFFIRMATIVE",
        "observed": {
            "unresolved": result["summary"]["unresolved_family_ids"],
            "affirmative": result["summary"]["affirmative_family_ids"],
        },
        "entry_point_id": result["entry_point_id"],
        "passed": result["summary"]["unresolved_family_ids"] == ["F_FR"]
        and result["summary"]["affirmative_family_ids"] == ["F_EH"],
    })

    result = evaluate_analysis(_fixture(
        [newton],
        ["F_EH", "F_EH_BOUNDARY"],
        {
            "R_NEWTON": {
                "F_EH": affirmative,
                "F_EH_BOUNDARY": affirmative,
            }
        },
        equivalence_map={"F_EH_BOUNDARY": "F_EH"},
    ))
    controls.append({
        "control_id": "CTRL_BOUNDARY_EQUIVALENCE",
        "mutation_count": 1,
        "expected": "CURRENT_REQUIREMENTS_COLLAPSE_TO_STANDARD_GR",
        "observed": result["scientific_outcome"],
        "entry_point_id": result["entry_point_id"],
        "passed": result["scientific_outcome"]
        == "CURRENT_REQUIREMENTS_COLLAPSE_TO_STANDARD_GR"
        and result["summary"]["affirmative_equivalence_classes"] == ["F_EH"],
    })

    discriminator = _synthetic_requirement("R_DISC")
    result = evaluate_analysis(_fixture(
        [discriminator],
        ["F_EH", "F_FR"],
        {"R_DISC": {"F_EH": affirmative, "F_FR": eliminated}},
    ))
    controls.append({
        "control_id": "CTRL_UNIQUE_NONDISTINCTIVE_EH",
        "mutation_count": 1,
        "expected": "CURRENT_REQUIREMENTS_COLLAPSE_TO_STANDARD_GR",
        "observed": result["scientific_outcome"],
        "entry_point_id": result["entry_point_id"],
        "passed": result["scientific_outcome"]
        == "CURRENT_REQUIREMENTS_COLLAPSE_TO_STANDARD_GR"
        and result["matching_scientific_outcome_count"] == 1,
    })

    result = evaluate_analysis(_fixture(
        [discriminator],
        ["F_NATIVE", "F_ALT"],
        {"R_DISC": {"F_NATIVE": affirmative, "F_ALT": eliminated}},
        evidence={
            "native_distinctiveness_demonstrated": True,
            "native_discriminating_requirement_ids": ["R_DISC"],
        },
    ))
    controls.append({
        "control_id": "CTRL_UNIQUE_NATIVE_DISTINCTIVE",
        "mutation_count": 1,
        "expected": "NATIVE_PRINCIPLE_SET_SELECTS_ACTION_FAMILY",
        "observed": result["scientific_outcome"],
        "entry_point_id": result["entry_point_id"],
        "passed": result["scientific_outcome"]
        == "NATIVE_PRINCIPLE_SET_SELECTS_ACTION_FAMILY"
        and result["matching_scientific_outcome_count"] == 1,
    })

    boundary_probes: list[dict[str, Any]] = []
    multiple_fixture = _fixture(
        [newton],
        ["F_EH", "F_FR"],
        {"R_NEWTON": {"F_EH": affirmative, "F_FR": affirmative}},
    )
    result = evaluate_analysis(multiple_fixture)
    boundary_probes.append({
        "probe_id": "PROBE_UNDERDETERMINED_WITHOUT_EXHAUSTION",
        "expected": "ACTION_FAMILY_UNDERDETERMINED",
        "observed": result["scientific_outcome"],
        "entry_point_id": result["entry_point_id"],
        "passed": result["scientific_outcome"] == "ACTION_FAMILY_UNDERDETERMINED",
    })
    exhausted_fixture = dict(multiple_fixture)
    exhausted_fixture["evidence"] = {
        "accepted_inventory_exhausted": True,
        "no_refinement_countermodel_bound": True,
    }
    result = evaluate_analysis(exhausted_fixture)
    boundary_probes.append({
        "probe_id": "PROBE_POSTULATE_REQUIRED_AFTER_EXHAUSTION",
        "expected": "DISTINCTIVE_GRAVITATIONAL_POSTULATE_REQUIRED",
        "observed": result["scientific_outcome"],
        "entry_point_id": result["entry_point_id"],
        "passed": result["scientific_outcome"]
        == "DISTINCTIVE_GRAVITATIONAL_POSTULATE_REQUIRED",
    })

    return {
        "production_entry_point_id": PRODUCTION_ENTRY_POINT_ID,
        "control_count": len(controls),
        "control_pass_count": sum(row["passed"] for row in controls),
        "controls": controls,
        "boundary_probe_count": len(boundary_probes),
        "boundary_probe_pass_count": sum(row["passed"] for row in boundary_probes),
        "boundary_probes": boundary_probes,
        "all_used_shared_entry_point": all(
            row["entry_point_id"] == PRODUCTION_ENTRY_POINT_ID
            for row in controls + boundary_probes
        ),
    }


def _validate_authority_and_sources() -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for relative_path, expected_hash in AUTHORITY_AND_SOURCE_HASHES.items():
        observed = _sha256((REPO_ROOT / relative_path).read_bytes())
        if observed != expected_hash:
            raise ValueError(f"native-principle v1 packet hash mismatch: {relative_path}")
        rows.append({"relative_path": relative_path, "sha256": observed})

    review = json.loads(
        (
            REPO_ROOT
            / "formal/docs/release/NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_"
            "AND_ACTION_SELECTION_PACKET_REVIEW_20260718_v0.json"
        ).read_text(encoding="utf-8")
    )
    if review.get("verdict") != (
        "BLOCKED_REQUIREMENTS_ACTION_SELECTION_CONTRACT_INCOMPLETE"
    ):
        raise ValueError("v0 requirements packet review verdict mismatch")
    if review.get("selected_next_target") != TARGET:
        raise ValueError("v0 review did not authorize v1 preparation")
    if review["requirement_source_audit"].get("pass_count") != 10:
        raise ValueError("retained requirement source count mismatch")
    if review["family_envelope_audit"].get("family_count") != 7:
        raise ValueError("retained family envelope count mismatch")
    if review["scope"].get("requirements_selection_analysis_executed") is not False:
        raise ValueError("v0 review unexpectedly executed the scientific analysis")

    packet_text = (REPO_ROOT / PACKET_RELATIVE_PATH).read_text(encoding="utf-8")
    for token in (
        "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "PROJECT_BOUND_NATIVE_REQUIREMENT",
        "NOT_DECIDABLE_FROM_REQUIREMENT",
        "These predicates are disjoint by construction",
        "evaluate_analysis(analysis_input)",
        "All controls call `evaluate_analysis`",
        "real matrix cells supplied:",
        "create an automation",
    ):
        if token not in packet_text:
            raise ValueError(f"human v1 packet token missing: {token}")
    return rows


def _validate_v1_contract() -> dict[str, Any]:
    if len(REPAIRED_REQUIREMENTS) != 10:
        raise ValueError("repaired requirement count mismatch")
    if any(row["statement_class"] not in STATEMENT_CLASSES for row in REPAIRED_REQUIREMENTS):
        raise ValueError("repaired requirement statement class mismatch")
    if any(row["statement_class"] != row["source_class_expected"] for row in REPAIRED_REQUIREMENTS):
        raise ValueError("repaired requirement source-class conflict")
    if len({row["canonical_requirement_id"] for row in REPAIRED_REQUIREMENTS}) != 10:
        raise ValueError("repaired requirement canonical identity mismatch")
    if len(SUPPLIED_ASSUMPTIONS) != 3 or any(
        row["native_elimination_allowed"] or row["native_distinctiveness_allowed"]
        for row in SUPPLIED_ASSUMPTIONS
    ):
        raise ValueError("supplied-assumption native firewall mismatch")
    if len(MATRIX_CELL_VALUES) != 7 or len(set(MATRIX_CELL_VALUES)) != 7:
        raise ValueError("v1 matrix vocabulary mismatch")
    if len(SCIENTIFIC_OUTCOMES) != 6 or len(set(SCIENTIFIC_OUTCOMES)) != 6:
        raise ValueError("scientific outcome vocabulary mismatch")
    controls = run_production_controls()
    if controls["control_count"] != 8 or controls["control_pass_count"] != 8:
        raise ValueError("not all production controls passed")
    if controls["boundary_probe_count"] != 2 or controls["boundary_probe_pass_count"] != 2:
        raise ValueError("outcome boundary probes failed")
    if not controls["all_used_shared_entry_point"]:
        raise ValueError("control path bypassed production evaluator")
    return controls


def build_packet() -> dict[str, Any]:
    authority = _validate_authority_and_sources()
    control_results = _validate_v1_contract()
    tool_path = Path(__file__).resolve()
    test_path = REPO_ROOT / TEST_RELATIVE_PATH
    if not test_path.exists():
        raise ValueError("native-principle v1 packet focused test missing")

    return {
        "schema_id": (
            "NATIVE_GRAVITATIONAL_PRINCIPLE_REQUIREMENTS_AND_ACTION_SELECTION_"
            "PACKET_20260718_v1"
        ),
        "captured_at_utc": "2026-07-18T00:00:00Z",
        "target": TARGET,
        "verdict": "PREPARED_PENDING_INDEPENDENT_REVIEW",
        "selected_next_target": SELECTED_NEXT_TARGET,
        "selected_next_target_kind": (
            "INDEPENDENT_REQUIREMENTS_ACTION_SELECTION_PACKET_V1_REVIEW_ONLY"
        ),
        "authority": {
            "v0_review_verdict": (
                "BLOCKED_REQUIREMENTS_ACTION_SELECTION_CONTRACT_INCOMPLETE"
            ),
            "retained_requirement_sources": 10,
            "retained_comparison_families": 7,
            "frozen_inputs": authority,
            "generator": {
                "relative_path": tool_path.relative_to(REPO_ROOT).as_posix(),
                "sha256": _sha256(tool_path.read_bytes()),
            },
            "test": {
                "relative_path": TEST_RELATIVE_PATH,
                "sha256": _sha256(test_path.read_bytes()),
            },
        },
        "repair_contract": {
            "repair_count": 4,
            "repairs": [
                "per-row immutable three-way statement class binding",
                "explicit completed-analysis undecidability matrix state",
                "disjoint six-outcome production predicates",
                "shared bounded production evaluator for controls and later analysis",
            ],
            "v0_sources_or_families_changed": False,
        },
        "statement_class_contract": {
            "class_count": len(STATEMENT_CLASSES),
            "classes": STATEMENT_CLASSES,
            "repaired_requirement_count": len(REPAIRED_REQUIREMENTS),
            "rows": REPAIRED_REQUIREMENTS,
            "all_rows_bind_exactly_one_class": True,
            "all_rows_source_class_compatible": True,
            "supplied_assumption_count": len(SUPPLIED_ASSUMPTIONS),
            "supplied_assumptions": SUPPLIED_ASSUMPTIONS,
            "supplied_assumptions_affect_native_elimination": False,
            "supplied_assumptions_affect_native_distinctiveness": False,
            "active_new_postulate_count": 0,
        },
        "comparison_family_envelope": {
            "family_count": len(ACTION_FAMILIES),
            "rows": ACTION_FAMILIES,
            "family_adopted_or_activated_count": 0,
            "unchanged_from_v0": True,
        },
        "matrix_contract": {
            "cell_value_count": len(MATRIX_CELL_VALUES),
            "cell_values": MATRIX_CELL_VALUES,
            "undecidable_is_affirmative": False,
            "undecidable_is_elimination": False,
            "undecidable_is_not_evaluated": False,
            "not_evaluated_blocks_scientific_outcome": True,
            "real_matrix_row_count": 10,
            "real_matrix_column_count": 7,
            "real_matrix_cell_count": 70,
            "real_matrix_cells_supplied_by_preparation": 0,
        },
        "production_evaluator_contract": {
            "entry_point": "evaluate_analysis",
            "entry_point_id": PRODUCTION_ENTRY_POINT_ID,
            "stages": [
                "requirement and statement-class preflight",
                "family envelope preflight",
                "matrix shape and cell preflight",
                "supplied-assumption exclusion from native selection",
                "local-bulk equivalence reduction",
                "eliminated affirmative and unresolved set computation",
                "native discriminating trace validation",
                "distinctiveness and exhaustion evidence validation",
                "disjoint scientific outcome selection",
            ],
            "scientific_outcome_count": len(SCIENTIFIC_OUTCOMES),
            "scientific_outcomes": SCIENTIFIC_OUTCOMES,
            "internal_result_count": len(INTERNAL_RESULTS),
            "internal_results": INTERNAL_RESULTS,
            "exactly_one_scientific_outcome_when_computed": True,
            "general_symbolic_algebra_or_theory_enumeration": False,
        },
        "control_execution": control_results,
        "retained_equivalence_contract": {
            "allowed_rules": v0.EQUIVALENCE_RULES,
            "forbidden_equivalences": v0.FORBIDDEN_EQUIVALENCES,
            "claim_scope": "LOCAL_BULK_ONLY",
            "proof_required_per_equivalence": True,
        },
        "standard_GR_isolation": {
            "Einstein_Hilbert_role": "COMPARISON_ORACLE_ONLY",
            "supplied_second_order_assumption_is_native": False,
            "supplied_assumption_eliminations_change_native_sets": False,
            "comparator_activated": False,
        },
        "outcome_exclusivity_contract": {
            "unique_nondistinctive_EH": (
                "CURRENT_REQUIREMENTS_COLLAPSE_TO_STANDARD_GR"
            ),
            "unique_native_distinctive": (
                "NATIVE_PRINCIPLE_SET_SELECTS_ACTION_FAMILY"
            ),
            "multiple_without_exhaustion": "ACTION_FAMILY_UNDERDETERMINED",
            "multiple_with_exhaustion_and_no_refinement_proof": (
                "DISTINCTIVE_GRAVITATIONAL_POSTULATE_REQUIRED"
            ),
            "inconsistency_requires_bound_inconsistent_subset": True,
            "no_go_requires_bound_distinctiveness_impossibility_proof": True,
            "overlap_is_production_failure": True,
        },
        "retained_boundaries": {
            "minimal_gravitational_contract": "ACCEPTED",
            "native_candidate_readiness": "BLOCKED_NO_NATIVE_GRAVITATIONAL_PRINCIPLE",
            "real_survivor_matrix": "NOT_COMPUTED",
            "native_gravitational_principle": "NOT_IDENTIFIED",
            "new_postulate": "NOT_AUTHORIZED",
            "gravitational_action": "NOT_PROPOSED_OR_SELECTED",
            "matter_sector": "NOT_SELECTED",
            "standard_GR_comparator": "NOT_ACTIVATED",
            "metric_variation": "NOT_EXECUTED",
            "gravitomagnetic_recovery": "BLOCKED_UPSTREAM",
            "C_k": "EXTERNAL_ADMISSIBILITY_AUDIT_ONLY",
        },
        "scope": {
            "packet_preparation_only": True,
            "synthetic_production_controls_executed": True,
            "independent_v1_review_executed": False,
            "real_requirements_family_analysis_executed": False,
            "real_survivor_matrix_computed": False,
            "real_scientific_outcome_selected": False,
            "native_gravitational_principle_identified": False,
            "new_postulate_authorized": False,
            "gravitational_action_proposed_or_selected": False,
            "real_action_family_eliminated_or_adopted": False,
            "matter_sector_selected": False,
            "standard_GR_comparator_activated": False,
            "metric_or_tetrad_variation_executed": False,
            "stress_energy_derived": False,
            "tensor_field_equation_derived": False,
            "recovery_ladder_entered": False,
            "gravitomagnetic_route_reopened": False,
            "C_k_embedded_or_varied": False,
            "symbolic_restoration_reopened": False,
            "unrestricted_theory_enumeration_created": False,
            "simulation_executed": False,
            "empirical_analysis_executed": False,
            "master_action_promoted": False,
            "GR_pillar_completed": False,
            "seam_closed": False,
            "automation_created": False,
        },
        "claim_ceiling": (
            "Prepared v1 contract repair only. Ten requirement classes, three supplied "
            "assumption firewalls, seven epistemically distinct matrix states, disjoint "
            "outcome logic, eight production controls, and two boundary probes are "
            "validated through one bounded table evaluator using synthetic fixtures. "
            "The real ten-by-seven matrix is untouched. No real family judgment, "
            "principle, postulate, action, matter sector, variation, GR result, general "
            "tooling lane, or automation is created."
        ),
    }


def artifact_bytes() -> bytes:
    return (
        json.dumps(build_packet(), indent=2, sort_keys=True, ensure_ascii=True) + "\n"
    ).encode("utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    report_path = REPO_ROOT / REPORT_RELATIVE_PATH
    raw = artifact_bytes()
    if args.check:
        if not report_path.exists() or report_path.read_bytes() != raw:
            raise SystemExit("native-principle v1 packet is stale or missing")
        report = json.loads(raw)
        print(json.dumps({
            "boundary_probes": report["control_execution"]["boundary_probe_pass_count"],
            "controls": report["control_execution"]["control_pass_count"],
            "real_matrix_cells": report["matrix_contract"]["real_matrix_cells_supplied_by_preparation"],
            "status": "CHECKED",
            "verdict": report["verdict"],
        }, sort_keys=True))
        return 0
    report_path.write_bytes(raw)
    print(report_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

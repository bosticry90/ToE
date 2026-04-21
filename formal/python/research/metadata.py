from __future__ import annotations

from dataclasses import dataclass


PRIMARY_CLASSES = (
    "SUPPORT_ONLY_RESEARCH_ARTIFACT",
    "SCIENTIFIC_DELTA_RESEARCH_ARTIFACT",
    "SANDBOX_CANDIDATE_RESEARCH_ARTIFACT",
)

ALLOWED_TEST_TYPES = {
    "DERIVATION",
    "REDUCTION_CHECK",
    "SIMULATION",
    "COUNTEREXAMPLE_SEARCH",
    "NOTATION_REPAIR",
    "DESIGN_ONLY",
}

ALLOWED_OUTPUT_KINDS = {
    "DERIVATION_NOTE",
    "RESULT_SUMMARY",
    "SIMULATION_ARTIFACT",
    "COUNTEREXAMPLE",
    "RETAIN",
    "PRUNE",
    "INCONCLUSIVE",
}

ALLOWED_TARGET_KINDS = {"PILLAR", "SEAM", "MASTER_ACTION", "NONE"}
ALLOWED_PROMOTABILITY = {
    "NOT_READY",
    "READY_FOR_SANDBOX_REVIEW",
    "READY_FOR_PROMOTION_REVIEW",
    "REJECTED_FROM_PROMOTION",
}
ALLOWED_ASSUMPTION_STABILITY = {"LOW", "MEDIUM", "HIGH"}
ALLOWED_ARTIFACT_NATURE = {"NUMERICAL", "SYMBOLIC", "STRUCTURAL", "MIXED"}
ALLOWED_FORMALIZATION_ROUTE = {
    "PYTHON_FIRST",
    "LEAN4_FIRST",
    "PYTHON_THEN_LEAN4",
    "DEFER_FORMALIZATION",
}


@dataclass(frozen=True)
class ResearchArtifactMetadata:
    artifact_id: str
    research_object: str
    research_question: str
    test_type: str
    output_kind: str
    target_kind: str
    target_binding: str
    delta_class: str
    contradiction_context: str
    provenance_family: str
    assumptions: tuple[str, ...]
    regime_scope: str
    numerical_provenance: str
    assumption_stability: str
    artifact_nature: str
    formalization_route: str
    route_justification: str
    lean_candidate_target: str
    lean_module_target: str
    nonclaim_boundary: str
    promotability: str


def _is_none_token(value: str) -> bool:
    return value.strip() in {"", "NONE"}


def _has_assumptions(assumptions: tuple[str, ...]) -> bool:
    return any(item.strip() for item in assumptions)


def validate_research_metadata(metadata: ResearchArtifactMetadata) -> list[str]:
    errors: list[str] = []
    if not metadata.artifact_id.strip():
        errors.append("artifact_id is required")
    if not metadata.research_object.strip():
        errors.append("research_object is required")
    if not metadata.research_question.strip():
        errors.append("research_question is required")
    if metadata.test_type not in ALLOWED_TEST_TYPES:
        errors.append(f"test_type must be one of {sorted(ALLOWED_TEST_TYPES)}")
    if metadata.output_kind not in ALLOWED_OUTPUT_KINDS:
        errors.append(f"output_kind must be one of {sorted(ALLOWED_OUTPUT_KINDS)}")
    if metadata.target_kind not in ALLOWED_TARGET_KINDS:
        errors.append(f"target_kind must be one of {sorted(ALLOWED_TARGET_KINDS)}")
    if metadata.promotability not in ALLOWED_PROMOTABILITY:
        errors.append(f"promotability must be one of {sorted(ALLOWED_PROMOTABILITY)}")
    if metadata.assumption_stability not in ALLOWED_ASSUMPTION_STABILITY:
        errors.append(f"assumption_stability must be one of {sorted(ALLOWED_ASSUMPTION_STABILITY)}")
    if metadata.artifact_nature not in ALLOWED_ARTIFACT_NATURE:
        errors.append(f"artifact_nature must be one of {sorted(ALLOWED_ARTIFACT_NATURE)}")
    if metadata.formalization_route not in ALLOWED_FORMALIZATION_ROUTE:
        errors.append(f"formalization_route must be one of {sorted(ALLOWED_FORMALIZATION_ROUTE)}")
    if not metadata.provenance_family.strip():
        errors.append("provenance_family is required")
    if not _has_assumptions(metadata.assumptions):
        errors.append("assumptions must declare at least one bounded assumption")
    if not metadata.regime_scope.strip():
        errors.append("regime_scope is required")
    if not metadata.route_justification.strip():
        errors.append("route_justification is required")
    if not metadata.nonclaim_boundary.strip():
        errors.append("nonclaim_boundary is required")
    if metadata.target_kind == "NONE" and not _is_none_token(metadata.target_binding):
        errors.append("target_binding must be NONE when target_kind is NONE")
    if metadata.target_kind != "NONE" and _is_none_token(metadata.target_binding):
        errors.append("target_binding is required when target_kind is not NONE")
    if metadata.artifact_nature == "NUMERICAL" and _is_none_token(metadata.numerical_provenance):
        errors.append("numerical_provenance is required for NUMERICAL artifacts")
    if metadata.formalization_route == "LEAN4_FIRST":
        if metadata.assumption_stability != "HIGH":
            errors.append("LEAN4_FIRST requires HIGH assumption_stability")
        if metadata.artifact_nature not in {"SYMBOLIC", "STRUCTURAL", "MIXED"}:
            errors.append("LEAN4_FIRST requires SYMBOLIC, STRUCTURAL, or MIXED artifact_nature")
        if _is_none_token(metadata.lean_module_target):
            errors.append("LEAN4_FIRST requires lean_module_target")
    if metadata.formalization_route in {"LEAN4_FIRST", "PYTHON_THEN_LEAN4"}:
        if _is_none_token(metadata.lean_candidate_target) and _is_none_token(metadata.lean_module_target):
            errors.append(
                "formalization routes that involve Lean require lean_candidate_target or lean_module_target"
            )
    if metadata.formalization_route == "DEFER_FORMALIZATION" and (
        not _is_none_token(metadata.lean_candidate_target) or not _is_none_token(metadata.lean_module_target)
    ):
        errors.append("DEFER_FORMALIZATION may not declare Lean targets")
    return errors


def ensure_valid_research_metadata(metadata: ResearchArtifactMetadata) -> None:
    errors = validate_research_metadata(metadata)
    if errors:
        raise ValueError("; ".join(errors))


def recommend_formalization_route(metadata: ResearchArtifactMetadata) -> str:
    if metadata.assumption_stability == "LOW" and metadata.test_type in {"DESIGN_ONLY", "NOTATION_REPAIR"}:
        return "DEFER_FORMALIZATION"
    if metadata.artifact_nature == "NUMERICAL" and metadata.assumption_stability != "HIGH":
        return "PYTHON_FIRST"
    if metadata.artifact_nature == "STRUCTURAL" and metadata.assumption_stability == "HIGH":
        return "LEAN4_FIRST"
    if metadata.assumption_stability == "LOW":
        return "DEFER_FORMALIZATION"
    return "PYTHON_THEN_LEAN4"


def classify_research_artifact(metadata: ResearchArtifactMetadata) -> str:
    if validate_research_metadata(metadata):
        return "SUPPORT_ONLY_RESEARCH_ARTIFACT"

    has_delta = metadata.delta_class.strip() not in {"", "NONE"}
    has_target_binding = metadata.target_kind != "NONE" and metadata.target_binding.strip() not in {"", "NONE"}
    has_contradiction_context = metadata.contradiction_context.strip() not in {"", "NONE"}

    if not has_delta or not has_target_binding:
        return "SUPPORT_ONLY_RESEARCH_ARTIFACT"
    if has_contradiction_context and metadata.promotability in {"READY_FOR_SANDBOX_REVIEW", "READY_FOR_PROMOTION_REVIEW"}:
        return "SANDBOX_CANDIDATE_RESEARCH_ARTIFACT"
    return "SCIENTIFIC_DELTA_RESEARCH_ARTIFACT"
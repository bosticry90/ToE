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
    nonclaim_boundary: str
    promotability: str


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
    if not metadata.provenance_family.strip():
        errors.append("provenance_family is required")
    if not metadata.nonclaim_boundary.strip():
        errors.append("nonclaim_boundary is required")
    return errors


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
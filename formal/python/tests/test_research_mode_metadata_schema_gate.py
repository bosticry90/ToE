from __future__ import annotations

from formal.python.research.metadata import ResearchArtifactMetadata, classify_research_artifact, validate_research_metadata


def test_research_metadata_defaults_to_support_only_without_delta_or_target() -> None:
    metadata = ResearchArtifactMetadata(
        artifact_id="research_support_only_demo",
        research_object="toy equation",
        research_question="Does the notation need normalization?",
        test_type="NOTATION_REPAIR",
        output_kind="INCONCLUSIVE",
        target_kind="NONE",
        target_binding="NONE",
        delta_class="NONE",
        contradiction_context="NONE",
        provenance_family="demo_family",
        nonclaim_boundary="Repository-local research artifact only.",
        promotability="NOT_READY",
    )

    assert validate_research_metadata(metadata) == []
    assert classify_research_artifact(metadata) == "SUPPORT_ONLY_RESEARCH_ARTIFACT"


def test_research_metadata_marks_scientific_delta_when_target_and_delta_are_present() -> None:
    metadata = ResearchArtifactMetadata(
        artifact_id="research_scientific_delta_demo",
        research_object="linearized seam ansatz",
        research_question="Does the bridge preserve the declared dispersion relation?",
        test_type="REDUCTION_CHECK",
        output_kind="RESULT_SUMMARY",
        target_kind="SEAM",
        target_binding="ROW-SEAM-QM-STAT-001",
        delta_class="DISPERSION_PRESERVATION_CHECK",
        contradiction_context="NONE",
        provenance_family="qm_stat_research_demo",
        nonclaim_boundary="Repository-local research artifact only.",
        promotability="NOT_READY",
    )

    assert validate_research_metadata(metadata) == []
    assert classify_research_artifact(metadata) == "SCIENTIFIC_DELTA_RESEARCH_ARTIFACT"


def test_research_metadata_marks_sandbox_candidate_when_ready_and_contradiction_context_exists() -> None:
    metadata = ResearchArtifactMetadata(
        artifact_id="research_sandbox_candidate_demo",
        research_object="master-action transport residual toy model",
        research_question="Can one bounded correction remove the residual in a local limit?",
        test_type="DERIVATION",
        output_kind="RETAIN",
        target_kind="MASTER_ACTION",
        target_binding="MASTER_ACTION_PACKET_01",
        delta_class="LOCAL_TRANSPORT_BINDING_RECOVERY",
        contradiction_context="formal/output/reports/science_maturity_contradiction_report_20260416_v0.json",
        provenance_family="master_action_research_demo",
        nonclaim_boundary="Repository-local research artifact only.",
        promotability="READY_FOR_SANDBOX_REVIEW",
    )

    assert validate_research_metadata(metadata) == []
    assert classify_research_artifact(metadata) == "SANDBOX_CANDIDATE_RESEARCH_ARTIFACT"


def test_research_metadata_validation_rejects_unknown_enums() -> None:
    metadata = ResearchArtifactMetadata(
        artifact_id="broken_demo",
        research_object="equation",
        research_question="question",
        test_type="UNKNOWN",
        output_kind="RESULT_SUMMARY",
        target_kind="PILLAR",
        target_binding="ROW-PILLAR-STAT-001",
        delta_class="LOCAL_CHECK",
        contradiction_context="NONE",
        provenance_family="family",
        nonclaim_boundary="Repository-local research artifact only.",
        promotability="NOT_READY",
    )

    errors = validate_research_metadata(metadata)
    assert errors
    assert classify_research_artifact(metadata) == "SUPPORT_ONLY_RESEARCH_ARTIFACT"
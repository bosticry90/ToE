from formal.python.tools.bounded_program_governance import scope_hash
from formal.python.toe.calculations.calc_toe_repository_wide_native_hypothesis_evidence_census_bounded_program_preparation_v0 import (
    build,
)
from formal.python.tools.toe_repository_wide_native_hypothesis_evidence_census_bounded_program_preparation_result_review import (
    build as build_review,
)


def test_proposal_is_five_stage_zero_repair_and_unopened() -> None:
    result = build()
    proposal = result["program_proposal"]
    assert proposal["proposal_only"] is True
    assert proposal["installed"] is False
    assert proposal["authorized"] is False
    assert proposal["open_event_created"] is False
    assert proposal["authorized_stage_count_proposed"] == 5
    assert proposal["repair_attempt_count_proposed"] == 0
    assert proposal["no_subsidiary_scientific_targets_proposed"] is True
    assert len(proposal["semantic_stages_proposed"]) == 5


def test_all_proposed_stage_scope_hashes_recompute() -> None:
    stages = build()["program_proposal"]["semantic_stages_proposed"]
    assert all(
        stage["canonical_scope_hash"] == scope_hash(stage["canonical_scope"])
        for stage in stages
    )


def test_archive_discovery_is_not_archive_adoption() -> None:
    result = build()
    proposal = result["program_proposal"]
    boundary = result["claim_boundary"]
    assert proposal["custody_contract"]["archive_is_read_only"] is True
    assert (
        proposal["custody_contract"]["whole_documents_not_promoted_automatically"]
        is True
    )
    assert boundary["archive_material_adopted"] is False
    assert boundary["repository_wide_census_performed"] is False


def test_stage_5_selects_but_does_not_execute() -> None:
    proposal = build()["program_proposal"]
    assert (
        proposal["transition_rules"][
            "stage_5_selects_but_does_not_execute_next_hypothesis"
        ]
        is True
    )
    assert proposal["transition_rules"]["no_automatic_successor"] is True


def test_independent_review_accepts_proposal_only() -> None:
    review = build_review()
    assert review["accepted"] is True
    assert not review["failed_checks"]
    assert all(review["checks"].values())
    assert review["program_installed"] is False
    assert review["stage_1_opened"] is False

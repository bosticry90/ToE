from __future__ import annotations

import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root

REPO_ROOT = find_repo_root(Path(__file__))
STANDARD_PATH = (
    REPO_ROOT
    / "formal"
    / "docs"
    / "release"
    / "PUBLIC_SUBMISSION_AI_HYGIENE_STANDARD_v0.md"
)
REPORT_PATH = (
    REPO_ROOT
    / "formal"
    / "output"
    / "reports"
    / "public_submission_ai_hygiene_v0.json"
)
README_PATH = REPO_ROOT / "README.md"
STATE_PATH = REPO_ROOT / "State_of_the_Theory.md"
ROADMAP_PATH = REPO_ROOT / "formal" / "docs" / "paper" / "PHYSICS_ROADMAP_v0.md"
SCALAR_REFS_PATH = (
    REPO_ROOT / "formal" / "docs" / "submission" / "scalar_paper1" / "refs.bib"
)

POLICY_SENTENCE = (
    "External science inputs may create benchmark pressure, caution notes, or future "
    "target categories, but they do not discharge theorem gaps, validate the master "
    "action, close seams, or promote ToE status without repo-local proof objects and "
    "verified primary sources."
)

EXPECTED_LIVE_TARGET = (
    "CURRENT_LIVE_NEXT_TARGET_v0: "
    "execute_qft_gr_weak_strong_conservation_comparison_scope_assumption_reduction_attempt"
)
POST_MR_LIVE_TARGET = (
    "CURRENT_LIVE_NEXT_TARGET_v0: "
    "execute_qft_gr_minimal_working_model_conservation_retest_attempt_after_post_retest_refinement"
)

FORBIDDEN_META_MARKERS = [
    "As an AI language model",
    "Here is a revised version",
    "Would you like me to",
    "I can revise this",
]

FORBIDDEN_PROMOTION_PHRASES = [
    "proves the ToE",
    "confirms the ToE",
    "validates the master action",
    "closes seams",
    "Phase 2 authorized",
]


def _read(path: Path) -> str:
    assert path.exists(), f"Missing required file: {path}"
    return path.read_text(encoding="utf-8")


def _read_json(path: Path) -> dict:
    return json.loads(_read(path))


def test_public_submission_hygiene_standard_and_report_exist() -> None:
    assert STANDARD_PATH.exists()
    assert REPORT_PATH.exists()


def test_public_submission_hygiene_standard_has_required_scope_and_policy() -> None:
    text = _read(STANDARD_PATH)
    required = [
        "PUBLIC_SUBMISSION_AI_HYGIENE_STANDARD_STATUS_v0: PREPARED_NONCLAIM",
        "NONCLAIM_BENCHMARK_INTAKE_AND_PUBLIC_SUBMISSION_HYGIENE_TRANCHE_PREPARED_WITH_NO_THEOREM_DISCHARGE_OR_PROMOTION",
        "README.md",
        "State_of_the_Theory.md",
        "formal/docs/paper/PHYSICS_ROADMAP_v0.md",
        "formal/docs/submission/scalar_paper1/**/*.{md,tex,bib,json}",
        "No public-facing submission surface may contain leftover AI meta-commentary.",
        POLICY_SENTENCE,
    ]
    for marker in required:
        assert marker in text, f"Missing hygiene marker: {marker}"


def test_public_submission_hygiene_report_schema_and_no_promotion_flags() -> None:
    payload = _read_json(REPORT_PATH)

    assert payload["report_id"] == "public_submission_ai_hygiene_v0"
    assert payload["report_status"] == "SUCCESS"
    assert payload["claim_status"] == "PUBLIC_SUBMISSION_HYGIENE_NONCLAIM"
    assert payload["formal_impact"] == "NO_THEOREM_DISCHARGE"
    assert payload["scope_expanded_to_all_docs"] is False
    assert payload["policy_sentence"] == POLICY_SENTENCE
    assert payload["current_live_next_target_unchanged_required"] is True

    for flag_value in payload["forbidden_promotion_flags"].values():
        assert flag_value is False

    for flag_value in payload["nonclaim_boundary"].values():
        assert flag_value is True


def test_release_facing_surfaces_do_not_contain_basic_ai_meta_markers() -> None:
    paths = [STANDARD_PATH, README_PATH, STATE_PATH, ROADMAP_PATH]
    for path in paths:
        text = _read(path)
        for marker in FORBIDDEN_META_MARKERS:
            assert marker not in text, f"{path} contains forbidden AI marker: {marker}"


def test_new_hygiene_surfaces_avoid_prohibited_promotion_language() -> None:
    combined = _read(STANDARD_PATH) + "\n" + _read(REPORT_PATH)
    for phrase in FORBIDDEN_PROMOTION_PHRASES:
        assert phrase not in combined, f"Forbidden promotion phrase present: {phrase}"


def test_scalar_submission_refs_remain_parseable_and_present() -> None:
    refs = _read(SCALAR_REFS_PATH)
    assert refs.count("@") >= 1
    assert "toescalarroute" in refs
    assert "schrodinger1926" in refs


def test_current_live_target_is_unchanged_in_public_authority_surfaces() -> None:
    assert EXPECTED_LIVE_TARGET in _read(README_PATH) or POST_MR_LIVE_TARGET in _read(
        README_PATH
    )
    assert EXPECTED_LIVE_TARGET in _read(STATE_PATH) or POST_MR_LIVE_TARGET in _read(
        STATE_PATH
    )
    assert EXPECTED_LIVE_TARGET in _read(ROADMAP_PATH) or POST_MR_LIVE_TARGET in _read(
        ROADMAP_PATH
    )

from __future__ import annotations

import argparse
import json
from pathlib import Path

from formal.python.meta.repo_environment import find_repo_root


REPO_ROOT = find_repo_root(Path(__file__))
REGISTRY_PATH = (
    REPO_ROOT / "formal" / "docs" / "release" / "LOOP_CONTROL_REGISTRY_v0.json"
)

OLD_EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "ToeNativeHypothesisFrontierSelectionResultReview.lean"
)
NEW_EVIDENCE = (
    "formal/toe_formal/ToeFormal/Derivation/"
    "ToeNativeCoherenceOntologyAndRepresentationBoundedProgram"
    "PreparationResultReview.lean"
)
OLD_REPORT = (
    "formal/docs/release/"
    "TOE_NATIVE_HYPOTHESIS_FRONTIER_SELECTION_RESULT_REVIEW_20260729_v0.json"
)
NEW_REPORT = (
    "formal/docs/release/"
    "TOE_NATIVE_COHERENCE_ONTOLOGY_AND_REPRESENTATION_"
    "BOUNDED_PROGRAM_PREPARATION_RESULT_REVIEW_20260729_v0.json"
)
OLD_OUTCOME = "SELECT_CCFT_COHERENCE_ONTOLOGY_AND_REPRESENTATION"
NEW_OUTCOME = (
    "COHERENCE_ONTOLOGY_AND_REPRESENTATION_BOUNDED_PROGRAM_"
    "PREPARED_NOT_INSTALLED_OR_OPEN"
)
OLD_STRICT_OUTCOME = (
    "PROGRAM_PREPARATION_ONLY_NO_PROGRAM_INSTALLATION_FIELD_ACTION_"
    "SEAM_PILLAR_OR_EMPIRICAL_CLAIM"
)
NEW_STRICT_OUTCOME = (
    "PROGRAM_PROPOSAL_COMPLETE_NO_REPRESENTATION_FIELD_ACTION_SEAM_"
    "PILLAR_OBSERVABLE_OR_EMPIRICAL_CLAIM"
)
OLD_REPORT_SHA256 = (
    "2bcce2cbde4d0e94f47735e163482c1d05a1d0677ccfce29b89d1f72a6507cda"
)
NEW_REPORT_SHA256 = (
    "4e890a575897e5196a1327515f3229e4a9c504a355acf2cea5b5ed261721d574"
)
OLD_QUEUE_SCOPE = (
    "prepare one bounded coherence ontology and representation program "
    "proposal plus its separate lifecycle-safe governance prerequisite"
)
NEW_QUEUE_SCOPE = (
    "prepared one bounded coherence ontology and representation program "
    "proposal; await separate maintenance and scientific authority decisions "
    "before installation or OPEN"
)
OLD_CLAIM_STATUS = (
    "selected native coherence ontology and representation program preparation "
    "only; no program installation or scientific stage opening"
)
NEW_CLAIM_STATUS = (
    "bounded coherence ontology and representation program proposal prepared; "
    "no installation, authorization, OPEN event, representation, field, "
    "action, seam, pillar, observable, or empirical claim"
)

REPLACEMENTS = (
    (OLD_EVIDENCE, NEW_EVIDENCE, 8),
    (OLD_REPORT, NEW_REPORT, 10),
    (OLD_OUTCOME, NEW_OUTCOME, 8),
    (OLD_STRICT_OUTCOME, NEW_STRICT_OUTCOME, 8),
    (OLD_REPORT_SHA256, NEW_REPORT_SHA256, 2),
    (OLD_QUEUE_SCOPE, NEW_QUEUE_SCOPE, 2),
    (OLD_CLAIM_STATUS, NEW_CLAIM_STATUS, 2),
)


def _validate_json(text: str) -> None:
    value = json.loads(text)
    if not isinstance(value, dict):
        raise ValueError("registry must remain a JSON object")


def write_projection() -> None:
    text = REGISTRY_PATH.read_text(encoding="utf-8")
    for old, new, count in REPLACEMENTS:
        actual = text.count(old)
        if actual != count:
            raise ValueError(
                f"registry source count mismatch for {old!r}: "
                f"expected {count}, got {actual}"
            )
        text = text.replace(old, new)
    _validate_json(text)
    REGISTRY_PATH.write_text(text, encoding="utf-8", newline="\n")


def check_projection() -> None:
    text = REGISTRY_PATH.read_text(encoding="utf-8")
    _validate_json(text)
    for old, new, count in REPLACEMENTS:
        if old in text:
            raise ValueError(f"stale registry projection value remains: {old}")
        actual = text.count(new)
        if actual != count:
            raise ValueError(
                f"registry projected count mismatch for {new!r}: "
                f"expected {count}, got {actual}"
            )


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Project the accepted coherence-program preparation review onto "
            "the current registry without rotating scientific authority."
        )
    )
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.write:
        write_projection()
        print("wrote coherence-program preparation registry projection")
    else:
        check_projection()
        print("coherence-program preparation registry projection: OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

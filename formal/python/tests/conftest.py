"""Cumulative-checkout fixtures for preserved historical stage tests."""

from __future__ import annotations

import importlib
import re
from pathlib import Path

import pytest

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tests.historical_stage_state import (
    historical_path_presence_overlay,
)


REPO_ROOT = find_repo_root(Path(__file__))
EOTWASH_EXTERNAL_CUSTODY_ROOT = (
    REPO_ROOT / "formal/data/eotwash_2020_primary_evidence_acquisition_v0"
)
EOTWASH_REPLAY_ONLY_TESTS = {
    (
        "test_eotwash_2020_yukawa_primary_evidence_custody_acquisition_v0.py::"
        "test_execution_regenerates_exactly_and_freezes_authority_and_"
        "acquired_objects"
    ),
    (
        "test_eotwash_2020_yukawa_primary_evidence_custody_acquisition_"
        "result_review_v0.py::"
        "test_review_regenerates_and_freezes_execution_and_raw_custody"
    ),
}
MECHANISM_OUTPUT_ROOT = (
    "formal/output/dirac_maxwell_instrumented_r13_mechanism_v0"
)
FREEZE_REVIEW_PATHS = {
    0: (
        "formal/docs/release/"
        "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
        "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_NUMERICAL_FREEZE_PACKET_"
        "REVIEW_20260715_v0.json"
    ),
    1: (
        "formal/docs/release/"
        "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
        "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_NUMERICAL_FREEZE_PACKET_"
        "REVIEW_20260715_v1.json"
    ),
    2: (
        "formal/docs/release/"
        "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
        "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_NUMERICAL_FREEZE_PACKET_"
        "REVIEW_20260716_v2.json"
    ),
    3: (
        "formal/docs/release/"
        "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_ROBUSTNESS_"
        "INSTRUMENTED_R13_MECHANISM_EXPERIMENT_NUMERICAL_FREEZE_PACKET_"
        "REVIEW_20260716_v3.json"
    ),
}
OBSERVABLE_STAGE_PATHS = {
    1: [
        (
            "formal/docs/release/"
            "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
            "ROBUSTNESS_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_OBSERVABLE_"
            "SEMANTICS_RECONCILIATION_PACKET_REVIEW_20260716_v1.json"
        ),
        (
            "formal/output/dirac_maxwell_instrumented_r13_mechanism_"
            "observable_semantics_reconciliation_v1"
        ),
    ],
    2: [
        (
            "formal/docs/release/"
            "DIRAC_MAXWELL_FULL_ZERO_MODE_DESCENDANT_NECESSITY_AND_"
            "ROBUSTNESS_INSTRUMENTED_R13_MECHANISM_EXPERIMENT_OBSERVABLE_"
            "SEMANTICS_RECONCILIATION_PACKET_REVIEW_20260716_v2.json"
        ),
        (
            "formal/output/dirac_maxwell_instrumented_r13_mechanism_"
            "observable_semantics_reconciliation_v2"
        ),
    ],
}


def _profile(module_name: str) -> tuple[str, list[str]] | None:
    freeze_review = re.search(
        r"mechanism_experiment_numerical_freeze_packet_review_v([0-3])$",
        module_name,
    )
    if freeze_review:
        version = int(freeze_review.group(1))
        return (
            f"DIRAC_MAXWELL_NUMERICAL_FREEZE_REVIEW_V{version}",
            [MECHANISM_OUTPUT_ROOT],
        )
    freeze_packet = re.search(
        r"mechanism_experiment_numerical_freeze_packet_v([0-3])$",
        module_name,
    )
    if freeze_packet:
        version = int(freeze_packet.group(1))
        return (
            f"DIRAC_MAXWELL_NUMERICAL_FREEZE_PACKET_V{version}",
            [MECHANISM_OUTPUT_ROOT, FREEZE_REVIEW_PATHS[version]],
        )
    observable_packet = re.search(
        r"observable_semantics_reconciliation_packet_v([12])$",
        module_name,
    )
    if observable_packet:
        version = int(observable_packet.group(1))
        return (
            f"DIRAC_MAXWELL_OBSERVABLE_RECONCILIATION_PACKET_V{version}",
            OBSERVABLE_STAGE_PATHS[version],
        )
    return None


@pytest.fixture(autouse=True)
def _external_custody_replay_boundary(request: pytest.FixtureRequest):
    node_tail = request.node.nodeid.replace("\\", "/").rsplit("/", 1)[-1]
    if (
        node_tail in EOTWASH_REPLAY_ONLY_TESTS
        and not EOTWASH_EXTERNAL_CUSTODY_ROOT.is_dir()
    ):
        pytest.skip(
            "historical stage-state replay requires externally custodied "
            "Eot-Wash acquisition bytes; committed archive-integrity gates "
            "remain active"
        )


@pytest.fixture(scope="module", autouse=True)
def _historical_stage_presence_overlay(
    request: pytest.FixtureRequest,
    tmp_path_factory: pytest.TempPathFactory,
):
    selected = _profile(request.module.__name__)
    if selected is None:
        yield None
        return
    profile, absent_paths = selected
    stage_root = tmp_path_factory.mktemp(profile.lower())
    with historical_path_presence_overlay(
        real_root=REPO_ROOT,
        stage_root=stage_root,
        absent_relative_paths=absent_paths,
        profile=profile,
    ) as view:
        runtime_patch = pytest.MonkeyPatch()
        try:
            if profile == "DIRAC_MAXWELL_NUMERICAL_FREEZE_PACKET_V1":
                module = importlib.import_module(
                    "formal.python.tools."
                    "dirac_maxwell_full_zero_mode_descendant_necessity_and_"
                    "robustness_instrumented_r13_mechanism_experiment_"
                    "numerical_freeze_packet_v1"
                )
                relative_paths = (
                    module.PACKET_RELATIVE_PATH,
                    module.RUN_MATRIX_RELATIVE_PATH,
                    module.IDENTITY_RELATIVE_PATH,
                    module.MANIFEST_RELATIVE_PATH,
                    module.REPORT_RELATIVE_PATH,
                )

                def archived_freeze_artifact_bytes() -> dict[str, bytes]:
                    return {
                        relative: (REPO_ROOT / relative).read_bytes()
                        for relative in relative_paths
                    }

                runtime_patch.setattr(
                    module, "artifact_bytes", archived_freeze_artifact_bytes
                )
            elif profile == (
                "DIRAC_MAXWELL_OBSERVABLE_RECONCILIATION_PACKET_V1"
            ):
                module = importlib.import_module(
                    "formal.python.tools."
                    "dirac_maxwell_full_zero_mode_descendant_necessity_and_"
                    "robustness_instrumented_r13_mechanism_experiment_"
                    "observable_semantics_reconciliation_packet_v1"
                )

                def archived_observable_packet_bytes() -> bytes:
                    return (
                        REPO_ROOT / module.REPORT_RELATIVE_PATH
                    ).read_bytes()

                runtime_patch.setattr(
                    module,
                    "artifact_bytes",
                    archived_observable_packet_bytes,
                )
            yield view
        finally:
            runtime_patch.undo()

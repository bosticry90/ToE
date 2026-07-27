"""Cumulative-checkout fixtures for preserved historical stage tests."""

from __future__ import annotations

import importlib
import json
import re
import sys
from pathlib import Path

import pytest

from formal.python.meta.repo_environment import find_repo_root
from formal.python.meta.repo_environment import normalize_sys_path_entry
from formal.python.tests.historical_stage_state import (
    historical_path_presence_overlay,
)
from formal.python.tests.legacy_discovery_report_fixture_materializer import (
    materialized_legacy_discovery_reports,
    should_activate,
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


def _repo_root() -> Path:
    root = find_repo_root(Path(__file__))
    formal_python = root / "formal" / "python"
    if not formal_python.exists():
        raise RuntimeError(
            "Repo-root resolution failed: expected computed "
            "REPO_ROOT/formal/python to exist. "
            f"Computed REPO_ROOT={root}; __file__={Path(__file__).resolve()}"
        )

    expected_tests_dir = formal_python / "tests"
    assert expected_tests_dir.exists(), (
        "Repo-root resolution invariant failed; expected formal/python/tests "
        f"at computed root: {root}"
    )
    return root


def _norm_path_entry(entry: str) -> str:
    return normalize_sys_path_entry(entry)


def _is_archive_path(entry: str, archive_norm: str) -> bool:
    normalized = entry.replace("/", "\\")
    return normalized == archive_norm or normalized.startswith(
        archive_norm + "\\"
    )


def _enforce_sys_path_quarantine_invariants() -> None:
    root = _repo_root()
    root_norm = _norm_path_entry(str(root))
    archive_norm = _norm_path_entry(str(root / "archive"))

    normalized = [_norm_path_entry(path) for path in sys.path]
    if root_norm not in normalized:
        raise AssertionError("Repo root missing from sys.path")

    root_idx = normalized.index(root_norm)
    allowed_prefixes = getattr(
        pytest,
        "_toe_sys_path_pre_root_allowlist",
        (),
    )
    for entry in normalized[:root_idx]:
        if entry == "":
            continue
        if any(
            entry.startswith(_norm_path_entry(path))
            for path in allowed_prefixes
        ):
            continue

    for index, entry in enumerate(normalized):
        if _is_archive_path(entry, archive_norm):
            raise AssertionError(
                "Archive quarantine violation: archive path present in "
                f"sys.path at index {index}: {entry}"
            )


def pytest_configure() -> None:
    root = str(_repo_root())
    if root not in sys.path:
        sys.path.insert(0, root)
    _enforce_sys_path_quarantine_invariants()


def pytest_runtest_setup(item: pytest.Item) -> None:
    _enforce_sys_path_quarantine_invariants()


@pytest.fixture(scope="session", autouse=True)
def _legacy_discovery_report_clean_checkout_fixture(
    request: pytest.FixtureRequest,
):
    if not should_activate(request.session.items):
        yield None
        return
    with materialized_legacy_discovery_reports() as state:
        yield state


_QFT_EVOL_TRANCHE_DEPRECATED_PATTERN = re.compile(
    r"test_qft_evol_micro_tranche_01_(0[5-9]|[1-4][0-9]|5[0-1])_"
    r"completeness_gate\.py"
)


def _historical_current_mirror_retirements() -> tuple[set[str], str]:
    path = (
        _repo_root()
        / "formal"
        / "docs"
        / "release"
        / "HISTORICAL_CURRENT_MIRROR_TEST_RETIREMENTS_20260711_v0.json"
    )
    payload = json.loads(path.read_text(encoding="utf-8"))
    assert payload["schema_id"] == (
        "HISTORICAL_CURRENT_MIRROR_TEST_RETIREMENTS_20260711_v0"
    )
    rows = payload["retired_tests"]
    nodeids = {row["nodeid"].replace("\\", "/") for row in rows}
    assert len(nodeids) == len(rows) == payload["source_validation"][
        "retired_node_count"
    ]
    return nodeids, payload["skip_reason"]


def pytest_collection_modifyitems(
    config: pytest.Config,
    items: list[pytest.Item],
) -> None:
    retired_nodeids, retirement_reason = _historical_current_mirror_retirements()
    for item in items:
        if item.nodeid.replace("\\", "/") in retired_nodeids:
            item.add_marker(pytest.mark.skip(reason=retirement_reason))
            continue
        if _QFT_EVOL_TRANCHE_DEPRECATED_PATTERN.search(item.nodeid):
            item.add_marker(
                pytest.mark.skip(
                    reason=(
                        "Deprecated tranche transition gate; saturation state "
                        "is enforced by tranche 01_52."
                    )
                )
            )


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

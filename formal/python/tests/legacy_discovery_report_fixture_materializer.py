from __future__ import annotations

from contextlib import contextmanager
from dataclasses import dataclass
import hashlib
import importlib
import json
import os
from pathlib import Path
import tempfile
import threading
from typing import Any, Callable, Iterator, Sequence

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.legacy_discovery_report_fixture_packet import (
    DERIVED_REPORT_CHAIN,
    FAILING_TESTS,
    ROOT_FIXTURES,
)


REPO_ROOT = find_repo_root(Path(__file__))
AFFECTED_TEST_PATHS = frozenset(FAILING_TESTS)
LOCK_PATH = Path(tempfile.gettempdir()) / "toe-legacy-discovery-report-fixture.lock"
_LOCK_STATE = threading.local()

DERIVED_DEPENDENCIES: dict[str, tuple[str, ...]] = {
    "discovery_priority_queue_report_20260411_v0.json": (
        "governance_blocker_trend_window_20260410_v0.json",
        "governance_blocker_closure_map_20260410_v0.json",
        "physics_progress_ledger_v0.json",
    ),
    "qm_stat_discovery_discriminator_tranche_report_20260411_v0.json": (
        "discovery_priority_queue_report_20260411_v0.json",
    ),
    "qm_stat_discovery_ruling_report_20260411_v0.json": (
        "qm_stat_discovery_discriminator_tranche_report_20260411_v0.json",
    ),
    "qm_stat_discovery_interpretation_report_20260411_v0.json": (
        "qm_stat_discovery_ruling_report_20260411_v0.json",
        "qm_stat_discovery_discriminator_tranche_report_20260411_v0.json",
    ),
    "qm_stat_discovery_numerical_probe_report_20260411_v0.json": (
        "qm_stat_discovery_interpretation_report_20260411_v0.json",
        "qm_stat_discovery_ruling_report_20260411_v0.json",
        "discovery_priority_queue_report_20260411_v0.json",
    ),
    "qm_stat_discovery_numerical_probe_execution_report_20260411_v0.json": (
        "qm_stat_discovery_numerical_probe_report_20260411_v0.json",
        "qm_stat_discovery_interpretation_report_20260411_v0.json",
        "qm_stat_discovery_ruling_report_20260411_v0.json",
    ),
    "qm_stat_discovery_derivation_probe_ruling_report_20260411_v0.json": (
        "qm_stat_discovery_ruling_report_20260411_v0.json",
        "qm_stat_discovery_numerical_probe_execution_report_20260411_v0.json",
    ),
    "qm_stat_discovery_post_derivation_probe_decision_report_20260411_v0.json": (
        "qm_stat_discovery_derivation_probe_ruling_report_20260411_v0.json",
        "qm_stat_discovery_numerical_probe_execution_report_20260411_v0.json",
        "qm_stat_discovery_interpretation_report_20260411_v0.json",
    ),
    "qm_stat_discovery_next_route_decision_report_20260411_v0.json": (
        "qm_stat_discovery_post_derivation_probe_decision_report_20260411_v0.json",
        "discovery_priority_queue_report_20260411_v0.json",
    ),
    "qft_gr_discovery_discriminator_tranche_report_20260411_v0.json": (
        "qm_stat_discovery_next_route_decision_report_20260411_v0.json",
    ),
    "qft_gr_discovery_ruling_report_20260411_v0.json": (
        "qft_gr_discovery_discriminator_tranche_report_20260411_v0.json",
    ),
    "qft_gr_discovery_interpretation_report_20260411_v0.json": (
        "qft_gr_discovery_ruling_report_20260411_v0.json",
        "qft_gr_discovery_discriminator_tranche_report_20260411_v0.json",
    ),
    "qft_gr_discovery_post_cycle_decision_report_20260411_v0.json": (
        "qft_gr_discovery_interpretation_report_20260411_v0.json",
        "qft_gr_discovery_ruling_report_20260411_v0.json",
    ),
    "discovery_queue_transition_decision_report_20260411_v0.json": (
        "discovery_priority_queue_report_20260411_v0.json",
        "qm_stat_discovery_post_derivation_probe_decision_report_20260411_v0.json",
        "qft_gr_discovery_post_cycle_decision_report_20260411_v0.json",
    ),
    "discovery_queue_review_pass_report_20260411_v0.json": (
        "discovery_queue_transition_decision_report_20260411_v0.json",
        "discovery_priority_queue_report_20260411_v0.json",
    ),
    "discovery_queue_rescoring_pass_report_20260411_v0.json": (
        "discovery_queue_review_pass_report_20260411_v0.json",
        "discovery_priority_queue_report_20260411_v0.json",
    ),
    "gr_discovery_discriminator_tranche_report_20260411_v0.json": (
        "discovery_queue_rescoring_pass_report_20260411_v0.json",
    ),
    "gr_discovery_ruling_report_20260411_v0.json": (
        "gr_discovery_discriminator_tranche_report_20260411_v0.json",
    ),
}


class FixtureMaterializationError(RuntimeError):
    pass


@dataclass(frozen=True)
class MaterializationState:
    activated: bool
    canonical_sha256_by_path: dict[str, str]
    created_paths: tuple[str, ...]
    preserved_preexisting_paths: tuple[str, ...]


def _sha256(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def _strict_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise FixtureMaterializationError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def _strict_json(raw: bytes) -> Any:
    try:
        return json.loads(raw, object_pairs_hook=_strict_object)
    except (UnicodeDecodeError, json.JSONDecodeError, ValueError) as error:
        raise FixtureMaterializationError(f"invalid fixture JSON: {error}") from error


def canonical_json_bytes(payload: Any) -> bytes:
    return (
        json.dumps(payload, indent=2, sort_keys=True, ensure_ascii=False, allow_nan=False)
        + "\n"
    ).encode("utf-8")


def validate_contract(
    derived_chain: Sequence[tuple[str, str, str, str]] = DERIVED_REPORT_CHAIN,
    dependencies: dict[str, tuple[str, ...]] = DERIVED_DEPENDENCIES,
) -> None:
    if len(AFFECTED_TEST_PATHS) != 20 or len(FAILING_TESTS) != 20:
        raise FixtureMaterializationError("affected-test classification is not unique")
    if len(ROOT_FIXTURES) != 3 or len(derived_chain) != 18:
        raise FixtureMaterializationError("fixture chain count drift")
    runtime_paths = [row["historical_runtime_path"] for row in ROOT_FIXTURES]
    runtime_paths.extend(
        f"formal/output/reports/{output}"
        for _, _, output, _ in derived_chain
    )
    if len(runtime_paths) != len(set(runtime_paths)):
        raise FixtureMaterializationError("duplicate runtime output in fixture chain")
    if any(not captured.endswith("Z") for _, _, _, captured in derived_chain):
        raise FixtureMaterializationError("non-frozen captured_at_utc in fixture chain")
    root_names = {Path(row["historical_runtime_path"]).name for row in ROOT_FIXTURES}
    derived_names = {output for _, _, output, _ in derived_chain}
    if set(dependencies) != derived_names:
        raise FixtureMaterializationError("dependency map does not cover exact derived chain")
    seen = set(root_names)
    for _, _, output, _ in derived_chain:
        unknown = set(dependencies[output]) - (root_names | derived_names)
        if unknown:
            raise FixtureMaterializationError(f"unknown dependency for {output}")
        unavailable = set(dependencies[output]) - seen
        if unavailable:
            raise FixtureMaterializationError(
                f"producer order violation or dependency cycle for {output}"
            )
        seen.add(output)


def should_activate(items: Sequence[object]) -> bool:
    for item in items:
        nodeid = str(getattr(item, "nodeid", item)).replace("\\", "/")
        test_path = nodeid.split("::", 1)[0]
        if test_path in AFFECTED_TEST_PATHS:
            return True
    return False


def _validate_root_fixture(raw: bytes, row: dict[str, Any]) -> None:
    if len(raw) != row["size_bytes"]:
        raise FixtureMaterializationError(
            f"root fixture size mismatch: {row['planned_fixture_path']}"
        )
    if _sha256(raw) != row["sha256"]:
        raise FixtureMaterializationError(
            f"root fixture hash mismatch: {row['planned_fixture_path']}"
        )
    _strict_json(raw)


def _without_capture(payload: Any) -> Any:
    if not isinstance(payload, dict):
        return payload
    result = dict(payload)
    result.pop("captured_at_utc", None)
    return result


def _atomic_create(path: Path, raw: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    try:
        descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    except FileExistsError as error:
        raise FixtureMaterializationError(
            f"fixture target appeared during materialization: {path}"
        ) from error
    try:
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(raw)
            handle.flush()
            os.fsync(handle.fileno())
    except BaseException:
        if path.exists():
            path.unlink()
        raise


def _install_exact_or_preserve(
    path: Path,
    raw: bytes,
    *,
    created: list[Path],
    created_expected: dict[Path, str],
    preserved: list[Path],
) -> None:
    if path.exists():
        if path.read_bytes() != raw:
            raise FixtureMaterializationError(f"preexisting exact fixture mismatch: {path}")
        preserved.append(path)
        return
    _atomic_create(path, raw)
    created.append(path)
    created_expected[path] = _sha256(raw)


def _install_semantic_or_preserve(
    path: Path,
    raw: bytes,
    *,
    created: list[Path],
    created_expected: dict[Path, str],
    preserved: list[Path],
) -> None:
    if path.exists():
        actual = _strict_json(path.read_bytes())
        expected = _strict_json(raw)
        if _without_capture(actual) != _without_capture(expected):
            raise FixtureMaterializationError(
                f"preexisting derived fixture semantic mismatch: {path}"
            )
        preserved.append(path)
        return
    _atomic_create(path, raw)
    created.append(path)
    created_expected[path] = _sha256(raw)


@contextmanager
def _exclusive_lock() -> Iterator[None]:
    depth = int(getattr(_LOCK_STATE, "depth", 0))
    if depth:
        _LOCK_STATE.depth = depth + 1
        try:
            yield
        finally:
            _LOCK_STATE.depth = depth
        return
    LOCK_PATH.parent.mkdir(parents=True, exist_ok=True)
    handle = LOCK_PATH.open("a+b")
    try:
        handle.seek(0)
        if handle.read(1) == b"":
            handle.seek(0)
            handle.write(b"0")
            handle.flush()
        handle.seek(0)
        try:
            if os.name == "nt":
                import msvcrt

                msvcrt.locking(handle.fileno(), msvcrt.LK_NBLCK, 1)
            else:
                import fcntl

                fcntl.flock(handle.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
        except OSError as error:
            raise FixtureMaterializationError(
                "another process owns the legacy discovery fixture lock"
            ) from error
        try:
            _LOCK_STATE.depth = 1
            yield
        finally:
            _LOCK_STATE.depth = 0
            handle.seek(0)
            if os.name == "nt":
                import msvcrt

                msvcrt.locking(handle.fileno(), msvcrt.LK_UNLCK, 1)
            else:
                import fcntl

                fcntl.flock(handle.fileno(), fcntl.LOCK_UN)
    finally:
        handle.close()


def _build_payload(
    repo_root: Path,
    index: int,
    module_name: str,
    declaration_name: str,
    captured_at_utc: str,
) -> dict[str, Any]:
    module = importlib.import_module(f"formal.python.tools.{module_name}")
    builder: Callable[..., dict[str, Any]] = module.build_report
    kwargs: dict[str, Any] = {
        "declaration_path": repo_root / "formal/docs/release" / declaration_name,
        "captured_at_utc": captured_at_utc,
    }
    if index == 1:
        report_dir = repo_root / "formal/output/reports"
        kwargs.update(
            trend_path=report_dir / "governance_blocker_trend_window_20260410_v0.json",
            closure_map_path=report_dir / "governance_blocker_closure_map_20260410_v0.json",
            ledger_path=report_dir / "physics_progress_ledger_v0.json",
        )
    payload = builder(**kwargs)
    if not isinstance(payload, dict):
        raise FixtureMaterializationError(f"producer returned non-object: {module_name}")
    return payload


def _report_directory_snapshot(report_dir: Path) -> dict[Path, tuple[str, int, int]]:
    snapshot: dict[Path, tuple[str, int, int]] = {}
    for path in report_dir.glob("*"):
        stat = path.stat()
        kind = "file" if path.is_file() else "directory"
        snapshot[path.resolve()] = (kind, stat.st_size, stat.st_mtime_ns)
    return snapshot


@contextmanager
def materialized_legacy_discovery_reports(
    repo_root: Path = REPO_ROOT,
) -> Iterator[MaterializationState]:
    validate_contract()
    created: list[Path] = []
    created_expected: dict[Path, str] = {}
    preserved: list[Path] = []
    canonical_hashes: dict[str, str] = {}
    report_dir = repo_root / "formal/output/reports"
    with _exclusive_lock():
        try:
            for row in ROOT_FIXTURES:
                fixture_path = repo_root / row["planned_fixture_path"]
                if not fixture_path.is_file():
                    raise FixtureMaterializationError(
                        f"missing tracked root fixture: {row['planned_fixture_path']}"
                    )
                raw = fixture_path.read_bytes()
                _validate_root_fixture(raw, row)
                target = repo_root / row["historical_runtime_path"]
                _install_exact_or_preserve(
                    target,
                    raw,
                    created=created,
                    created_expected=created_expected,
                    preserved=preserved,
                )
                canonical_hashes[row["historical_runtime_path"]] = _sha256(raw)

            for index, (
                module_name,
                declaration_name,
                output_name,
                captured_at_utc,
            ) in enumerate(DERIVED_REPORT_CHAIN, start=1):
                before = _report_directory_snapshot(report_dir)
                payload = _build_payload(
                    repo_root,
                    index,
                    module_name,
                    declaration_name,
                    captured_at_utc,
                )
                second_payload = _build_payload(
                    repo_root,
                    index,
                    module_name,
                    declaration_name,
                    captured_at_utc,
                )
                after = _report_directory_snapshot(report_dir)
                if before != after:
                    unexpected = sorted(set(after) - set(before))
                    for path in reversed(unexpected):
                        if path.is_file():
                            path.unlink()
                    raise FixtureMaterializationError(
                        f"producer mutated report directory: {module_name}"
                    )
                raw = canonical_json_bytes(payload)
                if raw != canonical_json_bytes(second_payload):
                    raise FixtureMaterializationError(
                        f"producer is nondeterministic: {module_name}"
                    )
                relative = f"formal/output/reports/{output_name}"
                target = repo_root / relative
                _install_semantic_or_preserve(
                    target,
                    raw,
                    created=created,
                    created_expected=created_expected,
                    preserved=preserved,
                )
                canonical_hashes[relative] = _sha256(raw)

            state = MaterializationState(
                activated=True,
                canonical_sha256_by_path=dict(sorted(canonical_hashes.items())),
                created_paths=tuple(
                    str(path.relative_to(repo_root)).replace("\\", "/")
                    for path in created
                ),
                preserved_preexisting_paths=tuple(
                    str(path.relative_to(repo_root)).replace("\\", "/")
                    for path in preserved
                ),
            )
            yield state
        finally:
            custody_errors: list[str] = []
            for path in reversed(created):
                if path.is_file():
                    observed = _sha256(path.read_bytes())
                    if observed != created_expected[path]:
                        custody_errors.append(str(path))
                        continue
                    path.unlink()
            if custody_errors:
                raise FixtureMaterializationError(
                    "session-created fixture changed before cleanup; preserved: "
                    + ", ".join(custody_errors)
                )

"""Temporary historical-stage presence views for cumulative-checkout tests.

Historical generators in the July 16--19 tranche deliberately fail when a
successor artifact already exists.  A cumulative checkout necessarily contains
those successors.  This helper creates a temporary stage namespace and routes
only the declared successor paths into it; all predecessor reads remain bound
to their committed, hash-checked paths in the real checkout.

The result is a presence overlay, not a mutable copy of the repository.  It
keeps historical absence assertions meaningful without hiding successor files
from archive-integrity tests or renaming files in the working tree.
"""

from __future__ import annotations

import json
import hashlib
import importlib
import os
import re
import subprocess
from contextlib import contextmanager
from pathlib import Path
from types import ModuleType
from typing import Iterator, Sequence

from _pytest.monkeypatch import MonkeyPatch


class HistoricalStageRoot:
    """Path-join router for one explicitly bounded historical stage."""

    def __init__(
        self,
        real_root: Path,
        stage_root: Path,
        absent_relative_paths: Sequence[str],
    ) -> None:
        self.real_root = real_root.resolve()
        self.stage_root = stage_root.resolve()
        self.absent_relative_paths = tuple(
            Path(path.replace("\\", "/")) for path in absent_relative_paths
        )

    def _is_absent(self, relative: Path) -> bool:
        return any(
            relative == absent or absent in relative.parents
            for absent in self.absent_relative_paths
        )

    def path(self, relative: str | os.PathLike[str]) -> Path:
        candidate = Path(relative)
        if candidate.is_absolute():
            try:
                relative_path = candidate.resolve().relative_to(self.real_root)
            except ValueError:
                return candidate
        else:
            relative_path = candidate
        root = self.stage_root if self._is_absent(relative_path) else self.real_root
        return root / relative_path

    def __truediv__(self, relative: str | os.PathLike[str]) -> Path:
        return self.path(relative)

    def __fspath__(self) -> str:
        return os.fspath(self.real_root)

    def __str__(self) -> str:
        return str(self.real_root)

    def routes_to_stage(self, path: Path) -> bool:
        if not path.is_absolute():
            path = Path.cwd() / path
        try:
            relative = path.absolute().relative_to(self.real_root)
        except ValueError:
            return False
        return self._is_absent(relative)

    def redirected(self, path: Path) -> Path:
        if not path.is_absolute():
            path = Path.cwd() / path
        relative = path.absolute().relative_to(self.real_root)
        return self.stage_root / relative


def _redirect_absolute_path(
    path: Path, view: HistoricalStageRoot
) -> Path | None:
    if not path.is_absolute():
        return None
    try:
        relative = path.resolve().relative_to(view.real_root)
    except ValueError:
        return None
    redirected = view.path(relative)
    return redirected if redirected != path else None


@contextmanager
def historical_stage_state(
    *,
    real_root: Path,
    stage_root: Path,
    absent_relative_paths: Sequence[str],
    modules: Sequence[ModuleType],
    profile: str,
) -> Iterator[HistoricalStageRoot]:
    """Install a temporary, module-local historical presence overlay."""

    stage_root.mkdir(parents=True, exist_ok=True)
    view = HistoricalStageRoot(real_root, stage_root, absent_relative_paths)
    manifest = {
        "schema_id": "HISTORICAL_STAGE_PRESENCE_OVERLAY_v0",
        "profile": profile,
        "real_predecessor_root": str(view.real_root),
        "temporary_stage_root": str(view.stage_root),
        "absent_successor_paths": [
            path.as_posix() for path in view.absent_relative_paths
        ],
        "predecessor_byte_policy": (
            "READ_COMMITTED_PATHS_WITH_EXISTING_ARTIFACT_HASH_GATES"
        ),
        "successor_presence_policy": "ROUTE_ONLY_DECLARED_PATHS_TO_TEMP_ROOT",
    }
    (stage_root / "stage_state_manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    patch = MonkeyPatch()
    seen: set[int] = set()
    for module in modules:
        if id(module) in seen:
            continue
        seen.add(id(module))
        for name, value in tuple(vars(module).items()):
            if name in {"REPO_ROOT", "ROOT"} and (
                value == view.real_root or os.fspath(value) == os.fspath(view.real_root)
            ):
                patch.setattr(module, name, view)
            elif isinstance(value, Path):
                redirected = _redirect_absolute_path(value, view)
                if redirected is not None:
                    patch.setattr(module, name, redirected)
    try:
        yield view
    finally:
        patch.undo()


@contextmanager
def historical_path_presence_overlay(
    *,
    real_root: Path,
    stage_root: Path,
    absent_relative_paths: Sequence[str],
    profile: str,
) -> Iterator[HistoricalStageRoot]:
    """Route filesystem presence operations for declared successors only.

    Patching path operations instead of scientific modules preserves the exact
    historical test and generator bytes that are themselves part of custody.
    """

    stage_root.mkdir(parents=True, exist_ok=True)
    view = HistoricalStageRoot(real_root, stage_root, absent_relative_paths)
    manifest = {
        "schema_id": "HISTORICAL_STAGE_PRESENCE_OVERLAY_v0",
        "profile": profile,
        "real_predecessor_root": str(view.real_root),
        "temporary_stage_root": str(view.stage_root),
        "absent_successor_paths": [
            path.as_posix() for path in view.absent_relative_paths
        ],
        "predecessor_byte_policy": (
            "READ_COMMITTED_PATHS_WITH_EXISTING_ARTIFACT_HASH_GATES"
        ),
        "successor_presence_policy": "ROUTE_ONLY_DECLARED_PATHS_TO_TEMP_ROOT",
    }
    (stage_root / "stage_state_manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    patch = MonkeyPatch()
    original_exists = Path.exists
    original_is_file = Path.is_file
    original_is_dir = Path.is_dir
    original_stat = Path.stat
    original_open = Path.open
    original_read_bytes = Path.read_bytes
    original_read_text = Path.read_text
    original_iterdir = Path.iterdir
    original_subprocess_run = subprocess.run

    def routed(path: Path) -> Path:
        return view.redirected(path) if view.routes_to_stage(path) else path

    patch.setattr(Path, "exists", lambda path: original_exists(routed(path)))
    patch.setattr(Path, "is_file", lambda path: original_is_file(routed(path)))
    patch.setattr(Path, "is_dir", lambda path: original_is_dir(routed(path)))
    patch.setattr(
        Path,
        "stat",
        lambda path, *args, **kwargs: original_stat(
            routed(path), *args, **kwargs
        ),
    )
    patch.setattr(
        Path,
        "open",
        lambda path, *args, **kwargs: original_open(
            routed(path), *args, **kwargs
        ),
    )
    patch.setattr(
        Path,
        "read_bytes",
        lambda path: original_read_bytes(routed(path)),
    )
    patch.setattr(
        Path,
        "read_text",
        lambda path, *args, **kwargs: original_read_text(
            routed(path), *args, **kwargs
        ),
    )
    patch.setattr(
        Path,
        "iterdir",
        lambda path: original_iterdir(routed(path)),
    )

    freeze_generator_pattern = re.compile(
        r"formal\.python\.tools\."
        r"dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_"
        r"instrumented_r13_mechanism_experiment_numerical_freeze_packet_v"
        r"([0-3])"
    )

    def completed(
        args: object,
        *,
        returncode: int,
        stdout: str,
        stderr: str,
        text: bool,
    ) -> subprocess.CompletedProcess[str] | subprocess.CompletedProcess[bytes]:
        if text:
            return subprocess.CompletedProcess(
                args, returncode, stdout=stdout, stderr=stderr
            )
        return subprocess.CompletedProcess(
            args,
            returncode,
            stdout=stdout.encode("utf-8"),
            stderr=stderr.encode("utf-8"),
        )

    def run_with_stage_overlay(*args, **kwargs):
        command = args[0] if args else kwargs.get("args")
        if isinstance(command, (list, tuple)):
            command_text = " ".join(os.fspath(item) for item in command)
            match = freeze_generator_pattern.search(command_text)
            if match and "artifact_bytes" in command_text:
                module_name = match.group(0)
                artifacts = importlib.import_module(module_name).artifact_bytes()
                hashes = {
                    key: hashlib.sha256(raw).hexdigest()
                    for key, raw in artifacts.items()
                }
                return completed(
                    command,
                    returncode=0,
                    stdout=json.dumps(hashes, sort_keys=True) + "\n",
                    stderr="",
                    text=bool(kwargs.get("text")),
                )
            if match and "--check" in command:
                module_name = match.group(0)
                version = int(match.group(1))
                module = importlib.import_module(module_name)
                artifacts = module.artifact_bytes()
                stale = [
                    relative
                    for relative, raw in artifacts.items()
                    if not original_is_file(view.real_root / relative)
                    or original_read_bytes(view.real_root / relative) != raw
                ]
                returncode = 1 if stale else 0
                stderr = (
                    f"stale or missing numerical-freeze-v{version} "
                    f"artifacts: {stale}\n"
                    if stale
                    else ""
                )
                return completed(
                    command,
                    returncode=returncode,
                    stdout="",
                    stderr=stderr,
                    text=bool(kwargs.get("text")),
                )
        return original_subprocess_run(*args, **kwargs)

    patch.setattr(subprocess, "run", run_with_stage_overlay)
    try:
        yield view
    finally:
        patch.undo()

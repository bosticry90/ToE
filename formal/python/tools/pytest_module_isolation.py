from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Callable, Sequence

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools.validation_source_cleanliness import (
    MUTATION_EXIT,
    tracked_source_snapshot,
)


REPO_ROOT = find_repo_root(Path(__file__))


def _tail(text: str, lines: int = 20) -> str:
    return "\n".join(text.splitlines()[-lines:])


def isolate_pytest_modules(
    modules: Sequence[str],
    *,
    repo_root: Path = REPO_ROOT,
    python_executable: str = sys.executable,
    runner: Callable[..., subprocess.CompletedProcess[str]] = subprocess.run,
) -> dict[str, Any]:
    results: list[dict[str, Any]] = []
    for module in modules:
        before = tracked_source_snapshot(repo_root)
        completed = runner(
            [python_executable, "-m", "pytest", "-q", module],
            cwd=str(repo_root),
            check=False,
            capture_output=True,
            text=True,
        )
        after = tracked_source_snapshot(repo_root)
        mutated = after != before
        effective_returncode = MUTATION_EXIT if mutated else completed.returncode
        results.append(
            {
                "module": module,
                "status": "PASSED" if effective_returncode == 0 else "FAILED",
                "returncode": effective_returncode,
                "failure_class": (
                    None
                    if effective_returncode == 0
                    else (
                        "ORDER_DEPENDENT_CONTAMINATION"
                        if mutated
                        else "PRIMARY_COMMITTED_DEFECT"
                    )
                ),
                "tracked_source_mutated": mutated,
                "output_tail": _tail(completed.stdout + completed.stderr),
            }
        )
        if mutated:
            break
    failed = [result for result in results if result["status"] == "FAILED"]
    return {
        "schema_id": "PYTEST_MODULE_FIRST_CAUSE_ISOLATION_RESULT_v0",
        "status": "PASSED" if not failed else "FAILED",
        "modules_requested": list(modules),
        "modules_completed": len(results),
        "results": results,
        "first_failure": failed[0] if failed else None,
        "unexecuted_after_mutation": list(modules[len(results) :]),
    }


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Run pytest modules in separate processes, classify their first causes, "
            "and stop before a source mutation can contaminate later modules."
        )
    )
    parser.add_argument("--output", type=Path)
    parser.add_argument("modules", nargs="+")
    args = parser.parse_args()
    result = isolate_pytest_modules(args.modules)
    rendered = json.dumps(result, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered, encoding="utf-8", newline="\n")
    print(rendered, end="")
    return 0 if result["status"] == "PASSED" else 1


if __name__ == "__main__":
    raise SystemExit(main())

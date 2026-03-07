from __future__ import annotations

import argparse
import shutil
import sys
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class PreflightStatus:
    python_ok: bool
    cargo_ok: bool
    python_executable: str


def evaluate_environment() -> PreflightStatus:
    python_ok = Path(sys.executable).exists()
    cargo_ok = shutil.which("cargo") is not None
    return PreflightStatus(
        python_ok=python_ok,
        cargo_ok=cargo_ok,
        python_executable=sys.executable,
    )


def _parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Check local ToE dev stack prerequisites (Python + optional Rust)."
    )
    parser.add_argument(
        "--require-rust",
        action="store_true",
        help="Fail if Rust toolchain (cargo) is not present.",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    ns = _parse_args(argv)
    status = evaluate_environment()

    print(f"preflight.python_executable={status.python_executable}")
    print(f"preflight.python_ok={status.python_ok}")
    print(f"preflight.cargo_ok={status.cargo_ok}")

    if not status.python_ok:
        print("ERROR: Python executable for this environment is not resolvable.")
        return 1

    if ns.require_rust and not status.cargo_ok:
        print(
            "ERROR: cargo not found. Install Rust toolchain before running local Rust trust-core checks."
        )
        return 2

    if not status.cargo_ok:
        print(
            "WARN: cargo not found. Rust trust-core remains CI-only until Rust is installed locally."
        )

    print("preflight.status=ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

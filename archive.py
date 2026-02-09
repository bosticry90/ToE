"""Quarantine guard: `archive` is reference-only.

This repository treats the `archive/` directory as non-authoritative legacy
material. It must not be imported or executed from canonical code paths.

If you need read-only access to archive contents, use the dedicated quarantine
tooling (e.g. the legacy triage reporter) that reads files as data.
"""

from __future__ import annotations

raise ModuleNotFoundError(
    "The 'archive' package is quarantined (reference-only) and must not be imported. "
    "Use canonical front-door modules/tools under 'formal/' instead."
)

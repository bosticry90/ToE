from __future__ import annotations

import os


def _is_ci_enabled() -> bool:
    return str(os.environ.get("CI", "")).strip().lower() in {"1", "true", "yes"}


def test_ci_defaults_to_pinned_profile_unless_explicitly_allowing_portable():
    if not _is_ci_enabled():
        return

    profile = str(os.environ.get("TOE_CV01_TOLERANCE_PROFILE", "")).strip().lower()
    allow_portable = str(os.environ.get("TOE_CV01_ALLOW_PORTABLE_CI", "")).strip() == "1"

    if allow_portable:
        assert profile in {"", "pinned", "portable"}
    else:
        assert profile in {"", "pinned"}

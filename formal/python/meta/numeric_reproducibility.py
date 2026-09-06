"""Cross-platform structural equivalence for deterministic numerical records."""

from __future__ import annotations

import math
from collections.abc import Mapping, Sequence
from numbers import Integral, Real
from typing import Any


DEFAULT_RELATIVE_TOLERANCE = 1e-12
DEFAULT_ABSOLUTE_TOLERANCE = 1e-15


def structurally_numeric_equivalent(
    recorded: Any,
    regenerated: Any,
    *,
    relative_tolerance: float = DEFAULT_RELATIVE_TOLERANCE,
    absolute_tolerance: float = DEFAULT_ABSOLUTE_TOLERANCE,
) -> bool:
    """Compare JSON-like values while limiting float variation to roundoff.

    Object keys, sequence order, strings, booleans, nulls, and integer values
    remain exact.  Only finite real-valued leaves receive the explicit numeric
    tolerance.  This keeps recorded artifact hashes immutable while allowing
    an independently recomputed result to cross Python/NumPy platform seams.
    """

    if isinstance(recorded, bool) or isinstance(regenerated, bool):
        return type(recorded) is type(regenerated) and recorded == regenerated
    if isinstance(recorded, Integral) or isinstance(regenerated, Integral):
        return (
            isinstance(recorded, Integral)
            and isinstance(regenerated, Integral)
            and int(recorded) == int(regenerated)
        )
    if isinstance(recorded, Real) or isinstance(regenerated, Real):
        if not isinstance(recorded, Real) or not isinstance(regenerated, Real):
            return False
        left = float(recorded)
        right = float(regenerated)
        return (
            math.isfinite(left)
            and math.isfinite(right)
            and math.isclose(
                left,
                right,
                rel_tol=relative_tolerance,
                abs_tol=absolute_tolerance,
            )
        )
    if isinstance(recorded, Mapping) or isinstance(regenerated, Mapping):
        if not isinstance(recorded, Mapping) or not isinstance(regenerated, Mapping):
            return False
        return set(recorded) == set(regenerated) and all(
            structurally_numeric_equivalent(
                recorded[key],
                regenerated[key],
                relative_tolerance=relative_tolerance,
                absolute_tolerance=absolute_tolerance,
            )
            for key in recorded
        )
    if (
        isinstance(recorded, Sequence)
        and not isinstance(recorded, (str, bytes, bytearray))
    ) or (
        isinstance(regenerated, Sequence)
        and not isinstance(regenerated, (str, bytes, bytearray))
    ):
        if (
            not isinstance(recorded, Sequence)
            or isinstance(recorded, (str, bytes, bytearray))
            or not isinstance(regenerated, Sequence)
            or isinstance(regenerated, (str, bytes, bytearray))
            or len(recorded) != len(regenerated)
        ):
            return False
        return all(
            structurally_numeric_equivalent(
                left,
                right,
                relative_tolerance=relative_tolerance,
                absolute_tolerance=absolute_tolerance,
            )
            for left, right in zip(recorded, regenerated)
        )
    return type(recorded) is type(regenerated) and recorded == regenerated

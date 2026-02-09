from __future__ import annotations

from formal.python.toe.observables.ovsnd03n2_secondary_density_conditions_digitized import (
    ovsnd03n2_secondary_density_conditions_digitized_record,
    write_ovsnd03n2_digitized_artifacts,
)


def test_ov_snd03n2_write_vs_no_write_consistent() -> None:
    """Regression guard: write and no-write paths must agree.

    Historically, the CLI could report a pre-write record while simultaneously
    writing artifacts/locks. This test enforces that the computed record is
    stable with respect to a re-run of artifact writing.
    """

    date = "2026-01-24"

    # "No-write" equivalent: compute record from current on-disk artifacts.
    pre = ovsnd03n2_secondary_density_conditions_digitized_record(date=date)

    # "Write" equivalent: rewrite artifacts deterministically (idempotent).
    write_ovsnd03n2_digitized_artifacts(date=date)

    post = ovsnd03n2_secondary_density_conditions_digitized_record(date=date)

    assert pre.to_jsonable() == post.to_jsonable()

    # And the intended governance gate: >=2 density conditions unblocks OV-SND-03N2.
    assert post.status["blocked"] is False
    assert post.dataset is not None
    assert int(post.dataset["row_count"]) >= 2

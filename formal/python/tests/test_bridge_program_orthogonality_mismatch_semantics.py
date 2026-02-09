from __future__ import annotations

from pathlib import Path

from formal.python.tools.bridge_program_orthogonality_mismatch_report_generate import (
    build_bridge_program_orthogonality_mismatch_report,
)
from formal.python.tools.bridge_program_orthogonality_report_generate import (
    build_bridge_program_orthogonality_report,
)


def _repo_root_from_test_file(p: Path) -> Path:
    p = p.resolve()
    if p.is_file():
        p = p.parent
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


def test_bridge_program_orthogonality_mismatch_report_contains_only_signature_disagreements() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))
    src = build_bridge_program_orthogonality_report(repo_root=repo_root)
    mismatch = build_bridge_program_orthogonality_mismatch_report(repo_root=repo_root)

    src_ids = {
        str(it.get("probe_id"))
        for it in src.get("items", [])
        if len(
            {
                bool(it["toyh_phase_bridge"]["pass"]),
                bool(it["toyh_current_bridge"]["pass"]),
                bool(it["toyhg_pair_bridge"]["pass"]),
            }
        )
        > 1
    }
    mismatch_ids = {str(it.get("probe_id")) for it in mismatch.get("items", [])}
    assert mismatch_ids == src_ids


def test_bridge_program_orthogonality_mismatch_signed_margins_are_structured() -> None:
    repo_root = _repo_root_from_test_file(Path(__file__))
    mismatch = build_bridge_program_orthogonality_mismatch_report(repo_root=repo_root)

    allowed_reason_codes = {
        "mismatch_toyh_phase_only",
        "mismatch_toyh_current_only",
        "mismatch_toyhg_pair_only",
        "mismatch_toyh_pair_only",
        "mismatch_phase_and_pair",
        "mismatch_current_and_pair",
        "mismatch_mixed",
    }

    items = list(mismatch.get("items", []))
    if not items:
        summary = dict(mismatch.get("summary", {}))
        assert int(summary.get("n_mismatch", 0)) == 0
        assert dict(summary.get("reason_code_counts", {})) == {}
        return

    for it in items:
        assert str(it.get("reason_code")) in allowed_reason_codes
        channels = dict(it.get("channels", {}))
        for ch in [
            "toyh_phase_bridge",
            "toyh_phase",
            "toyh_phase_anchor",
            "toyh_current_bridge",
            "toyh_current",
            "toyh_current_anchor",
            "toyg_bridge",
            "toyhg_pair_bridge",
            "toyg_winding",
            "toyg_mode",
            "toyg_unwrap",
        ]:
            assert ch in channels
            signed_margin = float(channels[ch]["signed_margin"])
            if not bool(channels[ch]["pass"]):
                assert signed_margin < 0.0

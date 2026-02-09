from __future__ import annotations

import json
from pathlib import Path

import pytest

from formal.python.tools.cross_anchor_bragg_vs_sound_report import build_report


def _write_lock(path: Path, obj: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        "# lock\n\n```json\n" + json.dumps(obj, indent=2) + "\n```\n",
        encoding="utf-8",
        newline="\n",
    )


def test_report_suppresses_when_mapping_missing(tmp_path: Path) -> None:
    repo_root = tmp_path

    bragg_lock = "formal/markdown/locks/observables/bragg.md"
    sound_lock = "formal/markdown/locks/observables/sound.md"
    audit_lock = "formal/markdown/locks/observables/audit.md"
    snd01_lock = "formal/markdown/locks/observables/ovbr_snd01.md"
    snd02_lock = "formal/markdown/locks/observables/ovbr_snd02.md"

    pairing_rel = "formal/external_evidence/pairing/mapping_tuples.json"
    pairing_abs = repo_root / pairing_rel
    pairing_abs.parent.mkdir(parents=True, exist_ok=True)
    pairing_abs.write_text(
        json.dumps({"schema": "OV-BR-SND-03_explicit_bragg_sound_pairing_tuples/v4", "mapping_tuples": []}, indent=2),
        encoding="utf-8",
        newline="\n",
    )

    _write_lock(
        repo_root / bragg_lock,
        {
            "rows": [
                {"condition_key": "condition_A", "c_mm_per_s": 1.0, "se_mm_per_s": 0.1},
            ]
        },
    )
    _write_lock(
        repo_root / sound_lock,
        {"results": {"primary": {"c_m_per_s": 0.001, "se_m_per_s": 0.0001}}},
    )
    _write_lock(
        repo_root / audit_lock,
        {
            "comparability": {"status": "present", "criterion": {"tolerance": 0.15}},
            "status": {
                "inputs": {
                    "mapping_tuples": {
                        "ovbr_snd03_bragg_sound_pairing": {"relpath": pairing_rel},
                    }
                }
            },
        },
    )
    _write_lock(
        repo_root / snd01_lock,
        {"comparability": {"comparable_in_principle": True, "current_blockers": [], "status": "ready"}},
    )
    _write_lock(
        repo_root / snd02_lock,
        {"mapping": {"status": "unblocked", "mapping_tuples": []}},
    )

    report = build_report(
        repo_root=repo_root,
        bragg_lock=bragg_lock,
        sound_locks=[("snd", sound_lock)],
        cross_lane_audit_lock=audit_lock,
        comparability_lock=snd01_lock,
        density_mapping_lock=snd02_lock,
        bragg_sound_pairing_mapping_relpath=None,
        mode="justified_only",
        include_suppressed=True,
    )

    assert "MODE=JUSTIFIED_ONLY" in report
    assert "JUSTIFIED=0" in report
    assert "SUPPRESSED=1" in report
    assert "No justified comparisons were produced" in report
    assert "NO_BRAGG_SOUND_MAPPING_TUPLE" in report


def test_report_includes_only_mapped_pairs(tmp_path: Path) -> None:
    repo_root = tmp_path

    bragg_lock = "formal/markdown/locks/observables/bragg.md"
    sound_lock = "formal/markdown/locks/observables/sound.md"
    audit_lock = "formal/markdown/locks/observables/audit.md"
    snd01_lock = "formal/markdown/locks/observables/ovbr_snd01.md"
    snd02_lock = "formal/markdown/locks/observables/ovbr_snd02.md"

    pairing_rel = "formal/external_evidence/pairing/mapping_tuples.json"
    pairing_abs = repo_root / pairing_rel
    pairing_abs.parent.mkdir(parents=True, exist_ok=True)
    pairing_abs.write_text(
        json.dumps(
            {
                "schema": "OV-BR-SND-03_explicit_bragg_sound_pairing_tuples/v4",
                "mapping_tuples": [
                    {"bragg_condition_key": "condition_A", "sound_lock_path": sound_lock},
                ],
            },
            indent=2,
        ),
        encoding="utf-8",
        newline="\n",
    )

    _write_lock(
        repo_root / bragg_lock,
        {
            "rows": [
                {"condition_key": "condition_A", "c_mm_per_s": 1.0, "se_mm_per_s": 0.1},
            ]
        },
    )
    _write_lock(
        repo_root / sound_lock,
        {"results": {"primary": {"c_m_per_s": 0.001, "se_m_per_s": 0.0001}}},
    )
    _write_lock(
        repo_root / audit_lock,
        {
            "comparability": {"status": "present", "criterion": {"tolerance": 0.15}},
            "status": {
                "inputs": {
                    "mapping_tuples": {
                        "ovbr_snd03_bragg_sound_pairing": {"relpath": pairing_rel},
                    }
                }
            },
        },
    )
    _write_lock(
        repo_root / snd01_lock,
        {"comparability": {"comparable_in_principle": True, "current_blockers": [], "status": "ready"}},
    )
    _write_lock(
        repo_root / snd02_lock,
        {"mapping": {"status": "unblocked", "mapping_tuples": []}},
    )

    report = build_report(
        repo_root=repo_root,
        bragg_lock=bragg_lock,
        sound_locks=[("snd", sound_lock)],
        cross_lane_audit_lock=audit_lock,
        comparability_lock=snd01_lock,
        density_mapping_lock=snd02_lock,
        bragg_sound_pairing_mapping_relpath=None,
        mode="justified_only",
        include_suppressed=False,
    )

    assert "MODE=JUSTIFIED_ONLY" in report
    assert "JUSTIFIED=1" in report
    assert "SUPPRESSED=0" in report
    assert "PASS" in report


def test_include_suppressed_does_not_emit_metrics_columns(tmp_path: Path) -> None:
    repo_root = tmp_path

    bragg_lock = "formal/markdown/locks/observables/bragg.md"
    sound_ok_lock = "formal/markdown/locks/observables/sound_ok.md"
    sound_supp_lock = "formal/markdown/locks/observables/sound_supp.md"
    audit_lock = "formal/markdown/locks/observables/audit.md"
    snd01_lock = "formal/markdown/locks/observables/ovbr_snd01.md"
    snd02_lock = "formal/markdown/locks/observables/ovbr_snd02.md"

    pairing_rel = "formal/external_evidence/pairing/mapping_tuples.json"
    pairing_abs = repo_root / pairing_rel
    pairing_abs.parent.mkdir(parents=True, exist_ok=True)
    pairing_abs.write_text(
        json.dumps(
            {
                "schema": "OV-BR-SND-03_explicit_bragg_sound_pairing_tuples/v4",
                "mapping_tuples": [
                    {"bragg_condition_key": "condition_A", "sound_lock_path": sound_ok_lock},
                ],
            },
            indent=2,
        ),
        encoding="utf-8",
        newline="\n",
    )

    _write_lock(
        repo_root / bragg_lock,
        {"rows": [{"condition_key": "condition_A", "c_mm_per_s": 1.0, "se_mm_per_s": 0.1}]},
    )
    _write_lock(repo_root / sound_ok_lock, {"results": {"primary": {"c_m_per_s": 0.001, "se_m_per_s": 0.0001}}})
    _write_lock(repo_root / sound_supp_lock, {"results": {"primary": {"c_m_per_s": 0.002, "se_m_per_s": 0.0001}}})
    _write_lock(
        repo_root / audit_lock,
        {
            "comparability": {"status": "present", "criterion": {"tolerance": 0.15}},
            "status": {
                "inputs": {
                    "mapping_tuples": {
                        "ovbr_snd03_bragg_sound_pairing": {"relpath": pairing_rel},
                    }
                }
            },
        },
    )
    _write_lock(
        repo_root / snd01_lock,
        {"comparability": {"comparable_in_principle": True, "current_blockers": [], "status": "ready"}},
    )
    _write_lock(repo_root / snd02_lock, {"mapping": {"status": "unblocked", "mapping_tuples": []}})

    report = build_report(
        repo_root=repo_root,
        bragg_lock=bragg_lock,
        sound_locks=[("ok", sound_ok_lock), ("supp", sound_supp_lock)],
        cross_lane_audit_lock=audit_lock,
        comparability_lock=snd01_lock,
        density_mapping_lock=snd02_lock,
        bragg_sound_pairing_mapping_relpath=None,
        mode="justified_only",
        include_suppressed=True,
    )

    marker = "## Unjustified numeric checks (suppressed by default)"
    assert marker in report
    after_marker = report.split(marker, 1)[1]
    table_header = "| Bragg condition_key | Sound lock | Status | Reasons |"
    assert table_header in after_marker

    # Only inspect the suppressed table block (stop at the first blank line after it)
    table_start = after_marker.index(table_header)
    table_text = after_marker[table_start:]
    table_lines = []
    for line in table_text.splitlines():
        if not line.strip() and table_lines:
            break
        if line.startswith("|"):
            table_lines.append(line)
    suppressed_table_block = "\n".join(table_lines)

    assert table_header in suppressed_table_block
    assert "|Δ|" not in suppressed_table_block
    assert "rel_err" not in suppressed_table_block
    assert "tol check" not in suppressed_table_block


@pytest.mark.parametrize("mode", ["numeric_only", "justified_only"])
def test_report_header_includes_mode(tmp_path: Path, mode: str) -> None:
    repo_root = tmp_path

    bragg_lock = "formal/markdown/locks/observables/bragg.md"
    sound_lock = "formal/markdown/locks/observables/sound.md"

    _write_lock(repo_root / bragg_lock, {"rows": [{"condition_key": "condition_A", "c_mm_per_s": 1.0}]})
    _write_lock(repo_root / sound_lock, {"results": {"primary": {"c_m_per_s": 0.001}}})

    report = build_report(
        repo_root=repo_root,
        bragg_lock=bragg_lock,
        sound_locks=[("snd", sound_lock)],
        cross_lane_audit_lock=None,
        comparability_lock=None,
        density_mapping_lock=None,
        bragg_sound_pairing_mapping_relpath=None,
        mode=mode,
        include_suppressed=False,
    )

    assert f"MODE={mode.upper()}" in report

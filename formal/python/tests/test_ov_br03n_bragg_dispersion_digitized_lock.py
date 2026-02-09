from __future__ import annotations

import json
import re
from pathlib import Path

from formal.python.toe.observables.ovbr03n_bragg_dispersion_k_omega_digitized import (
    ovbr03n_digitized_dispersion_record,
)


def find_repo_root(start: Path) -> Path:
    p = start.resolve()
    while p != p.parent:
        if (p / "formal").exists():
            return p
        p = p.parent
    raise RuntimeError("Could not locate repo root (expected a 'formal' directory).")


REPO_ROOT = find_repo_root(Path(__file__))


def _extract_json_block(md_text: str) -> dict:
    m = re.search(r"```json\s*(\{.*?\})\s*```", md_text, flags=re.DOTALL)
    if m is None:
        raise AssertionError("Missing JSON record block")
    return json.loads(m.group(1))


def _extract_record_fingerprint(md_text: str) -> str:
    m = re.search(r"Record fingerprint:\s*`([0-9a-f]{64})`", md_text)
    if m is None:
        raise AssertionError("Missing record fingerprint line")
    return m.group(1)


def test_ov_br03n_lock_exists_and_matches_computed_record_and_is_deterministic() -> None:
    rec = ovbr03n_digitized_dispersion_record(date="2026-01-25")

    lock_path = (
        REPO_ROOT
        / "formal"
        / "markdown"
        / "locks"
        / "observables"
        / "OV-BR-03_bragg_dispersion_k_omega_digitized.md"
    )
    lock_text = lock_path.read_text(encoding="utf-8")
    locked = _extract_json_block(lock_text)

    # Expected schema and basic fields.
    assert locked["schema"] == "OV-BR-03N/v1"
    assert locked["digitization_id"] == "OV-BR-03N"

    # Both conditions must exist and have stable row counts.
    ca = locked["dataset"]["condition_A"]
    cb = locked["dataset"]["condition_B"]

    assert ca["semantic"] == "filled circles"
    assert cb["semantic"] == "open circles"

    assert int(ca["row_count"]) >= 6
    assert int(cb["row_count"]) >= 6

    # Canonical selection currently targets 25 points per condition.
    assert int(ca["row_count"]) == 25
    assert int(cb["row_count"]) == 25

    # Locked record must match computed record, including fingerprint.
    assert locked == rec.to_jsonable()
    assert _extract_record_fingerprint(lock_text) == rec.fingerprint()


def test_ov_br03n_metadata_locks_signature_semantics() -> None:
    meta_path = (
        REPO_ROOT
        / "formal"
        / "external_evidence"
        / "bec_bragg_shammass_2012"
        / "ovbr03n_digitization"
        / "k_omega_digitization.metadata.json"
    )

    meta = json.loads(meta_path.read_text(encoding="utf-8"))

    assert meta["schema"] == "OV-BR-03N_k_omega_digitization_metadata/v1"
    dig = meta["digitization"]

    assert dig["classifier"] == "signature_split_v1"
    assert dig["discriminator_rule_id"] == "signature_split_v1"

    sig = dig["marker_signatures_used"]
    assert sig["condition_A_filled"]["area"] == 50
    assert sig["condition_A_filled"]["bbox_w"] == 10
    assert sig["condition_A_filled"]["bbox_h"] == 10

    assert sig["condition_B_open"]["area"] == 85
    assert sig["condition_B_open"]["bbox_w"] == 14
    assert sig["condition_B_open"]["bbox_h"] == 19

    counts = dig["classification_counts"]
    assert int(counts["exact"]["condition_A"]) >= 50
    assert int(counts["exact"]["condition_B"]) >= 50

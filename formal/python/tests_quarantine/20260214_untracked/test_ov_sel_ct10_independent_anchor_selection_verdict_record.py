from __future__ import annotations

from formal.python.toe.observables.ovselct10_independent_anchor_selection_verdict_record import (
    ovselct10_selection_verdict_record,
)


def test_ov_sel_ct10_selection_verdict_record_is_deterministic_and_admissible() -> None:
    rec1 = ovselct10_selection_verdict_record(status_date="2026-02-12")
    rec2 = ovselct10_selection_verdict_record(status_date="2026-02-12")

    assert rec1.to_jsonable() == rec2.to_jsonable()
    assert rec1.fingerprint() == rec2.fingerprint()

    assert rec1.schema == "OV-SEL-CT10-01_independent_anchor_selection_verdict/v1"
    assert rec1.verdict == "admissible"
    assert rec1.failed_checks == []

    assert rec1.policy["mode"] == "pre_activation_admission_gate_only"
    assert rec1.policy["scope_limit"] == "external_anchor_only"
    assert rec1.policy["filter_doc"] == "formal/docs/programs/CT10_independent_external_anchor_selection_filter_v0.md"

    required_fp_keys = {
        "filter_doc_sha256",
        "metadata_sha256",
        "source_citation_sha256",
        "preprocessing_lineage_sha256",
        "dataset_sha256",
    }
    assert set(rec1.fingerprints.keys()) == required_fp_keys
    assert all(len(str(v)) == 64 for v in rec1.fingerprints.values())

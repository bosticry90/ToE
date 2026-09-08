from __future__ import annotations

from formal.python.tools import pillar_v1_staging_identity_adjudication as subject


def test_all_staging_dependencies_are_mapped_once_without_provenance_gaps() -> None:
    ledger = subject.dependency_ledger()
    assert len(ledger) == 23
    assert len({entry["path"] for entry in ledger}) == 23
    assert all(entry["provenance"] == "VERIFIED" for entry in ledger)
    assert all(entry["current_critical"] is False for entry in ledger)


def test_each_historical_frozen_pin_is_reconstructible_without_dirty_main() -> None:
    for path, expected_sha256 in subject._expected_frozen_hashes().items():
        _, representation, raw = subject._historical_representation(
            path, expected_sha256
        )
        assert subject.sha256_bytes(raw) == expected_sha256
        assert representation in {
            "GIT_BLOB_EXACT",
            "CRLF_FROM_FROZEN_GIT_BLOB",
            "ACCEPTED_MIXED_EOL_RECONSTRUCTION",
        }


def test_in_memory_probe_exposes_no_new_root_beyond_accepted_v1_mismatch() -> None:
    adjudication = subject.build_adjudication()
    probe = adjudication["role_aware_in_memory_probe"]
    assert adjudication["result"].endswith("REPAIR_JUSTIFIED")
    assert adjudication["provenance_blocked_dependencies"] == 0
    assert adjudication["isolated_historical_reconstruction"]["passed"] is True
    assert probe["passed_decision_count"] == 25
    assert probe["failed_decision_ids"] == [
        "supporting_sources_have_authorized_bounded_class"
    ]
    assert probe["persisted_substitutions"] == 0

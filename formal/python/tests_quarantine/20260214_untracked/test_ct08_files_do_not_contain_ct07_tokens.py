from __future__ import annotations

from pathlib import Path


FORBIDDEN_TOKENS = [
    "CT-07",
    "ct07_",
    "CT07",
    "lowk",
    "k_max_um_inv",
    "c_s2_scale_negative",
    "_apply_lowk_slice",
]

CT08_FILES = [
    "formal/python/toe/comparators/ct08_external_anchor_dispersion_highk_slice_v0.py",
    "formal/python/tools/ct08_external_anchor_dispersion_highk_front_door.py",
    "formal/python/tests/test_ct08_external_anchor_dispersion_highk_slice_lane_doc.py",
    "formal/python/tests/test_ct08_external_anchor_dispersion_highk_slice_v0_front_door_contract_freeze.py",
    "formal/python/tests/test_ct08_external_anchor_dispersion_highk_slice_v0_front_door.py",
    "formal/python/tests/test_ct08_external_anchor_dispersion_highk_slice_v0_surface_contract_freeze.py",
    "formal/python/tests/test_ct08_external_anchor_dispersion_highk_slice_v0_pinned_artifacts.py",
    "formal/python/tests/test_ct08_external_anchor_dispersion_highk_slice_v0_lock.py",
    "formal/docs/programs/CT08_external_anchor_dispersion_highk_slice_v0.md",
    "formal/docs/ct08_external_anchor_dispersion_highk_slice_v0_front_door_contract.md",
    "formal/external_evidence/ct08_external_anchor_dispersion_highk_domain_01/README.md",
    "formal/external_evidence/ct08_external_anchor_dispersion_highk_domain_01/source_citation.md",
    "formal/external_evidence/ct08_external_anchor_dispersion_highk_domain_01/dataset_metadata.json",
    "formal/external_evidence/ct08_external_anchor_dispersion_highk_domain_01/ct08_reference_report.json",
    "formal/external_evidence/ct08_external_anchor_dispersion_highk_domain_01/ct08_candidate_report.json",
    "formal/markdown/locks/observables/CT-08_external_anchor_dispersion_highk_slice_v0.md",
]


def test_ct08_files_do_not_contain_ct07_or_lowk_residue() -> None:
    repo_root = Path(__file__).resolve().parents[3]

    for relpath in CT08_FILES:
        path = repo_root / relpath
        assert path.exists(), f"Expected CT-08 file is missing: {relpath}"
        text = path.read_text(encoding="utf-8")

        for token in FORBIDDEN_TOKENS:
            assert token not in text, f"Forbidden token '{token}' found in {relpath}"

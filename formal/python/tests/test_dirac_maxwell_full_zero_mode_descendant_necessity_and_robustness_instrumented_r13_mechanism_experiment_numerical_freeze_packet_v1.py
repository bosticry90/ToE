from __future__ import annotations

import json
from collections import Counter
from functools import lru_cache
from pathlib import Path
from typing import Any

from formal.python.meta.repo_environment import find_repo_root
from formal.python.tools import (
    dirac_maxwell_full_zero_mode_descendant_necessity_and_robustness_instrumented_r13_mechanism_experiment_numerical_freeze_packet_v1
    as freeze,
)


ROOT = find_repo_root(Path(__file__))


@lru_cache(maxsize=1)
def _artifact_bytes() -> dict[str, bytes]:
    return freeze.artifact_bytes()


@lru_cache(maxsize=1)
def _artifacts() -> tuple[
    dict[str, Any],
    dict[str, Any],
    dict[str, Any],
    dict[str, Any],
    dict[str, Any],
]:
    raw = _artifact_bytes()
    return tuple(
        json.loads(raw[path].decode("utf-8"))
        for path in (
            freeze.PACKET_RELATIVE_PATH,
            freeze.RUN_MATRIX_RELATIVE_PATH,
            freeze.IDENTITY_RELATIVE_PATH,
            freeze.MANIFEST_RELATIVE_PATH,
            freeze.REPORT_RELATIVE_PATH,
        )
    )  # type: ignore[return-value]


def test_exact_artifact_regeneration_is_current_and_deterministic() -> None:
    first = _artifact_bytes()
    assert set(first) == {
        freeze.PACKET_RELATIVE_PATH,
        freeze.RUN_MATRIX_RELATIVE_PATH,
        freeze.IDENTITY_RELATIVE_PATH,
        freeze.MANIFEST_RELATIVE_PATH,
        freeze.REPORT_RELATIVE_PATH,
    }
    assert all((ROOT / path).read_bytes() == raw for path, raw in first.items())

    # A second pure build must reproduce every byte.  No write or execution
    # entrypoint is involved in either build.
    assert freeze.artifact_bytes() == first


def test_v1_preserves_the_exact_v0_scientific_matrix() -> None:
    _, matrix, _, _, _ = _artifacts()
    predecessor = json.loads(
        (ROOT / freeze.PREDECESSOR_MATRIX_RELATIVE_PATH).read_text(
            encoding="utf-8"
        )
    )
    assert matrix["record_count"] == predecessor["record_count"] == 6
    assert matrix["expected_run_id_order"] == predecessor["expected_run_id_order"]

    for key, value in predecessor.items():
        if key not in {"schema_id", "generation_policy", "records"}:
            assert matrix[key] == value

    added_record_fields = {
        "implementation_closure_sha256",
        "executor_id",
        "executor_sha256",
        "raw_evidence_assembler_id",
        "raw_evidence_assembler_sha256",
        "classifier_id",
        "classifier_sha256",
        "semantic_contract_id",
        "semantic_contract_sha256",
        "physical_configuration_core",
        "physical_configuration_core_sha256",
        "scientific_input_core",
        "scientific_input_core_sha256",
        "input_hash_contract",
    }
    for old, new in zip(predecessor["records"], matrix["records"], strict=True):
        assert old["run_id"] == new["run_id"]
        assert set(new) - set(old) == added_record_fields
        assert set(old) - set(new) == {"input_hash_material_excludes"}
        for key, value in old.items():
            if key not in {"input_hash", "input_hash_material_excludes"}:
                assert new[key] == value

    assert matrix["supersedes_blocked_predecessor"][
        "scientific_configuration_changed"
    ] is False


def test_six_scientific_hashes_reconstruct_and_three_pairs_share_physics() -> None:
    _, matrix, _, _, _ = _artifacts()
    closure_hash = matrix["implementation_closure_sha256"]
    scientific_hashes: set[str] = set()
    physical_hashes: set[str] = set()
    records_by_id = {record["run_id"]: record for record in matrix["records"]}

    for record in matrix["records"]:
        reconstructed_physical = freeze.build_physical_configuration_core(
            record, closure_hash
        )
        assert reconstructed_physical == record["physical_configuration_core"]
        physical_hash = freeze.sha256_bytes(
            freeze.canonical_json_bytes(reconstructed_physical)
        )
        assert physical_hash == record["physical_configuration_core_sha256"]
        assert physical_hash == matrix["scientific_input_hash_contract"][
            "physical_configuration_sha256_by_run_id"
        ][record["run_id"]]

        reconstructed_scientific = freeze.build_scientific_input_core(
            record, reconstructed_physical, closure_hash
        )
        assert reconstructed_scientific == record["scientific_input_core"]
        scientific_hash = freeze.scientific_input_hash(reconstructed_scientific)
        assert scientific_hash == record["scientific_input_core_sha256"]
        assert scientific_hash == record["input_hash"]
        assert scientific_hash == matrix["scientific_input_hash_contract"][
            "scientific_input_sha256_by_run_id"
        ][record["run_id"]]
        scientific_hashes.add(scientific_hash)
        physical_hashes.add(physical_hash)

    assert len(scientific_hashes) == 6
    assert len(physical_hashes) == 3

    pair_sets = {
        frozenset((record["run_id"], record["paired_run_id"]))
        for record in matrix["records"]
    }
    assert len(pair_sets) == 3
    for pair in pair_sets:
        first_id, second_id = tuple(pair)
        first = records_by_id[first_id]
        second = records_by_id[second_id]
        assert first["physical_configuration_core_sha256"] == second[
            "physical_configuration_core_sha256"
        ]
        assert first["scientific_input_core_sha256"] != second[
            "scientific_input_core_sha256"
        ]


def test_scientific_input_hash_contract_has_zero_exclusions() -> None:
    packet, matrix, _, _, report = _artifacts()
    contract = matrix["scientific_input_hash_contract"]
    assert contract["positive_inclusion_only"] is True
    assert contract["exclusion_lists_authorized"] is False
    assert report["freeze_summary"]["input_exclusion_field_count"] == 0
    assert packet["predecessor_correction_scope"][
        "accepted_static_six_run_matrix_preserved"
    ] is True
    for record in matrix["records"]:
        assert "input_hash_material_excludes" not in record
        assert record["input_hash_contract"]["excluded_field_count"] == 0
        assert record["input_hash_contract"]["material"] == (
            "scientific_input_core positive-inclusion object only"
        )


def test_all_23_support_constants_have_complete_nonfuture_provenance() -> None:
    packet, _, _, _, report = _artifacts()
    classifier = packet["classifier_freeze"]
    constants = classifier["support_constants"]
    provenance = classifier["support_constant_provenance"]
    leaves = {
        (hypothesis, constant_id): value
        for hypothesis, hypothesis_constants in constants.items()
        for constant_id, value in hypothesis_constants.items()
    }
    records = {
        (record["hypothesis"], record["constant_id"]): record
        for record in provenance
    }
    assert classifier["support_constant_count"] == len(leaves) == 23
    assert len(provenance) == len(records) == 23
    assert set(records) == set(leaves)
    assert report["freeze_summary"]["support_constant_provenance_count"] == 23

    required_fields = {
        "hypothesis",
        "constant_id",
        "value",
        "unit",
        "units",
        "role",
        "source_category",
        "source_commit",
        "source_artifact",
        "source_record_ids",
        "derivation_formula",
        "rounding_rule",
        "scientific_meaning",
        "decision_bearing_or_descriptive",
        "nonfuture",
        "declared_before_mechanism_execution",
        "future_mechanism_outputs_used",
        "posthoc_fit_or_point_selection_used",
    }
    for key, record in records.items():
        assert required_fields <= set(record)
        assert record["value"] == leaves[key]
        assert record["unit"] == record["units"]
        assert record["source_category"] in freeze.semantic_v1.SOURCE_CATEGORIES
        assert record["source_record_ids"]
        assert record["derivation_formula"]
        assert record["rounding_rule"]
        assert record["scientific_meaning"]
        assert record["decision_bearing_or_descriptive"] == "DECISION_BEARING"
        assert record["nonfuture"] is True
        assert record["declared_before_mechanism_execution"] is True
        assert record["future_mechanism_outputs_used"] is False
        assert record["posthoc_fit_or_point_selection_used"] is False


def test_h_c_uses_independent_paths_and_gamma32_is_not_decision_bearing() -> None:
    packet, _, _, _, report = _artifacts()
    closure = packet["discrete_Maxwell_continuity_closure_freeze"]
    h_c = closure["decision_bearing_H_C"]
    assert h_c["path_A"] != h_c["path_B"]
    assert "directly stored" in h_c["path_A"]
    assert "independently recomputed" in h_c["path_B"]
    assert h_c["registered_Maxwell_source_reused_in_path_B"] is False
    assert h_c["gamma32_or_gamma_n_used"] is False
    assert closure["legacy_Q"]["mechanism_decision_bearing"] is False
    assert closure["legacy_Q"]["may_support_H_C"] is False

    observable = {
        item["observable_id"]: item
        for item in packet["mechanism_observable_registry"]
    }["MAXWELL_TO_CONTINUITY_CLOSURE_RESIDUAL"]
    assert "Rp_terminal_direct" in observable["formula"]
    assert "independently_recomputed_Dirac_current" in observable["formula"]
    assert observable["legacy_Q_status"] == (
        "OPERATOR_CONSISTENCY_GATE_ONLY_NOT_H_C_EVIDENCE"
    )
    assert all(
        "gamma" not in constant_id.casefold()
        for constant_id in packet["classifier_freeze"]["support_constants"]["H_C"]
    )
    assert report["freeze_summary"]["gamma32_mechanism_decision_count"] == 0


def test_exact_41_control_registry_contains_the_9_and_20_required_classes() -> None:
    packet, _, _, _, report = _artifacts()
    registry = packet["freeze_adversarial_control_registry"]
    control_ids = [record["control_id"] for record in registry]
    assert packet["freeze_adversarial_control_count"] == len(registry) == 41
    assert len(control_ids) == len(set(control_ids))
    assert report["freeze_summary"]["adversarial_control_count"] == 41
    assert Counter(record["category"] for record in registry) == {
        "PRESERVED_V0_REGISTERED_CONTROL": 12,
        "V0_REVIEW_REQUIRED_MISSING_CONTROL": 9,
        "V0_REVIEW_EXACT_MATRIX_IDENTITY_MUTATION": 20,
    }
    assert packet["review_missing_control_count"] == 9
    assert set(freeze.semantic_v1.MISSING_REVIEW_CONTROL_IDS) <= set(control_ids)
    identity_ids = {
        f"M_FREEZE_MATRIX_IDENTITY_FIELD_{field.upper()}"
        for field in freeze.semantic_v1.IDENTITY_MUTATION_FIELDS
    }
    assert packet["identity_mutation_control_count"] == len(identity_ids) == 20
    assert identity_ids <= set(control_ids)
    assert all(record["mutation"] for record in registry)
    assert all(
        "expected_decision_change" in record
        and (
            "expected_first_diagnostic" in record
            or "expected_first_diagnostic_by_variant" in record
        )
        for record in registry
    )


def test_twelve_role_payload_paths_form_exact_bijections() -> None:
    _, matrix, identity, _, _ = _artifacts()
    outputs = identity["outputs"]
    assert identity["record_count"] == len(outputs) == 6
    assert identity["role_payload_file_count"] == 12
    assert identity["raw_evidence_contract"]["required_role_payload_count"] == 12

    run_ids = {record["run_id"] for record in matrix["records"]}
    assert {output["run_id"] for output in outputs} == run_ids
    json_paths = {output["json_relative_output_path"] for output in outputs}
    npz_paths = {output["npz_relative_output_path"] for output in outputs}
    all_paths = json_paths | npz_paths
    assert len(json_paths) == len(npz_paths) == 6
    assert len(all_paths) == 12
    assert len({path.casefold() for path in all_paths}) == 12
    assert all(path.startswith(freeze.EXPERIMENT_OUTPUT_ROOT + "/") for path in all_paths)

    for output in outputs:
        run_id = output["run_id"]
        json_path = output["json_relative_output_path"]
        npz_path = output["npz_relative_output_path"]
        assert identity["run_id_to_json_relative_output_path"][run_id] == json_path
        assert identity["json_relative_output_path_to_run_id"][json_path] == run_id
        assert identity["run_id_to_npz_relative_output_path"][run_id] == npz_path
        assert identity["npz_relative_output_path_to_run_id"][npz_path] == run_id


def test_future_output_root_is_absent_and_authority_remains_preparation_only() -> None:
    packet, _, identity, manifest, report = _artifacts()
    output_root = ROOT / freeze.EXPERIMENT_OUTPUT_ROOT
    assert not output_root.exists()
    assert identity["output_root"] == freeze.EXPERIMENT_OUTPUT_ROOT
    assert identity["output_root_must_be_absent_before_authorized_execution"] is True
    assert manifest["future_experiment_output_root_absent"] is True
    assert manifest["execution_authorized"] is False
    assert packet["preparation_self_validation"]["simulation_invocation_count"] == 0
    assert packet["preparation_self_validation"]["future_output_root_created"] is False
    assert packet["runtime_execution_authority_proposal"][
        "execution_authorized_by_preparation"
    ] is False

    boundary = packet["authority_boundary"]
    assert packet["verdict"] == "PREPARED_PENDING_INDEPENDENT_REVIEW"
    assert packet["selected_next_target"] == report["selected_next_target"]
    assert packet["selected_next_target"] == freeze.REVIEW_TARGET
    assert packet["selected_next_target"] != freeze.POST_ACCEPTANCE_TARGET
    assert boundary == report["authority_boundary"]
    assert boundary["numerical_freeze_v1_prepared"] is True
    assert boundary["numerical_freeze_v1_independently_accepted"] is False
    assert boundary["experiment_execution_authorized"] is False
    assert boundary["experiment_execution_performed"] is False
    assert boundary["canonical_execution_count"] == 1
    assert boundary["canonical_robustness"] == "NUMERICALLY_BLOCKED"
    assert boundary["root_mechanism"] == "UNRESOLVED"
    assert boundary["materiality"] == "NOT_EVALUATED_NUMERICAL_BLOCK"
    assert boundary["robustness_reclassification_authorized"] is False
    assert boundary["materiality_evaluation_authorized"] is False
    assert boundary["threshold_change_from_future_data_authorized"] is False
    assert boundary["new_E_REPRO_claim"] is False
    custody = packet["output_custody_and_execution_freeze"]
    assert custody["execution_authorized_now"] is False
    assert custody["retry"] == custody["overwrite"] == "FORBIDDEN"

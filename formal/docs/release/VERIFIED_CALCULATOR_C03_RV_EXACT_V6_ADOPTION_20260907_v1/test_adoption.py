"""Read-only adoption-record regressions, not physics or owner authentication."""
import copy
from datetime import datetime
import hashlib
import json
from pathlib import Path
import subprocess
import unittest


HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
COMMIT = "f041a55782f8f1b33491dc03f62543e17c2714cc"
PACKET = "formal/docs/release/TOE_EXTERNAL_COMPARATORS_AND_V6_DECISION_20260907_v1/"
RELEASE = "formal/docs/release/"
CONTRACT_PATHS = [
    PACKET + "v6_decision_draft.md", PACKET + "v6_scope.json",
    PACKET + "manifest.json", PACKET + "validate_packet.py",
    RELEASE + "VERIFIED_CALCULATOR_C03_RV_EXACT_AMENDED_REQUALIFICATION_SEQUENCE_20260907_v1.md",
    RELEASE + "VERIFIED_CALCULATOR_C03_RV_EXACT_V6_EXECUTION_RUN_LOG_RESULT_20260907_3307e355.json",
]


def blob(path, commit=COMMIT):
    return subprocess.check_output(["git", "show", f"{commit}:{path}"], cwd=REPO)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def validate(record, scope, refs):
    require(record["schema_id"] == "C03RVV6AuthorityAdoptionRecordV1", "schema")
    require(record["disposition"] == "ADOPTED" and record["decision_adopted"] is True, "adoption")
    require(record["adopted_status"] == "C03_RV_EXACT_COMPUTATION_REQUALIFIED", "status")
    require(record["decision_maker"]["authorization_kind"] == "EXPLICIT_OWNER_INSTRUCTION", "owner authorization")
    remote = record["prior_remote_preservation"]
    require(remote["commit"] == remote["observed_remote_commit"] == COMMIT, "prior preservation")
    require(remote["confirmed_before_adoption"] is True, "prior preservation")
    parse = lambda t: datetime.fromisoformat(t.replace("Z", "+00:00"))
    require(parse(remote["confirmed_at_utc"]) < parse(record["effective_at_utc"]), "adoption order")
    require(record["pinned_references"] == refs, "evidence pins")
    adopted = record["scope"]
    for key in ("computation_id", "candidate_hash", "graph_hash", "runtime_certificate_hash",
                "windows_bundle_id", "linux_bundle_id", "original_v1_bundle_id",
                "dependency_closure_hashes", "challenge_packets_hash"):
        require(adopted[key] == scope[key], f"scope identity: {key}")
    for key in ("physics_profile_hash", "verification_policy_hash"):
        require(adopted[key] == scope["request"][key], f"contract identity: {key}")
    expected_roots = [{k: r[k] for k in ("root_id", "value_hash_domain", "canonical_value_hash", "verification_class")}
                      for r in scope["roots"]]
    require(adopted["roots"] == expected_roots and len(expected_roots) == 16, "root boundary")
    require(adopted["records"] == ["C03", "RV01", "RV02", "RV03", "RV04", "RV05", "RV06"], "record boundary")
    require([adopted[k] for k in ("source_node_count", "derived_node_count", "output_node_count",
                                 "total_node_count", "physics_operation_count", "mandatory_challenge_count")]
            == [31, 160, 16, 207, 19, 373], "census")
    for key in ("arbitrary_inputs_covered", "future_versions_automatically_covered",
                "numerical_observables_covered", "additional_records_or_roots_covered"):
        require(adopted[key] is False, "scope expansion")
    require(record["preserved_project_state"] == {
        "Route_C": "2/4", "strict_historical_native_exact_equivalence": "1/4",
        "production": "76/1188", "rows_77_through_96": "CLOSED", "scientific_promotion": False,
        "product_v1_release": False, "production_activation": False, "CCFT_promotion": False,
        "ToE_promotion": False}, "non-promotion")
    effect = record["authority_effect"]
    require(effect["bounded_computational_adoption"] is True, "adoption effect")
    for key in ("model_truth_authority_changed", "per_claim_historical_authority_changed",
                "original_bundle_authority_bindings_rewritten", "verification_receipts_rewritten",
                "computation_identity_changed", "new_AuthorityAttachmentV1_created",
                "new_FrozenEvidenceBundleV1_created", "historical_104_check_log_rewritten",
                "claimed_104_of_104_pass", "scope_document_historical_draft_status_rewritten"):
        require(effect[key] is False, "historical evidence / non-promotion")
    require([r["id"] for r in record["adjudication_reconciliations"]] == [
        "REVIEW_DISPOSITION_VOCABULARY", "ACTUAL_REVIEW_LINUX_ORDER",
        "HISTORICAL_104_CHECK_SNAPSHOT", "DURABLE_ARCHIVE_CUSTODY"], "reconciliations")
    require(record["closure"]["exact_profile_work"] == "STOP_UNLESS_NEW_FALSIFIER_OR_SEPARATELY_AUTHORIZED_SCOPE_CHANGE", "closure")
    for key in ("follow_on_scientific_or_product_tasks_started", "external_comparator_or_CCFT_work_launched"):
        require(record["closure"][key] is False, "follow-on authority")


class AdoptionChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.record = json.loads((HERE / "adoption.json").read_bytes())
        cls.scope = json.loads(blob(PACKET + "v6_scope.json"))
        cls.refs = [{"path": p, "git_commit": COMMIT, "hash_domain": "GIT_BLOB_BYTES_SHA256",
                     "git_blob_sha256": hashlib.sha256(blob(p)).hexdigest()} for p in CONTRACT_PATHS]
        cls.refs += [{"path": r["path"], "git_commit": cls.scope["evidence_git_commit"],
                      "hash_domain": r["hash_domain"], "git_blob_sha256": r["sha256"]}
                     for r in cls.scope["evidence_references"]]

    def test_adopted_record_matches_frozen_scope(self):
        validate(self.record, self.scope, self.refs)

    def test_pins_and_historical_payloads_unchanged(self):
        for r in self.refs + [self.record["linux_archive"]]:
            original = blob(r["path"], r["git_commit"])
            self.assertEqual(hashlib.sha256(original).hexdigest(), r["git_blob_sha256"])
            local = (REPO / r["path"]).read_bytes()
            # Text checkout representation may differ; all content must remain.
            normalize = lambda b: b.replace(b"\r\n", b"\n").replace(b"\r", b"\n")
            self.assertEqual(local if r["path"].endswith(".zip") else normalize(local),
                             original if r["path"].endswith(".zip") else normalize(original))
        self.assertEqual(self.scope["status"], "DRAFT_NOT_ADOPTED")
        self.assertFalse(json.loads(blob(PACKET + "manifest.json"))["decision_adopted"])

    def reject(self, mutation, message):
        changed = copy.deepcopy(self.record)
        mutation(changed)
        with self.assertRaisesRegex(ValueError, message):
            validate(changed, self.scope, self.refs)

    def test_missing_root_rejected(self):
        self.reject(lambda r: r["scope"]["roots"].pop(), "root boundary")

    def test_duplicate_root_rejected(self):
        self.reject(lambda r: r["scope"]["roots"].append(r["scope"]["roots"][0]), "root boundary")

    def test_altered_root_value_rejected(self):
        self.reject(lambda r: r["scope"]["roots"][0].update(canonical_value_hash="0" * 64), "root boundary")

    def test_different_computation_rejected(self):
        self.reject(lambda r: r["scope"].update(computation_id="0" * 64), "scope identity")

    def test_universal_scope_rejected(self):
        self.reject(lambda r: r["scope"].update(arbitrary_inputs_covered=True), "scope expansion")

    def test_scientific_and_production_promotion_rejected(self):
        for field in ("scientific_promotion", "product_v1_release", "production_activation", "CCFT_promotion", "ToE_promotion"):
            with self.subTest(field=field):
                self.reject(lambda r: r["preserved_project_state"].update({field: True}), "non-promotion")

    def test_altered_reference_rejected(self):
        self.reject(lambda r: r["pinned_references"][0].update(git_blob_sha256="0" * 64), "evidence pins")

    def test_premature_adoption_rejected(self):
        self.reject(lambda r: r.update(effective_at_utc="2026-09-08T01:00:00Z"), "adoption order")

    def test_self_promotion_rejected(self):
        self.reject(lambda r: r["decision_maker"].update(authorization_kind="AI_TESTS_PASSED"), "owner authorization")

    def test_retroactive_104_pass_claim_rejected(self):
        self.reject(lambda r: r["authority_effect"].update(claimed_104_of_104_pass=True), "historical evidence")


if __name__ == "__main__":
    unittest.main(verbosity=2)

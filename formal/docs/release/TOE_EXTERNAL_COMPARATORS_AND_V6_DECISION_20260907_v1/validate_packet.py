"""Read-only documentation/custody checks; not a VPC or authority verifier."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import zipfile

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
EVIDENCE_COMMIT = "ff282858"
WIN = "b5482f305b6b45e8dc928640c7d7d837ec28d7b3a8009644a4cf304fccca4ccc"
LINUX = "0f64b6d71f536416755e599e2e3ad440d455a02b67a9927c0cdc2ecf5f505a13"
V1 = "93691fa8f8793bb343ccebd0b1a92c15618b25a7f56e71f67ebaa7cff771471f"
RELEASE = "formal/docs/release/"
WINDOWS_PATH = RELEASE + f"verified_calculator/c03_rv_exact_v6/{WIN}.json"
V1_PATH = RELEASE + f"verified_calculator/c03_rv_exact/{V1}.json"
REVIEW_PATH = RELEASE + "VERIFIED_CALCULATOR_C03_RV_EXACT_V6_AMENDMENT_ONLY_NON_AUTHOR_REVIEW_RESULT_20260907_v1.json"
LINUX_PATH = RELEASE + "VERIFIED_CALCULATOR_C03_RV_LINUX_EGRESS_DENIED_EXECUTION_RESULT_20260907_v6.json"


def check(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def digest(value, domain):
    # Same documented domain-neutral JSON encoding; no physical evaluation.
    encoded = json.dumps(value, ensure_ascii=True, sort_keys=True, separators=(",", ":"))
    return sha(domain.encode("utf-8") + b"\0" + encoded.encode("ascii"))


def git_blob(path):
    return subprocess.check_output(["git", "show", f"{EVIDENCE_COMMIT}:{path}"], cwd=REPO)


def load_evidence():
    blobs = {p: git_blob(p) for p in (WINDOWS_PATH, V1_PATH, REVIEW_PATH, LINUX_PATH)}
    for p, raw in blobs.items():
        check(json.loads((REPO / p).read_bytes()) == json.loads(raw), f"Committed/local evidence mismatch: {p}")
    win, old = json.loads(blobs[WINDOWS_PATH]), json.loads(blobs[V1_PATH])
    check(digest(win, "FrozenEvidenceBundleV1") == WIN, "Windows bundle identity")
    check(digest(old, "FrozenEvidenceBundleV1") == V1, "Original bundle identity")
    return win, blobs


def scope_projection(win, blobs):
    receipt = win["verification_receipt"]
    certificate = win["runtime_certificate"]
    claims = {c["claim_id"]: c for c in receipt["claim_ledger"]}
    nodes = {n["node_id"]: n for n in win["candidate"]["graph"]["nodes"]}
    roots = []
    for output in sorted(receipt["outputs"], key=lambda o: o["root_id"]):
        root = output["root_id"]
        claim = root.replace(".OUTPUT.", ".claim.")
        value_hash = digest(output["value"], "ExactOutputValueV1")
        check(value_hash == certificate["output_value_hashes"][root], f"Value binding {root}")
        check(output["verification_class"] == "VERIFIED_EXACT", f"Evidence class {root}")
        check(output["challenge_coverage"]["complete"] is True, f"Coverage {root}")
        roots.append({"root_id": root, "value_type": nodes[root]["value_type"],
                      "value_hash_domain": "ExactOutputValueV1",
                      "canonical_value_hash": value_hash,
                      "verification_class": output["verification_class"],
                      "claim_ledger_entry": claims[claim],
                      "preserved_scientific_authority": win["authority_bindings"][0]["claim_bindings"][claim]})
    sources = sorted(n["node_id"] for n in nodes.values() if n["kind"] == "SOURCE")
    derived = [n for n in nodes.values() if n["kind"] == "DERIVED"]
    # 18 derived transformations plus OUTPUT_BIND; SOURCE_DECODE is separate.
    operations = sorted({n["operation"] for n in nodes.values() if n["kind"] != "SOURCE"})
    check((len(nodes), len(sources), len(derived), len(roots), len(operations)) == (207, 31, 160, 16, 19), "Scope census")
    check(set(win["request"]["requested_roots"]) == {r["root_id"] for r in roots}, "Root census")
    check(len(win["challenge_packets"]) == 373, "Challenge census")
    check(digest(win["request"], "CalculationRequestV1:computation") == receipt["computation_id"], "Request binding")
    return {
        "schema_id": "C03RVV6DecisionScopeProjectionV1",
        "status": "DRAFT_NOT_ADOPTED",
        "authority_effect": "NONE",
        "evidence_git_commit": subprocess.check_output(["git", "rev-parse", EVIDENCE_COMMIT], cwd=REPO, text=True).strip(),
        "evidence_references": [{"path": p, "hash_domain": "GIT_BLOB_BYTES_SHA256", "sha256": sha(raw)} for p, raw in sorted(blobs.items())],
        "computation_id": receipt["computation_id"],
        "request": win["request"],
        "windows_bundle_id": WIN,
        "linux_bundle_id": LINUX,
        "original_v1_bundle_id": V1,
        "candidate_hash": receipt["candidate_hash"],
        "runtime_certificate_hash": receipt["runtime_certificate_hash"],
        "graph_hash": certificate["graph_hash"],
        "dependency_closure_hashes": [d["closure_hash"] for d in win["dependency_manifests"]],
        "source_node_ids": sources,
        "derived_node_ids": sorted(n["node_id"] for n in derived),
        "physics_operation_ids": operations,
        "mandatory_challenge_count": len(win["challenge_packets"]),
        "challenge_packets_hash": digest(win["challenge_packets"], "DecisionScopeChallengePacketsV1"),
        "roots": roots,
        "preserved_calculator_profile_review_status": win["authority_bindings"][0]["calculator_profile_review_status"],
        "scientific_promotion": False, "product_v1_release": False, "production_activation": False,
    }


def archive_checks(manifest, win):
    info = manifest["archive"]
    path = HERE / info["file"]
    check(path.stat().st_size == info["size_bytes"], "Archive size")
    check(sha(path.read_bytes()) == info["sha256"], "Archive SHA256")
    with zipfile.ZipFile(path) as archive:
        names = archive.namelist()
        check(len(names) == len(set(names)), "Duplicate archive names")
        check(all(not PurePosixPath(n).is_absolute() and ".." not in PurePosixPath(n).parts for n in names), "Archive paths")
        outcome = json.loads(archive.read("outcome.json"))
        check(outcome["disposition"] == "PASS" and outcome["exit_code"] == 0, "Original Linux outcome")
        check(len(outcome["evidence_files"]) == 25, "Declared archive census")
        for row in outcome["evidence_files"]:
            raw = archive.read(row["path"])
            check(len(raw) == row["bytes"] and sha(raw) == row["sha256"], f"Archive evidence: {row['path']}")
        linux = json.loads(archive.read(f"bundles/{LINUX}.json"))
        check(digest(linux, "FrozenEvidenceBundleV1") == LINUX, "Linux bundle identity")
        check(linux["request"] == win["request"], "Cross-platform request")
        check(linux["runtime_certificate"] == win["runtime_certificate"], "Cross-platform certificate")
        values = lambda bundle: {r["root_id"]: r["value"] for r in bundle["verification_receipt"]["outputs"]}
        check(values(linux) == values(win), "Cross-platform 16-root values")
    return 25


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--emit-scope", action="store_true", help="Print a deterministic projection; never write or adopt it")
    args = parser.parse_args()
    win, blobs = load_evidence()
    scope = scope_projection(win, blobs)
    if args.emit_scope:
        print(json.dumps(scope, indent=2, sort_keys=True))
        return
    check(scope == json.loads((HERE / "v6_scope.json").read_bytes()), "Scope projection mismatch")
    manifest = json.loads((HERE / "manifest.json").read_bytes())
    check(manifest["decision"]["status"] == "DRAFT_NOT_ADOPTED", "Decision status")
    for flag in ("decision_adopted", "scientific_promotion", "product_v1_release", "production_activation", "ccft_promotion", "toe_promotion"):
        check(manifest[flag] is False, f"Promotion: {flag}")
    comparators = manifest["comparators"]
    check(len(comparators) == len({c["id"] for c in comparators}) == 4, "Comparator census")
    for c in comparators:
        check(c["implementation"] == "SPEC_ONLY_NOT_IMPLEMENTED" and c["verification_class"] == "NONE" and c["native_authority_effect"] == "NONE", "Comparator promotion")
        check(c["id"] in (HERE / c["file"]).read_text(encoding="utf-8"), "Comparator cross reference")
    checked_links = 0
    for doc in HERE.glob("*.md"):
        for link in re.findall(r"\]\(([^)]+)\)", doc.read_text(encoding="utf-8")):
            if not link.startswith(("http://", "https://", "#")):
                check((doc.parent / link.split("#")[0]).exists(), f"Missing link {doc.name}: {link}")
                checked_links += 1
    review = json.loads(blobs[REVIEW_PATH])
    check(review["overall_disposition"] == "SUPPORTED", "Review disposition")
    check(len(review["review_matrix"]) == 18, "Review matrix census")
    count = archive_checks(manifest, win)
    print(json.dumps({"documentation_validation": "PASS", "comparators": 4,
                      "scope_roots": len(scope["roots"]), "sources": 31,
                      "derived_nodes": 160, "operations": 19,
                      "archived_evidence_files_rehashed": count,
                      "local_links_checked": checked_links,
                      "new_physics_execution": False, "authority_adopted": False}, indent=2))


if __name__ == "__main__":
    main()

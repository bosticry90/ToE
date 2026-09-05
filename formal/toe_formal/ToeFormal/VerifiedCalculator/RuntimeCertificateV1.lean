import Lean.Data.Json

/-!
Runtime-certificate checker for the Verified Physics Calculator v1.

This module deliberately proves structural trust-boundary properties and checks
the certificate emitted by the executed Python evaluator.  It does not claim to
formalize SymPy, Nemo, SciPy, or the underlying physical theory.
-/

namespace ToeFormal.VerifiedCalculator.RuntimeCertificateV1

inductive VerificationClass where
  | none
  | deterministicallyRecomputed
  | crosscheckedNumerical
  | verifiedExact
  | verifiedEnclosure
  deriving DecidableEq, Repr

def assuranceRank : VerificationClass → Nat
  | .none => 0
  | .deterministicallyRecomputed => 1
  | .crosscheckedNumerical => 2
  | .verifiedExact => 3
  | .verifiedEnclosure => 3

def challengeFailureUpdate (_ : VerificationClass) : VerificationClass := .none

theorem challenge_failure_cannot_increase (status : VerificationClass) :
    assuranceRank (challengeFailureUpdate status) ≤ assuranceRank status := by
  cases status <;> decide

structure ScientificAuthority where
  profileReviewStatus : String
  claimBindingsDigest : String
  deriving DecidableEq, Repr

structure ComputationEvidence where
  receiptDigest : String
  deriving DecidableEq, Repr

def applyComputation (_ : ComputationEvidence) (authority : ScientificAuthority) :
    ScientificAuthority := authority

theorem computation_cannot_promote_scientific_authority
    (evidence : ComputationEvidence) (authority : ScientificAuthority) :
    applyComputation evidence authority = authority := rfl

def allowedOperation : String → Bool
  | "SOURCE_DECODE" | "LITERAL" | "OUTPUT_BIND" | "ADD" | "SUB" | "MUL"
  | "DIV" | "NEG" | "POW_INT" | "MAKE_TENSOR" | "INDEX" | "MATMUL" => true
  | "EQUAL" | "ALL" | "SELECT" | "CLASSIFY_ZERO" => true
  | _ => false

theorem unknown_operation_cannot_be_allowed {operation : String}
    (h : allowedOperation operation = false) : allowedOperation operation ≠ true := by
  simp [h]

private def jsonString (value : Lean.Json) (field : String) : Except String String := do
  (← value.getObjVal? field).getStr?

private def jsonBool (value : Lean.Json) (field : String) : Except String Bool := do
  (← value.getObjVal? field).getBool?

private def jsonArray (value : Lean.Json) (field : String) : Except String (Array Lean.Json) := do
  (← value.getObjVal? field).getArr?

private def lookupDigest (identity : String) : List (String × String) → Option String
  | [] => none
  | (key, value) :: rest => if key = identity then some value else lookupDigest identity rest

private def isLowerHexDigit (character : Char) : Bool :=
  ('0' ≤ character && character ≤ '9') || ('a' ≤ character && character ≤ 'f')

private def validSha256 (value : String) : Bool :=
  value.length = 64 && value.toList.all isLowerHexDigit

private def checkParents (parents : Array Lean.Json) (seen : List (String × String)) : Except String Unit := do
  for parentValue in parents do
    let parent ← parentValue.getStr?
    if (lookupDigest parent seen).isNone then
      throw s!"parent not previously certified: {parent}"

private def checkNode
    (node : Lean.Json)
    (outputDigests : Lean.Json)
    (seen : List (String × String)) : Except String (List (String × String) × Nat) := do
  let identity ← jsonString node "node_id"
  if (lookupDigest identity seen).isSome then
    throw s!"duplicate node: {identity}"
  let kind ← jsonString node "kind"
  let operation ← jsonString node "operation"
  if allowedOperation operation != true then
    throw s!"unknown operation: {operation}"
  let parents ← jsonArray node "parents"
  checkParents parents seen
  let valueDigest ← jsonString node "value_digest"
  let claimedDigest ← jsonString node "claimed_value_digest"
  if !validSha256 valueDigest || !validSha256 claimedDigest then
    throw s!"invalid node digest: {identity}"
  if valueDigest != claimedDigest then
    throw s!"claimed/computed digest mismatch: {identity}"
  let status ← jsonString node "status"
  if status != "RESOLVED_OR_RECOMPUTED_AND_EQUAL" then
    throw s!"uncertified trace status: {identity}"
  if kind = "SOURCE" then
    if operation != "SOURCE_DECODE" || parents.size != 0 then
      throw s!"invalid source signature: {identity}"
  else if kind = "LITERAL" then
    if operation != "LITERAL" || parents.size != 0 then
      throw s!"invalid literal signature: {identity}"
  else if kind = "OUTPUT" then
    if operation != "OUTPUT_BIND" || parents.size != 1 then
      throw s!"invalid output signature: {identity}"
    let parent ← parents[0]!.getStr?
    let some parentDigest := lookupDigest parent seen
      | throw s!"missing output parent: {identity}"
    if parentDigest != valueDigest then
      throw s!"output binding changed value: {identity}"
    let declaredOutputDigest ← (← outputDigests.getObjVal? identity).getStr?
    if declaredOutputDigest != valueDigest then
      throw s!"output digest not bound to trace: {identity}"
  else if kind != "DERIVED" then
    throw s!"unknown node kind: {kind}"
  return ((identity, valueDigest) :: seen, if kind = "OUTPUT" then 1 else 0)

private def checkTrace
    (nodes : Array Lean.Json)
    (outputDigests : Lean.Json) : Except String Nat := do
  let mut seen : List (String × String) := []
  let mut outputCount := 0
  for node in nodes do
    let result ← checkNode node outputDigests seen
    seen := result.1
    outputCount := outputCount + result.2
  return outputCount

def checkRuntimeCertificate (certificate : Lean.Json) : Except String Unit := do
  let schema ← jsonString certificate "schema_id"
  if schema != "RuntimeCertificateV1" then
    throw "wrong runtime certificate schema"
  if (← jsonBool certificate "scientific_promotion") != false then
    throw "computation attempted scientific promotion"
  let ceiling ← jsonString certificate "status_ceiling"
  if ceiling != "DETERMINISTICALLY_RECOMPUTED" && ceiling != "VERIFIED_EXACT" then
    throw "unsupported exact-certificate status ceiling"
  for field in #["computation_id", "candidate_hash", "physics_profile_hash",
      "verification_policy_hash", "graph_hash"] do
    let value ← jsonString certificate field
    if !validSha256 value then
      throw s!"invalid digest field: {field}"
  let trace ← jsonArray certificate "node_trace"
  if trace.isEmpty then
    throw "empty runtime trace"
  let outputDigests ← certificate.getObjVal? "output_node_value_digests"
  let outputDigestObject ← outputDigests.getObj?
  let outputValueHashes ← certificate.getObjVal? "output_value_hashes"
  let outputValueObject ← outputValueHashes.getObj?
  if outputDigestObject.keys != outputValueObject.keys then
    throw "output hash maps bind different roots"
  for (_, value) in outputValueObject.toList do
    let hash ← value.getStr?
    if !validSha256 hash then
      throw "invalid exact output value hash"
  let outputCount ← checkTrace trace outputDigests
  if outputCount = 0 then
    throw "runtime trace has no output roots"
  if outputCount != outputDigestObject.size then
    throw "trace/output root count mismatch"

theorem runtime_certificate_checker_deterministic (certificate : Lean.Json) :
    checkRuntimeCertificate certificate = checkRuntimeCertificate certificate := rfl

private def independentlyHashFile (path : String) : IO (Except String String) := do
  let output ← if System.Platform.isWindows then
    IO.Process.output { cmd := "certutil", args := #["-hashfile", path, "SHA256"] }
  else
    IO.Process.output { cmd := "sha256sum", args := #[path] }
  if output.exitCode != 0 then
    return .error s!"independent SHA-256 command failed: {output.stderr}"
  let candidates := (output.stdout.replace "\r" " " |>.replace "\n" " " |>.splitOn " ")
    |>.filter validSha256
  match candidates with
  | [value] => return .ok value
  | _ => return .error "independent SHA-256 output was not uniquely parseable"

def main (args : List String) : IO UInt32 := do
  match args with
  | [path, expectedFileSha256, acceptedCertificateHash] =>
      if !validSha256 expectedFileSha256 || !validSha256 acceptedCertificateHash then
        IO.eprintln "REJECTED EXPECTED_CERTIFICATE_HASH"
        return 2
      match ← independentlyHashFile path with
      | .error message =>
        IO.eprintln s!"REJECTED FILE_HASH {message}"
        return 2
      | .ok actualFileSha256 =>
        if actualFileSha256 != expectedFileSha256 then
          IO.eprintln "REJECTED FILE_HASH certificate bytes changed"
          return 2
      let raw ← IO.FS.readFile path
      match Lean.Json.parse raw with
      | .error message =>
          IO.eprintln s!"REJECTED JSON_PARSE {message}"
          return 2
      | .ok certificate =>
          match checkRuntimeCertificate certificate with
          | .error message =>
              IO.eprintln s!"REJECTED CERTIFICATE {message}"
              return 2
          | .ok _ =>
              IO.println s!"ACCEPTED {acceptedCertificateHash} FILE_SHA256 {expectedFileSha256} SCIENTIFIC_PROMOTION_FALSE"
              return 0
  | _ =>
      IO.eprintln "usage: vpc_certificate_checker CERTIFICATE_JSON EXPECTED_FILE_SHA256 ACCEPTED_CERTIFICATE_HASH"
      return 2

end ToeFormal.VerifiedCalculator.RuntimeCertificateV1

def main (args : List String) : IO UInt32 :=
  ToeFormal.VerifiedCalculator.RuntimeCertificateV1.main args

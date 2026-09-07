import Lean.Data.Json
import ToeFormal.VerifiedCalculator.RuntimeCertificateV1

/-!
D-01 checker for the actual runtime certificate plus qualification envelope.

The executable accepts paths only.  It computes both domain-separated
identities itself and compares every envelope commitment with an independently
serialized expected context.  No caller-selected accepted hash exists.
-/

namespace ToeFormal.VerifiedCalculator.QualificationEnvelopeV1

private def isLowerHexDigit (character : Char) : Bool :=
  ('0' ≤ character && character ≤ '9') || ('a' ≤ character && character ≤ 'f')

private def validSha256 (value : String) : Bool :=
  value.length = 64 && value.toList.all isLowerHexDigit

private def jsonString (value : Lean.Json) (field : String) : Except String String := do
  (← value.getObjVal? field).getStr?

private def jsonBool (value : Lean.Json) (field : String) : Except String Bool := do
  (← value.getObjVal? field).getBool?

private def equalField (left right : Lean.Json) (field : String) : Except String Unit := do
  let leftValue ← left.getObjVal? field
  let rightValue ← right.getObjVal? field
  if leftValue.compress != rightValue.compress then
    throw s!"context mismatch: {field}"

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

private def domainHash (path raw domain : String) : IO (Except String String) := do
  let identityPath := path ++ ".vpc-domain-hash-input"
  IO.FS.writeFile identityPath (domain ++ String.singleton (Char.ofNat 0) ++ raw)
  independentlyHashFile identityPath

private def parseFile (path : String) : IO (Except String (String × Lean.Json)) := do
  let raw ← IO.FS.readFile path
  match Lean.Json.parse raw with
  | .error message => return .error s!"JSON_PARSE {message}"
  | .ok value => return .ok (raw, value)

private def commitmentFields : Array String := #[
  "certificate_format_version", "runtime_certificate_hash", "computation_id",
  "calculation_request_hash", "candidate_hash", "physics_profile_hash",
  "verification_policy_hash", "source_receipt_set_hash", "graph_hash",
  "ordered_node_trace_hash", "authoritative_roots",
  "canonical_exact_output_value_hashes", "julia_evidence_hash",
  "mandatory_challenge_spec_set_hash", "mandatory_challenge_packet_set_hash",
  "mandatory_challenge_result_set_hash", "challenge_applicability_hash",
  "type_signature_set_hash", "status_ceiling", "scientific_promotion",
  "product_v1_release", "production_activation"
]

private def checkEnvelope
    (certificate envelope context : Lean.Json)
    (runtimeIdentity : String) : Except String Unit := do
  if (← jsonString envelope "schema_id") != "QualificationEnvelopeV1" then
    throw "wrong qualification envelope schema"
  if (← jsonString context "schema_id") != "QualificationExpectedContextV1" then
    throw "wrong qualification context schema"
  for field in commitmentFields do
    equalField envelope context field
  if (← jsonString envelope "certificate_format_version") !=
      "RuntimeCertificateV1+QualificationEnvelopeV1" then
    throw "wrong certificate format version"
  if (← jsonString envelope "runtime_certificate_hash") != runtimeIdentity then
    throw "runtime certificate identity mismatch"
  for field in #["computation_id", "candidate_hash", "physics_profile_hash",
      "verification_policy_hash", "graph_hash"] do
    if (← jsonString envelope field) != (← jsonString certificate field) then
      throw s!"runtime certificate field mismatch: {field}"
  -- RuntimeCertificateV1 names this map output_value_hashes.
  let outputHashes ← envelope.getObjVal? "canonical_exact_output_value_hashes"
  let runtimeOutputHashes ← certificate.getObjVal? "output_value_hashes"
  if outputHashes.compress != runtimeOutputHashes.compress then
    throw "runtime output-value hash mismatch"
  if (← jsonString envelope "status_ceiling") != "DETERMINISTICALLY_RECOMPUTED" then
    throw "qualification status ceiling promoted"
  for field in #["scientific_promotion", "product_v1_release", "production_activation"] do
    if (← jsonBool envelope field) != false then
      throw s!"forbidden promotion: {field}"

def main (args : List String) : IO UInt32 := do
  match args with
  | [certificatePath, envelopePath, contextPath] =>
      let certificateFileHash ← independentlyHashFile certificatePath
      let envelopeFileHash ← independentlyHashFile envelopePath
      let contextFileHash ← independentlyHashFile contextPath
      match certificateFileHash, envelopeFileHash, contextFileHash,
          (← parseFile certificatePath), (← parseFile envelopePath), (← parseFile contextPath) with
      | .ok certFile, .ok envFile, .ok ctxFile,
          .ok (certificateRaw, certificate), .ok (envelopeRaw, envelope), .ok (_, context) =>
          match ToeFormal.VerifiedCalculator.RuntimeCertificateV1.checkRuntimeCertificate certificate with
          | .error message =>
              IO.eprintln s!"REJECTED RUNTIME_CERTIFICATE {message}"
              return 2
          | .ok _ =>
              match ← domainHash certificatePath certificateRaw "RuntimeCertificateV1" with
              | .error message =>
                  IO.eprintln s!"REJECTED RUNTIME_IDENTITY {message}"
                  return 2
              | .ok runtimeIdentity =>
                  match checkEnvelope certificate envelope context runtimeIdentity with
                  | .error message =>
                      IO.eprintln s!"REJECTED ENVELOPE {message}"
                      return 2
                  | .ok _ =>
                      match ← domainHash envelopePath envelopeRaw "QualificationEnvelopeV1" with
                      | .error message =>
                          IO.eprintln s!"REJECTED ENVELOPE_IDENTITY {message}"
                          return 2
                      | .ok envelopeIdentity =>
                          IO.println s!"ACCEPTED ENVELOPE {envelopeIdentity} RUNTIME_CERTIFICATE {runtimeIdentity} ENVELOPE_FILE_SHA256 {envFile} CONTEXT_FILE_SHA256 {ctxFile} CERTIFICATE_FILE_SHA256 {certFile} SCIENTIFIC_PROMOTION_FALSE"
                          return 0
      | _, _, _, _, _, _ =>
          IO.eprintln "REJECTED INPUT_HASH_OR_PARSE"
          return 2
  | _ =>
      IO.eprintln "usage: vpc_qualification_envelope_checker RUNTIME_CERTIFICATE_JSON QUALIFICATION_ENVELOPE_JSON EXPECTED_CONTEXT_JSON"
      return 2

end ToeFormal.VerifiedCalculator.QualificationEnvelopeV1

def main (args : List String) : IO UInt32 :=
  ToeFormal.VerifiedCalculator.QualificationEnvelopeV1.main args

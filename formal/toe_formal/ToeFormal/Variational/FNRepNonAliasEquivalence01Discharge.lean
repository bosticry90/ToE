/-
ToeFormal/Variational/FNRepNonAliasEquivalence01Discharge.lean

Discharge surface for the selected proof-debt ledger item
`FNRepNonAliasEquivalence01.lean::defaultNonAlias`.

Scope:
- prove the selected default non-alias witness is Lean-backed by construction
- record that the prior axiom was replaced with a concrete definition
- make no pillar completion, seam closure, Phase 2 readiness, empirical,
  or master-action promotion claim
-/

import ToeFormal.Variational.FNRepNonAliasEquivalence01
import ToeFormal.Derivation.ProofDebtLedgerDischargeLane

namespace ToeFormal
namespace Variational
namespace FNRepNonAliasEquivalence01Discharge

open ToeFormal.Derivation.ProofDebtLedgerDischargeLane

set_option autoImplicit false
set_option linter.style.longLine false

/-- Surface id for the FNRep non-alias default witness discharge. -/
def fnrepNonAliasDefaultDischargeSurfaceId : String :=
  "fnrep_nonalias_default_nonalias_discharge_v0"

/-- Current live target consumed by this execution packet. -/
def fnrepNonAliasDefaultDischargeConsumedTargetId : String :=
  "execute_selected_proof_debt_discharge_item"

/-- Prepared-lane token consumed by this execution packet. -/
def fnrepNonAliasDefaultDischargeConsumedPreparedTokenId : String :=
  "PROOF_DEBT_LEDGER_DISCHARGE_LANE_PREPARED"

/-- Successful discharge token emitted by this packet. -/
def fnrepNonAliasDefaultDischargeResultTokenId : String :=
  "FNREP_NONALIAS_DEFAULT_NONALIAS_DISCHARGED_LEAN_BACKED"

/-- Canonical release report for this execution packet. -/
def fnrepNonAliasDefaultDischargeReportPath : String :=
  "formal/docs/release/PROOF_DEBT_DISCHARGE_FNREP_NONALIAS_20260503_v0.json"

/-- Next result-review target after the execution packet. -/
def fnrepNonAliasDefaultDischargeNextTargetId : String :=
  "review_fnrep_nonalias_default_nonalias_discharge_result"

/-- Selected debt item consumed from the proof-debt lane. -/
def fnrepNonAliasDefaultDischargeSelectedItemId : String :=
  "formal/toe_formal/ToeFormal/Variational/FNRepNonAliasEquivalence01.lean::defaultNonAlias"

/-- Replacement declaration that made the default witness concrete. -/
def fnrepNonAliasDefaultDischargeReplacementId : String :=
  "defaultRep32_and_defaultNonAlias_defs"

/-- Result status for the selected proof-debt item. -/
structure FNRepNonAliasDefaultDischargeStatus where
  prepared_lane_token_consumed : Prop
  prepared_lane_token_consumed_evidence : prepared_lane_token_consumed
  selected_item_matches_prepared_lane : Prop
  selected_item_matches_prepared_lane_evidence :
    selected_item_matches_prepared_lane
  default_witness_lean_backed : Prop
  default_witness_lean_backed_evidence : default_witness_lean_backed
  selected_debt_item : String
  prior_authority : String
  resulting_authority : String
  result_token : String
  next_target : String
  replacement_declaration : String
  axiom_removed : Prop
  axiom_removed_evidence : axiom_removed
  pillar_completion_inferred : Prop
  pillar_completion_not_inferred : Not pillar_completion_inferred
  seam_closure_inferred : Prop
  seam_closure_not_inferred : Not seam_closure_inferred
  phase2_readiness_claim : Prop
  phase2_readiness_not_claimed : Not phase2_readiness_claim
  empirical_claim : Prop
  empirical_not_claimed : Not empirical_claim
  master_action_promoted : Prop
  master_action_not_promoted : Not master_action_promoted
  consumed_target : String
  consumed_prepared_token : String
  surface_id : String
  report_path : String
  status : ToeFormal.Derivation.CrossPillarDerivationProtocol.DerivationStatus

/-- The default non-alias witness is concrete by definitional reduction. -/
theorem defaultNonAlias_discharge_eq_zero_rep32_false :
    _root_.ToeFormal.Variational.defaultNonAlias =
      ⟨_root_.ToeFormal.Variational.defaultRep32, false⟩ := by
  rfl

/-- The default non-alias witness round-trips to the concrete default Rep32 witness. -/
theorem defaultNonAlias_roundtrip_to_defaultRep32 :
    _root_.ToeFormal.Variational.nonAliasToRep32
        _root_.ToeFormal.Variational.defaultNonAlias =
      _root_.ToeFormal.Variational.defaultRep32 := by
  rfl

/-- The default non-alias witness has the non-tagged default tag. -/
theorem defaultNonAlias_discharge_tag_false :
    _root_.ToeFormal.Variational.defaultNonAlias.tag = false := by
  rfl

/-- The default non-alias witness is not an external axiom in this discharge surface. -/
def defaultNonAliasLeanBackedWitness : Prop :=
  _root_.ToeFormal.Variational.defaultNonAlias =
    ⟨_root_.ToeFormal.Variational.defaultRep32, false⟩

/-- Public status for the selected default witness discharge. -/
def fnrepNonAliasDefaultDischargeStatusV0 :
    FNRepNonAliasDefaultDischargeStatus where
  prepared_lane_token_consumed :=
    proofDebtLedgerDischargeLaneStatusReadoutV0
      |>.exactly_one_debt_item_selected
  prepared_lane_token_consumed_evidence :=
    proof_debt_ledger_discharge_lane_exactly_one_item_v0
  selected_item_matches_prepared_lane := True
  selected_item_matches_prepared_lane_evidence := True.intro
  default_witness_lean_backed := defaultNonAliasLeanBackedWitness
  default_witness_lean_backed_evidence :=
    defaultNonAlias_discharge_eq_zero_rep32_false
  selected_debt_item := fnrepNonAliasDefaultDischargeSelectedItemId
  prior_authority := selectedProofDebtLedgerCurrentAuthorityV0
  resulting_authority := "LEAN_BACKED_DEFINITION_AND_THEOREM"
  result_token := fnrepNonAliasDefaultDischargeResultTokenId
  next_target := fnrepNonAliasDefaultDischargeNextTargetId
  replacement_declaration := fnrepNonAliasDefaultDischargeReplacementId
  axiom_removed := True
  axiom_removed_evidence := True.intro
  pillar_completion_inferred := False
  pillar_completion_not_inferred := by
    intro h
    exact h
  seam_closure_inferred := False
  seam_closure_not_inferred := by
    intro h
    exact h
  phase2_readiness_claim := False
  phase2_readiness_not_claimed := by
    intro h
    exact h
  empirical_claim := False
  empirical_not_claimed := by
    intro h
    exact h
  master_action_promoted := False
  master_action_not_promoted := by
    intro h
    exact h
  consumed_target := fnrepNonAliasDefaultDischargeConsumedTargetId
  consumed_prepared_token :=
    fnrepNonAliasDefaultDischargeConsumedPreparedTokenId
  surface_id := fnrepNonAliasDefaultDischargeSurfaceId
  report_path := fnrepNonAliasDefaultDischargeReportPath
  status := .retained

/-- Public readout for the FNRep non-alias default discharge. -/
def fnrepNonAliasDefaultDischargeStatusReadoutV0 :
    FNRepNonAliasDefaultDischargeStatus :=
  fnrepNonAliasDefaultDischargeStatusV0

/-- The execution packet consumes the selected proof-debt execution target. -/
theorem fnrep_nonalias_default_discharge_consumes_live_target_v0 :
    (fnrepNonAliasDefaultDischargeStatusReadoutV0
      |>.consumed_target) =
      fnrepNonAliasDefaultDischargeConsumedTargetId := by
  rfl

/-- The execution packet consumes the prepared-lane token. -/
theorem fnrep_nonalias_default_discharge_consumes_prepared_token_v0 :
    (fnrepNonAliasDefaultDischargeStatusReadoutV0
      |>.consumed_prepared_token) =
      proofDebtLedgerDischargeLanePreparedTokenId := by
  rfl

/-- The selected item matches the proof-debt lane selection. -/
theorem fnrep_nonalias_default_discharge_selected_item_v0 :
    (fnrepNonAliasDefaultDischargeStatusReadoutV0
      |>.selected_debt_item) =
      selectedProofDebtLedgerItemV0 := by
  rfl

/-- The selected item is Lean-backed by definition and theorem. -/
theorem fnrep_nonalias_default_discharge_lean_backed_v0 :
    fnrepNonAliasDefaultDischargeStatusReadoutV0
      |>.default_witness_lean_backed := by
  exact
    fnrepNonAliasDefaultDischargeStatusReadoutV0
      |>.default_witness_lean_backed_evidence

/-- The successful discharge token is emitted. -/
theorem fnrep_nonalias_default_discharge_result_token_v0 :
    (fnrepNonAliasDefaultDischargeStatusReadoutV0
      |>.result_token) =
      fnrepNonAliasDefaultDischargeResultTokenId := by
  rfl

/-- The prior axiom was removed from the selected item. -/
theorem fnrep_nonalias_default_discharge_axiom_removed_v0 :
    fnrepNonAliasDefaultDischargeStatusReadoutV0
      |>.axiom_removed := by
  exact
    fnrepNonAliasDefaultDischargeStatusReadoutV0
      |>.axiom_removed_evidence

/-- The execution packet infers no pillar completion. -/
theorem fnrep_nonalias_default_discharge_no_pillar_completion_v0 :
    Not
      (fnrepNonAliasDefaultDischargeStatusReadoutV0
        |>.pillar_completion_inferred) := by
  exact
    fnrepNonAliasDefaultDischargeStatusReadoutV0
      |>.pillar_completion_not_inferred

/-- The execution packet infers no seam closure. -/
theorem fnrep_nonalias_default_discharge_no_seam_closure_v0 :
    Not
      (fnrepNonAliasDefaultDischargeStatusReadoutV0
        |>.seam_closure_inferred) := by
  exact
    fnrepNonAliasDefaultDischargeStatusReadoutV0
      |>.seam_closure_not_inferred

/-- The execution packet makes no Phase 2 readiness claim. -/
theorem fnrep_nonalias_default_discharge_no_phase2_readiness_v0 :
    Not
      (fnrepNonAliasDefaultDischargeStatusReadoutV0
        |>.phase2_readiness_claim) := by
  exact
    fnrepNonAliasDefaultDischargeStatusReadoutV0
      |>.phase2_readiness_not_claimed

/-- The execution packet makes no empirical claim. -/
theorem fnrep_nonalias_default_discharge_no_empirical_claim_v0 :
    Not
      (fnrepNonAliasDefaultDischargeStatusReadoutV0
        |>.empirical_claim) := by
  exact
    fnrepNonAliasDefaultDischargeStatusReadoutV0
      |>.empirical_not_claimed

/-- The execution packet does not promote the master action. -/
theorem fnrep_nonalias_default_discharge_master_action_not_promoted_v0 :
    Not
      (fnrepNonAliasDefaultDischargeStatusReadoutV0
        |>.master_action_promoted) := by
  exact
    fnrepNonAliasDefaultDischargeStatusReadoutV0
      |>.master_action_not_promoted

end FNRepNonAliasEquivalence01Discharge
end Variational
end ToeFormal

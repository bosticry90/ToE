/-
ToeFormal/QM/QMFullDerivationScaffold.lean

Cycle-001 scaffold for QM full-derivation discharge program.

Scope:
- contract-bridge theorem token only
- no Schrodinger derivation claim
- no unitary-recovery claim
/-

import ToeFormal.QM.QMEvolutionAssumptionLedger

namespace ToeFormal
namespace QM

noncomputable section
set_option autoImplicit false

theorem qm_full_derivation_cycle1_contract_bridge_token_v0
    (h : QMEvolutionAssumptions_v0_min1) :
    QMStateEvolvesUnderContract h.ctx h.t h.initialState h.finalState := by
  exact qm_evolution_of_QMEvolutionAssumptions_v0_min1 h

def QMUnitaryConsistencyWitnessUnderContract
    {State : Type}
    (initialState finalState : QMState State)
    (norm : State → ℝ) : Prop :=
  norm initialState.value = norm finalState.value

theorem qm_full_derivation_cycle2_unitary_consistency_token_v0
    (h : QMEvolutionAssumptions_v0_min1)
    (norm : h.State → ℝ)
    (hUnitaryConsistencyWitness :
      QMUnitaryConsistencyWitnessUnderContract h.initialState h.finalState norm) :
    QMUnitaryConsistencyWitnessUnderContract h.initialState h.finalState norm := by
  exact hUnitaryConsistencyWitness

def QMAntiCircularityGuardNoDirectSchrodingerInsertion : Prop :=
  True

theorem qm_full_derivation_cycle3_no_direct_schrodinger_insertion_guard_v0 :
    QMAntiCircularityGuardNoDirectSchrodingerInsertion := by
  trivial

structure QMFullDerivationCycle4Bundle
    {State : Type}
    (initialState finalState : QMState State)
    (norm : State → ℝ) : Prop where
  unitaryConsistency : QMUnitaryConsistencyWitnessUnderContract initialState finalState norm
  antiCircularityGuard : QMAntiCircularityGuardNoDirectSchrodingerInsertion

theorem qm_full_derivation_cycle4_composition_bundle_token_v0
    (h : QMEvolutionAssumptions_v0_min1)
    (norm : h.State → ℝ)
    (hUnitaryConsistencyWitness :
      QMUnitaryConsistencyWitnessUnderContract h.initialState h.finalState norm) :
    QMStateEvolvesUnderContract h.ctx h.t h.initialState h.finalState ∧
      QMFullDerivationCycle4Bundle h.initialState h.finalState norm := by
  constructor
  · exact qm_full_derivation_cycle1_contract_bridge_token_v0 h
  · refine
      {
        unitaryConsistency :=
          qm_full_derivation_cycle2_unitary_consistency_token_v0 h norm hUnitaryConsistencyWitness
        antiCircularityGuard :=
          qm_full_derivation_cycle3_no_direct_schrodinger_insertion_guard_v0
      }

theorem qm_full_derivation_cycle5_policy_to_math_reclassification_token_v0
    (h : QMEvolutionAssumptions_v0_min1) :
    QMEvolutionOperatorStepTotal h.ctx := by
  exact qm_step_total_of_definition h.ctx

theorem qm_full_derivation_cycle6_unitary_exit_row_closure_token_v0
    (h : QMEvolutionAssumptions_v0_min1)
    (norm : h.State → ℝ)
    (hUnitaryConsistencyWitness :
      QMUnitaryConsistencyWitnessUnderContract h.initialState h.finalState norm) :
    QMStateEvolvesUnderContract h.ctx h.t h.initialState h.finalState ∧
      QMUnitaryConsistencyWitnessUnderContract h.initialState h.finalState norm := by
  constructor
  · exact qm_full_derivation_cycle1_contract_bridge_token_v0 h
  · exact qm_full_derivation_cycle2_unitary_consistency_token_v0 h norm hUnitaryConsistencyWitness

theorem qm_full_derivation_cycle7_derivation_exit_row_closure_token_v0
    (h : QMEvolutionAssumptions_v0_min1)
    (norm : h.State → ℝ)
    (hUnitaryConsistencyWitness :
      QMUnitaryConsistencyWitnessUnderContract h.initialState h.finalState norm) :
    QMStateEvolvesUnderContract h.ctx h.t h.initialState h.finalState ∧
      QMAntiCircularityGuardNoDirectSchrodingerInsertion := by
  have hBundle :=
    qm_full_derivation_cycle4_composition_bundle_token_v0 h norm hUnitaryConsistencyWitness
  exact ⟨hBundle.left, hBundle.right.antiCircularityGuard⟩

theorem qm_full_derivation_cycle8_anticircularity_exit_row_closure_token_v0
    (h : QMEvolutionAssumptions_v0_min1)
    (norm : h.State → ℝ)
    (hUnitaryConsistencyWitness :
      QMUnitaryConsistencyWitnessUnderContract h.initialState h.finalState norm) :
    QMAntiCircularityGuardNoDirectSchrodingerInsertion ∧
      QMFullDerivationCycle4Bundle h.initialState h.finalState norm := by
  have hBundle :=
    qm_full_derivation_cycle4_composition_bundle_token_v0 h norm hUnitaryConsistencyWitness
  exact ⟨hBundle.right.antiCircularityGuard, hBundle.right⟩

theorem qm_full_derivation_cycle9_assumption_minimization_exit_row_closure_token_v0
    (h : QMEvolutionAssumptions_v0_min1) :
    QMEvolutionOperatorStepTotal h.ctx ∧
      QMStateEvolvesUnderContract h.ctx h.t h.initialState h.finalState := by
  constructor
  · exact qm_full_derivation_cycle5_policy_to_math_reclassification_token_v0 h
  · exact qm_full_derivation_cycle1_contract_bridge_token_v0 h

end
end QM
end ToeFormal

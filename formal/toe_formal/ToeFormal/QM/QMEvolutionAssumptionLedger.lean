/-
ToeFormal/QM/QMEvolutionAssumptionLedger.lean

Assumption-ledger bundle for QM evolution hardening (v0).

Scope:
- contract-only QM evolution theorem surface
- explicit assumption bundle classification support
- no Schrodinger derivation claim and no unitary-recovery claim
/-

import ToeFormal.QM.EvolutionContract

namespace ToeFormal
namespace QM

noncomputable section
set_option autoImplicit false

inductive QMEvolutionAssumptionClass_v0 where
  | MATH
  | DEF
  | POLICY
  | SCOPE
deriving DecidableEq, Repr

inductive QMEvolutionAssumptionId_v0 where
  | structuralContextTyping
  | explicitTypedBinders
  | nonDerivationalBoundary
  | stepTotalPolicy
deriving DecidableEq, Repr

def qmEvolutionAssumptionClass_v0 : QMEvolutionAssumptionId_v0 → QMEvolutionAssumptionClass_v0
  | .structuralContextTyping => .MATH
  | .explicitTypedBinders => .MATH
  | .nonDerivationalBoundary => .SCOPE
  | .stepTotalPolicy => .POLICY

def QMEvolutionOperatorStepTotal
    {Time State : Type}
    (ctx : EvolutionContext Time State) : Prop :=
  ∀ t : Time, ∀ ψ : State, ∃ ψ' : State, ctx.evolutionOperator.step t ψ = ψ'

theorem qm_step_total_of_definition
    {Time State : Type}
    (ctx : EvolutionContext Time State) :
    QMEvolutionOperatorStepTotal ctx := by
  intro t ψ
  exact ⟨ctx.evolutionOperator.step t ψ, rfl⟩

structure QMEvolutionAssumptions_v0 where
  Time : Type
  State : Type
  ctx : EvolutionContext Time State
  t : Time
  initialState : QMState State
  finalState : QMState State
  hEvolvesUnderContract : QMStateEvolvesUnderContract ctx t initialState finalState
  hStepTotalPolicy : QMEvolutionOperatorStepTotal ctx

structure QMEvolutionAssumptions_v0_min1 where
  Time : Type
  State : Type
  ctx : EvolutionContext Time State
  t : Time
  initialState : QMState State
  finalState : QMState State
  hEvolvesUnderContract : QMStateEvolvesUnderContract ctx t initialState finalState

theorem qm_evolution_of_QMEvolutionAssumptions_v0
    (h : QMEvolutionAssumptions_v0) :
    QMStateEvolvesUnderContract h.ctx h.t h.initialState h.finalState := by
  exact qm_evolution_under_contract_assumptions
    h.Time h.State h.ctx h.t h.initialState h.finalState h.hEvolvesUnderContract

theorem qm_evolution_of_QMEvolutionAssumptions_v0_min1
    (h : QMEvolutionAssumptions_v0_min1) :
    QMStateEvolvesUnderContract h.ctx h.t h.initialState h.finalState := by
  exact qm_evolution_under_contract_assumptions
    h.Time h.State h.ctx h.t h.initialState h.finalState h.hEvolvesUnderContract

theorem qm_evolution_of_QMEvolutionAssumptions_v0_min1_of_v0
    (h : QMEvolutionAssumptions_v0) :
    QMStateEvolvesUnderContract h.ctx h.t h.initialState h.finalState := by
  exact qm_evolution_of_QMEvolutionAssumptions_v0_min1
    {
      Time := h.Time
      State := h.State
      ctx := h.ctx
      t := h.t
      initialState := h.initialState
      finalState := h.finalState
      hEvolvesUnderContract := h.hEvolvesUnderContract
    }

end
end QM
end ToeFormal

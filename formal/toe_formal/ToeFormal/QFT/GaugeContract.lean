/-
ToeFormal/QFT/GaugeContract.lean

Planning-surface contract for QFT gauge object scaffolding.

Scope:
- Contract-only theorem surface.
- Typed gauge objects only.
- No Standard Model claim and no external truth claim.
-/

import Mathlib

namespace ToeFormal
namespace QFT

noncomputable section
set_option autoImplicit false

structure GaugeGroup (GaugeElem : Type) where
  carrier_nonempty : Nonempty GaugeElem
  compose : GaugeElem → GaugeElem → GaugeElem
  identity : GaugeElem
  inverse : GaugeElem → GaugeElem

structure GaugeAction (GaugeElem FieldValue : Type) where
  act : GaugeElem → FieldValue → FieldValue

structure GaugeContext (GaugeElem FieldValue : Type) where
  gaugeGroup : GaugeGroup GaugeElem
  gaugeAction : GaugeAction GaugeElem FieldValue

structure GaugeField (FieldValue : Type) where
  value : FieldValue

def FieldFixedUnderGaugeAction
    {GaugeElem FieldValue : Type}
    (ctx : GaugeContext GaugeElem FieldValue)
    (field : GaugeField FieldValue) : Prop :=
  ∀ g : GaugeElem, ctx.gaugeAction.act g field.value = field.value

theorem qft_gauge_invariance_under_contract_assumptions
    (GaugeElem FieldValue : Type)
    (ctx : GaugeContext GaugeElem FieldValue)
    (field : GaugeField FieldValue)
    (h_field_fixed_under_action : FieldFixedUnderGaugeAction ctx field) :
    FieldFixedUnderGaugeAction ctx field :=
  h_field_fixed_under_action

end
end QFT
end ToeFormal

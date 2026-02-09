/-
ToeFormal/SubstrateToyLaws/MetricClosure.lean

STRUCTURE-ONLY MODULE.
This file defines abstract interfaces for a "metric/closure" toy-law family.
No physical meaning is asserted. Predicates are admissibility gates only.
Python implementations, if any, are consequence-engine checks against these interfaces.
Admissibility semantics are instantiated in Python bounded-evidence tests.
Front doors emit reports; tests define admissibility predicates and thresholds.
-/

import Mathlib
import ToeFormal.SubstrateToyLaws.ViabilityFlow

namespace ToeFormal
namespace SubstrateToyLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Minimal metric-like summary (structure only; no physical meaning). -/
structure MetricSummary where
  g_tt : ℝ
  g_tx : ℝ
  g_xx : ℝ

/-- Candidate step for Family C (time-step form). -/
abbrev CandidateC (S : Type) := CandidateLaw S

/-- Metric-like map from substrate state to a summary object. -/
abbrev MetricLike (S : Type) := SubstrateState S -> MetricSummary

/-- Curvature-proxy map (structure only; no physical meaning). -/
abbrev CurvatureProxy (S : Type) := SubstrateState S -> ℝ

/-- Admissibility predicate (structural-only). -/
abbrev AdmissibleC (S : Type) := Admissible S

/-- Optional gate wrapper (CT/SYM/CAUS-style predicates). -/
abbrev GateC (S : Type) := Gates S

/-- Signature-like admissibility predicate (structure only). -/
def signatureLike (m : MetricSummary) : Prop :=
  m.g_tt < 0 ∧ m.g_xx > 0 ∧ m.g_tt * m.g_xx - m.g_tx * m.g_tx < 0

/-- Deterministic placeholder metric summary (constant). -/
def metricSummaryConstant : MetricSummary :=
  { g_tt := -1, g_tx := 0, g_xx := 1 }

/-- Metric-like map (constant placeholder). -/
def metricLikeConstant {S : Type} : MetricLike S :=
  fun _ => metricSummaryConstant

/-- Admissibility induced by a metric-like map. -/
def admissibleFromMetric {S : Type} (metric : MetricLike S) : AdmissibleC S :=
  fun s => signatureLike (metric s)

/-- Minimal candidate step (identity), paired with metric-based admissibility. -/
def candidateMetricClosure {S : Type} : CandidateC S :=
  fun s => s

/-- Alias: signature-style placeholder candidate (C1). -/
def candidateSignatureStyle {S : Type} : CandidateC S :=
  candidateMetricClosure

/-- Curvature-proxy map (constant placeholder). -/
def curvatureProxyConstant {S : Type} : CurvatureProxy S :=
  fun _ => 0

/-- Minimal curvature-proxy candidate (identity placeholder). -/
def candidateCurvatureProxy {S : Type} : CandidateC S :=
  fun s => s

end SubstrateToyLaws
end ToeFormal

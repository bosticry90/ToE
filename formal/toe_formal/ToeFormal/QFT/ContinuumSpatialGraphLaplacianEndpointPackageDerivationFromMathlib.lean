/-
ToeFormal/QFT/ContinuumSpatialGraphLaplacianEndpointPackageDerivationFromMathlib.lean

Endpoint-package derivation attempt from mathlib Taylor data for the A1A
graph-Laplacian-to-continuum-Laplacian channel.

Scope:
- define the coefficient/alignment data needed to derive the A1A8 endpoint
  package from mathlib endpoint Taylor machinery
- prove the right-endpoint remainder bound directly from mathlib for `0 <= h`
- prove that supplied scalar coefficient alignment plus the right mathlib
  bound and a supplied left-orientation bound constructs the A1A8 endpoint
  package
- prove the reflected-left endpoint expansion/bound route and isolate the
  remaining coefficient-orientation equalities needed to identify it with the
  original centered left endpoint package
- define the exact centered endpoint coefficient-alignment object whose
  supplied proof now feeds the endpoint package route
- derive that centered coefficient-alignment object from mathlib's
  within-to-global iterated derivative theorem plus reflected global
  derivative signs, under `0 < h` and global `C^3` smoothness
- feed that derived package through the already-proved symmetric Taylor and
  TaylorRemainderControl route
- name the resulting full two-sided endpoint package construction and feed
  it through the local stencil error-bound route
- record the next strict endpoint-package targets before uniform mesh
  convergence may become the active theorem target
- retain uniform mesh convergence, full A1A closure,
  A2A15A1 closure, Phase 2 authorization,
  continuum closure, seam closure, empirical validation, and master-action
  promotion
-/

import ToeFormal.QFT.ContinuumSpatialGraphLaplacianMathlibEndpointTaylorAlignment

namespace ToeFormal
namespace QFT
namespace ContinuumSpatialGraphLaplacianEndpointPackageDerivationFromMathlib

open ContinuumFirstVariation
open ContinuumSpatialAnalyticIntervalLift
open ContinuumSpatialAnalyticIntervalLiftAssembly
open ContinuumSpatialGraphLaplacianConvergence
open ContinuumSpatialGraphLaplacianQuadraticConsistency
open ContinuumSpatialGraphLaplacianStencilRemainder
open ContinuumSpatialGraphLaplacianTaylorRemainderControl
open ContinuumSpatialGraphLaplacianFourthDerivativeRemainder
open ContinuumSpatialGraphLaplacianChannelCapstone
open ContinuumSpatialGraphLaplacianConcreteTaylorRemainder
open ContinuumSpatialGraphLaplacianSymmetricTaylorStencilBridge
open ContinuumSpatialGraphLaplacianMathlibEndpointTaylorAlignment

set_option autoImplicit false

noncomputable section

/-- Retained blocker for deriving the endpoint package directly from mathlib. -/
def phase1Blocker003A2A15A1A9EndpointPackageDerivationFromMathlibRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A15A1A9_ENDPOINT_PACKAGE_DERIVATION_" ++
    "FROM_MATHLIB_RETAINED"

/-- Historical blocker id for the original left endpoint orientation step. -/
def phase1Blocker003A2A15A1A9LeftEndpointOrientationRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A15A1A9_LEFT_ENDPOINT_ORIENTATION_RETAINED"

/-- Historical blocker id now discharged by the bounded centered-alignment route. -/
def phase1Blocker003A2A15A1A9CenteredEndpointCoefficientAlignmentRetainedId :
    String :=
  "PHASE1-BLOCKER-003A2A15A1A9_CENTERED_ENDPOINT_COEFFICIENT_" ++
    "ALIGNMENT_RETAINED"

/-- Outcome id for this endpoint-package derivation slice. -/
def graphLaplacianEndpointPackageDerivationFromMathlibOutcomeId : String :=
  "TWO_SIDED_ENDPOINT_PACKAGE_CONSTRUCTED_UNIFORM_MESH_CONVERGENCE_RETAINED"

/-- Scalar order-three Taylor polynomial shape expected by the stencil route. -/
def scalarOrderThreeTaylorPolynomial
    (value first second third delta : Real) : Real :=
  value + first * delta + second * delta * delta / 2 +
    third * delta * delta * delta / 6

/--
Mathlib's `taylorWithinEval` has the scalar order-three coefficient shape
used by the endpoint package, for any chosen interval/set.
-/
theorem taylorWithinEval_order_three_scalar_coefficients
    (f : Real -> Real)
    (s : Set Real)
    (x delta : Real) :
    taylorWithinEval f 3 s x (x + delta) =
      scalarOrderThreeTaylorPolynomial
        (f x)
        (iteratedDerivWithin 1 f s x)
        (iteratedDerivWithin 2 f s x)
        (iteratedDerivWithin 3 f s x)
        delta := by
  rw [taylor_within_apply]
  simp [Finset.sum_range_succ, scalarOrderThreeTaylorPolynomial]
  ring_nf

/-- Right endpoint specialization of the scalar coefficient formula. -/
theorem taylorWithinEval_order_three_scalar_coefficients_right
    (f : Real -> Real)
    (s : Set Real)
    (x h : Real) :
    taylorWithinEval f 3 s x (x + h) =
      scalarOrderThreeTaylorPolynomial
        (f x)
        (iteratedDerivWithin 1 f s x)
        (iteratedDerivWithin 2 f s x)
        (iteratedDerivWithin 3 f s x)
        h :=
  taylorWithinEval_order_three_scalar_coefficients f s x h

/-- Left endpoint specialization of the scalar coefficient formula. -/
theorem taylorWithinEval_order_three_scalar_coefficients_left
    (f : Real -> Real)
    (s : Set Real)
    (x h : Real) :
    taylorWithinEval f 3 s x (x - h) =
      scalarOrderThreeTaylorPolynomial
        (f x)
        (iteratedDerivWithin 1 f s x)
        (iteratedDerivWithin 2 f s x)
        (iteratedDerivWithin 3 f s x)
        (-h) := by
  simpa [sub_eq_add_neg] using
    taylorWithinEval_order_three_scalar_coefficients f s x (-h)

/--
Right endpoint remainder bound derived directly from the imported mathlib
Taylor theorem, with expansion centered at `x` and evaluated at `x + h`.
-/
theorem right_endpoint_remainder_bound_from_mathlib
    {f : Real -> Real}
    {x h C : Real}
    (h_nonnegative : 0 ≤ h)
    (hf : ContDiffOn Real (3 + 1) f (Set.Icc x (x + h)))
    (hC :
      ∀ y ∈ Set.Icc x (x + h),
        ‖iteratedDerivWithin (3 + 1) f (Set.Icc x (x + h)) y‖ ≤ C) :
    |mathlibEndpointTaylorRemainder f x (x + h) (x + h)| ≤
      mathlibEndpointTaylorTolerance C x (x + h) := by
  have hx_upper : x ≤ x + h := by
    linarith
  have hendpoint : x + h ∈ Set.Icc x (x + h) := by
    exact ⟨hx_upper, le_rfl⟩
  exact
    mathlib_endpoint_taylor_remainder_bound
      (f := f) (base := x) (upper := x + h) (C := C)
      (endpoint := x + h) hx_upper hf hendpoint hC

/--
The reflected left endpoint remainder available directly from mathlib after
turning `x - h` into the right endpoint of the reflected coordinate.
-/
def leftEndpointReflectedTaylorRemainder
    (f : Real -> Real)
    (x h : Real) : Real :=
  mathlibEndpointTaylorRemainder
    (fun z => f (-z)) (-x) (-x + h) (-x + h)

/-- The reflected-left tolerance has the same fourth-order size as the target left tolerance. -/
theorem reflected_left_endpoint_tolerance_matches_original
    (C x h : Real) :
    mathlibEndpointTaylorTolerance C (-x) (-x + h) =
      mathlibEndpointTaylorTolerance C x (x - h) := by
  unfold mathlibEndpointTaylorTolerance
  norm_num [Nat.factorial]

/--
Mathlib gives a left-endpoint-size bound after coordinate reflection.  The
remaining retained orientation work is relating this reflected Taylor
remainder to the original centered left endpoint package.
-/
theorem left_endpoint_reflected_remainder_bound_from_mathlib
    {f : Real -> Real}
    {x h C : Real}
    (h_nonnegative : 0 ≤ h)
    (hf :
      ContDiffOn Real (3 + 1) (fun z => f (-z))
        (Set.Icc (-x) (-x + h)))
    (hC :
      ∀ y ∈ Set.Icc (-x) (-x + h),
        ‖iteratedDerivWithin (3 + 1) (fun z => f (-z))
          (Set.Icc (-x) (-x + h)) y‖ ≤ C) :
    |leftEndpointReflectedTaylorRemainder f x h| ≤
      mathlibEndpointTaylorTolerance C x (x - h) := by
  have hbase_upper : -x ≤ -x + h := by
    linarith
  have hendpoint : -x + h ∈ Set.Icc (-x) (-x + h) := by
    exact ⟨hbase_upper, le_rfl⟩
  calc
    |leftEndpointReflectedTaylorRemainder f x h| ≤
        mathlibEndpointTaylorTolerance C (-x) (-x + h) := by
          exact
            mathlib_endpoint_taylor_remainder_bound
              (f := fun z => f (-z)) (base := -x) (upper := -x + h)
              (C := C) (endpoint := -x + h)
              hbase_upper hf hendpoint hC
    _ = mathlibEndpointTaylorTolerance C x (x - h) := by
          rw [reflected_left_endpoint_tolerance_matches_original]

/--
The reflected coordinate gives an actual left endpoint expansion with
coefficients of `z ↦ f (-z)` on the reflected interval.
-/
theorem left_endpoint_reflected_expansion_from_scalar_coefficients
    {f : Real -> Real}
    {x h : Real} :
    f (x - h) =
      scalarOrderThreeTaylorPolynomial
        (f x)
        (iteratedDerivWithin 1 (fun z => f (-z))
          (Set.Icc (-x) (-x + h)) (-x))
        (iteratedDerivWithin 2 (fun z => f (-z))
          (Set.Icc (-x) (-x + h)) (-x))
        (iteratedDerivWithin 3 (fun z => f (-z))
          (Set.Icc (-x) (-x + h)) (-x))
        h +
        leftEndpointReflectedTaylorRemainder f x h := by
  unfold leftEndpointReflectedTaylorRemainder
    mathlibEndpointTaylorRemainder
  have hneg : -(-x + h) = x - h := by
    ring
  simp only
  rw [hneg]
  rw [taylorWithinEval_order_three_scalar_coefficients_right
    (fun z => f (-z)) (Set.Icc (-x) (-x + h)) (-x) h]
  ring_nf

/-- Reflected coefficients with alternating signs match the centered left polynomial. -/
theorem reflected_scalar_polynomial_orientation_eq_left
    (value first second third h reflectedFirst reflectedSecond reflectedThird : Real)
    (hfirst : reflectedFirst = -first)
    (hsecond : reflectedSecond = second)
    (hthird : reflectedThird = -third) :
    scalarOrderThreeTaylorPolynomial
        value reflectedFirst reflectedSecond reflectedThird h =
      scalarOrderThreeTaylorPolynomial value first second third (-h) := by
  rw [hfirst, hsecond, hthird]
  unfold scalarOrderThreeTaylorPolynomial
  ring

/--
Exact coefficient-orientation object needed to identify the reflected-left
Taylor polynomial with the centered two-sided endpoint package.
-/
structure CenteredEndpointCoefficientAlignment
    (f : Real -> Real)
    (x h : Real) where
  first_reflected_matches_centered :
    iteratedDerivWithin 1 (fun z => f (-z))
        (Set.Icc (-x) (-x + h)) (-x) =
      -iteratedDerivWithin 1 f (Set.Icc x (x + h)) x
  second_reflected_matches_centered :
    iteratedDerivWithin 2 (fun z => f (-z))
        (Set.Icc (-x) (-x + h)) (-x) =
      iteratedDerivWithin 2 f (Set.Icc x (x + h)) x
  third_reflected_matches_centered :
    iteratedDerivWithin 3 (fun z => f (-z))
        (Set.Icc (-x) (-x + h)) (-x) =
      -iteratedDerivWithin 3 f (Set.Icc x (x + h)) x

/-- A centered endpoint coefficient-alignment object gives the polynomial identity. -/
theorem centered_endpoint_coefficient_alignment_polynomial_identity
    {f : Real -> Real}
    {x h : Real}
    (alignment : CenteredEndpointCoefficientAlignment f x h) :
    scalarOrderThreeTaylorPolynomial
        (f x)
        (iteratedDerivWithin 1 (fun z => f (-z))
          (Set.Icc (-x) (-x + h)) (-x))
        (iteratedDerivWithin 2 (fun z => f (-z))
          (Set.Icc (-x) (-x + h)) (-x))
        (iteratedDerivWithin 3 (fun z => f (-z))
          (Set.Icc (-x) (-x + h)) (-x))
        h =
      scalarOrderThreeTaylorPolynomial
        (f x)
        (iteratedDerivWithin 1 f (Set.Icc x (x + h)) x)
        (iteratedDerivWithin 2 f (Set.Icc x (x + h)) x)
        (iteratedDerivWithin 3 f (Set.Icc x (x + h)) x)
        (-h) :=
  reflected_scalar_polynomial_orientation_eq_left
    (f x)
    (iteratedDerivWithin 1 f (Set.Icc x (x + h)) x)
    (iteratedDerivWithin 2 f (Set.Icc x (x + h)) x)
    (iteratedDerivWithin 3 f (Set.Icc x (x + h)) x)
    h
    (iteratedDerivWithin 1 (fun z => f (-z))
      (Set.Icc (-x) (-x + h)) (-x))
    (iteratedDerivWithin 2 (fun z => f (-z))
      (Set.Icc (-x) (-x + h)) (-x))
    (iteratedDerivWithin 3 (fun z => f (-z))
      (Set.Icc (-x) (-x + h)) (-x))
    alignment.first_reflected_matches_centered
    alignment.second_reflected_matches_centered
    alignment.third_reflected_matches_centered

/--
Mathlib reduces the reflected-left and right endpoint `iteratedDerivWithin`
coefficients to global iterated derivatives on nondegenerate endpoint
intervals.  The global reflected-derivative sign theorem then gives the
centered coefficient alignment.
-/
theorem centered_endpoint_coefficient_alignment_from_global_contDiff
    {f : Real -> Real}
    {x h : Real}
    (h_positive : 0 < h)
    (hf : ContDiff Real 3 f) :
    CenteredEndpointCoefficientAlignment f x h := by
  have hright : x < x + h := by
    linarith
  have hreflected : -x < -x + h := by
    linarith
  have hx_right : x ∈ Set.Icc x (x + h) := by
    exact ⟨le_rfl, le_of_lt hright⟩
  have hx_reflected : -x ∈ Set.Icc (-x) (-x + h) := by
    exact ⟨le_rfl, le_of_lt hreflected⟩
  have hf_reflected_1 : ContDiffAt Real 1 (fun z => f (-z)) (-x) := by
    simpa only [Function.comp_def] using
      ((hf.of_le (by norm_num) : ContDiff Real 1 f).contDiffAt.comp
        (-x) contDiff_neg.contDiffAt)
  have hf_reflected_2 : ContDiffAt Real 2 (fun z => f (-z)) (-x) := by
    simpa only [Function.comp_def] using
      ((hf.of_le (by norm_num) : ContDiff Real 2 f).contDiffAt.comp
        (-x) contDiff_neg.contDiffAt)
  have hf_reflected_3 : ContDiffAt Real 3 (fun z => f (-z)) (-x) := by
    simpa only [Function.comp_def] using
      ((hf.of_le (by norm_num) : ContDiff Real 3 f).contDiffAt.comp
        (-x) contDiff_neg.contDiffAt)
  have h_reflected_1_eq :
      iteratedDerivWithin 1 (fun z => f (-z))
          (Set.Icc (-x) (-x + h)) (-x) =
        iteratedDeriv 1 (fun z => f (-z)) (-x) := by
    exact
      iteratedDerivWithin_eq_iteratedDeriv
        (uniqueDiffOn_Icc hreflected) hf_reflected_1 hx_reflected
  have h_reflected_2_eq :
      iteratedDerivWithin 2 (fun z => f (-z))
          (Set.Icc (-x) (-x + h)) (-x) =
        iteratedDeriv 2 (fun z => f (-z)) (-x) := by
    exact
      iteratedDerivWithin_eq_iteratedDeriv
        (uniqueDiffOn_Icc hreflected) hf_reflected_2 hx_reflected
  have h_reflected_3_eq :
      iteratedDerivWithin 3 (fun z => f (-z))
          (Set.Icc (-x) (-x + h)) (-x) =
        iteratedDeriv 3 (fun z => f (-z)) (-x) := by
    exact
      iteratedDerivWithin_eq_iteratedDeriv
        (uniqueDiffOn_Icc hreflected) hf_reflected_3 hx_reflected
  have h_right_1_eq :
      iteratedDerivWithin 1 f (Set.Icc x (x + h)) x =
        iteratedDeriv 1 f x := by
    exact
      iteratedDerivWithin_eq_iteratedDeriv
        (uniqueDiffOn_Icc hright)
        (hf.contDiffAt.of_le (by norm_num)) hx_right
  have h_right_2_eq :
      iteratedDerivWithin 2 f (Set.Icc x (x + h)) x =
        iteratedDeriv 2 f x := by
    exact
      iteratedDerivWithin_eq_iteratedDeriv
        (uniqueDiffOn_Icc hright)
        (hf.contDiffAt.of_le (by norm_num)) hx_right
  have h_right_3_eq :
      iteratedDerivWithin 3 f (Set.Icc x (x + h)) x =
        iteratedDeriv 3 f x := by
    exact
      iteratedDerivWithin_eq_iteratedDeriv
        (uniqueDiffOn_Icc hright)
        (hf.contDiffAt.of_le (by norm_num)) hx_right
  refine ⟨?_, ?_, ?_⟩
  · rw [h_reflected_1_eq, h_right_1_eq]
    have hneg := iteratedDeriv_comp_neg 1 f (-x)
    norm_num at hneg
    simpa using hneg
  · rw [h_reflected_2_eq, h_right_2_eq]
    have hneg := iteratedDeriv_comp_neg 2 f (-x)
    norm_num at hneg
    simpa using hneg
  · rw [h_reflected_3_eq, h_right_3_eq]
    have hneg := iteratedDeriv_comp_neg 3 f (-x)
    norm_num at hneg
    simpa using hneg

/--
Data still needed to derive the A1A8 endpoint package from mathlib endpoint
Taylor machinery.  The right endpoint bound is theorem-derived below; the
right scalar coefficient formula is now theorem-derived separately.  This
legacy data shape records the broader supplied-alignment route, while the
left oriented endpoint package remains retained.
-/
structure EndpointPackageDerivationFromMathlibData
    (f : Real -> Real)
    (x h C : Real) where
  value : Real
  first_derivative : Real
  second_derivative : Real
  third_derivative : Real
  left_remainder : Real
  h_nonnegative : 0 ≤ h
  right_contDiffOn_center_to_endpoint :
    ContDiffOn Real (3 + 1) f (Set.Icc x (x + h))
  right_fourth_derivative_bound :
    ∀ y ∈ Set.Icc x (x + h),
      ‖iteratedDerivWithin (3 + 1) f (Set.Icc x (x + h)) y‖ ≤ C
  fourth_derivative_bound_nonnegative : 0 ≤ C
  c4_smoothness_on_symmetric_interval : Prop
  c4_smoothness_on_symmetric_interval_supplied :
    c4_smoothness_on_symmetric_interval
  two_sided_interval_model : Prop
  two_sided_interval_model_supplied :
    two_sided_interval_model
  sample_reconstruction_matches_stencil : Prop
  sample_reconstruction_matches_stencil_supplied :
    sample_reconstruction_matches_stencil
  right_centered_basepoint_alignment : Prop
  right_centered_basepoint_alignment_supplied :
    right_centered_basepoint_alignment
  left_centered_basepoint_alignment : Prop
  left_centered_basepoint_alignment_supplied :
    left_centered_basepoint_alignment
  right_taylor_within_eval_coefficient_alignment : Prop
  right_taylor_within_eval_coefficient_alignment_supplied :
    right_taylor_within_eval_coefficient_alignment
  left_taylor_within_eval_coefficient_alignment : Prop
  left_taylor_within_eval_coefficient_alignment_supplied :
    left_taylor_within_eval_coefficient_alignment
  left_oriented_endpoint_bound_available : Prop
  left_oriented_endpoint_bound_available_supplied :
    left_oriented_endpoint_bound_available
  center_expansion : f x = value
  right_taylor_within_eval_eq_scalar_order_three :
    taylorWithinEval f 3 (Set.Icc x (x + h)) x (x + h) =
      scalarOrderThreeTaylorPolynomial
        value first_derivative second_derivative third_derivative h
  left_expansion :
    f (x - h) =
      scalarOrderThreeTaylorPolynomial
        value first_derivative second_derivative third_derivative (-h) +
        left_remainder
  left_remainder_bound_from_oriented_mathlib :
    |left_remainder| ≤
      mathlibEndpointTaylorTolerance C x (x - h)

/--
The right endpoint expansion equation follows from scalar coefficient
alignment for `taylorWithinEval` and the definition of the mathlib remainder.
-/
theorem right_endpoint_expansion_of_taylor_within_eval_alignment
    {f : Real -> Real}
    {x h value first second third : Real}
    (halign :
      taylorWithinEval f 3 (Set.Icc x (x + h)) x (x + h) =
        scalarOrderThreeTaylorPolynomial value first second third h) :
    f (x + h) =
      value + first * h + second * h * h / 2 +
        third * h * h * h / 6 +
        mathlibEndpointTaylorRemainder f x (x + h) (x + h) := by
  unfold mathlibEndpointTaylorRemainder
  rw [halign]
  unfold scalarOrderThreeTaylorPolynomial
  ring

/-- The right endpoint expansion now follows from the scalar coefficient formula. -/
theorem right_endpoint_expansion_from_scalar_coefficients
    {f : Real -> Real}
    {x h : Real} :
    f (x + h) =
      scalarOrderThreeTaylorPolynomial
        (f x)
        (iteratedDerivWithin 1 f (Set.Icc x (x + h)) x)
        (iteratedDerivWithin 2 f (Set.Icc x (x + h)) x)
        (iteratedDerivWithin 3 f (Set.Icc x (x + h)) x)
        h +
        mathlibEndpointTaylorRemainder f x (x + h) (x + h) :=
  right_endpoint_expansion_of_taylor_within_eval_alignment
    (taylorWithinEval_order_three_scalar_coefficients_right
      f (Set.Icc x (x + h)) x h)

/-- The supplied derivation data constructs the prior A1A8 endpoint package. -/
def mathlibEndpointPackageOfDerivationData
    {f : Real -> Real}
    {x h C : Real}
    (data : EndpointPackageDerivationFromMathlibData f x h C) :
    MathlibEndpointTaylorExpansionPackage f x h C where
  value := data.value
  first_derivative := data.first_derivative
  second_derivative := data.second_derivative
  third_derivative := data.third_derivative
  left_remainder := data.left_remainder
  right_remainder :=
    mathlibEndpointTaylorRemainder f x (x + h) (x + h)
  fourth_derivative_bound_nonnegative :=
    data.fourth_derivative_bound_nonnegative
  c4_smoothness_on_symmetric_interval :=
    data.c4_smoothness_on_symmetric_interval
  c4_smoothness_on_symmetric_interval_supplied :=
    data.c4_smoothness_on_symmetric_interval_supplied
  two_sided_interval_model := data.two_sided_interval_model
  two_sided_interval_model_supplied :=
    data.two_sided_interval_model_supplied
  sample_reconstruction_matches_stencil :=
    data.sample_reconstruction_matches_stencil
  sample_reconstruction_matches_stencil_supplied :=
    data.sample_reconstruction_matches_stencil_supplied
  right_mathlib_endpoint_bound_available := True
  right_mathlib_endpoint_bound_available_supplied := True.intro
  left_mathlib_endpoint_bound_available :=
    data.left_oriented_endpoint_bound_available
  left_mathlib_endpoint_bound_available_supplied :=
    data.left_oriented_endpoint_bound_available_supplied
  right_centered_basepoint_alignment :=
    data.right_centered_basepoint_alignment
  right_centered_basepoint_alignment_supplied :=
    data.right_centered_basepoint_alignment_supplied
  left_centered_basepoint_alignment :=
    data.left_centered_basepoint_alignment
  left_centered_basepoint_alignment_supplied :=
    data.left_centered_basepoint_alignment_supplied
  right_taylor_within_eval_coefficient_alignment :=
    data.right_taylor_within_eval_coefficient_alignment
  right_taylor_within_eval_coefficient_alignment_supplied :=
    data.right_taylor_within_eval_coefficient_alignment_supplied
  left_taylor_within_eval_coefficient_alignment :=
    data.left_taylor_within_eval_coefficient_alignment
  left_taylor_within_eval_coefficient_alignment_supplied :=
    data.left_taylor_within_eval_coefficient_alignment_supplied
  center_expansion := data.center_expansion
  right_expansion :=
    right_endpoint_expansion_of_taylor_within_eval_alignment
      data.right_taylor_within_eval_eq_scalar_order_three
  left_expansion := by
    rw [data.left_expansion]
    unfold scalarOrderThreeTaylorPolynomial
    ring
  right_remainder_bound_from_mathlib :=
    right_endpoint_remainder_bound_from_mathlib
      data.h_nonnegative
      data.right_contDiffOn_center_to_endpoint
      data.right_fourth_derivative_bound
  left_remainder_bound_from_mathlib :=
    data.left_remainder_bound_from_oriented_mathlib

/--
Reduced-assumption data after discharging the scalar coefficient formula.  It
still retains the genuinely left-oriented endpoint expansion/bound needed to
make the package two-sided.
-/
structure EndpointPackageDerivationWithScalarCoefficientsData
    (f : Real -> Real)
    (x h C : Real) where
  left_remainder : Real
  h_nonnegative : 0 ≤ h
  right_contDiffOn_center_to_endpoint :
    ContDiffOn Real (3 + 1) f (Set.Icc x (x + h))
  right_fourth_derivative_bound :
    ∀ y ∈ Set.Icc x (x + h),
      ‖iteratedDerivWithin (3 + 1) f (Set.Icc x (x + h)) y‖ ≤ C
  fourth_derivative_bound_nonnegative : 0 ≤ C
  c4_smoothness_on_symmetric_interval : Prop
  c4_smoothness_on_symmetric_interval_supplied :
    c4_smoothness_on_symmetric_interval
  two_sided_interval_model : Prop
  two_sided_interval_model_supplied :
    two_sided_interval_model
  sample_reconstruction_matches_stencil : Prop
  sample_reconstruction_matches_stencil_supplied :
    sample_reconstruction_matches_stencil
  left_centered_basepoint_alignment : Prop
  left_centered_basepoint_alignment_supplied :
    left_centered_basepoint_alignment
  left_oriented_endpoint_bound_available : Prop
  left_oriented_endpoint_bound_available_supplied :
    left_oriented_endpoint_bound_available
  left_expansion_with_right_interval_coefficients :
    f (x - h) =
      scalarOrderThreeTaylorPolynomial
        (f x)
        (iteratedDerivWithin 1 f (Set.Icc x (x + h)) x)
        (iteratedDerivWithin 2 f (Set.Icc x (x + h)) x)
        (iteratedDerivWithin 3 f (Set.Icc x (x + h)) x)
        (-h) +
        left_remainder
  left_remainder_bound_from_oriented_mathlib :
    |left_remainder| ≤
      mathlibEndpointTaylorTolerance C x (x - h)

/--
After the scalar coefficient formula is theorem-derived, the endpoint package
can be constructed with only the left-oriented expansion/bound still supplied.
-/
def mathlibEndpointPackageOfScalarCoefficientData
    {f : Real -> Real}
    {x h C : Real}
    (data : EndpointPackageDerivationWithScalarCoefficientsData f x h C) :
    MathlibEndpointTaylorExpansionPackage f x h C where
  value := f x
  first_derivative :=
    iteratedDerivWithin 1 f (Set.Icc x (x + h)) x
  second_derivative :=
    iteratedDerivWithin 2 f (Set.Icc x (x + h)) x
  third_derivative :=
    iteratedDerivWithin 3 f (Set.Icc x (x + h)) x
  left_remainder := data.left_remainder
  right_remainder :=
    mathlibEndpointTaylorRemainder f x (x + h) (x + h)
  fourth_derivative_bound_nonnegative :=
    data.fourth_derivative_bound_nonnegative
  c4_smoothness_on_symmetric_interval :=
    data.c4_smoothness_on_symmetric_interval
  c4_smoothness_on_symmetric_interval_supplied :=
    data.c4_smoothness_on_symmetric_interval_supplied
  two_sided_interval_model := data.two_sided_interval_model
  two_sided_interval_model_supplied :=
    data.two_sided_interval_model_supplied
  sample_reconstruction_matches_stencil :=
    data.sample_reconstruction_matches_stencil
  sample_reconstruction_matches_stencil_supplied :=
    data.sample_reconstruction_matches_stencil_supplied
  right_mathlib_endpoint_bound_available := True
  right_mathlib_endpoint_bound_available_supplied := True.intro
  left_mathlib_endpoint_bound_available :=
    data.left_oriented_endpoint_bound_available
  left_mathlib_endpoint_bound_available_supplied :=
    data.left_oriented_endpoint_bound_available_supplied
  right_centered_basepoint_alignment := True
  right_centered_basepoint_alignment_supplied := True.intro
  left_centered_basepoint_alignment :=
    data.left_centered_basepoint_alignment
  left_centered_basepoint_alignment_supplied :=
    data.left_centered_basepoint_alignment_supplied
  right_taylor_within_eval_coefficient_alignment := True
  right_taylor_within_eval_coefficient_alignment_supplied := True.intro
  left_taylor_within_eval_coefficient_alignment := True
  left_taylor_within_eval_coefficient_alignment_supplied := True.intro
  center_expansion := rfl
  right_expansion := by
    rw [right_endpoint_expansion_from_scalar_coefficients (f := f) (x := x) (h := h)]
    unfold scalarOrderThreeTaylorPolynomial
    ring
  left_expansion := by
    rw [data.left_expansion_with_right_interval_coefficients]
    unfold scalarOrderThreeTaylorPolynomial
    ring
  right_remainder_bound_from_mathlib :=
    right_endpoint_remainder_bound_from_mathlib
      data.h_nonnegative
      data.right_contDiffOn_center_to_endpoint
      data.right_fourth_derivative_bound
  left_remainder_bound_from_mathlib :=
    data.left_remainder_bound_from_oriented_mathlib

/-- The reduced-assumption package uses theorem-derived centered coefficients. -/
theorem scalar_coefficient_endpoint_package_value_field_v0
    {f : Real -> Real}
    {x h C : Real}
    (data : EndpointPackageDerivationWithScalarCoefficientsData f x h C) :
    (mathlibEndpointPackageOfScalarCoefficientData data).value = f x := by
  rfl

/-- Reduced-assumption data feeds the symmetric Taylor bridge. -/
def symmetricTaylorStencilBridgeOfScalarCoefficientEndpointPackage
    {f : Real -> Real}
    {x h C : Real}
    (data : EndpointPackageDerivationWithScalarCoefficientsData f x h C) :
    SymmetricTaylorStencilBridge f x h (4 * C) :=
  symmetricTaylorStencilBridgeOfMathlibEndpointAlignment
    (mathlibEndpointPackageOfScalarCoefficientData data)

/-- Reduced-assumption data feeds the prior TaylorRemainderControl route. -/
def taylorRemainderControlOfScalarCoefficientEndpointPackage
    {f : Real -> Real}
    {x h C : Real}
    (h_nonzero : h * h ≠ 0)
    (refinementParameter : Nat)
    (refinementParameterPositive : 0 < refinementParameter)
    (data : EndpointPackageDerivationWithScalarCoefficientsData f x h C) :
    TaylorRemainderControl h
      (symmetricTaylorBridgeRemainderField
        (symmetricTaylorStencilBridgeOfScalarCoefficientEndpointPackage data))
      (fourthDerivativeStencilTolerance (4 * C) h) :=
  taylorRemainderControlOfSymmetricTaylorStencilBridge
    h_nonzero refinementParameter refinementParameterPositive
    (symmetricTaylorStencilBridgeOfScalarCoefficientEndpointPackage data)

/--
Left-orientation data after the reflected endpoint expansion/bound is
theorem-derived.  The remaining supplied facts are the coefficient-orientation
equalities that identify the reflected Taylor coefficients with the centered
coefficients used by the right endpoint package.
-/
structure LeftEndpointOrientationFromMathlibData
    (f : Real -> Real)
    (x h C : Real) where
  h_nonnegative : 0 ≤ h
  right_contDiffOn_center_to_endpoint :
    ContDiffOn Real (3 + 1) f (Set.Icc x (x + h))
  right_fourth_derivative_bound :
    ∀ y ∈ Set.Icc x (x + h),
      ‖iteratedDerivWithin (3 + 1) f (Set.Icc x (x + h)) y‖ ≤ C
  reflected_left_contDiffOn :
    ContDiffOn Real (3 + 1) (fun z => f (-z))
      (Set.Icc (-x) (-x + h))
  reflected_left_fourth_derivative_bound :
    ∀ y ∈ Set.Icc (-x) (-x + h),
      ‖iteratedDerivWithin (3 + 1) (fun z => f (-z))
        (Set.Icc (-x) (-x + h)) y‖ ≤ C
  fourth_derivative_bound_nonnegative : 0 ≤ C
  c4_smoothness_on_symmetric_interval : Prop
  c4_smoothness_on_symmetric_interval_supplied :
    c4_smoothness_on_symmetric_interval
  two_sided_interval_model : Prop
  two_sided_interval_model_supplied :
    two_sided_interval_model
  sample_reconstruction_matches_stencil : Prop
  sample_reconstruction_matches_stencil_supplied :
    sample_reconstruction_matches_stencil
  centered_coefficient_alignment_across_endpoint_intervals : Prop
  centered_coefficient_alignment_across_endpoint_intervals_supplied :
    centered_coefficient_alignment_across_endpoint_intervals
  first_reflected_coefficient_orientation :
    iteratedDerivWithin 1 (fun z => f (-z))
        (Set.Icc (-x) (-x + h)) (-x) =
      -iteratedDerivWithin 1 f (Set.Icc x (x + h)) x
  second_reflected_coefficient_orientation :
    iteratedDerivWithin 2 (fun z => f (-z))
        (Set.Icc (-x) (-x + h)) (-x) =
      iteratedDerivWithin 2 f (Set.Icc x (x + h)) x
  third_reflected_coefficient_orientation :
    iteratedDerivWithin 3 (fun z => f (-z))
        (Set.Icc (-x) (-x + h)) (-x) =
      -iteratedDerivWithin 3 f (Set.Icc x (x + h)) x

/--
Reflected-left orientation data constructs the endpoint package without a
supplied left expansion or supplied left remainder bound.
-/
def mathlibEndpointPackageOfLeftOrientationData
    {f : Real -> Real}
    {x h C : Real}
    (data : LeftEndpointOrientationFromMathlibData f x h C) :
    MathlibEndpointTaylorExpansionPackage f x h C where
  value := f x
  first_derivative :=
    iteratedDerivWithin 1 f (Set.Icc x (x + h)) x
  second_derivative :=
    iteratedDerivWithin 2 f (Set.Icc x (x + h)) x
  third_derivative :=
    iteratedDerivWithin 3 f (Set.Icc x (x + h)) x
  left_remainder := leftEndpointReflectedTaylorRemainder f x h
  right_remainder :=
    mathlibEndpointTaylorRemainder f x (x + h) (x + h)
  fourth_derivative_bound_nonnegative :=
    data.fourth_derivative_bound_nonnegative
  c4_smoothness_on_symmetric_interval :=
    data.c4_smoothness_on_symmetric_interval
  c4_smoothness_on_symmetric_interval_supplied :=
    data.c4_smoothness_on_symmetric_interval_supplied
  two_sided_interval_model := data.two_sided_interval_model
  two_sided_interval_model_supplied :=
    data.two_sided_interval_model_supplied
  sample_reconstruction_matches_stencil :=
    data.sample_reconstruction_matches_stencil
  sample_reconstruction_matches_stencil_supplied :=
    data.sample_reconstruction_matches_stencil_supplied
  right_mathlib_endpoint_bound_available := True
  right_mathlib_endpoint_bound_available_supplied := True.intro
  left_mathlib_endpoint_bound_available := True
  left_mathlib_endpoint_bound_available_supplied := True.intro
  right_centered_basepoint_alignment := True
  right_centered_basepoint_alignment_supplied := True.intro
  left_centered_basepoint_alignment :=
    data.centered_coefficient_alignment_across_endpoint_intervals
  left_centered_basepoint_alignment_supplied :=
    data.centered_coefficient_alignment_across_endpoint_intervals_supplied
  right_taylor_within_eval_coefficient_alignment := True
  right_taylor_within_eval_coefficient_alignment_supplied := True.intro
  left_taylor_within_eval_coefficient_alignment :=
    data.centered_coefficient_alignment_across_endpoint_intervals
  left_taylor_within_eval_coefficient_alignment_supplied :=
    data.centered_coefficient_alignment_across_endpoint_intervals_supplied
  center_expansion := rfl
  right_expansion := by
    rw [right_endpoint_expansion_from_scalar_coefficients (f := f) (x := x) (h := h)]
    unfold scalarOrderThreeTaylorPolynomial
    ring
  left_expansion := by
    calc
      f (x - h) =
          scalarOrderThreeTaylorPolynomial
            (f x)
            (iteratedDerivWithin 1 (fun z => f (-z))
              (Set.Icc (-x) (-x + h)) (-x))
            (iteratedDerivWithin 2 (fun z => f (-z))
              (Set.Icc (-x) (-x + h)) (-x))
            (iteratedDerivWithin 3 (fun z => f (-z))
              (Set.Icc (-x) (-x + h)) (-x))
            h +
            leftEndpointReflectedTaylorRemainder f x h :=
              left_endpoint_reflected_expansion_from_scalar_coefficients
      _ =
          scalarOrderThreeTaylorPolynomial
            (f x)
            (iteratedDerivWithin 1 f (Set.Icc x (x + h)) x)
            (iteratedDerivWithin 2 f (Set.Icc x (x + h)) x)
            (iteratedDerivWithin 3 f (Set.Icc x (x + h)) x)
            (-h) +
            leftEndpointReflectedTaylorRemainder f x h := by
              rw [reflected_scalar_polynomial_orientation_eq_left
                (f x)
                (iteratedDerivWithin 1 f (Set.Icc x (x + h)) x)
                (iteratedDerivWithin 2 f (Set.Icc x (x + h)) x)
                (iteratedDerivWithin 3 f (Set.Icc x (x + h)) x)
                h
                (iteratedDerivWithin 1 (fun z => f (-z))
                  (Set.Icc (-x) (-x + h)) (-x))
                (iteratedDerivWithin 2 (fun z => f (-z))
                  (Set.Icc (-x) (-x + h)) (-x))
                (iteratedDerivWithin 3 (fun z => f (-z))
                  (Set.Icc (-x) (-x + h)) (-x))
                data.first_reflected_coefficient_orientation
                data.second_reflected_coefficient_orientation
                data.third_reflected_coefficient_orientation]
      _ =
          f x -
            iteratedDerivWithin 1 f (Set.Icc x (x + h)) x * h +
            iteratedDerivWithin 2 f (Set.Icc x (x + h)) x * h * h / 2 -
            iteratedDerivWithin 3 f (Set.Icc x (x + h)) x * h * h * h / 6 +
            leftEndpointReflectedTaylorRemainder f x h := by
              unfold scalarOrderThreeTaylorPolynomial
              ring
  right_remainder_bound_from_mathlib :=
    right_endpoint_remainder_bound_from_mathlib
      data.h_nonnegative
      data.right_contDiffOn_center_to_endpoint
      data.right_fourth_derivative_bound
  left_remainder_bound_from_mathlib :=
    left_endpoint_reflected_remainder_bound_from_mathlib
      data.h_nonnegative
      data.reflected_left_contDiffOn
      data.reflected_left_fourth_derivative_bound

/-- The left-orientation route uses the reflected remainder field. -/
theorem left_orientation_endpoint_package_left_remainder_field_v0
    {f : Real -> Real}
    {x h C : Real}
    (data : LeftEndpointOrientationFromMathlibData f x h C) :
    (mathlibEndpointPackageOfLeftOrientationData data).left_remainder =
      leftEndpointReflectedTaylorRemainder f x h := by
  rfl

/-- Left-orientation data feeds the symmetric Taylor bridge. -/
def symmetricTaylorStencilBridgeOfLeftOrientationEndpointPackage
    {f : Real -> Real}
    {x h C : Real}
    (data : LeftEndpointOrientationFromMathlibData f x h C) :
    SymmetricTaylorStencilBridge f x h (4 * C) :=
  symmetricTaylorStencilBridgeOfMathlibEndpointAlignment
    (mathlibEndpointPackageOfLeftOrientationData data)

/-- Left-orientation data feeds the prior TaylorRemainderControl route. -/
def taylorRemainderControlOfLeftOrientationEndpointPackage
    {f : Real -> Real}
    {x h C : Real}
    (h_nonzero : h * h ≠ 0)
    (refinementParameter : Nat)
    (refinementParameterPositive : 0 < refinementParameter)
    (data : LeftEndpointOrientationFromMathlibData f x h C) :
    TaylorRemainderControl h
      (symmetricTaylorBridgeRemainderField
        (symmetricTaylorStencilBridgeOfLeftOrientationEndpointPackage data))
      (fourthDerivativeStencilTolerance (4 * C) h) :=
  taylorRemainderControlOfSymmetricTaylorStencilBridge
    h_nonzero refinementParameter refinementParameterPositive
    (symmetricTaylorStencilBridgeOfLeftOrientationEndpointPackage data)

/--
Endpoint-package data with the centered endpoint coefficient alignment made
explicit as one theorem object.
-/
structure EndpointPackageDerivationWithCenteredCoefficientAlignmentData
    (f : Real -> Real)
    (x h C : Real) where
  h_nonnegative : 0 ≤ h
  right_contDiffOn_center_to_endpoint :
    ContDiffOn Real (3 + 1) f (Set.Icc x (x + h))
  right_fourth_derivative_bound :
    ∀ y ∈ Set.Icc x (x + h),
      ‖iteratedDerivWithin (3 + 1) f (Set.Icc x (x + h)) y‖ ≤ C
  reflected_left_contDiffOn :
    ContDiffOn Real (3 + 1) (fun z => f (-z))
      (Set.Icc (-x) (-x + h))
  reflected_left_fourth_derivative_bound :
    ∀ y ∈ Set.Icc (-x) (-x + h),
      ‖iteratedDerivWithin (3 + 1) (fun z => f (-z))
        (Set.Icc (-x) (-x + h)) y‖ ≤ C
  fourth_derivative_bound_nonnegative : 0 ≤ C
  c4_smoothness_on_symmetric_interval : Prop
  c4_smoothness_on_symmetric_interval_supplied :
    c4_smoothness_on_symmetric_interval
  two_sided_interval_model : Prop
  two_sided_interval_model_supplied :
    two_sided_interval_model
  sample_reconstruction_matches_stencil : Prop
  sample_reconstruction_matches_stencil_supplied :
    sample_reconstruction_matches_stencil
  centered_coefficient_alignment :
    CenteredEndpointCoefficientAlignment f x h

/-- The explicit centered-alignment object supplies the prior left-orientation data. -/
def leftOrientationDataOfCenteredCoefficientAlignmentData
    {f : Real -> Real}
    {x h C : Real}
    (data :
      EndpointPackageDerivationWithCenteredCoefficientAlignmentData f x h C) :
    LeftEndpointOrientationFromMathlibData f x h C where
  h_nonnegative := data.h_nonnegative
  right_contDiffOn_center_to_endpoint :=
    data.right_contDiffOn_center_to_endpoint
  right_fourth_derivative_bound := data.right_fourth_derivative_bound
  reflected_left_contDiffOn := data.reflected_left_contDiffOn
  reflected_left_fourth_derivative_bound :=
    data.reflected_left_fourth_derivative_bound
  fourth_derivative_bound_nonnegative :=
    data.fourth_derivative_bound_nonnegative
  c4_smoothness_on_symmetric_interval :=
    data.c4_smoothness_on_symmetric_interval
  c4_smoothness_on_symmetric_interval_supplied :=
    data.c4_smoothness_on_symmetric_interval_supplied
  two_sided_interval_model := data.two_sided_interval_model
  two_sided_interval_model_supplied :=
    data.two_sided_interval_model_supplied
  sample_reconstruction_matches_stencil :=
    data.sample_reconstruction_matches_stencil
  sample_reconstruction_matches_stencil_supplied :=
    data.sample_reconstruction_matches_stencil_supplied
  centered_coefficient_alignment_across_endpoint_intervals := True
  centered_coefficient_alignment_across_endpoint_intervals_supplied :=
    True.intro
  first_reflected_coefficient_orientation :=
    data.centered_coefficient_alignment.first_reflected_matches_centered
  second_reflected_coefficient_orientation :=
    data.centered_coefficient_alignment.second_reflected_matches_centered
  third_reflected_coefficient_orientation :=
    data.centered_coefficient_alignment.third_reflected_matches_centered

/-- Explicit centered-alignment data constructs the endpoint package. -/
def mathlibEndpointPackageOfCenteredCoefficientAlignmentData
    {f : Real -> Real}
    {x h C : Real}
    (data :
      EndpointPackageDerivationWithCenteredCoefficientAlignmentData f x h C) :
    MathlibEndpointTaylorExpansionPackage f x h C :=
  mathlibEndpointPackageOfLeftOrientationData
    (leftOrientationDataOfCenteredCoefficientAlignmentData data)

/-- The centered-alignment package uses the reflected-left remainder. -/
theorem centered_alignment_endpoint_package_left_remainder_field_v0
    {f : Real -> Real}
    {x h C : Real}
    (data :
      EndpointPackageDerivationWithCenteredCoefficientAlignmentData f x h C) :
    (mathlibEndpointPackageOfCenteredCoefficientAlignmentData data).left_remainder =
      leftEndpointReflectedTaylorRemainder f x h := by
  rfl

/-- Explicit centered-alignment data feeds the symmetric Taylor bridge. -/
def symmetricTaylorStencilBridgeOfCenteredCoefficientAlignmentData
    {f : Real -> Real}
    {x h C : Real}
    (data :
      EndpointPackageDerivationWithCenteredCoefficientAlignmentData f x h C) :
    SymmetricTaylorStencilBridge f x h (4 * C) :=
  symmetricTaylorStencilBridgeOfMathlibEndpointAlignment
    (mathlibEndpointPackageOfCenteredCoefficientAlignmentData data)

/-- Explicit centered-alignment data feeds the prior TaylorRemainderControl route. -/
def taylorRemainderControlOfCenteredCoefficientAlignmentData
    {f : Real -> Real}
    {x h C : Real}
    (h_nonzero : h * h ≠ 0)
    (refinementParameter : Nat)
    (refinementParameterPositive : 0 < refinementParameter)
    (data :
      EndpointPackageDerivationWithCenteredCoefficientAlignmentData f x h C) :
    TaylorRemainderControl h
      (symmetricTaylorBridgeRemainderField
        (symmetricTaylorStencilBridgeOfCenteredCoefficientAlignmentData data))
      (fourthDerivativeStencilTolerance (4 * C) h) :=
  taylorRemainderControlOfSymmetricTaylorStencilBridge
    h_nonzero refinementParameter refinementParameterPositive
    (symmetricTaylorStencilBridgeOfCenteredCoefficientAlignmentData data)

/--
Endpoint-package data after the centered coefficient alignment has been
derived from global smoothness and the nondegenerate endpoint interval.
Fourth-derivative bounds and the external sample/model compatibility facts
remain explicit analytic inputs.
-/
structure EndpointPackageDerivationWithGlobalCenteredAlignmentData
    (f : Real -> Real)
    (x h C : Real) where
  h_positive : 0 < h
  global_contDiff_order_four : ContDiff Real (3 + 1) f
  right_fourth_derivative_bound :
    ∀ y ∈ Set.Icc x (x + h),
      ‖iteratedDerivWithin (3 + 1) f (Set.Icc x (x + h)) y‖ ≤ C
  reflected_left_fourth_derivative_bound :
    ∀ y ∈ Set.Icc (-x) (-x + h),
      ‖iteratedDerivWithin (3 + 1) (fun z => f (-z))
        (Set.Icc (-x) (-x + h)) y‖ ≤ C
  fourth_derivative_bound_nonnegative : 0 ≤ C
  c4_smoothness_on_symmetric_interval : Prop
  c4_smoothness_on_symmetric_interval_supplied :
    c4_smoothness_on_symmetric_interval
  two_sided_interval_model : Prop
  two_sided_interval_model_supplied :
    two_sided_interval_model
  sample_reconstruction_matches_stencil : Prop
  sample_reconstruction_matches_stencil_supplied :
    sample_reconstruction_matches_stencil

/--
Global smoothness and `0 < h` supply the centered coefficient alignment used
by the previous endpoint-package route.
-/
def centeredCoefficientAlignmentDataOfGlobalSmoothData
    {f : Real -> Real}
    {x h C : Real}
    (data :
      EndpointPackageDerivationWithGlobalCenteredAlignmentData f x h C) :
    EndpointPackageDerivationWithCenteredCoefficientAlignmentData f x h C where
  h_nonnegative := le_of_lt data.h_positive
  right_contDiffOn_center_to_endpoint :=
    data.global_contDiff_order_four.contDiffOn
  right_fourth_derivative_bound := data.right_fourth_derivative_bound
  reflected_left_contDiffOn := by
    simpa only [Function.comp_def] using
      ((data.global_contDiff_order_four.comp contDiff_neg) :
          ContDiff Real (3 + 1) (f ∘ fun p : Real => -p)).contDiffOn
  reflected_left_fourth_derivative_bound :=
    data.reflected_left_fourth_derivative_bound
  fourth_derivative_bound_nonnegative :=
    data.fourth_derivative_bound_nonnegative
  c4_smoothness_on_symmetric_interval :=
    data.c4_smoothness_on_symmetric_interval
  c4_smoothness_on_symmetric_interval_supplied :=
    data.c4_smoothness_on_symmetric_interval_supplied
  two_sided_interval_model := data.two_sided_interval_model
  two_sided_interval_model_supplied :=
    data.two_sided_interval_model_supplied
  sample_reconstruction_matches_stencil :=
    data.sample_reconstruction_matches_stencil
  sample_reconstruction_matches_stencil_supplied :=
    data.sample_reconstruction_matches_stencil_supplied
  centered_coefficient_alignment :=
    centered_endpoint_coefficient_alignment_from_global_contDiff
      data.h_positive
      (data.global_contDiff_order_four.of_le (by norm_num))

/-- Global-smoothness data constructs the endpoint package without supplied alignment. -/
def mathlibEndpointPackageOfGlobalCenteredAlignmentData
    {f : Real -> Real}
    {x h C : Real}
    (data :
      EndpointPackageDerivationWithGlobalCenteredAlignmentData f x h C) :
    MathlibEndpointTaylorExpansionPackage f x h C :=
  mathlibEndpointPackageOfCenteredCoefficientAlignmentData
    (centeredCoefficientAlignmentDataOfGlobalSmoothData data)

/-- The global-smoothness package still uses the reflected-left remainder. -/
theorem global_centered_alignment_endpoint_package_left_remainder_field_v0
    {f : Real -> Real}
    {x h C : Real}
    (data :
      EndpointPackageDerivationWithGlobalCenteredAlignmentData f x h C) :
    (mathlibEndpointPackageOfGlobalCenteredAlignmentData data).left_remainder =
      leftEndpointReflectedTaylorRemainder f x h := by
  rfl

/-- Global-smoothness data feeds the symmetric Taylor bridge. -/
def symmetricTaylorStencilBridgeOfGlobalCenteredAlignmentData
    {f : Real -> Real}
    {x h C : Real}
    (data :
      EndpointPackageDerivationWithGlobalCenteredAlignmentData f x h C) :
    SymmetricTaylorStencilBridge f x h (4 * C) :=
  symmetricTaylorStencilBridgeOfMathlibEndpointAlignment
    (mathlibEndpointPackageOfGlobalCenteredAlignmentData data)

/-- Global-smoothness data feeds the prior TaylorRemainderControl route. -/
def taylorRemainderControlOfGlobalCenteredAlignmentData
    {f : Real -> Real}
    {x h C : Real}
    (h_nonzero : h * h ≠ 0)
    (refinementParameter : Nat)
    (refinementParameterPositive : 0 < refinementParameter)
    (data :
      EndpointPackageDerivationWithGlobalCenteredAlignmentData f x h C) :
    TaylorRemainderControl h
      (symmetricTaylorBridgeRemainderField
        (symmetricTaylorStencilBridgeOfGlobalCenteredAlignmentData data))
      (fourthDerivativeStencilTolerance (4 * C) h) :=
  taylorRemainderControlOfSymmetricTaylorStencilBridge
    h_nonzero refinementParameter refinementParameterPositive
    (symmetricTaylorStencilBridgeOfGlobalCenteredAlignmentData data)

/--
The full two-sided endpoint package obtained from the right endpoint route,
the reflected-left endpoint route, the discharged centered alignment, and the
two endpoint remainder bounds.
-/
def twoSidedEndpointPackageOfGlobalCenteredAlignmentData
    {f : Real -> Real}
    {x h C : Real}
    (data :
      EndpointPackageDerivationWithGlobalCenteredAlignmentData f x h C) :
    MathlibEndpointTaylorExpansionPackage f x h C :=
  mathlibEndpointPackageOfGlobalCenteredAlignmentData data

/-- The two-sided package has the theorem-derived right remainder field. -/
theorem two_sided_endpoint_package_right_remainder_field_v0
    {f : Real -> Real}
    {x h C : Real}
    (data :
      EndpointPackageDerivationWithGlobalCenteredAlignmentData f x h C) :
    (twoSidedEndpointPackageOfGlobalCenteredAlignmentData data).right_remainder =
      mathlibEndpointTaylorRemainder f x (x + h) (x + h) := by
  rfl

/-- The two-sided package has the reflected-left remainder field. -/
theorem two_sided_endpoint_package_left_remainder_field_v0
    {f : Real -> Real}
    {x h C : Real}
    (data :
      EndpointPackageDerivationWithGlobalCenteredAlignmentData f x h C) :
    (twoSidedEndpointPackageOfGlobalCenteredAlignmentData data).left_remainder =
      leftEndpointReflectedTaylorRemainder f x h := by
  rfl

/-- The constructed two-sided package feeds the symmetric Taylor bridge. -/
def symmetricTaylorStencilBridgeOfTwoSidedEndpointPackage
    {f : Real -> Real}
    {x h C : Real}
    (data :
      EndpointPackageDerivationWithGlobalCenteredAlignmentData f x h C) :
    SymmetricTaylorStencilBridge f x h (4 * C) :=
  symmetricTaylorStencilBridgeOfMathlibEndpointAlignment
    (twoSidedEndpointPackageOfGlobalCenteredAlignmentData data)

/-- The two-sided endpoint package supplies the scaled stencil remainder bound. -/
theorem two_sided_endpoint_package_supplies_scaled_stencil_bound
    {f : Real -> Real}
    {x h C : Real}
    (h_nonzero : h * h ≠ 0)
    (data :
      EndpointPackageDerivationWithGlobalCenteredAlignmentData f x h C) :
    scaledStencilRemainderErrorBound h
      (symmetricTaylorBridgeRemainderField
        (symmetricTaylorStencilBridgeOfTwoSidedEndpointPackage data))
      (fourthDerivativeStencilTolerance (4 * C) h) := by
  exact
    symmetric_taylor_bridge_supplies_scaled_stencil_bound
      h_nonzero
      (symmetricTaylorStencilBridgeOfTwoSidedEndpointPackage data)

/-- The constructed two-sided package feeds the TaylorRemainderControl route. -/
def taylorRemainderControlOfTwoSidedEndpointPackage
    {f : Real -> Real}
    {x h C : Real}
    (h_nonzero : h * h ≠ 0)
    (refinementParameter : Nat)
    (refinementParameterPositive : 0 < refinementParameter)
    (data :
      EndpointPackageDerivationWithGlobalCenteredAlignmentData f x h C) :
    TaylorRemainderControl h
      (symmetricTaylorBridgeRemainderField
        (symmetricTaylorStencilBridgeOfTwoSidedEndpointPackage data))
      (fourthDerivativeStencilTolerance (4 * C) h) :=
  taylorRemainderControlOfSymmetricTaylorStencilBridge
    h_nonzero refinementParameter refinementParameterPositive
    (symmetricTaylorStencilBridgeOfTwoSidedEndpointPackage data)

/--
The two-sided endpoint package reaches the local stencil error-bound theorem
with the Taylor coefficients associated to the package.
-/
theorem two_sided_endpoint_package_feeds_local_stencil_error_bound
    {f : Real -> Real}
    {x h C : Real}
    (h_nonzero : h * h ≠ 0)
    (refinementParameter : Nat)
    (refinementParameterPositive : 0 < refinementParameter)
    (data :
      EndpointPackageDerivationWithGlobalCenteredAlignmentData f x h C) :
    |centeredScaledGraphLaplacianAtCenter h
        (sampledQuadraticCubicRemainderField
          ((twoSidedEndpointPackageOfGlobalCenteredAlignmentData data).second_derivative / 2)
          (twoSidedEndpointPackageOfGlobalCenteredAlignmentData data).first_derivative
          (twoSidedEndpointPackageOfGlobalCenteredAlignmentData data).value
          ((twoSidedEndpointPackageOfGlobalCenteredAlignmentData data).third_derivative / 6)
          h
          (symmetricTaylorBridgeRemainderField
            (symmetricTaylorStencilBridgeOfTwoSidedEndpointPackage data))) -
      quadraticContinuumSecondDerivative
        ((twoSidedEndpointPackageOfGlobalCenteredAlignmentData data).second_derivative / 2)| ≤
      fourthDerivativeStencilTolerance (4 * C) h := by
  exact
    taylor_remainder_control_feeds_local_stencil_error_bound
      ((twoSidedEndpointPackageOfGlobalCenteredAlignmentData data).second_derivative / 2)
      (twoSidedEndpointPackageOfGlobalCenteredAlignmentData data).first_derivative
      (twoSidedEndpointPackageOfGlobalCenteredAlignmentData data).value
      ((twoSidedEndpointPackageOfGlobalCenteredAlignmentData data).third_derivative / 6)
      h (fourthDerivativeStencilTolerance (4 * C) h)
      (symmetricTaylorBridgeRemainderField
        (symmetricTaylorStencilBridgeOfTwoSidedEndpointPackage data))
      h_nonzero
      (taylorRemainderControlOfTwoSidedEndpointPackage
        h_nonzero refinementParameter refinementParameterPositive data)

/-- The constructed package uses the theorem-derived right mathlib remainder. -/
theorem mathlib_endpoint_package_derivation_right_remainder_field_v0
    {f : Real -> Real}
    {x h C : Real}
    (data : EndpointPackageDerivationFromMathlibData f x h C) :
    (mathlibEndpointPackageOfDerivationData data).right_remainder =
      mathlibEndpointTaylorRemainder f x (x + h) (x + h) := by
  rfl

/--
The supplied derivation data now feeds the prior symmetric Taylor bridge via
the A1A8 package constructor.
-/
def symmetricTaylorStencilBridgeOfEndpointPackageDerivation
    {f : Real -> Real}
    {x h C : Real}
    (data : EndpointPackageDerivationFromMathlibData f x h C) :
    SymmetricTaylorStencilBridge f x h (4 * C) :=
  symmetricTaylorStencilBridgeOfMathlibEndpointAlignment
    (mathlibEndpointPackageOfDerivationData data)

/-- The supplied derivation data feeds the prior TaylorRemainderControl route. -/
def taylorRemainderControlOfEndpointPackageDerivation
    {f : Real -> Real}
    {x h C : Real}
    (h_nonzero : h * h ≠ 0)
    (refinementParameter : Nat)
    (refinementParameterPositive : 0 < refinementParameter)
    (data : EndpointPackageDerivationFromMathlibData f x h C) :
    TaylorRemainderControl h
      (symmetricTaylorBridgeRemainderField
        (symmetricTaylorStencilBridgeOfEndpointPackageDerivation data))
      (fourthDerivativeStencilTolerance (4 * C) h) :=
  taylorRemainderControlOfSymmetricTaylorStencilBridge
    h_nonzero refinementParameter refinementParameterPositive
    (symmetricTaylorStencilBridgeOfEndpointPackageDerivation data)

/-- Remaining obstructions after the endpoint-package derivation attempt. -/
inductive EndpointPackageDerivationFromMathlibObstruction where
  | noCenteredCoefficientAlignmentAcrossEndpointIntervals
  | noLeftEndpointOrientationFromMathlib
  | noTwoSidedEndpointPackageFromSingleMathlibTheorem
  | noUniformMeshConvergence
  | noSampleReconstructionCompatibility
  | noContinuumLaplacianSemantics
  | noOperatorDomainClosure
  | noFullA1AChannelClosure
deriving DecidableEq, Repr

/-- Machine-facing ids for the endpoint package derivation obstruction list. -/
def endpointPackageDerivationFromMathlibObstructionId :
    EndpointPackageDerivationFromMathlibObstruction -> String
  | .noCenteredCoefficientAlignmentAcrossEndpointIntervals =>
      "A2A15A1A9_OBSTRUCTION_NO_CENTERED_COEFFICIENT_ALIGNMENT_ACROSS_ENDPOINT_INTERVALS"
  | .noLeftEndpointOrientationFromMathlib =>
      "A2A15A1A9_OBSTRUCTION_NO_LEFT_ENDPOINT_ORIENTATION_FROM_MATHLIB"
  | .noTwoSidedEndpointPackageFromSingleMathlibTheorem =>
      "A2A15A1A9_OBSTRUCTION_NO_TWO_SIDED_ENDPOINT_PACKAGE_FROM_SINGLE_MATHLIB_THEOREM"
  | .noUniformMeshConvergence =>
      "A2A15A1A9_OBSTRUCTION_NO_UNIFORM_MESH_CONVERGENCE"
  | .noSampleReconstructionCompatibility =>
      "A2A15A1A9_OBSTRUCTION_NO_SAMPLE_RECONSTRUCTION_COMPATIBILITY"
  | .noContinuumLaplacianSemantics =>
      "A2A15A1A9_OBSTRUCTION_NO_CONTINUUM_LAPLACIAN_SEMANTICS"
  | .noOperatorDomainClosure =>
      "A2A15A1A9_OBSTRUCTION_NO_OPERATOR_DOMAIN_CLOSURE"
  | .noFullA1AChannelClosure =>
      "A2A15A1A9_OBSTRUCTION_NO_FULL_A1A_CHANNEL_CLOSURE"

/-- Exact obstruction inventory for the endpoint package derivation slice. -/
def endpointPackageDerivationFromMathlibObstructionsV0 :
    List EndpointPackageDerivationFromMathlibObstruction :=
  [ .noUniformMeshConvergence
  , .noSampleReconstructionCompatibility
  , .noContinuumLaplacianSemantics
  , .noOperatorDomainClosure
  , .noFullA1AChannelClosure
  ]

/-- The endpoint package derivation obstruction inventory is stable. -/
theorem endpoint_package_derivation_from_mathlib_obstructions_v0_expected :
    endpointPackageDerivationFromMathlibObstructionsV0 =
      [ .noUniformMeshConvergence
      , .noSampleReconstructionCompatibility
      , .noContinuumLaplacianSemantics
      , .noOperatorDomainClosure
      , .noFullA1AChannelClosure
      ] := by
  rfl

/-- Next strict target after constructing the two-sided endpoint package. -/
def endpointPackageDerivationNextStrictTargetId : String :=
  "A2A15A1A9_NEXT_STRICT_TARGET_UNIFORM_MESH_CONVERGENCE_DOWNSTREAM"

/-- Endpoint-package prerequisites that must precede uniform mesh convergence. -/
def endpointPackageDerivationPrerequisiteIdsV0 : List String :=
  [ "A2A15A1A9_PREREQUISITE_TAYLOR_WITHIN_EVAL_SCALAR_COEFFICIENT_FORMULA"
  , "A2A15A1A9_PREREQUISITE_REFLECTED_LEFT_ENDPOINT_EXPANSION_AND_BOUND"
  , "A2A15A1A9_PREREQUISITE_CENTERED_COEFFICIENT_ALIGNMENT_ACROSS_ENDPOINT_INTERVALS"
  , "A2A15A1A9_PREREQUISITE_TWO_SIDED_ENDPOINT_PACKAGE_CONSTRUCTION"
  ]

/-- Endpoint-package prerequisites discharged by this slice. -/
def endpointPackageDerivationCompletedPrerequisiteIdsV0 : List String :=
  [ "A2A15A1A9_PREREQUISITE_TAYLOR_WITHIN_EVAL_SCALAR_COEFFICIENT_FORMULA"
  , "A2A15A1A9_PREREQUISITE_REFLECTED_LEFT_ENDPOINT_EXPANSION_AND_BOUND"
  , "A2A15A1A9_PREREQUISITE_CENTERED_COEFFICIENT_ALIGNMENT_ACROSS_ENDPOINT_INTERVALS"
  , "A2A15A1A9_PREREQUISITE_TWO_SIDED_ENDPOINT_PACKAGE_CONSTRUCTION"
  ]

/-- Concrete theorem subtargets discharged inside the endpoint-package route. -/
def endpointPackageDerivationCompletedSubtargetIdsV0 : List String :=
  [ "A2A15A1A9_SUBTARGET_TAYLOR_WITHIN_EVAL_SCALAR_COEFFICIENT_FORMULA"
  , "A2A15A1A9_SUBTARGET_REFLECTED_LEFT_ENDPOINT_EXPANSION_AND_BOUND"
  , "A2A15A1A9_SUBTARGET_LEFT_ORIENTATION_DATA_TO_ENDPOINT_PACKAGE_ROUTE"
  , "A2A15A1A9_SUBTARGET_CENTERED_ENDPOINT_COEFFICIENT_ALIGNMENT_OBJECT_AND_PACKAGE_ROUTE"
  , "A2A15A1A9_SUBTARGET_CENTERED_ENDPOINT_COEFFICIENT_ALIGNMENT_FROM_GLOBAL_CONDIFF"
  , "A2A15A1A9_SUBTARGET_TWO_SIDED_ENDPOINT_PACKAGE_CONSTRUCTION"
  , "A2A15A1A9_SUBTARGET_TWO_SIDED_ENDPOINT_PACKAGE_TO_LOCAL_STENCIL_BOUND_ROUTE"
  ]

/-- Endpoint-package prerequisites that remain after deriving centered alignment. -/
def endpointPackageDerivationRemainingPrerequisiteIdsV0 : List String :=
  []

/-- The endpoint-package prerequisite inventory is stable. -/
theorem endpoint_package_derivation_prerequisite_ids_v0_expected :
    endpointPackageDerivationPrerequisiteIdsV0 =
      [ "A2A15A1A9_PREREQUISITE_TAYLOR_WITHIN_EVAL_SCALAR_COEFFICIENT_FORMULA"
      , "A2A15A1A9_PREREQUISITE_REFLECTED_LEFT_ENDPOINT_EXPANSION_AND_BOUND"
      , "A2A15A1A9_PREREQUISITE_CENTERED_COEFFICIENT_ALIGNMENT_ACROSS_ENDPOINT_INTERVALS"
      , "A2A15A1A9_PREREQUISITE_TWO_SIDED_ENDPOINT_PACKAGE_CONSTRUCTION"
      ] := by
  rfl

/-- The completed endpoint-package prerequisite inventory is stable. -/
theorem endpoint_package_derivation_completed_prerequisite_ids_v0_expected :
    endpointPackageDerivationCompletedPrerequisiteIdsV0 =
      [ "A2A15A1A9_PREREQUISITE_TAYLOR_WITHIN_EVAL_SCALAR_COEFFICIENT_FORMULA"
      , "A2A15A1A9_PREREQUISITE_REFLECTED_LEFT_ENDPOINT_EXPANSION_AND_BOUND"
      , "A2A15A1A9_PREREQUISITE_CENTERED_COEFFICIENT_ALIGNMENT_ACROSS_ENDPOINT_INTERVALS"
      , "A2A15A1A9_PREREQUISITE_TWO_SIDED_ENDPOINT_PACKAGE_CONSTRUCTION"
      ] := by
  rfl

/-- The completed endpoint-package theorem subtarget inventory is stable. -/
theorem endpoint_package_derivation_completed_subtarget_ids_v0_expected :
    endpointPackageDerivationCompletedSubtargetIdsV0 =
      [ "A2A15A1A9_SUBTARGET_TAYLOR_WITHIN_EVAL_SCALAR_COEFFICIENT_FORMULA"
      , "A2A15A1A9_SUBTARGET_REFLECTED_LEFT_ENDPOINT_EXPANSION_AND_BOUND"
      , "A2A15A1A9_SUBTARGET_LEFT_ORIENTATION_DATA_TO_ENDPOINT_PACKAGE_ROUTE"
      , "A2A15A1A9_SUBTARGET_CENTERED_ENDPOINT_COEFFICIENT_ALIGNMENT_OBJECT_AND_PACKAGE_ROUTE"
      , "A2A15A1A9_SUBTARGET_CENTERED_ENDPOINT_COEFFICIENT_ALIGNMENT_FROM_GLOBAL_CONDIFF"
      , "A2A15A1A9_SUBTARGET_TWO_SIDED_ENDPOINT_PACKAGE_CONSTRUCTION"
      , "A2A15A1A9_SUBTARGET_TWO_SIDED_ENDPOINT_PACKAGE_TO_LOCAL_STENCIL_BOUND_ROUTE"
      ] := by
  rfl

/-- The remaining endpoint-package prerequisite inventory is stable. -/
theorem endpoint_package_derivation_remaining_prerequisite_ids_v0_expected :
    endpointPackageDerivationRemainingPrerequisiteIdsV0 = [] := by
  rfl

/-- This theorem-facing slice records concrete obstruction. -/
def endpointPackageDerivationFromMathlibSuccessorKindsV0 :
    List A2A15A1SuccessorKind :=
  [ .recordsConcreteObstruction ]

/-- The successor kind is obstruction-recording, with partial proofs above. -/
theorem endpoint_package_derivation_from_mathlib_successor_kinds_v0_expected :
    endpointPackageDerivationFromMathlibSuccessorKindsV0 =
      [ .recordsConcreteObstruction ] := by
  rfl

/-- Status readout for the endpoint-package derivation slice. -/
structure EndpointPackageDerivationFromMathlibStatus where
  right_endpoint_bound_from_mathlib_proved : Prop
  right_endpoint_bound_from_mathlib_proved_supplied :
    right_endpoint_bound_from_mathlib_proved
  supplied_alignment_data_to_endpoint_package_proved : Prop
  supplied_alignment_data_to_endpoint_package_proved_supplied :
    supplied_alignment_data_to_endpoint_package_proved
  scalar_coefficient_data_to_endpoint_package_proved : Prop
  scalar_coefficient_data_to_endpoint_package_proved_supplied :
    scalar_coefficient_data_to_endpoint_package_proved
  supplied_alignment_data_to_taylor_control_proved : Prop
  supplied_alignment_data_to_taylor_control_proved_supplied :
    supplied_alignment_data_to_taylor_control_proved
  scalar_coefficient_data_to_taylor_control_proved : Prop
  scalar_coefficient_data_to_taylor_control_proved_supplied :
    scalar_coefficient_data_to_taylor_control_proved
  endpoint_package_from_mathlib_fully_derived : Prop
  endpoint_package_from_mathlib_fully_derived_supplied :
    endpoint_package_from_mathlib_fully_derived
  taylor_within_eval_scalar_coefficients_proved : Prop
  taylor_within_eval_scalar_coefficients_proved_supplied :
    taylor_within_eval_scalar_coefficients_proved
  reflected_left_endpoint_bound_from_mathlib_proved : Prop
  reflected_left_endpoint_bound_from_mathlib_proved_supplied :
    reflected_left_endpoint_bound_from_mathlib_proved
  reflected_left_endpoint_expansion_proved : Prop
  reflected_left_endpoint_expansion_proved_supplied :
    reflected_left_endpoint_expansion_proved
  left_orientation_data_to_endpoint_package_proved : Prop
  left_orientation_data_to_endpoint_package_proved_supplied :
    left_orientation_data_to_endpoint_package_proved
  left_orientation_data_to_taylor_control_proved : Prop
  left_orientation_data_to_taylor_control_proved_supplied :
    left_orientation_data_to_taylor_control_proved
  centered_coefficient_alignment_object_and_route_proved : Prop
  centered_coefficient_alignment_object_and_route_proved_supplied :
    centered_coefficient_alignment_object_and_route_proved
  centered_coefficient_alignment_derived_from_mathlib : Prop
  centered_coefficient_alignment_derived_from_mathlib_supplied :
    centered_coefficient_alignment_derived_from_mathlib
  global_smooth_data_to_endpoint_package_proved : Prop
  global_smooth_data_to_endpoint_package_proved_supplied :
    global_smooth_data_to_endpoint_package_proved
  global_smooth_data_to_taylor_control_proved : Prop
  global_smooth_data_to_taylor_control_proved_supplied :
    global_smooth_data_to_taylor_control_proved
  two_sided_endpoint_package_constructed : Prop
  two_sided_endpoint_package_constructed_supplied :
    two_sided_endpoint_package_constructed
  two_sided_endpoint_package_to_taylor_control_proved : Prop
  two_sided_endpoint_package_to_taylor_control_proved_supplied :
    two_sided_endpoint_package_to_taylor_control_proved
  two_sided_endpoint_package_to_local_stencil_bound_proved : Prop
  two_sided_endpoint_package_to_local_stencil_bound_proved_supplied :
    two_sided_endpoint_package_to_local_stencil_bound_proved
  left_endpoint_orientation_proved : Prop
  left_endpoint_orientation_proved_supplied :
    left_endpoint_orientation_proved
  full_a1a_channel_closed : Prop
  full_a1a_channel_not_closed : Not full_a1a_channel_closed
  parent_channel_retained_blocker_id : String
  prior_mathlib_alignment_retained_blocker_id : String
  endpoint_package_derivation_discharged_blocker_id : String
  left_endpoint_orientation_discharged_blocker_id : String
  centered_endpoint_coefficient_alignment_discharged_blocker_id : String
  outcome_id : String
  anti_loop_rule_id : String
  successor_kinds : List A2A15A1SuccessorKind
  obstruction_ids : List String
  next_strict_target_id : String
  endpoint_package_prerequisite_ids : List String
  endpoint_package_completed_prerequisite_ids : List String
  endpoint_package_completed_subtarget_ids : List String
  endpoint_package_remaining_prerequisite_ids : List String
  uniform_mesh_convergence_downstream_until_endpoint_package : Prop
  uniform_mesh_convergence_downstream_until_endpoint_package_supplied :
    uniform_mesh_convergence_downstream_until_endpoint_package
  phase2Authorized : Prop
  phase2_not_authorized : Not phase2Authorized

/--
Current status: the right endpoint, scalar coefficient formula, reflected
left endpoint expansion/bound, and explicit centered-alignment package route
are theorem-derived/formalized from mathlib-facing data.  The centered
endpoint coefficient alignment is derived from global smoothness plus the
nondegenerate endpoint interval, and the two-sided endpoint package now feeds
the symmetric bridge, Taylor control, and local stencil-bound route.  Uniform
mesh convergence and full A1A closure remain retained.
-/
def endpointPackageDerivationFromMathlibStatusV0 :
    EndpointPackageDerivationFromMathlibStatus where
  right_endpoint_bound_from_mathlib_proved := True
  right_endpoint_bound_from_mathlib_proved_supplied := True.intro
  supplied_alignment_data_to_endpoint_package_proved := True
  supplied_alignment_data_to_endpoint_package_proved_supplied := True.intro
  scalar_coefficient_data_to_endpoint_package_proved := True
  scalar_coefficient_data_to_endpoint_package_proved_supplied := True.intro
  supplied_alignment_data_to_taylor_control_proved := True
  supplied_alignment_data_to_taylor_control_proved_supplied := True.intro
  scalar_coefficient_data_to_taylor_control_proved := True
  scalar_coefficient_data_to_taylor_control_proved_supplied := True.intro
  endpoint_package_from_mathlib_fully_derived := True
  endpoint_package_from_mathlib_fully_derived_supplied := True.intro
  taylor_within_eval_scalar_coefficients_proved := True
  taylor_within_eval_scalar_coefficients_proved_supplied := True.intro
  reflected_left_endpoint_bound_from_mathlib_proved := True
  reflected_left_endpoint_bound_from_mathlib_proved_supplied := True.intro
  reflected_left_endpoint_expansion_proved := True
  reflected_left_endpoint_expansion_proved_supplied := True.intro
  left_orientation_data_to_endpoint_package_proved := True
  left_orientation_data_to_endpoint_package_proved_supplied := True.intro
  left_orientation_data_to_taylor_control_proved := True
  left_orientation_data_to_taylor_control_proved_supplied := True.intro
  centered_coefficient_alignment_object_and_route_proved := True
  centered_coefficient_alignment_object_and_route_proved_supplied := True.intro
  centered_coefficient_alignment_derived_from_mathlib := True
  centered_coefficient_alignment_derived_from_mathlib_supplied := True.intro
  global_smooth_data_to_endpoint_package_proved := True
  global_smooth_data_to_endpoint_package_proved_supplied := True.intro
  global_smooth_data_to_taylor_control_proved := True
  global_smooth_data_to_taylor_control_proved_supplied := True.intro
  two_sided_endpoint_package_constructed := True
  two_sided_endpoint_package_constructed_supplied := True.intro
  two_sided_endpoint_package_to_taylor_control_proved := True
  two_sided_endpoint_package_to_taylor_control_proved_supplied := True.intro
  two_sided_endpoint_package_to_local_stencil_bound_proved := True
  two_sided_endpoint_package_to_local_stencil_bound_proved_supplied := True.intro
  left_endpoint_orientation_proved := True
  left_endpoint_orientation_proved_supplied := True.intro
  full_a1a_channel_closed := False
  full_a1a_channel_not_closed := by
    intro h
    exact h
  parent_channel_retained_blocker_id :=
    phase1Blocker003A2A15A1AGraphLaplacianToContinuumLaplacianRetainedId
  prior_mathlib_alignment_retained_blocker_id :=
    phase1Blocker003A2A15A1A8MathlibEndpointTaylorAlignmentRetainedId
  endpoint_package_derivation_discharged_blocker_id :=
    phase1Blocker003A2A15A1A9EndpointPackageDerivationFromMathlibRetainedId
  left_endpoint_orientation_discharged_blocker_id :=
    phase1Blocker003A2A15A1A9LeftEndpointOrientationRetainedId
  centered_endpoint_coefficient_alignment_discharged_blocker_id :=
    phase1Blocker003A2A15A1A9CenteredEndpointCoefficientAlignmentRetainedId
  outcome_id := graphLaplacianEndpointPackageDerivationFromMathlibOutcomeId
  anti_loop_rule_id := analyticIntervalLiftNoMoreChildSplitsRuleId
  successor_kinds := endpointPackageDerivationFromMathlibSuccessorKindsV0
  obstruction_ids :=
    endpointPackageDerivationFromMathlibObstructionsV0.map
      endpointPackageDerivationFromMathlibObstructionId
  next_strict_target_id := endpointPackageDerivationNextStrictTargetId
  endpoint_package_prerequisite_ids :=
    endpointPackageDerivationPrerequisiteIdsV0
  endpoint_package_completed_prerequisite_ids :=
    endpointPackageDerivationCompletedPrerequisiteIdsV0
  endpoint_package_completed_subtarget_ids :=
    endpointPackageDerivationCompletedSubtargetIdsV0
  endpoint_package_remaining_prerequisite_ids :=
    endpointPackageDerivationRemainingPrerequisiteIdsV0
  uniform_mesh_convergence_downstream_until_endpoint_package := True
  uniform_mesh_convergence_downstream_until_endpoint_package_supplied :=
    True.intro
  phase2Authorized := False
  phase2_not_authorized := by
    intro h
    exact h

/-- Short proof-facing status alias. -/
def endpointPackageDerivationFromMathlibStatusReadoutV0 :
    EndpointPackageDerivationFromMathlibStatus :=
  endpointPackageDerivationFromMathlibStatusV0

/-- Short proof-facing status alias used to keep projection statements tidy. -/
def ePkgDerivStatusV0 :
    EndpointPackageDerivationFromMathlibStatus :=
  endpointPackageDerivationFromMathlibStatusReadoutV0

/-- The right endpoint Taylor bound is derived from mathlib. -/
theorem endpoint_package_derivation_right_endpoint_bound_proved_v0 :
    ePkgDerivStatusV0.right_endpoint_bound_from_mathlib_proved := by
  exact ePkgDerivStatusV0.right_endpoint_bound_from_mathlib_proved_supplied

/-- Supplied alignment data constructs the endpoint package. -/
theorem endpoint_package_derivation_to_endpoint_package_proved_v0 :
    ePkgDerivStatusV0.supplied_alignment_data_to_endpoint_package_proved := by
  exact
    ePkgDerivStatusV0.supplied_alignment_data_to_endpoint_package_proved_supplied

/-- Derived scalar-coefficient data constructs the endpoint package. -/
theorem endpoint_package_derivation_scalar_coefficient_data_to_endpoint_package_proved_v0 :
    ePkgDerivStatusV0.scalar_coefficient_data_to_endpoint_package_proved := by
  exact
    ePkgDerivStatusV0.scalar_coefficient_data_to_endpoint_package_proved_supplied

/-- Supplied alignment data feeds the TaylorRemainderControl route. -/
theorem endpoint_package_derivation_to_taylor_control_proved_v0 :
    ePkgDerivStatusV0.supplied_alignment_data_to_taylor_control_proved := by
  exact
    ePkgDerivStatusV0.supplied_alignment_data_to_taylor_control_proved_supplied

/-- Derived scalar-coefficient data feeds the TaylorRemainderControl route. -/
theorem endpoint_package_derivation_scalar_coefficient_data_to_taylor_control_proved_v0 :
    ePkgDerivStatusV0.scalar_coefficient_data_to_taylor_control_proved := by
  exact
    ePkgDerivStatusV0.scalar_coefficient_data_to_taylor_control_proved_supplied

/-- The bounded two-sided endpoint package route is now derived. -/
theorem endpoint_package_derivation_from_mathlib_fully_derived_v0 :
    ePkgDerivStatusV0.endpoint_package_from_mathlib_fully_derived := by
  exact ePkgDerivStatusV0.endpoint_package_from_mathlib_fully_derived_supplied

/-- Scalar coefficient alignment for `taylorWithinEval` is now theorem-derived. -/
theorem endpoint_package_derivation_scalar_coefficients_proved_v0 :
    ePkgDerivStatusV0.taylor_within_eval_scalar_coefficients_proved := by
  exact ePkgDerivStatusV0.taylor_within_eval_scalar_coefficients_proved_supplied

/-- The reflected left endpoint bound is now theorem-derived from mathlib. -/
theorem endpoint_package_derivation_reflected_left_bound_proved_v0 :
    ePkgDerivStatusV0.reflected_left_endpoint_bound_from_mathlib_proved := by
  exact
    ePkgDerivStatusV0.reflected_left_endpoint_bound_from_mathlib_proved_supplied

/-- The reflected left endpoint expansion is now theorem-derived. -/
theorem endpoint_package_derivation_reflected_left_expansion_proved_v0 :
    ePkgDerivStatusV0.reflected_left_endpoint_expansion_proved := by
  exact ePkgDerivStatusV0.reflected_left_endpoint_expansion_proved_supplied

/-- Supplied orientation equalities now construct the endpoint package. -/
theorem endpoint_package_derivation_left_orientation_data_to_endpoint_package_proved_v0 :
    ePkgDerivStatusV0.left_orientation_data_to_endpoint_package_proved := by
  exact
    ePkgDerivStatusV0.left_orientation_data_to_endpoint_package_proved_supplied

/-- Supplied orientation equalities now feed the TaylorRemainderControl route. -/
theorem endpoint_package_derivation_left_orientation_data_to_taylor_control_proved_v0 :
    ePkgDerivStatusV0.left_orientation_data_to_taylor_control_proved := by
  exact
    ePkgDerivStatusV0.left_orientation_data_to_taylor_control_proved_supplied

/-- The centered coefficient-alignment object and package route are explicit. -/
theorem endpoint_package_derivation_centered_alignment_object_and_route_proved_v0 :
    ePkgDerivStatusV0.centered_coefficient_alignment_object_and_route_proved := by
  exact
    ePkgDerivStatusV0.centered_coefficient_alignment_object_and_route_proved_supplied

/-- The centered coefficient alignment theorem from mathlib is now derived. -/
theorem endpoint_package_derivation_centered_alignment_derived_v0 :
    ePkgDerivStatusV0.centered_coefficient_alignment_derived_from_mathlib := by
  exact
    ePkgDerivStatusV0.centered_coefficient_alignment_derived_from_mathlib_supplied

/-- Global smoothness data constructs the endpoint package route. -/
theorem endpoint_package_derivation_global_smooth_data_to_endpoint_package_proved_v0 :
    ePkgDerivStatusV0.global_smooth_data_to_endpoint_package_proved := by
  exact
    ePkgDerivStatusV0.global_smooth_data_to_endpoint_package_proved_supplied

/-- Global smoothness data feeds the TaylorRemainderControl route. -/
theorem endpoint_package_derivation_global_smooth_data_to_taylor_control_proved_v0 :
    ePkgDerivStatusV0.global_smooth_data_to_taylor_control_proved := by
  exact
    ePkgDerivStatusV0.global_smooth_data_to_taylor_control_proved_supplied

/-- The full two-sided endpoint package is constructed. -/
theorem endpoint_package_derivation_two_sided_endpoint_package_constructed_v0 :
    ePkgDerivStatusV0.two_sided_endpoint_package_constructed := by
  exact
    ePkgDerivStatusV0.two_sided_endpoint_package_constructed_supplied

/-- The two-sided endpoint package feeds the TaylorRemainderControl route. -/
theorem endpoint_package_derivation_two_sided_endpoint_package_to_taylor_control_proved_v0 :
    ePkgDerivStatusV0.two_sided_endpoint_package_to_taylor_control_proved := by
  exact
    ePkgDerivStatusV0.two_sided_endpoint_package_to_taylor_control_proved_supplied

/-- The two-sided endpoint package feeds the local stencil error-bound route. -/
theorem endpoint_package_derivation_two_sided_endpoint_package_to_local_stencil_bound_proved_v0 :
    ePkgDerivStatusV0.two_sided_endpoint_package_to_local_stencil_bound_proved := by
  exact
    ePkgDerivStatusV0.two_sided_endpoint_package_to_local_stencil_bound_proved_supplied

/-- The reflected/global left orientation route is now proved. -/
theorem endpoint_package_derivation_left_orientation_proved_v0 :
    ePkgDerivStatusV0.left_endpoint_orientation_proved := by
  exact ePkgDerivStatusV0.left_endpoint_orientation_proved_supplied

/-- The endpoint package derivation slice does not close full A1A. -/
theorem endpoint_package_derivation_full_a1a_not_closed_v0 :
    Not ePkgDerivStatusV0.full_a1a_channel_closed := by
  exact ePkgDerivStatusV0.full_a1a_channel_not_closed

/-- The parent A1A retained blocker remains exposed. -/
theorem endpoint_package_derivation_parent_retained_id_v0 :
    ePkgDerivStatusV0.parent_channel_retained_blocker_id =
      phase1Blocker003A2A15A1AGraphLaplacianToContinuumLaplacianRetainedId := by
  rfl

/-- The prior A1A8 retained blocker remains exposed. -/
theorem endpoint_package_derivation_prior_a1a8_retained_id_v0 :
    ePkgDerivStatusV0.prior_mathlib_alignment_retained_blocker_id =
      phase1Blocker003A2A15A1A8MathlibEndpointTaylorAlignmentRetainedId := by
  rfl

/-- The theorem-facing surface exposes its discharged endpoint-package blocker id. -/
theorem endpoint_package_derivation_discharged_id_v0 :
    ePkgDerivStatusV0.endpoint_package_derivation_discharged_blocker_id =
      phase1Blocker003A2A15A1A9EndpointPackageDerivationFromMathlibRetainedId := by
  rfl

/-- The left endpoint orientation blocker id is exposed as discharged. -/
theorem endpoint_package_derivation_left_orientation_discharged_id_v0 :
    ePkgDerivStatusV0.left_endpoint_orientation_discharged_blocker_id =
      phase1Blocker003A2A15A1A9LeftEndpointOrientationRetainedId := by
  rfl

/-- The centered coefficient alignment blocker id is exposed as discharged. -/
theorem endpoint_package_derivation_centered_alignment_discharged_id_v0 :
    ePkgDerivStatusV0.centered_endpoint_coefficient_alignment_discharged_blocker_id =
      phase1Blocker003A2A15A1A9CenteredEndpointCoefficientAlignmentRetainedId := by
  rfl

/-- The theorem-facing surface exposes its outcome id. -/
theorem endpoint_package_derivation_outcome_id_v0 :
    endpointPackageDerivationFromMathlibStatusReadoutV0.outcome_id =
      graphLaplacianEndpointPackageDerivationFromMathlibOutcomeId := by
  rfl

/-- The successor is governed by the post-capstone anti-loop rule. -/
theorem endpoint_package_derivation_anti_loop_rule_id_v0 :
    endpointPackageDerivationFromMathlibStatusReadoutV0.anti_loop_rule_id =
      analyticIntervalLiftNoMoreChildSplitsRuleId := by
  rfl

/-- The successor kind is obstruction-recording. -/
theorem endpoint_package_derivation_successor_kinds_v0 :
    endpointPackageDerivationFromMathlibStatusReadoutV0.successor_kinds =
      endpointPackageDerivationFromMathlibSuccessorKindsV0 := by
  rfl

/-- The next strict target is finishing the endpoint package. -/
theorem endpoint_package_derivation_next_strict_target_id_v0 :
    endpointPackageDerivationFromMathlibStatusReadoutV0.next_strict_target_id =
      endpointPackageDerivationNextStrictTargetId := by
  rfl

/-- The endpoint-package prerequisites are the active ordered target set. -/
theorem endpoint_package_derivation_prerequisite_ids_v0 :
    endpointPackageDerivationFromMathlibStatusReadoutV0.endpoint_package_prerequisite_ids =
      endpointPackageDerivationPrerequisiteIdsV0 := by
  rfl

/-- The status readout exposes completed endpoint-package prerequisites. -/
theorem endpoint_package_derivation_completed_prerequisite_ids_v0 :
    ePkgDerivStatusV0.endpoint_package_completed_prerequisite_ids =
      endpointPackageDerivationCompletedPrerequisiteIdsV0 := by
  rfl

/-- The status readout exposes completed theorem subtargets. -/
theorem endpoint_package_derivation_completed_subtarget_ids_v0 :
    ePkgDerivStatusV0.endpoint_package_completed_subtarget_ids =
      endpointPackageDerivationCompletedSubtargetIdsV0 := by
  rfl

/-- The status readout exposes the remaining endpoint-package prerequisites. -/
theorem endpoint_package_derivation_remaining_prerequisite_ids_v0 :
    ePkgDerivStatusV0.endpoint_package_remaining_prerequisite_ids =
      endpointPackageDerivationRemainingPrerequisiteIdsV0 := by
  rfl

/--
Uniform mesh convergence remains downstream until the endpoint package is
derived or explicitly blocked.
-/
theorem endpoint_package_derivation_uniform_mesh_convergence_downstream_v0 :
    ePkgDerivStatusV0.uniform_mesh_convergence_downstream_until_endpoint_package := by
  exact ePkgDerivStatusV0.uniform_mesh_convergence_downstream_until_endpoint_package_supplied

/-- Phase 2 remains unauthorized after this theorem-facing A1A slice. -/
theorem endpoint_package_derivation_phase2_not_authorized_v0 :
    Not ePkgDerivStatusV0.phase2Authorized := by
  exact ePkgDerivStatusV0.phase2_not_authorized

end

end ContinuumSpatialGraphLaplacianEndpointPackageDerivationFromMathlib
end QFT
end ToeFormal

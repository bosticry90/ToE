# Scalar-Only Quadratic-Gravity Viability and Native-Relevance Result Review V0

## Review result

```text
target:
review_scalar_only_quadratic_gravity_viability_and_native_relevance_v0_result

verdict:
ACCEPTED_BOUNDED_SCALAR_ONLY_COMPARISON_RESULT

principal outcome:
SCALAR_BRANCH_COMPARISON_VIABLE_NATIVE_RELEVANCE_UNESTABLISHED

review gates:
18 / 18 PASSED

comparison branch adopted:
NO

native scalar bridge identified:
NO
```

The completed execution is accepted as a bounded comparison result.  It
supports scalar-sector viability only in the tested linear domains and does
not establish a ToE-native reason to include the scalar.

## Execution custody

The human result, JSON result, generator, focused test, and Lean witness all
match their frozen SHA-256 values.  The execution consumed exactly its one
authorized run and rotated to this independent review.

## Independent metric and trace reproduction

For

\[
f(R)=R+\alpha R^2,
\qquad f_R=1+2\alpha R,
\]

the independently reproduced metric equation is

\[
(1+2\alpha R)R_{\mu\nu}
-\frac12(R+\alpha R^2)g_{\mu\nu}
+2\alpha(g_{\mu\nu}\Box-\nabla_\mu\nabla_\nu)R
=\kappa T_{\mu\nu}.
\]

Its exact four-dimensional trace is

\[
-R+6\alpha\Box R=\kappa T,
\]

so

\[
m_0^2=-\frac1{6\alpha}.
\]

No literature mass formula was used as an input.

## Convention and scalar-frame audit

The bound translation

```text
R_literature     = -R_packet
alpha_literature = -alpha_packet
f_RR_literature  = -2 alpha_packet
```

is internally consistent.  Therefore `alpha_packet < 0` implies both
`m0^2 > 0` and `f_RR_literature > 0`.

The auxiliary equation, Legendre inverse, and Jordan potential reproduce as

\[
2\alpha(R-\chi)=0,
\qquad
\Phi=1+2\alpha\chi,
\qquad
U(\Phi)=\frac{(\Phi-1)^2}{4\alpha}.
\]

Local scalar equivalence requires `alpha != 0`.  The conformal map requires
`Phi > 0`, and

\[
g^E_{\mu\nu}=\Phi g_{\mu\nu},
\qquad
\varphi=\sqrt{\frac{3}{2\kappa}}\ln\Phi,
\qquad
A(\varphi)=\Phi^{-1/2}.
\]

After the complete whole-action convention translation, the physical
comparison potential is

\[
V_E^{\rm phys}
=\frac{1}{8\kappa(-\alpha)}
\left(1-e^{-\sqrt{2\kappa/3}\,\varphi}\right)^2,
\]

and its curvature at `varphi = 0` is exactly `-1/(6 alpha)`.  Thus the frame
transformation did not lose the mass sign.

## Independent background review

### Minkowski

`R0 = 0`, `Phi0 = 1`, and `T_mu_nu = 0` solve the complete field equation and
leave no tadpole.  The accepted positive isolated scalar residue and the
independently reproduced positive mass-squared for `alpha < 0` support the
bounded Minkowski statement.

### Pure vacuum constant curvature

The constant-curvature equation is

\[
f_R(R_0)R_0-2f(R_0)=-R_0=0.
\]

Hence the pure branch has no nonzero vacuum constant-curvature solution.

### Supplied constant-density background

The supplied comparison source

\[
S_\rho=\frac1c\int d^4x\sqrt{-g}\,\rho_\Lambda
\]

varies as

\[
\delta S_\rho
=-\frac1{2c}\int d^4x\sqrt{-g}\,
\rho_\Lambda g_{\mu\nu}\delta g^{\mu\nu},
\]

so the packet convention gives

\[
T_{\mu\nu}=\rho_\Lambda g_{\mu\nu},
\qquad T=4\rho_\Lambda.
\]

For constant `rho_Lambda`, metric compatibility gives
`nabla_mu T^mu_nu = 0`.  On a maximally symmetric background, the complete
tensor equation reduces to

\[
\left[
\frac14(1+2\alpha R_0)R_0
-\frac12(R_0+\alpha R_0^2)
\right]g_{\mu\nu}
=-\frac{R_0}{4}g_{\mu\nu}
=\kappa\rho_\Lambda g_{\mu\nu}.
\]

Thus

\[
R_0=-4\kappa\rho_\Lambda,
\qquad
\Phi_0=1-8\kappa\alpha\rho_\Lambda.
\]

The trace and full tensor equations agree.  For the tested
`alpha < 0`, `rho_Lambda >= 0` stratum, `Phi0 > 0`.  Because the supplied
source has the exact fixed trace `4 rho_Lambda`, `delta T = 0`, and the
curvature perturbation obeys

\[
(\bar\Box+m_0^2)\delta R=0.
\]

This establishes one bounded supplied-background curvature-mode test, not
arbitrary-background, nonlinear, or dynamical-matter stability.

The complete tensor equation, not merely the trace equation, is therefore the
background acceptance gate.

## Matter-trace and screening review

The convention translation gives `f_RR_literature > 0` in the same packet
stratum in which `m0^2 > 0`.  Together with the exact fixed-source curvature
perturbation equation, this reproduces the bounded matter-sector curvature
stability check.  It does not establish stability of a coupled dynamical
matter model.

The exact trace operator has constant mass and constant source coefficient:

\[
(\Box+m_0^2)R=\frac{\kappa}{6\alpha}T.
\]

Therefore an exactly traceless supplied classical source has no direct linear
scalar excitation.  Mass terms, interactions, anomalies, curved-background
effects, and nonlinear corrections are outside this statement.

The fixed-source branch supplies ordinary Yukawa suppression only.  No
environment-dependent mass, coupling, chameleon mechanism, or Vainshtein
mechanism was derived in the tested model.  This is not a claim about every
scalar theory or every self-consistent nonlinear matter problem.

```text
FINITE_MASS_SUPPRESSION_ONLY
```

## Native-bridge review

All three audited project surfaces fail at the first required bridge step:

| Surface | First failed criterion | Review finding |
| --- | --- | --- |
| `NATIVE_PHI_ALIGNMENT_WITNESS` | `FIELD_DEFINITION` | No defined map to `Phi=f_R`; native generation remains blocked. |
| `PROVISIONAL_CLASSICAL_SCALAR_SOURCE_SANDBOX` | `FIELD_DEFINITION` | A supplied on-shell source is not a native scalaron definition. |
| `PHI_CK_ADMISSIBILITY_RULE_FAMILY` | `FIELD_DEFINITION` | A nondynamical admissibility rule defines neither `Phi` nor its equation. |

No later resemblance overrides these failures.  Complete bridges remain
`0 / 3`.

## Accepted bounded claim

Under the frozen supplied `R+alpha R^2` comparison, convention map,
`alpha != 0`, `Phi > 0`, external-source treatment, Minkowski background, and
one supplied constant-density maximally symmetric background, the scalar has
a coherent scalar-tensor representation and a bounded non-tachyonic linear
domain for packet `alpha < 0`.  Traceful matter directly sources it at the
tested order; exactly traceless supplied classical matter does not.  The
model exhibits finite-range suppression but no intrinsic environmental
screening in the tested fixed-source domain.  No ToE-native scalar bridge is
identified.

## Claim firewall and next authority

This review does not adopt `beta=0`, select a sign or value of `alpha`, adopt
the scalar branch, select matter, identify a native gravitational principle,
select an action, authorize empirical fitting, establish nonlinear or
arbitrary-background stability, resume orbital transport or frame dragging,
or mutate the master action.

The only authorized successor is

```text
select_post_scalar_only_quadratic_gravity_viability_and_native_relevance_scientific_response_v0
```

That selector may compare bounded next scientific routes.  It may not adopt a
branch or action.

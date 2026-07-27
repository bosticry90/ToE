# Scalar-Only Quadratic-Gravity Viability and Native-Relevance Execution V0

## Result

```text
target:
execute_scalar_only_quadratic_gravity_viability_and_native_relevance_v0

verdict:
COMPLETE_BOUNDED_SCALAR_ONLY_COMPARISON_PENDING_INDEPENDENT_REVIEW

principal outcome:
SCALAR_BRANCH_COMPARISON_VIABLE_NATIVE_RELEVANCE_UNESTABLISHED

authorized executions consumed:
1 / 1

work packages:
6 / 6 COMPLETED

decision questions:
8 / 8 ANSWERED

scalar-tensor obligations:
8 / 8 DERIVED

background rows:
3 / 3 ANALYZED

shared-path controls:
12 / 12 PASSED

native scalar bridges:
0
```

The scalar-only branch is a boundedly coherent supplied comparison in the
tested domain. No ToE-specific reason for this scalar was identified. Neither
`beta=0` nor any sign or value of `alpha` has been adopted.

## Frozen comparison and conventions

The executed branch is

\[
S_g^{\rm cmp}
=\frac{1}{2\kappa c}\int d^4x\sqrt{-g}\left(R+\alpha R^2\right),
\qquad
\kappa=\frac{8\pi G}{c^4},
\]

with signature `(+,-,-,-)`, the previously frozen curvature convention, and
`beta=0` used only as a comparison restriction.

The review-bound literature translation remains in force:

```text
R_literature     = -R_packet
alpha_literature = -alpha_packet
f_RR_literature  = -2 alpha_packet
```

Consequently `alpha_packet<0` is consistent both with positive packet scalar
mass-squared and the translated standard `f_RR>0` matter-stability sign.

## D1–D2 — metric and trace equations

Direct metric variation gives

\[
(1+2\alpha R)R_{\mu\nu}
-\frac12(R+\alpha R^2)g_{\mu\nu}
+2\alpha\left(g_{\mu\nu}\Box-\nabla_\mu\nabla_\nu\right)R
=\kappa T_{\mu\nu}.
\]

Its exact four-dimensional trace is

\[
-R+6\alpha\Box R=\kappa T.
\]

Writing

\[
m_0^2=-\frac{1}{6\alpha},
\]

the trace equation becomes

\[
(\Box+m_0^2)R=\frac{\kappa}{6\alpha}T.
\]

This equation was derived from the frozen action; no literature field equation
was imported.

## D3–D5 — scalar-tensor representation

Introduce an auxiliary curvature variable `chi`:

\[
f(\chi)+f_\chi(\chi)(R-\chi).
\]

For \(f(\chi)=\chi+\alpha\chi^2\), its equation is

\[
2\alpha(R-\chi)=0.
\]

Thus local equivalence requires \(\alpha\ne0\). Define

\[
\Phi=1+2\alpha\chi,
\qquad
\chi=\frac{\Phi-1}{2\alpha}.
\]

The Jordan-frame action is

\[
S_J=\frac{1}{2\kappa c}\int d^4x\sqrt{-g}
\left[\Phi R-U(\Phi)\right]+S_m[g,\Psi],
\]

where

\[
U(\Phi)=\frac{(\Phi-1)^2}{4\alpha}.
\]

The `alpha=0` Einstein comparison point is a noninvertible limit of this scalar
map; it is not obtained by dividing by `alpha` there.

For

\[
\Phi>0,
\]

the Einstein-frame metric and canonically normalized scalar are

\[
g^E_{\mu\nu}=\Phi g_{\mu\nu},
\qquad
\varphi=\sqrt{\frac{3}{2\kappa}}\ln\Phi.
\]

Matter sees

\[
g^{\rm matter}_{\mu\nu}=\Phi^{-1}g^E_{\mu\nu},
\qquad
A(\varphi)=\Phi^{-1/2}
=e^{-\sqrt{\kappa/6}\,\varphi}.
\]

Therefore

\[
\frac{d\ln A}{d\varphi}=-\sqrt{\frac{\kappa}{6}},
\]

so the scalar has a fixed universal trace coupling in this supplied comparison.

The direct packet-frame potential is

\[
V_E^{\rm packet}=\frac{U}{2\kappa\Phi^2}.
\]

After the complete review-bound whole-action convention translation, the
positive physical comparison potential for `alpha_packet<0` is

\[
V_E^{\rm phys}(\varphi)
=\frac{1}{8\kappa(-\alpha)}
\left(1-e^{-\sqrt{2\kappa/3}\,\varphi}\right)^2.
\]

It has a minimum at \(\varphi=0\), \(\Phi=1\), and

\[
\left.\frac{d^2V_E^{\rm phys}}{d\varphi^2}\right|_0
=-\frac{1}{6\alpha}=m_0^2.
\]

Kinetic health is read using the bound whole-action convention map and the
accepted conserved-source-saturated scalar residue, not from an isolated
printed action sign.

## D6 — Minkowski control

For `T_mu_nu=0`:

```text
R0:             0
Phi0:           1
tadpole:        NONE
scalar residue: POSITIVE RELATIVE ISOLATED CHANNEL
m0^2:           -1/(6 alpha)
```

The bounded non-tachyonic domain is

\[
\alpha<0.
\]

The accepted scalar-only point-mass response is reproduced:

\[
h_{00}(r)=-\frac{2GM}{c^2r}
\left(1+\frac13e^{-m_0r}\right).
\]

The direct scalar projector contribution to the stationary conserved `0i`
channel remains zero. This does not establish absence of indirect scalar effects
in nonlinear rotating systems.

## D7 — pure vacuum constant-curvature control

For a constant vacuum curvature,

\[
f_R(R_0)R_0-2f(R_0)=-R_0=0.
\]

Therefore

```text
pure vacuum solution:
R0 = 0 ONLY

nonzero vacuum de Sitter / anti-de Sitter:
NOT ADMITTED
```

No stability calculation was assigned to a nonexistent nonzero vacuum
background.

## D8 — supplied non-Minkowski background

The execution uses one explicitly supplied, nondynamical vacuum-energy
comparison source:

\[
S_\rho^{\rm cmp}=\frac1c\int d^4x\sqrt{-g}\,\rho_\Lambda,
\qquad \rho_\Lambda=\text{constant}.
\]

Under the packet stress-tensor convention,

\[
T_{\mu\nu}=\rho_\Lambda g_{\mu\nu},
\qquad
\nabla_\mu T^{\mu\nu}=0,
\qquad
T=4\rho_\Lambda.
\]

For a maximally symmetric background,

\[
R_{\mu\nu}=\frac{R_0}{4}g_{\mu\nu},
\]

the complete field equation gives

\[
R_0=-4\kappa\rho_\Lambda,
\qquad
\Phi_0=1-8\kappa\alpha\rho_\Lambda.
\]

For

\[
\alpha<0,
\qquad
\rho_\Lambda\ge0,
\]

one has \(\Phi_0>0\). Because the source trace is constant,
\(\delta T=0\), and the scalar curvature perturbation obeys

\[
(\bar\Box+m_0^2)\delta R=0,
\qquad
m_0^2=-\frac1{6\alpha}>0.
\]

Thus this one supplied non-Minkowski background passes background existence,
conformal-domain, isolated scalar residue, non-tachyonic, and linear runaway
tests. It does not establish arbitrary-background, dynamical-matter, or
nonlinear stability.

## D9 — matter trace and screening

For a supplied trace perturbation,

\[
(\bar\Box+m_0^2)\delta R
=\frac{\kappa}{6\alpha}\delta T.
\]

Therefore:

```text
traceful nonrelativistic source:
DIRECT SCALAR SOURCE

classically traceless source:
NO DIRECT LINEAR SCALAR SOURCE
```

In the Einstein frame, the traces obey

\[
T_E=\Phi^{-2}T_J.
\]

For the exact fixed-source trace operator of the pure quadratic branch, the
mass and coupling are constant. The bounded screening result is therefore

```text
FINITE_MASS_SUPPRESSION_ONLY

intrinsic environment-dependent chameleon mechanism:
NOT IDENTIFIED

Vainshtein-type mechanism:
NOT IDENTIFIED
```

The static suppression is the ordinary Yukawa factor `exp(-m0 r)`. This is not
a proof about every nonlinear matter backreaction problem.

## D10 — native-relevance audit

All three project surfaces were tested against:

```text
FIELD_DEFINITION
TRANSFORMATION_LAW
DIMENSIONS
COUPLINGS
EQUATION_OF_MOTION
DOMAIN
OBSERVABLE_ROLE
```

Results:

| Candidate | Result | Decisive failure |
| --- | --- | --- |
| `NATIVE_PHI_ALIGNMENT_WITNESS` | `NOT_IDENTIFIED` | No map to `Phi=f_R`; native generation remains blocked. |
| `PROVISIONAL_CLASSICAL_SCALAR_SOURCE_SANDBOX` | `NOT_IDENTIFIED` | Supplied on-shell source is neither native matter nor a scalaron map. |
| `PHI_CK_ADMISSIBILITY_RULE_FAMILY` | `NOT_IDENTIFIED` | Admissibility rules are nondynamical and derive neither `Phi` nor its equation. |

No bridge field was credited by thematic resemblance. No seam packet is
triggered.

```text
NO_NATIVE_SCALAR_BRIDGE_IDENTIFIED
```

## Eight decision answers

1. **Linear scalar domain:** supported for `alpha<0` and `Phi>0`.
2. **One non-Minkowski background:** supported for the supplied constant
   vacuum-energy source under the stated domain.
3. **Exciting source:** the exact trace `T`; a classically traceless source has
   no direct linear excitation.
4. **Suppression mechanism:** finite scalar mass only in the tested domain.
5. **Most decisive future limit:** static trace-sensitive range or fifth-force
   constraints on `m0^-1`; no data or value is used here.
6. **Native object:** none identified.
7. **ToE-specific value:** none identified beyond supplied metric `f(R)` scalar
   physics.
8. **Minimal-mode priority:** not automatically triggered, because bounded
   scalar viability was not obstructed; native relevance remains absent.

## Two-axis result

```text
comparison viability:
SUPPORTED IN BOUNDED LINEAR AND ONE SUPPLIED NON-MINKOWSKI DOMAIN

native relevance:
NOT IDENTIFIED

branch adopted:
NO
```

This is why the principal outcome is

```text
SCALAR_BRANCH_COMPARISON_VIABLE_NATIVE_RELEVANCE_UNESTABLISHED
```

## Controls

All 12 shared-path controls passed:

1. exact single-execution authority;
2. auxiliary and Legendre algebra;
3. fail-closed `alpha=0` scalar map;
4. `Phi>0` conformal domain;
5. Minkowski control;
6. no nonzero pure-vacuum curvature root;
7. supplied background solves the complete field equation;
8. traceless-source direct decoupling;
9. potential mass agrees with trace mass;
10. `alpha -> 0-` infinite-mass decoupling;
11. finite mass is not screening; and
12. zero native bridges and zero branch adoption.

## Claim ceiling and stop

The result does not establish:

- `beta=0` as a native principle;
- a selected sign or value of `alpha`;
- adoption of the scalar-only branch;
- arbitrary-background or nonlinear stability;
- intrinsic nonlinear screening;
- empirical viability;
- a ToE scalar bridge;
- a native gravitational principle or action;
- a native matter sector;
- orbital transport or frame dragging; or
- a master-action change.

Authority stops at:

```text
review_scalar_only_quadratic_gravity_viability_and_native_relevance_v0_result
```

# Shared Linearized Quadratic-Gravity Source and Spectrum Comparison Result Review v0

Date: 2026-07-18  
Target: `review_shared_linearized_quadratic_gravity_source_and_spectrum_comparison_v0_result`  
Verdict: `ACCEPTED_BOUNDED_SHARED_LINEARIZED_QUADRATIC_GRAVITY_COMPARISON_RESULT`  
Selected next target: `select_post_quadratic_gravity_comparison_scientific_response_v0`

## Outcome

The completed comparison result is accepted within its frozen local,
four-dimensional, metric, Minkowski-background, conserved-external-source
domain. The review independently reproduced the variation, background gate,
projector inverse, isolated-pole residues, static 00 and 0i responses, and all
special finite-parameter strata needed by the claim.

```text
independent scientific review gates: 16 / 16 PASSED
execution accepted:                  YES
authorized execution consumed:       1 / 1
derivation stages reviewed:          10 / 10
mode rows reviewed:                   3 / 3
physical outputs reviewed:           11 / 11
controls reviewed:                   10 / 10
comparison action adopted:           NO
native gravitational principle:      NOT IDENTIFIED
```

Acceptance establishes a supplied comparison result. It does not establish a
ToE action, empirical viability, nonlinear stability, arbitrary-background mode
content, or frame-dragging recovery.

## Independent field-equation reproduction

For

$$
S_g=A_{\rm EH}\int d^4x\sqrt{-g}
\left(R+\alpha R^2+\beta R_{\mu\nu}R^{\mu\nu}\right),
$$

the review separately varied each quadratic invariant under the frozen inverse-
metric convention.

The $R^2$ contribution is

$$
H^{(R^2)}_{\mu\nu}
=2R\left(R_{\mu\nu}-\frac14g_{\mu\nu}R\right)
+2(g_{\mu\nu}\Box-\nabla_\mu\nabla_\nu)R.
$$

The Ricci-squared contribution is

$$
H^{(R_{\rho\sigma}^2)}_{\mu\nu}
=2R_{\mu\rho\nu\sigma}R^{\rho\sigma}
-\nabla_\mu\nabla_\nu R+\Box R_{\mu\nu}
+\frac12g_{\mu\nu}
(\Box R-R_{\rho\sigma}R^{\rho\sigma}).
$$

Their four-dimensional traces are respectively $6\Box R$ and $2\Box R$.
The second result follows explicitly because the two curvature-square traces
cancel and the derivative terms leave $2\Box R$. Therefore

$$
-R+2(3\alpha+\beta)\Box R=\kappa T.
$$

At linear order, the Ricci-squared tensor becomes

$$
H^{(R_{\rho\sigma}^2),L}_{\mu\nu}
=\Box G^L_{\mu\nu}
+(\eta_{\mu\nu}\Box-\partial_\mu\partial_\nu)R^L.
$$

Adding the $R^2$ term independently reproduces

$$
\boxed{
(1+\beta\Box)G^L_{\mu\nu}
+(2\alpha+\beta)
(\eta_{\mu\nu}\Box-\partial_\mu\partial_\nu)R^L
=\kappa T_{\mu\nu}.}
$$

The flat divergence vanishes before imposing a gauge. The source variation
again gives

$$
\kappa=\frac{1}{2cA_{\rm EH}}=\frac{8\pi G}{c^4}
$$

with positive sign.

## Independent background review

With $T_{\mu\nu}=0$, $g=\eta$, and no cosmological term, all background
curvatures and curvature derivatives vanish. Substitution into the independently
reproduced exact tensor gives $E_{\mu\nu}[\eta]=0$. Because the first variation
vanishes, no $O(h)$ tadpole remains under the compact-support local-bulk rule.
The background gate is valid.

## Independent projector reconstruction

Using the frozen Fourier sign and de Donder gauge-fixing action, the review
reconstructed the complete Barnes–Rivers operator. Its physical eigenvalues are

$$
\lambda_2=-\frac12k^2(1-\beta k^2),
\qquad
\lambda_0=k^2(1+2\Sigma k^2),
\qquad \Sigma=3\alpha+\beta.
$$

The gauge-fixed scalar block is

$$
k^2\begin{pmatrix}
\frac14+2\Sigma k^2&\frac{\sqrt3}{4}\\
\frac{\sqrt3}{4}&-\frac14
\end{pmatrix},
$$

with determinant

$$
-\frac14k^4(1+2\Sigma k^2).
$$

Direct matrix multiplication independently reproduces the execution's full
inverse. Only after contraction with $k_\mu T^{\mu\nu}=0$ do the $P^1$,
$P^{0w}$, and mixed sectors vanish. The physical response is

$$
h=2\kappa\left[
\frac{P^2}{k^2(1-\beta k^2)}
-\frac{P^{0s}}{2k^2(1+2\Sigma k^2)}
\right]T.
$$

## Independent pole and residue review

For finite generic $\beta\ne0$ and $\Sigma\ne0$,

$$
m_2^2=\frac1\beta,
\qquad
m_0^2=-\frac1{2\Sigma}.
$$

Exact partial fractions give

$$
h=2\kappa\left[
\frac{P^2-\frac12P^{0s}}{k^2}
-\frac{P^2}{k^2-m_2^2}
+\frac{\frac12P^{0s}}{k^2-m_0^2}
\right]T.
$$

After factoring the common positive source normalization, the isolated scalar
residue is positive and the isolated massive-spin-2 residue is negative. The
latter is therefore ghostlike at the frozen linearized flat-space pole. The
mass-squared signs independently give

```text
scalar non-tachyonic:         Sigma < 0
massive spin-2 non-tachyonic: beta > 0
```

These are convention-specific linearized statements. A residue sign is not an
arbitrary-background or nonlinear-stability theorem.

## Coincident-mass audit

The review explicitly substituted $2\alpha+\beta=0$ with $\beta\ne0$. Then

$$
\Sigma=-\frac\beta2,
\qquad
m_0^2=m_2^2=\frac1\beta.
$$

The massive response becomes

$$
2\kappa\frac{-P^2+\frac12P^{0s}}{k^2-m^2}T.
$$

There is no $(k^2-m^2)^{-2}$ term. The Barnes–Rivers projectors remain
orthogonal idempotents, $P^2P^{0s}=0$, so the operator is channel-diagonalizable
despite the coincident eigenvalue. Channel-wise residue signs are therefore
defined here. This is a coincident pole location, not an unresolved Jordan or
higher-order pole.

The conservative rule remains binding for any future non-diagonalizable or
genuinely repeated pole:

```text
DEGENERATE — RESIDUE SIGN NOT ASSIGNED
```

## Independent static-kernel review

At $k^0=0$, the review used the same saturated response for both components and

$$
\int\frac{d^3q}{(2\pi)^3}
\frac{e^{i\boldsymbol q\cdot\boldsymbol r}}
{\boldsymbol q^2+m^2}
=\frac{e^{-mr}}{4\pi r}
$$

when $m^2>0$. The massless inverse is $1/(4\pi r)$. Combining

$$
P^2_{00,00}=\frac23,
\qquad
P^{0s}_{00,00}=\frac13
$$

reproduces the relative point-source coefficients

$$
1,\qquad \frac13,\qquad-\frac43.
$$

Thus, with absent modes deleted,

$$
h_{00}(r)=-\frac{2GM}{c^2r}
\left(1+\frac13e^{-m_0r}-\frac43e^{-m_2r}\right)
$$

in the non-tachyonic sector.

For the stationary current component, $k^0=0$ gives
$\theta_{0i}=0$ and hence

$$
P^{0s}_{0i,\rho\sigma}T^{\rho\sigma}=0.
$$

For a conserved source, the spin-2 projector returns the transverse covariant
$T_{0i}$. Accounting for $k^2=-\boldsymbol q^2$ independently reproduces

$$
h_{0i}(\boldsymbol x)=-2\kappa\int d^3x'
\left[K_0(r)-K_{m_2^2}(r)\right]T_{0i}(\boldsymbol x').
$$

The scalar-current decoupling and overall current-kernel sign therefore pass.

## Parameter-stratum review

- `beta != 0, Sigma != 0`: generic three-sector formula.
- `beta = 0`: no massive spin-2 pole; $1/\beta$ is not substituted.
- `Sigma = 0`: no massive scalar pole; $-1/(2\Sigma)$ is not substituted.
- `alpha = beta = 0`: Einstein comparison baseline.
- `2 alpha + beta = 0, beta != 0`: coincident but projector-resolved masses.
- `beta < 0` or `Sigma > 0`: the corresponding pole is tachyonic under the
  frozen conventions and its static kernel is oscillatory, not a stable Yukawa
  screen.
- No finite $\alpha,\beta$ stratum creates an extra massless pole. A zero extra
  mass would require an unbounded-coupling limit outside the finite symbolic
  parameter surface reviewed here.

## Sixteen review gates

1. Execution custody and current authority: PASS.
2. Exact Minkowski background and tadpole: PASS.
3. Independent $R^2$ variation: PASS.
4. Independent Ricci-squared variation: PASS.
5. Linearized equation and Bianchi identity: PASS.
6. Source sign, coefficient, and conservation: PASS.
7. Complete gauge-fixed projector inverse: PASS.
8. Conserved-source saturation and partial fractions: PASS.
9. Isolated scalar and spin-2 residues: PASS.
10. Stationary 00 kernel and $1,1/3,-4/3$ factors: PASS.
11. Stationary 0i kernel and explicit scalar decoupling: PASS.
12. Fourier, $4\pi r$, source-index, and overall signs: PASS.
13. Generic, absent-mode, tachyonic, and infinite-mass strata: PASS.
14. Coincident-mass diagonalizability and simple-pole test: PASS.
15. Ten controls share the production path; literature is post-derivation: PASS.
16. Comparison-only claim boundary and hard stop: PASS.

## Oracle consistency after reproduction

After the independent algebra was complete, the review compared it with the
same primary sources. Hindawi, Ovrut, and Waldram support the massless,
massive-scalar, and massive-spin-2 decomposition and the flat-space ghostlike
spin-2 result. Stabile supports the two finite-range scales and Gauss–Bonnet
removal of a third independent local-bulk scale. Berry and Gair support the
extra Ricci-scalar mode in analytic metric $f(R)$. These checks agree after
convention translation and did not supply the reviewed equations.

## Accepted bounded claim

Under the frozen four-dimensional local metric, flat-background,
conserved-external-source, normalization, gauge, and Green-function conventions,
the supplied quadratic comparison has:

- the Einstein massless response;
- a trace-coupled scalar pole at $m_0^2=-1/[2(3\alpha+\beta)]$ when present,
  with positive isolated/projector-resolved saturated residue;
- an additional spin-2 pole at $m_2^2=1/\beta$ when present, with negative
  isolated/projector-resolved saturated residue;
- a scalar correction in stationary 00 but no scalar contribution in stationary
  conserved 0i;
- an additional spin-2 correction in both stationary channels.

This is the maximum accepted claim.

## Not authorized by acceptance

- adoption of this or any gravitational action;
- selection of $\alpha$ or $\beta$;
- a native gravitational principle or postulate;
- empirical fitting or modified-gravity constraints;
- nonlinear or arbitrary-background stability claims;
- orbital precession, frame dragging, Lense–Thirring, or LARES-2;
- a ToE matter action, stress tensor, or master-action mutation;
- V2 matrix population or automated theory selection.

## Current posture and next authority

```text
comparison result:             ACCEPTED — 16 / 16 GATES
comparison execution:          COMPLETED ONCE
comparison action:             SUPPLIED COMPARISON ONLY
native gravitational action:  NOT SELECTED
native gravitational principle:NOT IDENTIFIED
frame dragging:                NOT RESUMED
selected next authority:
select_post_quadratic_gravity_comparison_scientific_response_v0
```

The selected next target may rank the scientific implications and choose a
bounded research response. It may not adopt an action or authorize a postulate
without fresh explicit authority.

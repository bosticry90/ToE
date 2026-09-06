# Shared Linearized Quadratic-Gravity Source and Spectrum Comparison v0

Date: 2026-07-18  
Target: `execute_shared_linearized_quadratic_gravity_source_and_spectrum_comparison_v0`  
Result: `COMPLETE_BOUNDED_COMPARISON_PENDING_INDEPENDENT_REVIEW`  
Selected next target: `review_shared_linearized_quadratic_gravity_source_and_spectrum_comparison_v0_result`

## Claim boundary

This is one execution of a supplied standard-physics comparison instrument:

$$
S_g^{\rm cmp}=A_{\rm EH}\int d^4x\sqrt{-g}
\left(R+\alpha R^2+\beta R_{\mu\nu}R^{\mu\nu}\right),
\qquad A_{\rm EH}=\frac{c^3}{16\pi G}.
$$

It is not a ToE action, native postulate, candidate master action, matter-sector
completion, or theory-selection result. The source is the frozen external,
symmetric, conserved comparison source. The calculation stops before orbital
observables, fitting, or frame dragging.

```text
authorized execution consumed:   1 / 1
derivation stages:               10 / 10 COMPLETED
mode rows:                        3 / 3 DERIVED
prepared outputs:                11 / 11 PRODUCED
shared-path controls:            10 / 10 PASSED
ToE gravitational action:        NOT SELECTED
native gravitational principle:  NOT IDENTIFIED
```

## Frozen notation

The signature is `(+,-,-,-)`, $x^0=ct$, and

$$
R^\rho{}_{\sigma\mu\nu}
=\partial_\mu\Gamma^\rho{}_{\nu\sigma}
-\partial_\nu\Gamma^\rho{}_{\mu\sigma}
+\Gamma^\rho{}_{\mu\lambda}\Gamma^\lambda{}_{\nu\sigma}
-\Gamma^\rho{}_{\nu\lambda}\Gamma^\lambda{}_{\mu\sigma}.
$$

The Fourier pair uses $e^{-ik\cdot x}=e^{i(\boldsymbol{k}\cdot
\boldsymbol{x}-\omega t)}$, so

$$
\partial_\mu\mapsto-ik_\mu,
\qquad \Box\mapsto-k^2,
\qquad k^2=(\omega/c)^2-|\boldsymbol{k}|^2.
$$

Define

$$
\Sigma:=3\alpha+\beta,
\qquad \kappa:=\frac{8\pi G}{c^4}.
$$

All pole signs and mass conditions below are tied to these conventions. They
must be translated before comparison with a source using another signature,
curvature sign, or action normalization.

## D1 — Four-dimensional local-bulk reduction: completed

The unreduced quadratic part may be written

$$
\alpha_u R^2+\beta_u R_{\mu\nu}R^{\mu\nu}
+\gamma R_{\mu\nu\rho\sigma}R^{\mu\nu\rho\sigma}.
$$

Using

$$
E_4=R_{\mu\nu\rho\sigma}R^{\mu\nu\rho\sigma}
-4R_{\mu\nu}R^{\mu\nu}+R^2,
$$

the compact-support four-dimensional local-bulk variation is represented by

$$
\alpha=\alpha_u-\gamma,
\qquad \beta=\beta_u+4\gamma.
$$

No boundary-charge, global-topology, other-dimensional, or nonlocal
equivalence is claimed.

## D2–D3 — Exact variation and Euler tensor: completed

After inverse-metric variation and the frozen compact-support treatment, the
exact comparison equation is

$$
E_{\mu\nu}[g;\alpha,\beta]=\kappa T_{\mu\nu},
$$

where

$$
\begin{aligned}
E_{\mu\nu}={}&G_{\mu\nu}
+2\alpha R\left(R_{\mu\nu}-\frac14g_{\mu\nu}R\right)
+2\alpha\left(g_{\mu\nu}\Box-\nabla_\mu\nabla_\nu\right)R\\
&+\beta\bigg[
2R_{\mu\rho\nu\sigma}R^{\rho\sigma}
-\nabla_\mu\nabla_\nu R+\Box R_{\mu\nu}
+\frac12g_{\mu\nu}
\left(\Box R-R_{\rho\sigma}R^{\rho\sigma}\right)
\bigg].
\end{aligned}
$$

Diffeomorphism invariance gives $\nabla^\mu E_{\mu\nu}=0$. Its trace is
particularly simple:

$$
-R+2(3\alpha+\beta)\Box R=\kappa T.
$$

The source sign is derived rather than inserted. With

$$
\delta S_g=A_{\rm EH}\int d^4x\sqrt{-g}\,
E_{\mu\nu}\delta g^{\mu\nu},
\qquad
\delta S_{\rm ext}|_\eta=-\frac1{2c}\int d^4x\,
T_{\mu\nu}\delta g^{\mu\nu},
$$

stationarity gives

$$
E_{\mu\nu}=\frac{1}{2cA_{\rm EH}}T_{\mu\nu}
=\frac{8\pi G}{c^4}T_{\mu\nu}.
$$

## D4 — Formal Minkowski background gate: passed

Set $T_{\mu\nu}=0$ and $g_{\mu\nu}=\eta_{\mu\nu}$. Then

$$
R_{\mu\nu\rho\sigma}=R_{\mu\nu}=R=0,
\qquad \nabla_\lambda R_{\mu\nu\rho\sigma}=0.
$$

Every displayed term in $E_{\mu\nu}$ vanishes for every finite symbolic
$\alpha,\beta$. There is no cosmological term and the external source is absent
from the background equation. Therefore $E_{\mu\nu}[\eta]=0$. Equivalently,
the action has no term linear in $h_{\mu\nu}$ under the frozen compact-support
variation. Propagator construction is admitted.

## D5–D6 — Linearized equation and source normalization: completed

For $g_{\mu\nu}=\eta_{\mu\nu}+h_{\mu\nu}$, retain $O(h)$ in the equation and
keep $\alpha,\beta$ exact. The result is

$$
\boxed{
(1+\beta\Box)G^L_{\mu\nu}
+(2\alpha+\beta)
(\eta_{\mu\nu}\Box-\partial_\mu\partial_\nu)R^L
=\kappa T_{\mu\nu}.
}
$$

Its divergence vanishes identically. Its trace reproduces

$$
-R^L+2\Sigma\Box R^L=\kappa T.
$$

In de Donder gauge,

$$
\partial^\mu\bar h_{\mu\nu}=0,
\qquad
G^L_{\mu\nu}=-\frac12\Box\bar h_{\mu\nu},
$$

but this Einstein-form identity is not used to delete the higher-derivative
trace or spin-2 factors.

## D7–D8 — Quadratic operator and complete gauge-fixed inverse: completed

Let $P^2,P^1,P^{0s},P^{0w},P^{0sw},P^{0ws}$ be the standard complete
Barnes–Rivers basis built from

$$
\theta_{\mu\nu}=\eta_{\mu\nu}-\frac{k_\mu k_\nu}{k^2},
\qquad
\omega_{\mu\nu}=\frac{k_\mu k_\nu}{k^2}.
$$

Write the quadratic action as

$$
S^{(2)}_g+S_{\rm gf}=\frac{A_{\rm EH}}2
\int\frac{d^4k}{(2\pi)^4}h(-k)\,\mathcal O(k)\,h(k)
$$

with the frozen de Donder gauge fixing and $\xi=1$. Direct expansion gives

$$
\begin{aligned}
\mathcal O={}&
-\frac12k^2(1-\beta k^2)P^2
-\frac12k^2P^1\\
&+k^2\left(\frac14+2\Sigma k^2\right)P^{0s}
-\frac14k^2P^{0w}
+\frac{\sqrt3}{4}k^2(P^{0sw}+P^{0ws}).
\end{aligned}
$$

The full inverse is

$$
\begin{aligned}
\mathcal O^{-1}={}&
-\frac{2P^2}{k^2(1-\beta k^2)}-\frac{2P^1}{k^2}
+\frac{P^{0s}+\sqrt3(P^{0sw}+P^{0ws})
-(1+8\Sigma k^2)P^{0w}}
{k^2(1+2\Sigma k^2)}.
\end{aligned}
$$

Multiplication in the projector algebra gives the identity on symmetric
rank-two tensors away from its poles. In particular, the scalar-sector matrix

$$
k^2\begin{pmatrix}
\frac14+2\Sigma k^2&\frac{\sqrt3}{4}\\
\frac{\sqrt3}{4}&-\frac14
\end{pmatrix}
$$

has determinant $-\frac14k^4(1+2\Sigma k^2)$ and its displayed inverse
multiplies to the $2\times2$ identity. Thus gauge fixing has not erased the
physical scalar factor.

## D9 — Conserved-source propagator, poles, and residues: completed

Stationarity in the covariant $h_{\mu\nu}$ variable gives
$\mathcal O h=-\kappa T$. When $k_\mu T^{\mu\nu}=0$, every $P^1$, $P^{0w}$,
and mixed scalar-longitudinal term drops out. The one shared physical response is

$$
\boxed{
h_{\mu\nu}(k)=2\kappa\left[
\frac{P^2}{k^2(1-\beta k^2)}
-\frac{P^{0s}}{2k^2(1+2\Sigma k^2)}
\right]_{\mu\nu,\rho\sigma}T^{\rho\sigma}(k).
}
$$

For generic $\beta\ne0$ and $\Sigma\ne0$, define

$$
m_2^2=\frac1\beta,
\qquad
m_0^2=-\frac1{2\Sigma}.
$$

Partial fractions give

$$
h=2\kappa\left[
\frac{P^2-\frac12P^{0s}}{k^2}
-\frac{P^2}{k^2-m_2^2}
+\frac{\frac12P^{0s}}{k^2-m_0^2}
\right]T.
$$

All dynamic denominators inherit the frozen retarded continuation. The mode
table is therefore:

| sector | pole | source channel | saturated residue | non-tachyon condition |
|---|---|---|---|---|
| massless spin 2 | $k^2=0$ | conserved $P^2-\frac12P^{0s}$ combination | positive reference | massless |
| massive scalar | $k^2=m_0^2$ when $\Sigma\ne0$ | trace $T$ through $P^{0s}$ | positive relative to the frozen reference | $\Sigma<0$ |
| massive spin 2 | $k^2=m_2^2$ when $\beta\ne0$ | transverse spin-2 $P^2$ | negative: ghostlike in this local linearized comparison | $\beta>0$ |

The ghost judgment is a residue statement, not a tachyon statement. If
$\beta<0$, the massive spin-2 pole is also tachyonic; if $\Sigma>0$, the scalar
pole is tachyonic. These statements are confined to Minkowski linearization.

### Parameter partitions and degenerate cases

- $\beta=0$: the massive spin-2 pole is absent/infinite-mass; do not substitute
  $m_2^2=1/\beta$.
- $\Sigma=0$: the massive scalar pole is absent/infinite-mass; do not substitute
  $m_0^2=-1/(2\Sigma)$.
- $\alpha=\beta=0$: only the Einstein massless response remains.
- $2\alpha+\beta=0$ with $\beta\ne0$: $m_0^2=m_2^2$, but the pole is resolved
  into orthogonal $P^{0s}$ and $P^2$ channels. The residue rule therefore
  permits the two channel signs above. It is not treated as an unresolved
  non-diagonalizable pole.
- Any future genuinely repeated or non-diagonalizable pole must be labeled
  `DEGENERATE — RESIDUE SIGN NOT ASSIGNED` until separately resolved.

## D10 — One static inversion for the 00 and 0i channels: completed

For a stationary source, $k^0=0$ and $k^2=-\boldsymbol q^2$. Define

$$
K_0(r)=\frac1{4\pi r},
\qquad
K_{m^2}(r)=\int\frac{d^3q}{(2\pi)^3}
\frac{e^{i\boldsymbol q\cdot\boldsymbol r}}
{\boldsymbol q^2+m^2}
$$

with the static prescription inherited from the retarded operator and no
growing branch. For $m^2>0$,

$$
K_{m^2}(r)=\frac{e^{-\sqrt{m^2}r}}{4\pi r}.
$$

For $m^2<0$, the pole is tachyonic and the inherited Helmholtz kernel is
oscillatory rather than Yukawa; it must not be presented as a stable screened
mode. At $m^2\to+\infty$, $K_{m^2}(r)\to0$ for fixed $r>0$.

Let $T=\eta^{\mu\nu}T_{\mu\nu}$ and
$r=|\boldsymbol x-\boldsymbol x'|$. Direct components of the same saturated
operator give

$$
\boxed{
\begin{aligned}
h_{00}(\boldsymbol x)=-2\kappa\int d^3x'\bigg[&
\left(T_{00}-\frac12T\right)K_0(r)
+\frac16T K_{m_0^2}(r)\\
&-\left(T_{00}-\frac13T\right)K_{m_2^2}(r)
\bigg],
\end{aligned}}
$$

where a kernel is omitted when its mode is absent. For a pressureless point
probe, $T_{00}=Mc^2\delta^3(\boldsymbol x)$ and $T=T_{00}$, so

$$
\boxed{
h_{00}(r)=-\frac{2GM}{c^2r}
\left[1+\frac13e^{-m_0r}-\frac43e^{-m_2r}\right]
}
$$

in the non-tachyonic sector, with absent-mode terms deleted. This is a
comparison-source metric response, not an empirical potential fit.

For the covariant current component $T_{0i}$, stationarity gives
$P^{0s}_{0i,\rho\sigma}T^{\rho\sigma}=0$. Hence the scalar does not contribute,
as a derived projector contraction rather than an assumption. The shared
current response is

$$
\boxed{
h_{0i}(\boldsymbol x)=-2\kappa\int d^3x'
\left[K_0(r)-K_{m_2^2}(r)\right]T_{0i}(\boldsymbol x').
}
$$

When $\beta=0$, the massive kernel is absent and the Einstein comparison
response remains. No orbital averaging, gravitomagnetic precession, or
frame-dragging observable is computed.

## Ten shared-path controls

| control | result | shared-path finding |
|---|---|---|
| C1 Einstein baseline | PASS | $\alpha=\beta=0$ gives $2\kappa(P^2-\frac12P^{0s})T/k^2$ and the Einstein 00/0i kernels. |
| C2 scalar representative | PASS | $\beta=0$ removes the massive $P^2$ pole while retaining the scalar when $\alpha\ne0$. |
| C3 current zero | PASS | $T_{0i}=0$ makes the current-sourced $h_{0i}$ vanish. |
| C4 current sign | PASS | Linearity gives $T_{0i}\mapsto-T_{0i}\Rightarrow h_{0i}\mapsto-h_{0i}$. |
| C5 source conservation | PASS | A deliberately nonconserved source is rejected before physical saturation. |
| C6 heavy-mode limits | PASS | $\beta\to0$ and $\Sigma\to0$ are treated as nonsingular infinite-mass limits away from source support, not direct mass substitutions. |
| C7 scalar degeneracy | PASS | $\Sigma=0$ removes the scalar factor in both the operator and static kernel. |
| C8 gauge sector | PASS | Longitudinal projectors are retained in $\mathcal O^{-1}$ and vanish only after conserved-source saturation. |
| C9 dimensions/normalization | PASS | Every action term has units J s and the varied source coefficient is $8\pi G/c^4$. |
| C10 Gauss–Bonnet local bulk | PASS | Reduced and unreduced compact-support local-bulk equations agree; no boundary/global result is emitted. |

No coefficient was adjusted to make a control pass.

## Eleven produced outputs

1. Normalized action and external-source record.
2. Four-dimensional compact-support Gauss–Bonnet reduction.
3. Exact metric Euler tensor and divergence identity.
4. Linearized field equation with exact $\alpha,\beta$.
5. Complete de Donder gauge-fixed Barnes–Rivers operator and inverse.
6. Conserved-source-saturated propagator.
7. Pole, mass, residue, tachyon, and degeneracy table.
8. Stationary 00 Green function.
9. Stationary 0i Green function.
10. Ten shared-path control results.
11. Post-derivation literature comparison and hard-stop record.

## Post-derivation oracle comparison

Only after the internal derivation was complete were the results compared with
the prepared sources:

- Hindawi, Ovrut, and Waldram describe the canonical massless-gravity,
  massive-scalar, and massive-spin-2 content and the ghostlike flat-space
  spin-2 sector.
- Stabile finds two fourth-order weak-field length scales and explains why the
  Gauss–Bonnet relation removes a third independent Riemann-squared scale.
- Berry and Gair identify the extra Ricci-scalar mode in analytic metric
  $f(R)$ gravity.

The sector count, two-scale structure, point-source coefficients, and ghost
oracle agree after translating to the frozen signature, curvature, and coupling
conventions. Literature supplied no executable equation or matrix entry.

## Result and hard stop

The bounded comparison completed. Within the frozen local, four-dimensional,
metric, Minkowski, external-conserved-source domain:

- the scalar mode is trace-coupled and does not enter the stationary 0i channel;
- the extra spin-2 mode enters both 00 and 0i and has negative saturated residue;
- tachyon absence requires $\Sigma<0$ for the scalar and $\beta>0$ for the
  massive spin-2 mode under the frozen conventions;
- the 00/0i contrast therefore separates scalar response from additional
  spin-2/current response.

These are supplied-comparison findings pending independent result review. They
do not select a theory or establish empirical viability.

```text
comparison execution:          COMPLETE ONCE
result status:                 PENDING INDEPENDENT REVIEW
derivation:                    10 / 10
mode rows:                      3 / 3
outputs:                       11 / 11
controls:                      10 / 10 PASSED
comparison action:             SUPPLIED COMPARISON ONLY
native gravitational action:  NOT SELECTED
frame dragging:                NOT RESUMED
selected next authority:
review_shared_linearized_quadratic_gravity_source_and_spectrum_comparison_v0_result
```

# FN-01 Plane-Wave Mode-Closure Diagnostic (Science Phase Entry)

Date: 2026-01-17

This is an evidence-only diagnostic that evaluates each registered FN-01 candidate deformation representative `P[psi]` on a single Fourier-mode plane wave and checks whether the output stays within that same mode.

Interpretation (narrow):

- If `P(psi)` is proportional to the input plane wave `psi`, then the plane wave remains a consistent single-mode ansatz for the perturbed evolution equation `i psi_t = -1/2 Laplacian(psi) + P(psi)`.
- If `P(psi)` leaks into other Fourier modes, then a pure plane wave is not mode-closed under that candidate (consistent with failing translation/phase/source-free gates).

This file does not claim physical validity or PDE completeness.

## Configuration

- Domain: periodic square, L = 2*pi
- Grid: N = 64
- Plane-wave mode: (kx0, ky0) = (2, 1)
- Amplitude: A = 1e-4
- Baseline omega0 = (1/2) * (kx0^2 + ky0^2) = 2.5

For each candidate, compute:

- alpha := <P(psi), basis> / <psi, basis>
- leak_ratio := ||P(psi) - alpha*psi|| / ||P(psi)||

where `basis = exp(-i(kx0 X + ky0 Y))` and the inner product is the same normalized grid sum used in the test suite.

## Results (numerical)

| candidate | alpha (complex) | leak_ratio | omega_pred = omega0 + alpha | notes |
|---|---:|---:|---:|---|
| P_cubic | 3.0e-09 + 5.37e-27 i | 6.01e-16 | 2.500000003 + ~0 i | mode-closed; tiny nonlinear shift at A=1e-4 |
| P_conj | ~0 + 5.45e-18 i | 1.0 | 2.5 + ~0 i | not mode-closed; mixes k and -k |
| P_xpsi | 3.0925052683774514 + ~0 i | 0.5058710426690024 | 5.592505268377451 + ~0 i | not mode-closed; explicitly breaks translation/rotation |
| P_lap | -5.0 + ~0 i | 8.01e-14 | -2.5 + ~0 i | mode-closed; linear derivative term shifts dispersion |
| P_dxx | -4.0 + ~0 i | 6.80e-14 | -1.5 + ~0 i | mode-closed; anisotropic linear derivative term |
| P_dxx_minus_dyy | -3.0 + ~0 i | 1.04e-13 | -0.5 + ~0 i | mode-closed; anisotropic linear derivative term |
| P_constant_source | ~0 + ~0 i | 1.0 | ~2.5 + ~0 i | not mode-closed; injects k=0 forcing |

Notes:

- The tiny imaginary parts reported above are numerical noise from FFT/finite precision.
- For `P_constant_source`, the projection coefficient is near zero because the constant source is (nearly) orthogonal to the chosen nonzero mode, but the leak_ratio correctly flags that the output is not proportional to the input plane wave.

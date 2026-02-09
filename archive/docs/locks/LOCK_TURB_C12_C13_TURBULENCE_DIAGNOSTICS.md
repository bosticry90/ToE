============================================================

LOCK\_TURB\_C12\_C13\_TURBULENCE\_DIAGNOSTICS.md

============================================================

LOCK: CRFT TURB C12–C13 TURBULENCE DIAGNOSTICS (1D SPECTRUM AND COHERENT STRUCTURES)

============================================================

Status

This document locks the turbulence diagnostic utilities and the tests C12–C13 as implemented in the numerical layer. The lock applies to:

The 1D spectrum computation (real-to-complex rFFT, wavenumber construction, and spectral energy density definition).

The 1D spectrum partitioning into low/mid/high bands using (k\_low, k\_mid) thresholds.

The 1D coherent-structure detector implemented as thresholded contiguous-segment detection on a periodic 1D grid.

The specific test constructions and the exact test assertions executed and passed in C12 and C13.

This lock does not assert general turbulence correctness, completeness, or physical interpretation beyond what is explicitly computed and asserted by the referenced tests.

Files Covered by This Lock

Primary implementation:

crft/diagnostics/turbulence.py

Test driver:

crft/tests/crft\_turb\_c12\_c13.py

No other files are required to define the authoritative diagnostic behavior locked here. Supporting infrastructure may exist elsewhere in CRFT, but C12–C13 directly exercise the functions listed above.

============================================================
1D Spectrum Diagnostic (Authoritative Implementation)

Function

compute\_spectrum\_1d(field, L)

Inputs

field
A real-valued 1D array of length N representing a scalar field sampled uniformly on a periodic domain \[0, L).

L
The physical domain length.

Algorithm (as implemented)

Convert field to a NumPy array and define:
N = field.size
dx = L / N

Construct the non-negative rFFT wavenumber array:
k = 2π \* rfftfreq(N, d=dx)

Compute Fourier coefficients using a real-to-complex FFT:
F = rfft(field)

Define spectral energy density per stored rFFT mode as:
E\_k = |F|^2 / N^2

Output

A Spectrum1D container with:

k: ndarray of non-negative wavenumbers (rFFT convention)

E\_k: ndarray of spectral energy density values corresponding to k

Normalization Note (Locked)

The normalization used by the implementation is exactly:
E\_k = |F|^2 / N^2

No additional scaling by dx or by 2 is applied in this diagnostic.

============================================================
Band Energy Partition Diagnostic (Authoritative Implementation)

Function

partition\_spectrum\_1d(spectrum, k\_low, k\_mid)

Inputs

spectrum
A Spectrum1D instance with fields (k, E\_k).

k\_low
Boundary between low and mid bands.

k\_mid
Boundary between mid and high bands.

Band Definitions (as implemented)

The spectrum is partitioned using the following masks over the non-negative k array:

Low band:
0 <= k < k\_low

Mid band:
k\_low <= k < k\_mid

High band:
k >= k\_mid

Returned Values

A SpectralBands1D container with:

E\_low = sum(E\_k over the low-band mask)

E\_mid = sum(E\_k over the mid-band mask)

E\_high = sum(E\_k over the high-band mask)

E\_tot = sum(E\_k over all stored rFFT modes)

Locked Parameter Names

The partitioning function uses (k\_low, k\_mid). It does not accept or use a parameter named k\_high.

============================================================
Coherent Structure Detection in 1D (Authoritative Implementation)

Function

detect\_coherent\_structures\_1d(field, dx, threshold\_fraction=0.5)

Inputs

field
A real-valued 1D array of length N.

dx
Grid spacing in physical units.

threshold\_fraction
A user-provided scalar. Default is 0.5. The tests use threshold\_fraction = 0.5. The implementation does not enforce bounds on this value. Structures are defined by:
field >= threshold\_fraction \* max(field).

Algorithm (as implemented)

Convert field to a NumPy array and define N = field.size.

If N == 0, return an empty list.

Compute:
max\_val = max(field)

If max\_val <= 0, return an empty list.

Define:
threshold = threshold\_fraction \* max\_val
mask = (field >= threshold)

Scan i = 0..N-1 to find contiguous True segments in mask.

For each contiguous True segment from start to end (inclusive), compute:
center\_index = 0.5 \* (start + end)
width = (end - start + 1) \* dx
center\_x = center\_index \* dx

Append CoherentStructure1D(center\_index, center\_x, width) for each segment.

If a segment reaches the end of the array (i = N-1), it is closed and recorded using end = N-1.

Important Scope Note (Locked)

This detector:

Uses the raw field values (not |field|, not amplitude = |signal|).

Uses a single global threshold based on max(field).

Detects contiguous segments in the 1D index space.

Does not implement explicit periodic wrap-around merging of segments that touch both ends of the array; it only separately handles the “segment reaches last index” case by closing it at N-1.

============================================================
Locked Test Claims (What Is Actually Verified)

C12: Single-Mode Spectrum and Band Partitioning

Test

test\_C12\_turbulence\_spectrum\_single\_mode in crft/tests/crft\_turb\_c12\_c13.py

Construction

N = 256

L = 2π

x = linspace(0, L, N, endpoint=False)

k0 = 4.0

field(x) = cos(k0 \* x)

Procedure and Assertions (locked)

spectrum = compute\_spectrum\_1d(field, L)

Total spectral energy:
E\_tot = sum(E\_k)
Assertion: E\_tot is finite and E\_tot > 0

Dominant mode identification:
The test ignores the k = 0 entry when searching for the peak:
idx\_peak = 1 + argmax(E\_k\[1:]) (when k.size > 1)

k\_peak = k\[idx\_peak] (note: this is non-negative because rFFT k is non-negative)

Peak location assertion:
abs(k\_peak - k0) < 1e-6

This is an exacting structural check for the single-mode construction under the rFFT wavenumber convention.

Band partitioning:
bands = partition\_spectrum\_1d(spectrum, k\_low=2.0, k\_mid=6.0)

Mid-band dominance assertion:
bands.E\_mid > 0
bands.E\_mid > 5.0 \* max(bands.E\_low, bands.E\_high)

This locks that, for the test construction above, the spectrum implementation places the dominant peak at k0 (within 1e-6) and the band partitioning identifies the k0-containing band as dominant under the stated thresholds.

C13: Coherent Structure Detection on Two Gaussian Packets

Test

test\_C13\_turbulence\_coherent\_structures\_two\_gaussians in crft/tests/crft\_turb\_c12\_c13.py

Construction

N = 512

L = 10.0

dx = L / N

x = linspace(0, L, N, endpoint=False)

sigma = 0.3

peak1 = exp(-((x - 2.0)^2) / (2\*sigma^2))

peak2 = 0.8 \* exp(-((x - 7.0)^2) / (2\*sigma^2))

noise: Gaussian random noise with fixed seed (default\_rng(12345)), scaled by 0.01

field = peak1 + peak2 + noise

Detection call

structures = detect\_coherent\_structures\_1d(field, dx=dx, threshold\_fraction=0.5)

Assertions (locked)

Exactly two structures are detected:
len(structures) == 2

Each detected width is strictly positive and finite:
widths > 0
widths finite

Each true peak position has a detected structure center nearby:
min(|centers\_x - 2.0|) < 0.5
min(|centers\_x - 7.0|) < 0.5

This locks that the thresholded contiguous-segment detector returns exactly two structures for this seeded two-Gaussian construction, with reasonable center localization and positive finite widths.

============================================================
Evidence

The claims above are exactly those asserted by the test module:

crft/tests/crft\_turb\_c12\_c13.py

The authoritative implementations are:

crft/diagnostics/turbulence.py

Your executed result (as reported) was:

pytest -q crft/tests/crft\_turb\_c12\_c13.py
.. (2 tests passed)

============================================================
Scope Limits (Explicit Non-Claims)

This lock does not claim:

That the spectral energy density normalization is uniquely or physically correct for all intended scientific interpretations; it is locked as implemented (E\_k = |F|^2 / N^2) for structural diagnostics.

That the coherent-structure detector is optimal, noise-robust for arbitrary regimes, or equivalent to more advanced methods (wavelets, vorticity-based criteria, POD/DMD, etc.).

That these utilities validate a dynamical turbulence model; they validate only the diagnostic computations and the narrow constructions in tests C12 and C13.

============================================================
Locked Status

The following are locked at the level described above:

compute\_spectrum\_1d (rFFT-based wavenumber construction and E\_k definition)

partition\_spectrum\_1d (k\_low/k\_mid band partition definitions and energy sums)

detect\_coherent\_structures\_1d (thresholded contiguous-segment detection and returned structure fields)

The specific correctness properties asserted in tests C12 and C13

Any future modification to these functions, their signatures, their definitions of k or E\_k, their band masks, or their coherent-structure segmentation logic must explicitly invalidate or extend this lock.

============================================================




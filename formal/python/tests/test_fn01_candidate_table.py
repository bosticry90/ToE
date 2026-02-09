import numpy as np
import pytest
import ast
from pathlib import Path


def mk_grid(N=64, L=2 * np.pi):
    x = np.linspace(0, L, N, endpoint=False)
    X, Y = np.meshgrid(x, x, indexing="ij")
    k = 2 * np.pi * np.fft.fftfreq(N, d=L / N)
    KX, KY = np.meshgrid(k, k, indexing="ij")
    return X, Y, KX, KY


def lap(psi, KX, KY):
    phat = np.fft.fft2(psi)
    return np.fft.ifft2(-((KX ** 2 + KY ** 2)) * phat)


def dxx(psi, KX):
    phat = np.fft.fft2(psi)
    return np.fft.ifft2(-(KX ** 2) * phat)


def dyy(psi, KY):
    phat = np.fft.fft2(psi)
    return np.fft.ifft2(-(KY ** 2) * phat)


def rand_field(N, seed=0):
    rng = np.random.default_rng(seed)
    a = rng.normal(size=(N, N))
    b = rng.normal(size=(N, N))
    return (a + 1j * b).astype(np.complex128)


def l2_norm(z):
    z = np.asarray(z)
    return float(np.sqrt(np.sum(np.abs(z) ** 2)))


def close(a, b, rtol=1e-9, atol=1e-9):
    return np.allclose(a, b, rtol=rtol, atol=atol)


# --- candidate deformation representatives P[ψ] ---

def P_cubic(psi, **kw):
    g = kw.get("g", 0.3)
    return g * (np.abs(psi) ** 2) * psi


def P_conj(psi, **kw):
    return np.conj(psi)


def P_xpsi(psi, **kw):
    X = kw["X"]
    return X * psi


def P_lap(psi, **kw):
    return lap(psi, kw["KX"], kw["KY"])


def P_dxx(psi, **kw):
    return dxx(psi, kw["KX"])


def P_dxx_minus_dyy(psi, **kw):
    return dxx(psi, kw["KX"]) - dyy(psi, kw["KY"])


def P_constant_source(psi, **kw):
    C = kw.get("C", 0.123 - 0.456j)
    return np.zeros_like(psi) + C


def check_caus_c1_no_forcing_at0(P, *, X, Y, KX, KY):
    psi0 = np.zeros_like(X, dtype=np.complex128)
    out0 = P(psi0, X=X, Y=Y, KX=KX, KY=KY)
    return close(out0, 0.0 + 0.0j, rtol=0.0, atol=1e-12)


def check_ct01_no_linear_part_at0(P, *, X, Y, KX, KY, seed=1):
    """
    Numerical surrogate for CT-01's 'no linear part at 0' (structural evidence only):

    Define Q(ψ) := P(ψ) - P(0). Then the linear part at 0 vanishes iff
        ||Q(εψ)|| / (ε ||ψ||) -> 0 as ε -> 0.

    This passes for purely nonlinear deformations and also for constant sources
    (since Q ≡ 0), while failing for genuine linear terms.
    """
    N = X.shape[0]
    psi = rand_field(N, seed=seed)
    psi_norm = l2_norm(psi)
    assert psi_norm > 0

    psi0 = np.zeros_like(psi)
    P0 = P(psi0, X=X, Y=Y, KX=KX, KY=KY)

    eps = 1e-3
    out = P(eps * psi, X=X, Y=Y, KX=KX, KY=KY)
    q = out - P0

    ratio = l2_norm(q) / (eps * psi_norm)
    return ratio < 1e-2


def check_sym01_phase_invariance(P, *, X, Y, KX, KY, seed=2):
    N = X.shape[0]
    psi = rand_field(N, seed=seed)
    theta = 0.7

    lhs = P(np.exp(1j * theta) * psi, X=X, Y=Y, KX=KX, KY=KY)
    rhs = np.exp(1j * theta) * P(psi, X=X, Y=Y, KX=KX, KY=KY)
    return close(lhs, rhs, rtol=1e-7, atol=1e-7)


def check_sym01_translation_invariance(P, *, X, Y, KX, KY, seed=3):
    """
    Mirrors the translation invariance semantics used in
    formal/python/tests/test_sym01_symmetry_gates.py.
    """
    N = X.shape[0]
    psi = rand_field(N, seed=seed)

    shifts = [(1, 0), (0, 3), (5, 7)]
    ok = True
    for sx, sy in shifts:
        psi_s = np.roll(np.roll(psi, sx, axis=0), sy, axis=1)
        lhs = P(psi_s, X=X, Y=Y, KX=KX, KY=KY)
        rhs = np.roll(np.roll(P(psi, X=X, Y=Y, KX=KX, KY=KY), sx, axis=0), sy, axis=1)
        ok = ok and close(lhs, rhs, rtol=1e-7, atol=1e-7)

    return ok


def check_sym01_rotation_invariance(P, *, X, Y, KX, KY, seed=4):
    """
    Mirrors the rotation invariance semantics used in
    formal/python/tests/test_sym01_symmetry_gates.py.

    IMPORTANT: keep grids FIXED for invariance checks.
    """
    N = X.shape[0]
    psi = rand_field(N, seed=seed)

    ok = True
    for k in [1, 2, 3]:
        psi_r = np.rot90(psi, k=k)
        lhs = P(psi_r, X=X, Y=Y, KX=KX, KY=KY)
        rhs = np.rot90(P(psi, X=X, Y=Y, KX=KX, KY=KY), k=k)
        ok = ok and close(lhs, rhs, rtol=1e-7, atol=1e-7)

    return ok


CASES = [
    # POLICY (front door): any new FN candidate term MUST be added here with expected outcomes for:
    # - CT-01 (no linear part at 0)      [CT01-OK]
    # - CAUS C1 (P(0)=0 / no forcing)    [CAUS-C1-OK]
    # - SYM-01 global phase invariance  [SYM-PH-OK]
    # - SYM translation invariance      [SYM-TR-OK]
    # - SYM rotation invariance         [SYM-ROT-OK]
    # This prevents silent candidate sprawl.
    #
    # name, P, CT01-OK, CAUS-C1-OK, SYM-PH-OK, SYM-TR-OK, SYM-ROT-OK
    ("P_cubic", P_cubic, True, True, True, True, True),
    ("P_conj", P_conj, False, True, False, True, True),
    ("P_xpsi", P_xpsi, False, True, True, False, False),
    ("P_lap", P_lap, False, True, True, True, True),
    ("P_dxx", P_dxx, False, True, True, True, False),
    ("P_dxx_minus_dyy", P_dxx_minus_dyy, False, True, True, True, False),
    # key evidence case: no linear part at 0 can still fail source-free (CAUS C1)
    ("P_constant_source", P_constant_source, True, False, False, True, True),
]


def _table_rows():
    return list(CASES)


def _table_candidate_names():
    return {name for (name, *_rest) in _table_rows()}


def _table_candidate_fn_names():
    return {P.__name__ for (_name, P, *_rest) in _table_rows()}


def _collect_candidate_function_defs_under_formal_python_tests():
    """Collect top-level Python function definitions of the form `def P_*`.

    Policy intent: any new candidate deformation representative should be
    registered in the FN-01 candidate outcome table.

    NOTE: we intentionally scope this to `formal/python/tests` to avoid false
    positives in unrelated tooling scripts.
    """
    root = Path(__file__).resolve().parent  # .../formal/python/tests
    assert root.name == "tests"
    found = set()

    for path in root.glob("*.py"):
        src = path.read_text(encoding="utf-8")
        mod = ast.parse(src, filename=str(path))
        for node in mod.body:
            if isinstance(node, ast.FunctionDef) and node.name.startswith("P_"):
                found.add(node.name)
    return found


def test_fn01_candidate_table_is_complete_and_stable():
    # Stable identifiers: table name should match the underlying function name.
    rows = _table_rows()
    assert rows, "CASES must be non-empty"

    names = []
    for row in rows:
        assert len(row) == 7, f"Row must have 7 entries, got {len(row)}: {row!r}"
        name, P, exp_ct01, exp_caus, exp_sym_ph, exp_sym_tr, exp_sym_rot = row

        assert isinstance(name, str) and name.startswith("P_"), f"Bad candidate id: {name!r}"
        assert callable(P), f"Candidate must be callable: {name}"
        assert name == P.__name__, f"Table id {name} must equal function name {P.__name__}"

        for flag_name, flag in [
            ("CT01-OK", exp_ct01),
            ("CAUS-C1-OK", exp_caus),
            ("SYM-PH-OK", exp_sym_ph),
            ("SYM-TR-OK", exp_sym_tr),
            ("SYM-ROT-OK", exp_sym_rot),
        ]:
            assert isinstance(flag, bool), f"{name}: {flag_name} must be bool, got {flag!r}"

        names.append(name)

    assert len(names) == len(set(names)), "Duplicate candidate ids in CASES"


def test_fn01_front_door_policy_enforced():
    declared = _table_candidate_fn_names()
    discovered = _collect_candidate_function_defs_under_formal_python_tests()

    missing = sorted(discovered - declared)
    assert not missing, (
        "Front-door violation: new candidate function(s) detected under formal/python/tests "
        "but not listed in FN-01 candidate table CASES: "
        f"{missing}"
    )

    # Also enforce that CASES does not contain typos / stale names.
    stale = sorted(declared - discovered)
    assert not stale, (
        "FN-01 table contains candidate(s) that are not defined anywhere under formal/python/tests: "
        f"{stale}"
    )


@pytest.mark.parametrize("name,P,exp_ct01,exp_caus,exp_sym_ph,exp_sym_tr,exp_sym_rot", CASES)
def test_fn01_candidate_outcome_table(name, P, exp_ct01, exp_caus, exp_sym_ph, exp_sym_tr, exp_sym_rot):
    X, Y, KX, KY = mk_grid(N=64)

    got_caus = check_caus_c1_no_forcing_at0(P, X=X, Y=Y, KX=KX, KY=KY)
    got_ct01 = check_ct01_no_linear_part_at0(P, X=X, Y=Y, KX=KX, KY=KY)
    got_sym_ph = check_sym01_phase_invariance(P, X=X, Y=Y, KX=KX, KY=KY)
    got_sym_tr = check_sym01_translation_invariance(P, X=X, Y=Y, KX=KX, KY=KY)
    got_sym_rot = check_sym01_rotation_invariance(P, X=X, Y=Y, KX=KX, KY=KY)

    assert got_ct01 == exp_ct01, f"{name}: CT-01 expected {exp_ct01}, got {got_ct01}"
    assert got_caus == exp_caus, f"{name}: CAUS C1 expected {exp_caus}, got {got_caus}"
    assert got_sym_ph == exp_sym_ph, f"{name}: SYM-PH expected {exp_sym_ph}, got {got_sym_ph}"
    assert got_sym_tr == exp_sym_tr, f"{name}: SYM-TR expected {exp_sym_tr}, got {got_sym_tr}"
    assert got_sym_rot == exp_sym_rot, f"{name}: SYM-ROT expected {exp_sym_rot}, got {got_sym_rot}"

import numpy as np

from formal.python.crft import acoustic_metric as mt01


def test_mt01_acoustic_metric_1d_lock_identities():
    rng = np.random.default_rng(0)
    rho = rng.uniform(0.1, 3.0, size=32)
    u = rng.normal(0.0, 0.5, size=32)
    g_eff = 1.25

    m = mt01.compute_acoustic_metric_1d(rho=rho, u=u, g_eff=g_eff)

    # Locked definitions.
    assert np.allclose(m.c_s2, g_eff * rho)
    assert np.allclose(m.g_tt, -(m.c_s2 - u**2))
    assert np.allclose(m.g_tx, -u)
    assert np.allclose(m.g_xx, 1.0)

    # Determinant form and reduction for g_xx = 1.
    det = mt01.metric_determinant_1d(m)
    assert np.allclose(det, m.g_tt * m.g_xx - m.g_tx**2)
    assert np.allclose(det, m.g_tt - m.g_tx**2)


def test_mt01_acoustic_metric_2d_lock_identities_and_det_reduction():
    rng = np.random.default_rng(1)
    rho = rng.uniform(0.1, 3.0, size=(16, 12))
    u_x = rng.normal(0.0, 0.5, size=(16, 12))
    u_y = rng.normal(0.0, 0.5, size=(16, 12))
    g_eff = 0.9

    m = mt01.compute_acoustic_metric_2d(rho=rho, u_x=u_x, u_y=u_y, g_eff=g_eff)

    assert np.allclose(m.c_s2, g_eff * rho)
    assert np.allclose(m.g_tt, -(m.c_s2 - u_x**2 - u_y**2))
    assert np.allclose(m.g_tx, -u_x)
    assert np.allclose(m.g_ty, -u_y)
    assert np.allclose(m.g_xx, 1.0)
    assert np.allclose(m.g_yy, 1.0)

    det = mt01.metric_determinant_2d(m)
    assert np.allclose(det, m.g_tt * m.g_xx * m.g_yy - (m.g_tx**2) * m.g_yy - (m.g_ty**2) * m.g_xx)

    # Reduction for computed metrics where g_xx = g_yy = 1.
    assert np.allclose(det, m.g_tt - m.g_tx**2 - m.g_ty**2)


def test_mt01_python_front_door_matches_archive_reference():
    # Cross-check against the legacy diagnostic implementation used by prior CRFT tooling.
    # We load the archived file directly to avoid importing the full archive package,
    # which expects a separate top-level `crft` module.
    import importlib.util
    from pathlib import Path

    repo_root = Path(__file__).resolve().parents[3]
    ref_path = repo_root / "archive" / "fundamental_theory" / "crft" / "diagnostics" / "acoustic_metric.py"
    spec = importlib.util.spec_from_file_location("_archive_acoustic_metric_ref", ref_path)
    assert spec is not None and spec.loader is not None
    ref = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(ref)

    ref_compute_1d = ref.compute_acoustic_metric_1d
    ref_compute_2d = ref.compute_acoustic_metric_2d
    ref_det_1d = ref.metric_determinant_1d
    ref_det_2d = ref.metric_determinant_2d

    rng = np.random.default_rng(2)

    rho1 = rng.uniform(0.1, 3.0, size=20)
    u1 = rng.normal(0.0, 0.5, size=20)
    g_eff1 = 1.1

    m1 = mt01.compute_acoustic_metric_1d(rho=rho1, u=u1, g_eff=g_eff1)
    r1 = ref_compute_1d(rho=rho1, u=u1, g_eff=g_eff1)
    assert np.allclose(m1.g_tt, r1.g_tt)
    assert np.allclose(m1.g_tx, r1.g_tx)
    assert np.allclose(m1.g_xx, r1.g_xx)
    assert np.allclose(mt01.metric_determinant_1d(m1), ref_det_1d(r1))

    rho2 = rng.uniform(0.1, 3.0, size=(8, 9))
    u2x = rng.normal(0.0, 0.5, size=(8, 9))
    u2y = rng.normal(0.0, 0.5, size=(8, 9))
    g_eff2 = 0.7

    m2 = mt01.compute_acoustic_metric_2d(rho=rho2, u_x=u2x, u_y=u2y, g_eff=g_eff2)
    r2 = ref_compute_2d(rho=rho2, u_x=u2x, u_y=u2y, g_eff=g_eff2)
    assert np.allclose(m2.g_tt, r2.g_tt)
    assert np.allclose(m2.g_tx, r2.g_tx)
    assert np.allclose(m2.g_ty, r2.g_ty)
    assert np.allclose(m2.g_xx, r2.g_xx)
    assert np.allclose(m2.g_yy, r2.g_yy)
    assert np.allclose(mt01.metric_determinant_2d(m2), ref_det_2d(r2))

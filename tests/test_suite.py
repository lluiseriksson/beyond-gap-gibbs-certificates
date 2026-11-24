"""
Comprehensive Gate-2 verification & adversarial falsification test suite (pytest) for Paper 04.
"""
import glob
import json
import math
import os
import sys
from fractions import Fraction
import numpy as np

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)

from src.kms_gibbs import (
    X2, Y2, Z2,
    tfim_hamiltonian,
    xxz_hamiltonian,
    local_pauli_jumps,
    build_kms_davies_generator,
    compute_eigenmode_christoffel_tiers,
    compute_pauli_weight_tiers,
    exact_lindbladian_trajectory,
)
from src.superpoincare_certifier import (
    ceil_rational,
    floor_rational,
    log_rational_upper_bound_exact,
    compute_exact_ldlt_q,
    verify_ldlt_psd_exact,
    build_upper_convex_hull,
    evaluate_hull_mixing_time_float,
    evaluate_hull_trajectory_float,
    verify_mixing_certificate_exact,
)


def test_kms_detailed_balance_and_psd():
    """Verify exact KMS Hermiticity, zero steady-state mode, and positive gap on 1D TFIM & XXZ."""
    for H, jset in [
        (tfim_hamiltonian(3, J=1.0, h=0.8, g_z=0.3), [X2, Z2]),
        (xxz_hamiltonian(3, Delta_z=1.5, h_stag=0.4, h_x=0.25), [X2, Y2]),
    ]:
        gen = build_kms_davies_generator(H, beta=1.2, jumps=local_pauli_jumps(3, jset))
        assert gen["herm_err"] < 1e-8
        assert abs(gen["evals_M"][0]) < 1e-12
        assert gen["evals_M"][1] > 0.05


def test_quantum_christoffel_superpoincare_soundness():
    """Verify Theorem 2.1: E(X_rho, X_rho) >= max_k lambda_k (chi2 - (bar_Lambda_k - 1)) on random pure states."""
    rng = np.random.default_rng(2026)
    H = tfim_hamiltonian(3, J=1.0, h=0.6, g_z=0.2)
    gen = build_kms_davies_generator(H, beta=1.5, jumps=local_pauli_jumps(3, [X2, Z2]))
    eig_tiers = compute_eigenmode_christoffel_tiers(gen)
    pauli_tiers = compute_pauli_weight_tiers(3, gen)
    d = gen["d"]
    p = gen["p"]
    M = gen["M_kms"]
    pm14 = p ** (-0.25)
    S_inv = np.outer(pm14, pm14)

    for _ in range(40):
        psi = rng.standard_normal(d) + 1j * rng.standard_normal(d)
        psi /= np.linalg.norm(psi)
        rho = np.outer(psi, psi.conj())
        B = (rho * S_inv).reshape(-1)
        chi2 = float(np.real(np.vdot(B, B)) - 1.0)
        E_dir = float(np.real(np.vdot(B, M @ B)))
        for t in eig_tiers:
            assert E_dir + 1e-10 >= t["lambda_r"] * (chi2 - t["C_r"])
        for t in pauli_tiers:
            assert E_dir + 1e-10 >= t["lambda_k"] * (chi2 - t["C_k"])


def test_hull_trajectory_dominates_exact_evolution():
    """Verify Theorem 2.2 & Theorem 4.1: exact chi2(t) <= y_env(t), ||rho-sigma||_1 <= sqrt(y_env(t)), D <= D2."""
    H = tfim_hamiltonian(3, J=1.0, h=0.25, g_z=0.05)
    gen = build_kms_davies_generator(H, beta=2.0, jumps=local_pauli_jumps(3, [X2, Y2]))
    tiers = compute_eigenmode_christoffel_tiers(gen)
    hull = build_upper_convex_hull([(t["lambda_r"], t["C_r"]) for t in tiers])
    d = gen["d"]
    rho0 = np.zeros((d, d), dtype=np.complex128)
    rho0[d - 1, d - 1] = 1.0
    times = [0.0, 0.2, 0.5, 1.0, 2.0, 5.0, 10.0]
    traj = exact_lindbladian_trajectory(gen, rho0, times)
    y_env = evaluate_hull_trajectory_float(hull, gen["y0_worst"], times)
    for row, ye in zip(traj, y_env):
        assert row["chi2"] <= ye * (1.0 + 1e-9) + 1e-12
        assert row["trace_norm"] <= math.sqrt(ye) + 1e-10
        assert row["rel_entropy"] <= math.log1p(ye) + 1e-10


def test_exact_rational_log_and_quantizer_guards():
    """Verify exact unquantized log upper bound and strict positive-int guards."""
    for num, den in [(1, 1), (3, 2), (5, 2), (10, 1), (1000, 3)]:
        x = Fraction(num, den)
        ub = log_rational_upper_bound_exact(x, terms=16)
        exact = math.log(num / den)
        assert float(ub) >= exact - 1e-15
        assert float(ub) - exact < 1e-10
    for bad in [-1, 0, True, False, 1.5]:
        try:
            ceil_rational(Fraction(1, 2), denom=bad)
            assert False, f"ceil_rational accepted invalid denom={bad}"
        except ValueError:
            pass
        try:
            floor_rational(Fraction(1, 2), denom=bad)
            assert False, f"floor_rational accepted invalid denom={bad}"
        except ValueError:
            pass


def test_exact_ldlt_psd_and_adversarial_rejection():
    """Verify exact-Q LDL^T accepts PSD matrices and rejects indefinite, float, and tampered witnesses."""
    A_psd = [[Fraction(4), Fraction(2)], [Fraction(2), Fraction(5)]]
    ok, L, D = compute_exact_ldlt_q(A_psd)
    assert ok
    assert verify_ldlt_psd_exact(A_psd, L, D)[0]

    # Indefinite matrix must fail factorization
    A_indef = [[Fraction(1), Fraction(3)], [Fraction(3), Fraction(1)]]
    assert not compute_exact_ldlt_q(A_indef)[0]

    # Live float64 roundoff indefinite bypass attack (det = -1e-18 < 0) MUST be rejected!
    A_flt_indef = [[1.0, 1.0, 1.0], [1.0, 2.0, 1.0 + 1e-9], [1.0, 1.0 + 1e-9, 1.0]]
    L_flt_indef = [[1.0, 0.0, 0.0], [1.0, 1.0, 0.0], [1.0, 1e-9, 1.0]]
    D_flt_indef = [1.0, 1.0, 0.0]
    assert not verify_ldlt_psd_exact(A_flt_indef, L_flt_indef, D_flt_indef)[0]

    # Tampered negative pivot D must fail verifier
    bad_D = [D[0], Fraction(-1, 100)]
    assert not verify_ldlt_psd_exact(A_psd, L, bad_D)[0]

    # Tampered non-unit diagonal L must fail verifier
    bad_L = [[Fraction(2), Fraction(0)], [L[1][0], Fraction(1)]]
    assert not verify_ldlt_psd_exact(A_psd, bad_L, D)[0]

    # Tampered non-lower-triangular L must fail verifier
    bad_tri = [[Fraction(1), Fraction(1)], [L[1][0], Fraction(1)]]
    assert not verify_ldlt_psd_exact(A_psd, bad_tri, D)[0]


def test_mixing_verifier_adversarial_falsifiers():
    """Adversarial falsification: verifier MUST reject 15 distinct classes of forged/malformed certificates."""
    import copy
    cert_dir = os.path.join(ROOT, "results", "rational_certificates")
    with open(os.path.join(cert_dir, "tfim_n2_ferro_b2p0_ldlt.cert.json")) as f:
        good = json.load(f)
    assert verify_mixing_certificate_exact(good)[0]

    # 1. Forged tighter T_sp_ub_q
    assert not verify_mixing_certificate_exact(dict(good, T_sp_ub_q="1/10", T_sp_ub_float=0.1))[0]
    # 2. Forged tighter T_gap_ub_q
    assert not verify_mixing_certificate_exact(dict(good, T_gap_ub_q="1/10", T_gap_ub_float=0.1))[0]
    # 3. NaN / Inf / bool display float bypass
    assert not verify_mixing_certificate_exact(dict(good, T_sp_ub_float=float("nan")))[0]
    assert not verify_mixing_certificate_exact(dict(good, T_sp_ub_float=float("inf")))[0]
    assert not verify_mixing_certificate_exact(dict(good, T_sp_ub_float=True))[0]
    # 4. Tampered display float alone & tampered speedup_float (including NaN)
    assert not verify_mixing_certificate_exact(dict(good, T_sp_ub_float=0.123))[0]
    assert not verify_mixing_certificate_exact(dict(good, speedup_float=999999.0))[0]
    assert not verify_mixing_certificate_exact(dict(good, speedup_float=float("nan")))[0]
    # 5. Tampered hull knot_q
    bad_tiers = copy.deepcopy(good["tiers"])
    bad_tiers[1]["knot_q"] = "1/1"
    assert not verify_mixing_certificate_exact(dict(good, tiers=bad_tiers))[0]
    # 6. Non-zero C_0 on tier 0
    bad_t0 = copy.deepcopy(good["tiers"])
    bad_t0[0]["C_q"] = "1/10"
    assert not verify_mixing_certificate_exact(dict(good, tiers=bad_t0))[0]
    # 7. Non-increasing lambda_q
    bad_lam = copy.deepcopy(good["tiers"])
    bad_lam[1]["lambda_q"] = bad_lam[0]["lambda_q"]
    assert not verify_mixing_certificate_exact(dict(good, tiers=bad_lam))[0]
    # 8. Boolean / float injection into exact rational fields (y0=True, y0=100.0)
    assert not verify_mixing_certificate_exact(dict(good, y0=True))[0]
    assert not verify_mixing_certificate_exact(dict(good, y0=100.0, eps=0.5))[0]
    # 9. Malformed / missing fields (must return False cleanly, never throw uncaught exception)
    assert not verify_mixing_certificate_exact(dict(good, tiers=[{"lambda_q": "bad"}]))[0]
    assert not verify_mixing_certificate_exact(dict(good, ldlt_bundle="not_a_dict"))[0]
    # 10. Forged unlinked 1x1 LDL^T witness attack + forged larger lambda_q (linked bundle MUST reject!)
    forged_tier = copy.deepcopy(good)
    forged_tier["tiers"][0]["lambda_q"] = "1000/1"
    forged_tier["tiers"][1]["lambda_q"] = "2000/1"
    forged_tier["tiers"][1]["knot_q"] = "20000/1000"
    assert not verify_mixing_certificate_exact(forged_tier)[0]
    # 11. Tampered LDL^T pivot inside linked ldlt_bundle
    bad_piv = copy.deepcopy(good)
    bad_piv["ldlt_bundle"]["gap_witnesses"][0]["D"][0] = "-1/100"
    assert not verify_mixing_certificate_exact(bad_piv)[0]
    # 12. Missing gap witness coverage for an active tier
    bad_cov = copy.deepcopy(good)
    bad_cov["ldlt_bundle"]["gap_witnesses"].pop()
    assert not verify_mixing_certificate_exact(bad_cov)[0]
    # 13. Missing christoffel witness coverage for an active tier
    bad_chr = copy.deepcopy(good)
    bad_chr["ldlt_bundle"]["christoffel_witnesses"].pop()
    assert not verify_mixing_certificate_exact(bad_chr)[0]
    # 14. Missing ldlt_bundle when end_to_end_ldlt flag is True
    assert not verify_mixing_certificate_exact(dict(good, ldlt_bundle=None))[0]
    # 15. Legacy unlinked ldlt_witnesses injection attack
    assert not verify_mixing_certificate_exact(dict(good, ldlt_witnesses=[{"A": [["1/1"]], "L": [["1/1"]], "D": ["1/1"]}]))[0]


def test_exported_exact_Q_certificates_replay():
    cert_dir = os.path.join(ROOT, "results", "rational_certificates")
    files = sorted(glob.glob(os.path.join(cert_dir, "*.cert.json")))
    assert len(files) >= 6, f"Expected >= 6 exact-Q certificates, found {len(files)}"
    total_ldlt = 0
    for fp in files:
        with open(fp) as f:
            cert = json.load(f)
        ok, info = verify_mixing_certificate_exact(cert)
        assert ok, f"Exact-Q replay failed on {os.path.basename(fp)}: {info}"
        assert info["T_sp_ub_q"] < info["T_gap_ub_q"]
        total_ldlt += info["n_ldlt_witnesses"]
    assert total_ldlt >= 14, f"Expected >= 14 verified linked LDL^T PSD witnesses across certs, got {total_ldlt}"
    # Verify depolarizing_n100 exact integer precision (no float64 truncation above 2^53!)
    with open(os.path.join(cert_dir, "depolarizing_n100_exact.cert.json")) as f:
        c100 = json.load(f)
    assert Fraction(c100["y0"]) == Fraction((2 ** 100) - 1, 1)
    for t in c100["tiers"]:
        k = int(Fraction(t["lambda_q"])) - 1
        exact_Ck = sum(math.comb(100, j) * (3 ** j) for j in range(k + 1)) - 1
        assert Fraction(t["C_q"]) == Fraction(exact_Ck, 1), f"Float truncation on n=100 tier k={k}!"


def test_two_tier_sharpness_asymptotics():
    """Verify Theorem 2.2(c): 2-tier semigroup satisfies t_exact <= T_SP <= 2*t_exact + O(1) and strong speedup."""
    with open(os.path.join(ROOT, "results", "experiment4_sharpness_and_two_stage.json")) as f:
        d4 = json.load(f)
    last = d4["sweep"][-1]
    assert last["t_exact"] <= last["T_sp"] + 1e-12
    assert last["ratio_sp_to_exact"] < 1.20
    assert last["speedup_over_gap"] > 2.9

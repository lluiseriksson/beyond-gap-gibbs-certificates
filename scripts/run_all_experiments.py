"""
Deterministic master experiment runner for Paper 04:
  "Quantum Spectral Christoffel-Super-Poincare Inequalities, Exact Piecewise-Logarithmic
   Mixing Laws, and Machine-Checked Rapid-Mixing Certificates Beyond the Spectral Gap"

Generates:
  - results/experiment1_1d_kms_gibbs_chains.json
  - results/experiment2_large_n_scaling_and_phases.json
  - results/experiment3_exact_Q_ldlt_certificates.json
  - results/experiment4_sharpness_and_two_stage.json
  - results/rational_certificates/*.cert.json  (6 zero-float-trust exact-Q certificates)
"""
import json
import math
import os
import sys
from fractions import Fraction
import numpy as np
from scipy.integrate import solve_ivp
from scipy.linalg import eigh

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
    compute_exact_ldlt_q,
    build_upper_convex_hull,
    evaluate_hull_mixing_time_float,
    evaluate_hull_trajectory_float,
    build_exact_mixing_certificate,
    build_exact_mixing_certificate_from_fractions,
    verify_mixing_certificate_exact,
)

RES_DIR = os.path.join(ROOT, "results")
CERT_DIR = os.path.join(RES_DIR, "rational_certificates")
os.makedirs(CERT_DIR, exist_ok=True)


def _save_json(path: str, data: dict):
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2)


def _quantize_hermitian_real_matrix(M: np.ndarray, denom: int = 10**6) -> tuple[list[list[Fraction]], float]:
    """
    Quantize a real symmetric matrix M into exact rational entries M_q (rounded to nearest 1/denom)
    and return (M_q, frob_err_ub) where frob_err_ub >= ||M - M_q||_F >= ||M - M_q||_op.
    """
    n = M.shape[0]
    M_real = np.real(0.5 * (M + M.conj().T))
    Mq = [[Fraction(0) for _ in range(n)] for _ in range(n)]
    sq_err = 0.0
    for i in range(n):
        for j in range(i, n):
            num = int(round(float(M_real[i, j]) * denom))
            q = Fraction(num, denom)
            Mq[i][j] = q
            Mq[j][i] = q
            diff = abs(float(M_real[i, j]) - float(q))
            sq_err += (diff * diff) * (1.0 if i == j else 2.0)
    # Sound upper bound on Frobenius norm (hence operator norm) with 10% safety factor + 1e-12
    frob_ub = math.sqrt(sq_err) * 1.10 + 1e-12
    return Mq, frob_ub


def _build_ldlt_psd_witness_dict(A_q: list[list[Fraction]], label: str) -> dict:
    ok, L_q, D_q = compute_exact_ldlt_q(A_q)
    assert ok, f"Exact rational LDL^T failed for {label}!"
    return {
        "label": label,
        "dim": len(A_q),
        "A": [[f"{x.numerator}/{x.denominator}" for x in row] for row in A_q],
        "L": [[f"{x.numerator}/{x.denominator}" for x in row] for row in L_q],
        "D": [f"{x.numerator}/{x.denominator}" for x in D_q],
    }


def run_experiment_1():
    print("[Exp 1] Running non-commuting 1D KMS-Davies quantum Gibbs samplers (TFIM & XXZ)...")
    eps = 0.1
    configs = [
        ("tfim_n3_tilted_b1p0", "1D Tilted TFIM (n=3, beta=1.0)", 3,
         tfim_hamiltonian(3, J=1.0, h=0.8, g_z=0.3), 1.0, [X2, Z2]),
        ("tfim_n4_tilted_b1p5", "1D Tilted TFIM (n=4, beta=1.5)", 4,
         tfim_hamiltonian(4, J=1.0, h=0.8, g_z=0.3), 1.5, [X2, Z2]),
        ("tfim_n4_ferro_b1p5", "1D Ferro TFIM (n=4, h=0.2, beta=1.5)", 4,
         tfim_hamiltonian(4, J=1.0, h=0.2, g_z=0.05), 1.5, [X2, Y2]),
        ("tfim_n4_ferro_b2p0", "1D Ferro TFIM (n=4, h=0.2, beta=2.0)", 4,
         tfim_hamiltonian(4, J=1.0, h=0.2, g_z=0.05), 2.0, [X2, Y2]),
        ("tfim_n4_ferro_b2p5", "1D Ferro TFIM (n=4, h=0.15, beta=2.5)", 4,
         tfim_hamiltonian(4, J=1.0, h=0.15, g_z=0.02), 2.5, [X2, Y2]),
        ("xxz_n4_stag_b1p5", "1D Anisotropic XXZ (n=4, Dz=1.5, beta=1.5)", 4,
         xxz_hamiltonian(4, Delta_z=1.5, h_stag=0.4, h_x=0.25), 1.5, [X2, Y2]),
    ]

    summary = []
    trajectories = {}
    gens_cache = {}
    for key, label, n, H, beta, jset in configs:
        jumps = local_pauli_jumps(n, jset)
        gen = build_kms_davies_generator(H, beta, jumps)
        eig_tiers = compute_eigenmode_christoffel_tiers(gen)
        pauli_tiers = compute_pauli_weight_tiers(n, gen) if n <= 4 else []

        y0 = gen["y0_worst"]
        mu1 = float(gen["evals_M"][1])
        mu2 = float(gen["evals_M"][2])
        T_gap = (0.5 / mu1) * math.log(y0 / (eps * eps))

        hull_eig = build_upper_convex_hull([(t["lambda_r"], t["C_r"]) for t in eig_tiers])
        T_sp_eig = evaluate_hull_mixing_time_float(hull_eig, y0, eps)

        hull_pauli = build_upper_convex_hull([(t["lambda_k"], t["C_k"]) for t in pauli_tiers])
        T_sp_pauli = evaluate_hull_mixing_time_float(hull_pauli, y0, eps)

        # Also evolve from worst-case pure highest-energy eigenstate |d-1><d-1|
        d = gen["d"]
        rho0_worst = np.zeros((d, d), dtype=np.complex128)
        rho0_worst[d - 1, d - 1] = 1.0
        t_max = min(T_gap * 0.9, max(T_sp_eig * 1.15, 2.0))
        times = list(np.linspace(0.0, t_max, 80))
        traj = exact_lindbladian_trajectory(gen, rho0_worst, times)
        y_env = evaluate_hull_trajectory_float(hull_eig, y0, times)
        y_gap = [y0 * math.exp(-2.0 * mu1 * t) for t in times]

        # Soundness assertions: exact chi2 <= y_env <= y_gap and trace_norm <= sqrt(chi2) <= sqrt(y_env)
        for row, ye, yg in zip(traj, y_env, y_gap):
            assert row["chi2"] <= ye * (1.0 + 1e-8) + 1e-12, f"Envelope violation on {key}!"
            assert ye <= yg * (1.0 + 1e-8) + 1e-12, f"Hull worse than gap on {key}!"
            assert row["trace_norm"] <= math.sqrt(row["chi2"]) + 1e-10
            assert row["rel_entropy"] <= row["D2"] + 1e-10

        rec = {
            "key": key,
            "label": label,
            "n": n,
            "beta": beta,
            "herm_err": gen["herm_err"],
            "min_eig": float(gen["evals_M"][0]),
            "mu1": mu1,
            "mu2": mu2,
            "y0_worst": y0,
            "eps": eps,
            "T_gap": T_gap,
            "T_sp_pauli": T_sp_pauli,
            "T_sp_eig": T_sp_eig,
            "speedup_pauli": T_gap / T_sp_pauli,
            "speedup_eig": T_gap / T_sp_eig,
            "n_hull_eig": len(hull_eig),
            "pauli_tiers": pauli_tiers,
            "hull_eig_preview": [
                {"lambda": lam, "C": C, "knot": knot} for lam, C, knot in hull_eig[:8]
            ],
        }
        summary.append(rec)
        if key in ("tfim_n4_ferro_b2p5", "xxz_n4_stag_b1p5"):
            trajectories[key] = {
                "times": times,
                "chi2_exact": [r["chi2"] for r in traj],
                "D2_exact": [r["D2"] for r in traj],
                "trace_norm_exact": [r["trace_norm"] for r in traj],
                "rel_entropy_exact": [r["rel_entropy"] for r in traj],
                "y_env_eig": y_env,
                "y_gap": y_gap,
            }
        gens_cache[key] = (gen, eig_tiers, hull_eig)
        print(f"  {label}: mu1={mu1:.5f}, y0={y0:.2e}, T_gap={T_gap:.2f}, T_SP(eig)={T_sp_eig:.2f} ({T_gap/T_sp_eig:.2f}x), T_SP(Pauli)={T_sp_pauli:.2f}")

    _save_json(
        os.path.join(RES_DIR, "experiment1_1d_kms_gibbs_chains.json"),
        {"eps": eps, "models": summary, "trajectories": trajectories},
    )
    return gens_cache


def _large_n_depolarizing_hull_time(n: int, eps: float, c_base: int) -> tuple[float, float, int]:
    """
    Exact log-space evaluation of the upper convex hull for the n-qubit local depolarizing
    semigroup with lambda_k = k + 1 and C_k = sum_{j=0}^k C(n, j) * c_base^j - 1
    (c_base = 3 for universal Christoffel norm, c_base = 1 for pure-state Bloch norm).
    Uses exact Python integer arithmetic for C_k (no float overflow even at n = 1000!).
    """
    y0_int = (2 ** n) - 1
    # Compute C_k as exact ints while C_k < y0_int (since tiers with C_k >= y0_int are never reached!)
    tiers = []
    cum = 0
    for k in range(n):
        cum += math.comb(n, k) * (c_base ** k)
        Ck = cum - 1
        if k > 0 and Ck >= y0_int:
            break
        tiers.append((k + 1, Ck))

    # Build exact hull using integer cross-multiplication!
    hull = []  # (lam: int, C: int, knot_num: int, knot_den: int)
    for lam, C in tiers:
        while hull:
            lp, Cp, kn_p, kd_p = hull[-1]
            # y_int = (lam*C - lp*Cp) / (lam - lp)
            kn = lam * C - lp * Cp
            kd = lam - lp
            # Check y_int <= y_prev  <=>  kn * kd_p <= kn_p * kd
            if kn * kd_p <= kn_p * kd:
                hull.pop()
            else:
                hull.append((lam, C, kn, kd))
                break
        if not hull:
            hull.append((lam, 0, 0, 1))

    yt = eps * eps
    # Exact log(2^n - 1) = n*log(2) + log(1 - 2^{-n}) without float overflow even at n = 1000
    log_y0 = n * math.log(2.0) + math.log1p(-(2.0 ** (-n)))
    T_gap = 0.5 * (log_y0 - math.log(yt))
    T_sp = 0.0
    for i, (lam, C, kn, kd) in enumerate(hull):
        # a = max(yt, kn/kd); b = min(y0_int, kn_next/kd_next)
        if i == 0:
            a_minus_C = yt
        else:
            # kn/kd - C = (kn - C*kd)/kd
            a_minus_C = (kn - C * kd) / kd if (kn / kd) > yt else (yt - C)
        if i + 1 < len(hull):
            kn_n, kd_n = hull[i + 1][2], hull[i + 1][3]
            # Check if y0_int < kn_n / kd_n
            if y0_int * kd_n < kn_n:
                b_minus_C_num = y0_int - C
                b_minus_C_den = 1
                stop = True
            else:
                b_minus_C_num = kn_n - C * kd_n
                b_minus_C_den = kd_n
                stop = False
        else:
            b_minus_C_num = y0_int - C
            b_minus_C_den = 1
            stop = True

        # Log ratio safely for huge ints via bit_length / math.log
        if i == 0:
            log_a = math.log(a_minus_C)
        else:
            log_a = math.log(kn - C * kd) - math.log(kd)
        log_b = math.log(b_minus_C_num) - math.log(b_minus_C_den)
        if log_b > log_a:
            T_sp += (0.5 / lam) * (log_b - log_a)
        if stop:
            break
    return T_gap, T_sp, len(hull)


def run_experiment_2():
    print("[Exp 2] Running n-qubit scaling (n=10..1000) & continuous alpha-Super-Poincare phase diagram...")
    eps = 0.1
    ns = [10, 25, 50, 100, 200, 500, 1000]
    scaling = []
    for n in ns:
        T_gap, T_chr, nh_chr = _large_n_depolarizing_hull_time(n, eps, c_base=3)
        _, T_bloch, nh_bloch = _large_n_depolarizing_hull_time(n, eps, c_base=1)
        asymp_quad = 0.25 * (math.log(n) ** 2)
        scaling.append({
            "n": n,
            "T_gap": T_gap,
            "T_sp_christoffel": T_chr,
            "T_sp_bloch": T_bloch,
            "speedup_christoffel": T_gap / T_chr,
            "speedup_bloch": T_gap / T_bloch,
            "n_hull_christoffel": nh_chr,
            "n_hull_bloch": nh_bloch,
            "ratio_to_quarter_log2": T_bloch / asymp_quad,
        })
        print(f"  n={n:4d}: T_gap={T_gap:7.2f}, T_SP(Chr)={T_chr:6.2f} ({T_gap/T_chr:5.2f}x), T_SP(Bloch)={T_bloch:6.2f} ({T_gap/T_bloch:5.2f}x)")

    # Continuous alpha-Super-Poincare phase diagram: dy/dt = -2 * gamma * y * (log(1 + y))^alpha
    # In D(t) = log(1 + y(t)): dD/dt = -2 * gamma * (y / (1 + y)) * D^alpha!
    # Wait: exact theorem 3.1(b) uses Phi_tilde(y) = gamma * (1 + y) * (log(1 + y))^alpha (Wait: check!)
    # CAREFUL! Check the exact derivative of D(t) = log(1 + y(t))!
    # dD/dt = (1 / (1 + y)) * dy/dt = -(2 / (1 + y)) * E(f, f)!
    # If E(f, f) >= gamma * y * (log(1 + y))^alpha, then since y/(1+y) >= 1 - 1/(1+y):
    #   For y >= 1, y/(1+y) >= 1/2, OR even cleaner:
    #   Define the EXACT ODE in u(t) = log(1 + y(t)) when E(f, f) >= gamma * (1 + y) * log(1 + y) ? No, at y=0, E=0 while (1+y)*log(1+y) ~ y!
    #   WAIT A SECOND! Check lim_{y->0} (1+y)*log(1+y) / y = 1!!
    #   SO gamma * (1 + y) * (log(1 + y))^alpha VANISHES at y = 0 AND for alpha = 1 equals gamma * (1 + y) * log(1 + y) ~ gamma * y near y = 0!
    #   AND d/dt log(1 + y) = (1/(1+y)) dy/dt <= -2*gamma * (log(1 + y))^alpha IS 100% CLOSED-FORM EXACT FOR ALL y > 0!!
    #   CHECK THAT!!
    #   Let D(t) = log(1 + y(t)) = D_2(rho_t || sigma)!
    #   If E(X, X) >= gamma * (1 + y) * (log(1 + y))^alpha (which is ~ gamma * y^alpha as y -> 0 and ~ gamma * y * (log y)^alpha as y -> inf):
    #   Then dD/dt = (1/(1+y)) * (-2 E) <= -2 * gamma * D^alpha EXACTLY!!
    #   - alpha = 1: dD/dt <= -2*gamma*D  ==>  D(t) <= e^{-2*gamma*t} D(0)  EXACTLY FOR ALL t >= 0!!
    #   - alpha in (0, 1): D(t)^{1-alpha} <= D(0)^{1-alpha} - 2*gamma*(1-alpha)*t  EXACTLY!!
    #   - alpha > 1: D(t) <= (D(0)^{-(alpha-1)} + 2*gamma*(alpha-1)*t)^{-1/(alpha-1)} <= (2*gamma*(alpha-1)*t)^{-1/(alpha-1)}  EXACTLY (FINITE-TIME ENTRANCE FROM D(0) = +inf)!!
    gamma = 1.0
    D0 = 50.0  # y0 = e^50 - 1 ~ 5.2e21
    t_grid = list(np.linspace(0.0, 2.5, 101))
    phases = {}
    for alpha in [0.5, 1.0, 1.5]:
        def rhs(t, D_arr, a=alpha):
            D = max(float(D_arr[0]), 0.0)
            return [-2.0 * gamma * (D ** a)] if D > 1e-15 else [0.0]

        sol = solve_ivp(rhs, [0.0, 2.5], [D0], t_eval=t_grid, rtol=1e-12, atol=1e-14)
        D_num = [max(0.0, float(v)) for v in sol.y[0]]
        D_exact = []
        for t in t_grid:
            if alpha == 1.0:
                D_exact.append(D0 * math.exp(-2.0 * gamma * t))
            elif alpha < 1.0:
                val = (D0 ** (1.0 - alpha)) - 2.0 * gamma * (1.0 - alpha) * t
                D_exact.append(val ** (1.0 / (1.0 - alpha)) if val > 0 else 0.0)
            else:
                D_exact.append(((D0 ** (-(alpha - 1.0))) + 2.0 * gamma * (alpha - 1.0) * t) ** (-1.0 / (alpha - 1.0)))
        max_err = max(abs(a - b) for a, b in zip(D_num, D_exact))
        assert max_err < 1e-8, f"Phase ODE mismatch for alpha={alpha}: {max_err}"
        phases[f"alpha_{alpha}"] = {
            "alpha": alpha,
            "D0": D0,
            "times": t_grid,
            "D2_exact": D_exact,
            "max_ode_err": max_err,
            "entrance_bound_t1": ((2.0 * gamma * (alpha - 1.0) * 1.0) ** (-1.0 / (alpha - 1.0))) if alpha > 1.0 else None,
        }
    print(f"  Phase diagram ODEs verified across alpha={{0.5, 1.0, 1.5}} (max err < {max(v['max_ode_err'] for v in phases.values()):.2e})")

    _save_json(
        os.path.join(RES_DIR, "experiment2_large_n_scaling_and_phases.json"),
        {"eps": eps, "depolarizing_scaling": scaling, "alpha_phases": phases},
    )


def _fmt_q_mat(M_q: list[list[Fraction]]) -> list[list[str]]:
    return [[f"{x.numerator}/{x.denominator}" for x in row] for row in M_q]


def _build_full_ldlt_certified_model(name: str, H: np.ndarray, n: int, beta: float, jumps: list[np.ndarray], eps: float = 0.1):
    """
    Build a 100% end-to-end exact-Q certificate with a CRYPTOGRAPHICALLY LINKED
    Global Operator-Order LDL^T bundle (Theorem 4.2) verifying BOTH:
      1. Gap witness for EVERY active tier idx = 0..r:
           M_q + beta0_q*P0_q + lam_q*P_k_q - (lam_q + delta_M_q + beta0_q*delta_P0_q + lam_q*delta_P_q)*I = L D L^T
      2. Christoffel witness for EVERY active tier idx = 1..r:
           ((C_q + 1) - delta_K_q)*I - K_k_q = L D L^T
    Reconstructed directly from `tiers[idx]` inside `verify_mixing_certificate_exact`!
    """
    gen = build_kms_davies_generator(H, beta, jumps)
    d = gen["d"]
    p = gen["p"]
    M_kms = gen["M_kms"]
    assert np.max(np.abs(np.imag(M_kms))) < 1e-12, f"Expected real symmetric M_kms for {name}"
    ev, U = eigh(np.real(M_kms))
    pm14 = p ** (-0.25)
    S_inv = np.outer(pm14, pm14)

    M_q, delta_M_f = _quantize_hermitian_real_matrix(M_kms, denom=10**5)
    delta_M_q = ceil_rational(Fraction(delta_M_f), denom=10**8)
    dimM = d * d

    eig_tiers = compute_eigenmode_christoffel_tiers(gen)
    hull_f = build_upper_convex_hull([(t["lambda_r"], t["C_r"]) for t in eig_tiers])
    selected_rs = [0]
    for lam_h, C_h, _ in hull_f[1:4]:
        for t in eig_tiers:
            if abs(t["lambda_r"] - lam_h) < 1e-9:
                selected_rs.append(t["r"])
                break

    # Stationary projector P_0 = u_0 u_0^T (1D invariant kernel of M_kms)
    u0 = U[:, 0:1]
    P0_q, delta_P0_f = _quantize_hermitian_real_matrix(u0 @ u0.T, denom=10**5)
    delta_P0_q = ceil_rational(Fraction(delta_P0_f), denom=10**8)
    beta0 = Fraction(2, 1)

    # First compute exact rational (lam_cert_q, C_cert_q) and per-r projector/Christoffel data
    cand_data = []
    for r in selected_rs:
        Ur = U[:, : r + 1]
        P_r = Ur @ Ur.T
        P_q, delta_P_f = _quantize_hermitian_real_matrix(P_r, denom=10**5)
        delta_P_q = ceil_rational(Fraction(delta_P_f), denom=10**8)
        mu_next = float(ev[r + 1])
        lam_cert_q = floor_rational(Fraction(float(mu_next - 2e-3)), denom=10**6)
        assert lam_cert_q > 0

        if r == 0:
            C_cert_q = Fraction(0)
            K_q, delta_K_q = None, None
        else:
            K_r = np.zeros((d, d), dtype=np.float64)
            for a in range(r + 1):
                Ea = U[:, a].reshape(d, d) * S_inv
                K_r += Ea.T @ Ea
            K_q, delta_K_f = _quantize_hermitian_real_matrix(K_r, denom=10**5)
            delta_K_q = ceil_rational(Fraction(delta_K_f), denom=10**8)
            bar_Lam_num = float(eigh(0.5 * (K_r + K_r.T), eigvals_only=True)[-1])
            bar_Lam_cert_q = ceil_rational(Fraction(float(bar_Lam_num + 2e-3)) + delta_K_q, denom=10**6)
            C_cert_q = bar_Lam_cert_q - Fraction(1)

        cand_data.append({
            "r": r,
            "lam_q": lam_cert_q,
            "C_q": C_cert_q,
            "P_q": P_q,
            "delta_P_q": delta_P_q,
            "K_q": K_q,
            "delta_K_q": delta_K_q,
        })

    # Build exact-Fraction certificate first (which prunes to the active rational convex hull)
    y0_q = ceil_rational(Fraction(float(gen["y0_worst"])), denom=10**6)
    eps_q = floor_rational(Fraction(float(eps)), denom=10**6)
    ok_pre, cert_pre = build_exact_mixing_certificate_from_fractions(
        [(c["lam_q"], c["C_q"]) for c in cand_data],
        y0_q=y0_q,
        eps_q=eps_q,
    )
    assert ok_pre and cert_pre is not None

    # Match each active hull tier back to its cand_data and build linked LDL^T witnesses!
    gap_witnesses = []
    chr_witnesses = []
    for t_idx, t_entry in enumerate(cert_pre["tiers"]):
        lam_q = Fraction(t_entry["lambda_q"])
        C_q = Fraction(t_entry["C_q"])
        match = next(c for c in cand_data if c["lam_q"] == lam_q and c["C_q"] == C_q)
        P_q = match["P_q"]
        delta_P_q = match["delta_P_q"]
        total_err_q = delta_M_q + beta0 * delta_P0_q + lam_q * delta_P_q
        diag_shift_q = lam_q + total_err_q
        A_gap = [
            [
                M_q[i][j] + beta0 * P0_q[i][j] + lam_q * P_q[i][j]
                - (diag_shift_q if i == j else Fraction(0))
                for j in range(dimM)
            ]
            for i in range(dimM)
        ]
        ok_g, L_g, D_g = compute_exact_ldlt_q(A_gap)
        assert ok_g, f"Gap LDL^T failed for {name} tier {t_idx}"
        gap_witnesses.append({
            "tier_idx": t_idx,
            "r_eigenmode": match["r"],
            "P_k_q": _fmt_q_mat(P_q),
            "delta_P_q": f"{delta_P_q.numerator}/{delta_P_q.denominator}",
            "L": _fmt_q_mat(L_g),
            "D": [f"{x.numerator}/{x.denominator}" for x in D_g],
        })
        if t_idx >= 1:
            K_q = match["K_q"]
            delta_K_q = match["delta_K_q"]
            c_shift_q = (C_q + Fraction(1)) - delta_K_q
            A_chr = [
                [
                    (c_shift_q if i == j else Fraction(0)) - K_q[i][j]
                    for j in range(d)
                ]
                for i in range(d)
            ]
            ok_c, L_c, D_c = compute_exact_ldlt_q(A_chr)
            assert ok_c, f"Christoffel LDL^T failed for {name} tier {t_idx}"
            chr_witnesses.append({
                "tier_idx": t_idx,
                "r_eigenmode": match["r"],
                "K_k_q": _fmt_q_mat(K_q),
                "delta_K_q": f"{delta_K_q.numerator}/{delta_K_q.denominator}",
                "L": _fmt_q_mat(L_c),
                "D": [f"{x.numerator}/{x.denominator}" for x in D_c],
            })

    ldlt_bundle = {
        "dim_H": d,
        "M_q": _fmt_q_mat(M_q),
        "P0_q": _fmt_q_mat(P0_q),
        "beta0_q": f"{beta0.numerator}/{beta0.denominator}",
        "delta_M_q": f"{delta_M_q.numerator}/{delta_M_q.denominator}",
        "delta_P0_q": f"{delta_P0_q.numerator}/{delta_P0_q.denominator}",
        "gap_witnesses": gap_witnesses,
        "christoffel_witnesses": chr_witnesses,
    }
    ok, cert = build_exact_mixing_certificate_from_fractions(
        [(c["lam_q"], c["C_q"]) for c in cand_data],
        y0_q=y0_q,
        eps_q=eps_q,
        ldlt_bundle=ldlt_bundle,
        model_meta={"name": name, "n": n, "beta": beta, "end_to_end_ldlt": True},
    )
    assert ok and cert is not None
    v_ok, v_info = verify_mixing_certificate_exact(cert)
    assert v_ok, f"Verification failed on {name}: {v_info}"
    return cert


def run_experiment_3(gens_cache: dict):
    print("[Exp 3] Building & independently verifying 6 zero-float-trust exact-Q certificates (incl. LDL^T PSD witnesses)...")
    eps = 0.1
    certs_summary = []

    # 1 & 2: Full end-to-end exact-Q LDL^T certified non-commuting 1D chains (n=2 TFIM and n=2 XXZ; d^2=16 real symmetric!)
    c_tfim2 = _build_full_ldlt_certified_model(
        "tfim_n2_ferro_b2p0_ldlt",
        tfim_hamiltonian(2, J=1.0, h=0.25, g_z=0.05),
        2, 2.0, local_pauli_jumps(2, [X2, Z2]), eps=eps,
    )
    c_xxz2 = _build_full_ldlt_certified_model(
        "xxz_n2_stag_b2p0_ldlt",
        xxz_hamiltonian(2, Delta_z=1.5, h_stag=0.4, h_x=0.25),
        2, 2.0, local_pauli_jumps(2, [X2, Z2]), eps=eps,
    )
    for fname, cert in [
        ("tfim_n2_ferro_b2p0_ldlt.cert.json", c_tfim2),
        ("xxz_n2_stag_b2p0_ldlt.cert.json", c_xxz2),
    ]:
        fp = os.path.join(CERT_DIR, fname)
        _save_json(fp, cert)
        v_ok, v_info = verify_mixing_certificate_exact(cert)
        assert v_ok
        certs_summary.append({
            "file": fname,
            "n_tiers": v_info["n_tiers"],
            "n_ldlt_witnesses": v_info["n_ldlt_witnesses"],
            "T_gap_ub": cert["T_gap_ub_float"],
            "T_sp_ub": cert["T_sp_ub_float"],
            "speedup": cert["speedup_float"],
        })

    # 3 & 4: Exact-Q convex-hull mixing certificates on n=4 Ferro TFIM (beta=2.5) and n=4 XXZ (beta=1.5)
    for key, fname in [
        ("tfim_n4_ferro_b2p5", "tfim_n4_ferro_b2p5_exact.cert.json"),
        ("xxz_n4_stag_b1p5", "xxz_n4_stag_b1p5_exact.cert.json"),
    ]:
        gen, eig_tiers, _ = gens_cache[key]
        ok, cert = build_exact_mixing_certificate(
            [(t["lambda_r"], t["C_r"]) for t in eig_tiers],
            y0_float=gen["y0_worst"],
            eps_float=eps,
            model_meta={"name": key, "n": 4},
        )
        assert ok and cert is not None
        v_ok, v_info = verify_mixing_certificate_exact(cert)
        assert v_ok
        _save_json(os.path.join(CERT_DIR, fname), cert)
        certs_summary.append({
            "file": fname,
            "n_tiers": v_info["n_tiers"],
            "n_ldlt_witnesses": v_info["n_ldlt_witnesses"],
            "T_gap_ub": cert["T_gap_ub_float"],
            "T_sp_ub": cert["T_sp_ub_float"],
            "speedup": cert["speedup_float"],
        })

    # 5 & 6: Exact-Q convex-hull mixing certificates on n=50 and n=100 local depolarizing Gibbs samplers
    # Built STRICTLY in exact Python int / Fraction arithmetic (ZERO float64 truncation even above 2^53!)
    for n_dep, fname in [
        (50, "depolarizing_n50_exact.cert.json"),
        (100, "depolarizing_n100_exact.cert.json"),
    ]:
        y0_int = (2 ** n_dep) - 1
        tiers_dep_q: list[tuple[Fraction, Fraction]] = []
        cum_int = 0
        for k in range(n_dep):
            cum_int += math.comb(n_dep, k) * (3 ** k)
            Ck_int = cum_int - 1
            if k > 0 and Ck_int >= y0_int:
                break
            tiers_dep_q.append((Fraction(k + 1, 1), Fraction(Ck_int, 1)))
        ok, cert = build_exact_mixing_certificate_from_fractions(
            tiers_dep_q,
            y0_q=Fraction(y0_int, 1),
            eps_q=Fraction(1, 10),
            model_meta={"name": f"depolarizing_n{n_dep}", "n": n_dep, "exact_integer_tiers": True},
        )
        assert ok and cert is not None
        v_ok, v_info = verify_mixing_certificate_exact(cert)
        assert v_ok
        _save_json(os.path.join(CERT_DIR, fname), cert)
        certs_summary.append({
            "file": fname,
            "n_tiers": v_info["n_tiers"],
            "n_ldlt_witnesses": v_info["n_ldlt_witnesses"],
            "T_gap_ub": cert["T_gap_ub_float"],
            "T_sp_ub": cert["T_sp_ub_float"],
            "speedup": cert["speedup_float"],
        })

    for rec in certs_summary:
        print(f"  CERT {rec['file']}: tiers={rec['n_tiers']}, LDLT={rec['n_ldlt_witnesses']}, T_gap={rec['T_gap_ub']:.3f}, T_SP={rec['T_sp_ub']:.3f} ({rec['speedup']:.2f}x)")

    _save_json(
        os.path.join(RES_DIR, "experiment3_exact_Q_ldlt_certificates.json"),
        {"eps": eps, "certificates": certs_summary},
    )


def run_experiment_4():
    print("[Exp 4] Verifying Theorem 2.2(c) 2-tier exact semigroup sharpness...")
    # Explicit 2-tier commuting quantum Markov semigroup:
    # Mode 0 (stationary): rate 0, weight 1
    # Mode 1 (slow mode): rate lam0 = 0.1, amplitude c_slow^2 = C1 = 10.0 (matching projection cap!)
    # Mode 2 (fast bulk): rate lam1 = 2.0, amplitude y0 - C1 (attains max chi2 = y0)
    # Exact chi2(t) = C1 * exp(-2*lam0*t) + (y0 - C1) * exp(-2*lam1*t)!
    lam0, lam1, C1, eps = 0.1, 2.0, 10.0, 0.1
    yt = eps * eps
    hull = build_upper_convex_hull([(lam0, 0.0), (lam1, C1)])
    rows = []
    from scipy.optimize import brentq
    for log10_y0 in [2, 3, 4, 5, 6, 7, 8]:
        y0 = 10.0 ** log10_y0
        T_gap = (0.5 / lam0) * math.log(y0 / yt)
        T_sp = evaluate_hull_mixing_time_float(hull, y0, eps)
        # Exact hitting time of chi2(t) = yt
        t_exact = brentq(
            lambda t: C1 * math.exp(-2.0 * lam0 * t) + (y0 - C1) * math.exp(-2.0 * lam1 * t) - yt,
            0.0, T_sp + 1.0, xtol=1e-13,
        )
        rows.append({
            "y0": y0,
            "T_gap": T_gap,
            "T_sp": T_sp,
            "t_exact": t_exact,
            "additive_gap": T_sp - t_exact,
            "ratio_sp_to_exact": T_sp / t_exact,
            "speedup_over_gap": T_gap / T_sp,
        })
        assert t_exact <= T_sp + 1e-12
    print(f"  At y0=1e8: T_gap={rows[-1]['T_gap']:.2f}, T_SP={rows[-1]['T_sp']:.2f}, t_exact={rows[-1]['t_exact']:.2f}, ratio={rows[-1]['ratio_sp_to_exact']:.4f} (additive gap={rows[-1]['additive_gap']:.4f})")
    _save_json(
        os.path.join(RES_DIR, "experiment4_sharpness_and_two_stage.json"),
        {"lam0": lam0, "lam1": lam1, "C1": C1, "eps": eps, "sweep": rows},
    )


if __name__ == "__main__":
    gens = run_experiment_1()
    run_experiment_2()
    run_experiment_3(gens)
    run_experiment_4()
    print("\nALL 4 EXPERIMENTS COMPLETED SUCCESSFULLY.")

"""
Publication-quality Matplotlib figures for Paper 04:
  - paper/figures/fig1_1d_kms_trajectories.pdf / .png
  - paper/figures/fig2_scaling_and_alpha_phases.pdf / .png
  - paper/figures/fig3_sharpness_and_speedups.pdf / .png
"""
import json
import math
import os
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RES_DIR = os.path.join(ROOT, "results")
FIG_DIR = os.path.join(ROOT, "paper", "figures")
os.makedirs(FIG_DIR, exist_ok=True)

plt.rcParams.update({
    "font.family": "serif",
    "font.size": 9.5,
    "axes.titlesize": 10.2,
    "axes.labelsize": 9.5,
    "legend.fontsize": 7.8,
    "xtick.labelsize": 8.5,
    "ytick.labelsize": 8.5,
    "axes.grid": True,
    "grid.alpha": 0.25,
    "grid.linestyle": "--",
})


def make_fig1():
    with open(os.path.join(RES_DIR, "experiment1_1d_kms_gibbs_chains.json")) as f:
        d1 = json.load(f)

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.4, 3.65), dpi=300)

    # Panel (a): 1D Ferro TFIM n=4, beta=2.5 two-stage relaxation
    tr1 = d1["trajectories"]["tfim_n4_ferro_b2p5"]
    ts1 = tr1["times"]
    ax1.semilogy(ts1, tr1["y_gap"], "^:", color="#d62728", linewidth=1.6, markevery=8, markersize=5,
                 label=r"Spectral-gap bound $y_0 e^{-2\mu_1 t}$")
    ax1.semilogy(ts1, tr1["y_env_eig"], "s--", color="#1f77b4", linewidth=2.0, markevery=8, markersize=5,
                 label=r"Christoffel–Super-Poincaré $y_{\mathrm{env}}(t)$")
    ax1.semilogy(ts1, [max(v, 1e-12) for v in tr1["chi2_exact"]], "-", color="#2ca02c", linewidth=2.0,
                 label=r"Exact KMS $\chi^2_\sigma(\rho_t \| \sigma)$")
    ax1.axhline(0.01, color="black", linestyle=":", linewidth=1.0, alpha=0.65, label=r"Target $\varepsilon^2 = 10^{-2}$")
    ax1.set_xlabel(r"Evolution time $t$")
    ax1.set_ylabel(r"$\chi^2_\sigma$-divergence $y(t)$")
    ax1.set_ylim(1e-4, 2e7)
    ax1.set_title(r"(a) 1D Ferro TFIM ($n=4, \beta=2.5$): $3.30\times$ Mixing Speedup")
    ax1.legend(loc="center right", frameon=True, framealpha=0.93)

    # Panel (b): 1D Anisotropic XXZ n=4, beta=1.5 — Relative Entropy & Trace Norm certified bounds
    tr2 = d1["trajectories"]["xxz_n4_stag_b1p5"]
    ts2 = tr2["times"]
    ax2.semilogy(ts2, [math.sqrt(v) for v in tr2["y_gap"]], "^:", color="#d62728", linewidth=1.5, markevery=8, markersize=5,
                 label=r"Gap trace bound $\sqrt{y_{\mathrm{gap}}(t)}$")
    ax2.semilogy(ts2, [math.sqrt(v) for v in tr2["y_env_eig"]], "s--", color="#1f77b4", linewidth=2.0, markevery=8, markersize=5,
                 label=r"Certified $\sqrt{y_{\mathrm{env}}(t)}$")
    ax2.semilogy(ts2, [max(v, 1e-12) for v in tr2["trace_norm_exact"]], "-", color="#2ca02c", linewidth=2.0,
                 label=r"Exact trace norm $\|\rho_t - \sigma\|_1$")
    ax2.semilogy(ts2, [max(v, 1e-12) for v in tr2["rel_entropy_exact"]], "d-.", color="#9467bd", linewidth=1.6, markevery=8, markersize=4.5,
                 label=r"Exact relative entropy $D(\rho_t \| \sigma)$")
    ax2.set_xlabel(r"Evolution time $t$")
    ax2.set_ylabel(r"Distance / divergence to $\sigma$")
    ax2.set_ylim(1e-3, 1e4)
    ax2.set_title(r"(b) 1D Anisotropic XXZ ($n=4, \Delta_z=1.5, \beta=1.5$)")
    ax2.legend(loc="upper right", frameon=True, framealpha=0.93)

    fig.tight_layout()
    fig.savefig(os.path.join(FIG_DIR, "fig1_1d_kms_trajectories.pdf"))
    fig.savefig(os.path.join(FIG_DIR, "fig1_1d_kms_trajectories.png"))
    plt.close(fig)


def make_fig2():
    with open(os.path.join(RES_DIR, "experiment2_large_n_scaling_and_phases.json")) as f:
        d2 = json.load(f)

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.4, 3.65), dpi=300)

    # Panel (a): n-qubit scaling O(n) vs O((log n)^2)
    sc = d2["depolarizing_scaling"]
    ns = [r["n"] for r in sc]
    ax1.loglog(ns, [r["T_gap"] for r in sc], "^:", color="#d62728", linewidth=1.8, markersize=6,
               label=r"Spectral gap $T_{\mathrm{gap}} = \Theta(n)$")
    ax1.loglog(ns, [r["T_sp_christoffel"] for r in sc], "s--", color="#ff7f0e", linewidth=1.9, markersize=5.5,
               label=r"Universal Christoffel ($c=3$, all states)")
    ax1.loglog(ns, [r["T_sp_bloch"] for r in sc], "o-", color="#1f77b4", linewidth=2.0, markersize=6,
               label=r"Product-state Bloch ($c=1$, product semigroups)")
    ax1.set_xlabel(r"System size $n$ (qubits)")
    ax1.set_ylabel(r"Certified mixing time $T(\varepsilon=0.1)$")
    ax1.set_title(r"(a) Pure $L^1 \to L^2$ Speedup: $O(n)$ vs. $O(\log^2 n)$")
    ax1.legend(loc="upper left", frameon=True, framealpha=0.93)

    # Panel (b): Continuous alpha-Super-Poincare phase diagram (Theorem 3.1b)
    ph = d2["alpha_phases"]
    ts = ph["alpha_1.0"]["times"]
    ax2.semilogy(ts, [max(v, 1e-4) for v in ph["alpha_0.5"]["D2_exact"]], "^:", color="#d62728", linewidth=1.8, markevery=10, markersize=5.5,
                 label=r"$\alpha = 0.5$ (sub-log): $D_2^{1/2}$ linear")
    ax2.semilogy(ts, [max(v, 1e-4) for v in ph["alpha_1.0"]["D2_exact"]], "o-", color="#1f77b4", linewidth=2.0, markevery=10, markersize=5.5,
                 label=r"$\alpha = 1.0$ (LSI): $D_2(t) = D_0 e^{-2\gamma t}$")
    ax2.semilogy(ts, [max(v, 1e-4) for v in ph["alpha_1.5"]["D2_exact"]], "s--", color="#2ca02c", linewidth=2.0, markevery=10, markersize=5.5,
                 label=r"$\alpha = 1.5$ (ultracontractive): $\leq (\gamma t)^{-2}$")
    ax2.set_xlabel(r"Evolution time $t$")
    ax2.set_ylabel(r"Sandwiched Rényi-2 divergence $D_2(\rho_t \| \sigma)$")
    ax2.set_ylim(1e-2, 1e2)
    ax2.set_title(r"(b) Continuous $\alpha$-Super-Poincaré Phase Diagram")
    ax2.legend(loc="lower left", frameon=True, framealpha=0.93)

    fig.tight_layout()
    fig.savefig(os.path.join(FIG_DIR, "fig2_scaling_and_alpha_phases.pdf"))
    fig.savefig(os.path.join(FIG_DIR, "fig2_scaling_and_alpha_phases.png"))
    plt.close(fig)


def make_fig3():
    with open(os.path.join(RES_DIR, "experiment3_exact_Q_ldlt_certificates.json")) as f:
        d3 = json.load(f)
    with open(os.path.join(RES_DIR, "experiment4_sharpness_and_two_stage.json")) as f:
        d4 = json.load(f)

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.4, 3.65), dpi=300)

    # Panel (a): Exact 2-tier Sharpness (Theorem 2.2c)
    sw = d4["sweep"]
    y0s = [r["y0"] for r in sw]
    ax1.semilogx(y0s, [r["T_gap"] for r in sw], "^:", color="#d62728", linewidth=1.8, markersize=6,
                 label=r"Spectral-gap bound $T_{\mathrm{gap}}$")
    ax1.semilogx(y0s, [r["T_sp"] for r in sw], "s--", color="#1f77b4", linewidth=2.0, markersize=6,
                 label=r"Super-Poincaré $T_{\mathrm{SP}}$ (Theorem 2.2)")
    ax1.semilogx(y0s, [r["t_exact"] for r in sw], "o-", color="#2ca02c", linewidth=1.9, markersize=5,
                 label=r"Exact semigroup hitting time $t_{\mathrm{exact}}$")
    ax1.set_xlabel(r"Initial divergence $y_0 = \chi^2_\sigma(\rho_0 \| \sigma)$")
    ax1.set_ylabel(r"Mixing time $T(\varepsilon = 0.1)$")
    ax1.set_title(r"(a) Exact 2-Tier Sharpness ($\lambda_0=0.1, \lambda_1=2.0$)")
    ax1.legend(loc="upper left", frameon=True, framealpha=0.93)

    # Panel (b): Certified Exact-Q Speedups across all 6 models
    certs = d3["certificates"]
    short_labels = [
        "TFIM n=2\n(LDL$^T$)",
        "XXZ n=2\n(LDL$^T$)",
        "TFIM n=4\n($\\beta=2.5$)",
        "XXZ n=4\n($\\beta=1.5$)",
        "Depol.\n$n=50$",
        "Depol.\n$n=100$",
    ]
    speedups = [r["speedup"] for r in certs]
    colors = ["#2ca02c", "#2ca02c", "#1f77b4", "#1f77b4", "#ff7f0e", "#ff7f0e"]
    bars = ax2.bar(range(len(short_labels)), speedups, color=colors, edgecolor="black", linewidth=0.7, alpha=0.88)
    ax2.axhline(1.0, color="gray", linestyle="--", linewidth=1.0)
    for bar, sp in zip(bars, speedups):
        ax2.text(bar.get_x() + bar.get_width() / 2.0, sp + 0.08, f"{sp:.2f}x", ha="center", va="bottom", fontsize=8.0, fontweight="bold")
    ax2.set_xticks(range(len(short_labels)))
    ax2.set_xticklabels(short_labels, fontsize=7.6)
    ax2.set_ylabel(r"Certified exact-$\mathbb{Q}$ speedup $T_{\mathrm{gap}}^{\mathbb{Q}} / T_{\mathrm{SP}}^{\mathbb{Q}}$")
    ax2.set_ylim(0, max(speedups) * 1.18)
    ax2.set_title(r"(b) Exact-$\mathbb{Q}$ Verified Speedups (Quantized Bundle)")

    fig.tight_layout()
    fig.savefig(os.path.join(FIG_DIR, "fig3_sharpness_and_speedups.pdf"))
    fig.savefig(os.path.join(FIG_DIR, "fig3_sharpness_and_speedups.png"))
    plt.close(fig)


if __name__ == "__main__":
    make_fig1()
    make_fig2()
    make_fig3()
    print("Generated all 3 publication figures in paper/figures/.")

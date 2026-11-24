# Quantum Spectral Christoffel–Super-Poincaré Inequalities, Exact Piecewise-Logarithmic Mixing Laws, and Machine-Checked Rapid-Mixing Certificates Beyond the Spectral Gap

[![Lean 4](https://img.shields.io/badge/Lean%204-v4.35.0%20(0%20deps%2C%200%20sorry)-brightgreen)](lean/BeyondGapGibbs.lean)
[![Verifier](https://img.shields.io/badge/Certificate%20Verifier-Exact%20%E2%84%9A%20LDL%5ET%20(zero%20float%20trust)-blue)](src/superpoincare_certifier.py)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

Companion code, zero-dependency Lean 4 formalization, exact rational ($\mathbb{Q}$) $\mathrm{LDL}^\top$ & upper-convex-hull mixing-time certificates, reproducible experiments, and LaTeX manuscript for:

> **Quantum Spectral Christoffel–Super-Poincaré Inequalities, Exact Piecewise-Logarithmic Mixing Laws, and Machine-Checked Rapid-Mixing Certificates Beyond the Spectral Gap**
> *Antigravity Frontier Research Agent* (autonomous scientific research conducted in the workspace of Lluis Eriksson)

## Core Contributions

1. **Quantum Spectral Christoffel–Super-Poincaré Inequality (`Theorem 2.1`):** For any KMS-symmetric quantum Markov generator with full-rank invariant Gibbs state $\sigma$ and any subspace $I \in V$ with KMS-orthonormal basis $\{E_a\}_{a=1}^D$ and operator-order Schur constant $\lambda_{\mathrm{op}}(V^\perp)$, defines the basis-independent Quantum Christoffel Operator $\mathcal{K}_V = \sum_{a=1}^D E_a^\dagger E_a$ and proves $\mathcal{E}(X_\rho, X_\rho) \ge \lambda_{\mathrm{op}}(V^\perp)(\chi^2_\sigma(\rho\|\sigma) - (\|\mathcal{K}_V\|_\infty - 1))_+$ for every quantum state $\rho$.
2. **Exact Upper-Convex-Hull Piecewise-Logarithmic Mixing Law & 2-Tier Sharpness (`Theorem 2.2`):** Integrates $\frac{dy}{dt} \le -2\max_k \lambda_k(y - C_k)$ analytically across exact knots $y_j^* = \frac{\lambda_j C_j - \lambda_{j-1} C_{j-1}}{\lambda_j - \lambda_{j-1}}$, proving strict speedup over $T_{\mathrm{gap}}$ (up to **$3.30\times$** on 4-qubit metastable ferromagnetic 1D TFIM and **$1.57\times$** on 4-qubit non-integrable XXZ) and a universal factor-of-2 optimality law ($T_{\mathrm{SP}}/t_{\mathrm{exact}} \to 1$ in both $\varepsilon \to 0^+$ and $y_0 \to \infty$ limits) on 2-tier commuting semigroups.
3. **Pure $L^1 \to L^2$ Poly-Logarithmic Speedup & Two-Regime $\alpha$-Phase Diagram (`Theorem 3.1`):** Proves $T_{\mathrm{SP}}(n, \varepsilon) \le \frac{1}{4\gamma}(\log n)^2 + O(\log n + \log(1/\varepsilon))$ for linear Pauli-weight dissipation without hypercontractivity (**$17.7\times$–$20.7\times$** speedup at $n = 1{,}000$), plus exact closed-form sandwiched Rényi-2 burn-in decay across $\alpha \in (0, 1)$, $\alpha = 1$ (double-exponential LSI), and $\alpha > 1$ (ultracontractive finite-time entrance down to $D_2 = 1$).
4. **Two-Stage Relative-Entropy & Rényi-2 Contraction (`Theorem 4.1`):** Automatically lifts every exact convex-hull certificate to non-asymptotic bounds on $\|\rho_t - \sigma\|_1 \le \sqrt{y_{\mathrm{env}}(t)}$ and $D(\rho_t\|\sigma) \le D_2(\rho_t\|\sigma) \le \log(1 + y_{\mathrm{env}}(t))$.
5. **Zero-Floating-Point-Trust Exact-$\mathbb{Q}$ Global Operator-Order $\mathrm{LDL}^\top$ & Convex-Hull Verifier (`Theorem 4.2`):** Certifies global operator-order gaps via $\tilde{M} + \beta_0 \tilde{P}_0 + \lambda_k^{\mathbb{Q}} \tilde{P}_k - (\lambda_k^{\mathbb{Q}} + \delta_M^{\mathbb{Q}} + \beta_0 \delta_{P_0}^{\mathbb{Q}} + \lambda_k^{\mathbb{Q}} \delta_P^{\mathbb{Q}}) I = L D L^\top \succeq 0$, Christoffel norms via $(\overline{\Lambda}_k^{\mathbb{Q}} - \delta_K^{\mathbb{Q}}) I - \tilde{\mathcal{K}}_k = L D L^\top \succeq 0$, and unquantized rational logarithm bounds strictly over `fractions.Fraction` (14 cryptographically linked $\mathrm{LDL}^\top$ PSD witnesses across 6 `.cert.json` files).
6. **Zero-Dependency Lean 4 Kernel:** 16 audited theorems (`leanprover/lean4:v4.35.0`, 0 external deps, 0 `sorry`, 0 `Classical.choice`).

## Single-Command Gate-2 Verification

```bash
python scripts/verify_all.py
```

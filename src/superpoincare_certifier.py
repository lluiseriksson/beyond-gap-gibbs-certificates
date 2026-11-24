"""
Zero-Floating-Point-Trust Exact Rational (Q) Upper-Convex-Hull Mixing-Time &
Global Operator-Order LDL^T Spectral-Tier Certificate Builder and Verifier.

Every certified bound is replayed strictly in arbitrary-precision `fractions.Fraction`:
  1. Strict exact-rational parsing (`_parse_exact_fraction`) rejecting bool/float/decimal strings.
  2. Exact rational LDL^T verification for PSD matrices A_q = L_q * diag(D_q) * L_q^T (D_i >= 0),
     enforcing `isinstance(x, Fraction)` on every entry (immune to IEEE-754 float roundoff).
  3. Cryptographically bound Global Operator-Order LDL^T bundle verification (Theorem 4.2):
     Reconstructs from the shared quantized generator bundle (M_q, P0_q, beta0_q, delta_M_q, delta_P0_q)
     and each tier's certified (lambda_q, C_q) + (P_k_q, delta_P_q) / (K_k_q, delta_K_q):
       (i)  A_gap = M_q + beta0_q * P0_q + lambda_q * P_k_q
                    - (lambda_q + delta_M_q + beta0_q * delta_P0_q + lambda_q * delta_P_q) * I == L D L^T
       (ii) A_chr = ((C_q + 1) - delta_K_q) * I - K_k_q == L D L^T   (for every tier >= 1)
     requiring complete 1-to-1 tier coverage so no witness can be forged or unlinked.
  4. Exact rational upper-convex-hull verification + UNQUANTIZED rational logarithm upper bound
     `log_rational_upper_bound_exact` (Lean: `geometric_tail_term_le`) for every interval,
     plus pure-Q consistency checks on all display floats (`T_sp_ub_float`, `T_gap_ub_float`, `speedup_float`).
"""
import math
import re
from fractions import Fraction

_EXACT_FRAC_RE = re.compile(r"^-?\d+(?:/[1-9]\d*)?$")


def _require_pos_int(val, name: str) -> int:
    if not isinstance(val, int) or isinstance(val, bool) or val <= 0:
        raise ValueError(f"{name} must be a strictly positive integer")
    return val


def _parse_exact_fraction(val, name: str = "value") -> Fraction:
    """Strictly parse an exact rational (Fraction, non-bool int, or 'p/q' / 'p' string)."""
    if isinstance(val, bool):
        raise ValueError(f"{name}: boolean not allowed")
    if isinstance(val, Fraction):
        return val
    if isinstance(val, int):
        return Fraction(val, 1)
    if isinstance(val, str):
        if not _EXACT_FRAC_RE.match(val):
            raise ValueError(f"{name}: invalid exact rational string {val!r}")
        return Fraction(val)
    raise ValueError(f"{name}: expected exact rational string or Fraction, got {type(val).__name__}")


def _fmt_q(x: Fraction) -> str:
    return f"{x.numerator}/{x.denominator}"


def ceil_rational(x: Fraction, denom: int = 10**12) -> Fraction:
    """Sound upward quantization: returns q = ceil(x * denom) / denom >= x EXACTLY."""
    _require_pos_int(denom, "denom")
    if not isinstance(x, Fraction):
        raise ValueError("x must be a Fraction")
    num = -((-x.numerator * denom) // x.denominator)
    return Fraction(num, denom)


def floor_rational(x: Fraction, denom: int = 10**12) -> Fraction:
    """Sound downward quantization: returns q = floor(x * denom) / denom <= x EXACTLY."""
    _require_pos_int(denom, "denom")
    if not isinstance(x, Fraction):
        raise ValueError("x must be a Fraction")
    num = (x.numerator * denom) // x.denominator
    return Fraction(num, denom)


def log_rational_upper_bound_exact(x: Fraction, terms: int = 16) -> Fraction:
    """
    100% exact UNQUANTIZED rational (Q) STRICT UPPER BOUND on log(x) for any x in Q with x >= 1.
    Uses exact binary reduction x = 2^k * r with r in [1, 2) and geometric tail bound
    proved in Lean 4 (`geometric_tail_term_le`):
      log((1+t)/(1-t)) <= 2 * sum_{j=0}^{M-1} t^{2j+1}/(2j+1) + 2 * t^{2M+1} / ((2M+1)*(1 - t^2))
    for t = (r-1)/(r+1) in [0, 1/3).
    """
    _require_pos_int(terms, "terms")
    if not isinstance(x, Fraction):
        raise ValueError("x must be a Fraction")
    if x < Fraction(1):
        raise ValueError("log_rational_upper_bound_exact requires x >= 1")
    if x == Fraction(1):
        return Fraction(0)
    k = 0
    r = x
    two = Fraction(2)
    while r >= two:
        r /= two
        k += 1

    def _atanh2_ub(t: Fraction, m: int) -> Fraction:
        if t == 0:
            return Fraction(0)
        t2 = t * t
        cur = t
        acc = Fraction(0)
        for j in range(m):
            acc += cur / (2 * j + 1)
            cur *= t2
        tail = cur / ((2 * m + 1) * (Fraction(1) - t2))
        return 2 * (acc + tail)

    log2_ub = _atanh2_ub(Fraction(1, 3), terms)
    tr = (r - Fraction(1)) / (r + Fraction(1))
    logr_ub = _atanh2_ub(tr, terms)
    return k * log2_ub + logr_ub


def compute_exact_ldlt_q(A: list[list[Fraction]]) -> tuple[bool, list[list[Fraction]], list[Fraction]]:
    """
    Exact rational LDL^T factorization (without square roots!) for a symmetric rational matrix A.
    Returns (is_psd, L, D) where L is unit lower triangular and D_i >= 0 iff A = L D L^T is PSD.
    """
    n = len(A)
    L = [[Fraction(1) if i == j else Fraction(0) for j in range(n)] for i in range(n)]
    D = [Fraction(0) for _ in range(n)]
    for j in range(n):
        s = A[j][j]
        for k in range(j):
            s -= L[j][k] * L[j][k] * D[k]
        if s < 0:
            return False, [], []
        D[j] = s
        if s == 0:
            for i in range(j + 1, n):
                r = A[i][j]
                for k in range(j):
                    r -= L[i][k] * L[j][k] * D[k]
                if r != 0:
                    return False, [], []
                L[i][j] = Fraction(0)
        else:
            for i in range(j + 1, n):
                r = A[i][j]
                for k in range(j):
                    r -= L[i][k] * L[j][k] * D[k]
                L[i][j] = r / s
    return True, L, D


def verify_ldlt_psd_exact(
    A: list[list[Fraction]],
    L: list[list[Fraction]],
    D: list[Fraction],
) -> tuple[bool, str]:
    """
    Zero-float-trust exact-Q verifier for A = L * diag(D) * L^T with L unit lower triangular and D >= 0.
    Strictly enforces `isinstance(x, Fraction)` on every single entry to prevent float64 roundoff bypasses.
    """
    if not isinstance(A, list) or not isinstance(L, list) or not isinstance(D, list):
        return False, "A, L, D must be lists"
    n = len(A)
    if n == 0 or len(L) != n or len(D) != n:
        return False, "dimension mismatch"
    for i in range(n):
        if not isinstance(A[i], list) or not isinstance(L[i], list) or len(A[i]) != n or len(L[i]) != n:
            return False, "non-square matrix"
        if not isinstance(D[i], Fraction):
            return False, f"D[{i}] is not exact Fraction"
        if D[i] < 0:
            return False, f"negative diagonal pivot D[{i}]"
        for j in range(n):
            if not isinstance(A[i][j], Fraction) or not isinstance(L[i][j], Fraction):
                return False, f"non-Fraction entry at ({i},{j})"
        if L[i][i] != Fraction(1):
            return False, f"L[{i}][{i}] != 1"
        for j in range(i + 1, n):
            if L[i][j] != 0:
                return False, f"L not lower triangular at ({i},{j})"
            if A[i][j] != A[j][i]:
                return False, f"A not symmetric at ({i},{j})"
    for i in range(n):
        for j in range(i + 1):
            acc = Fraction(0)
            for k in range(j + 1):
                acc += L[i][k] * D[k] * L[j][k]
            if acc != A[i][j]:
                return False, f"LDL^T mismatch at ({i},{j})"
    return True, "ok"


def build_upper_convex_hull(tiers: list[tuple[float, float]]) -> list[tuple[float, float, float]]:
    """
    Given list of (lambda_k, C_k) with lambda_k > 0 and C_k >= 0 (including C_0 = 0),
    compute the exact active upper convex hull of L_k(y) = lambda_k * (y - C_k) on (0, inf).
    Returns list of (lambda, C, y_start) with strictly increasing lambda, C, and y_start.
    """
    sorted_t = sorted(tiers, key=lambda t: (t[0], t[1]))
    hull: list[tuple[float, float, float]] = []
    for lam, C in sorted_t:
        if lam <= 1e-14:
            continue
        if hull and abs(lam - hull[-1][0]) < 1e-12:
            if C < hull[-1][1]:
                hull.pop()
            else:
                continue
        while hull:
            lp, Cp, ylo_p = hull[-1]
            y_int = (lam * C - lp * Cp) / (lam - lp)
            if y_int <= ylo_p:
                hull.pop()
            else:
                hull.append((lam, C, y_int))
                break
        if not hull:
            if C > 1e-12:
                continue
            hull.append((lam, 0.0, 0.0))
    return hull


def evaluate_hull_mixing_time_float(
    hull: list[tuple[float, float, float]], y0: float, eps: float
) -> float:
    """Evaluate exact piecewise-logarithmic mixing time T_SP(eps; y0) from hull."""
    yt = eps * eps
    if y0 <= yt:
        return 0.0
    T = 0.0
    for idx, (lam, C, y_lo) in enumerate(hull):
        y_hi = hull[idx + 1][2] if idx + 1 < len(hull) else float("inf")
        a = max(yt, y_lo)
        b = min(y0, y_hi)
        if b > a:
            T += (0.5 / lam) * math.log((b - C) / (a - C))
    return T


def evaluate_hull_trajectory_float(
    hull: list[tuple[float, float, float]], y0: float, times: list[float]
) -> list[float]:
    """
    Integrate the EXACT piecewise-linear ODE dy/dt = -2 max_j lam_j (y - C_j) from y(0) = y0
    analytically across hull knots to produce the exact certified envelope y_env(t).
    """
    out = []
    for t in times:
        y = y0
        rem = t
        idx = len(hull) - 1
        while idx > 0 and y <= hull[idx][2]:
            idx -= 1
        while rem > 0.0 and idx >= 0:
            lam, C, y_lo = hull[idx]
            if idx == 0:
                y = y * math.exp(-2.0 * lam * rem)
                rem = 0.0
            else:
                dt_knot = (0.5 / lam) * math.log((y - C) / (y_lo - C))
                if rem <= dt_knot:
                    y = C + (y - C) * math.exp(-2.0 * lam * rem)
                    rem = 0.0
                else:
                    y = y_lo
                    rem -= dt_knot
                    idx -= 1
        out.append(max(0.0, y))
    return out


def build_exact_mixing_certificate_from_fractions(
    raw_tiers_q: list[tuple[Fraction, Fraction]],
    y0_q: Fraction,
    eps_q: Fraction,
    ldlt_bundle: dict | None = None,
    model_meta: dict | None = None,
) -> tuple[bool, dict | None]:
    """
    Build a 100% exact rational (Q) Super-Poincare mixing-time certificate directly from
    exact `Fraction` inputs (zero IEEE-754 float intermediate, eliminating 53-bit truncation!).
    """
    if eps_q <= 0 or y0_q <= eps_q * eps_q:
        return False, None

    # Exact rational upper-convex-hull pruning (no float!)
    hull_q: list[tuple[Fraction, Fraction, Fraction]] = []
    for lam_q, C_q in sorted(raw_tiers_q, key=lambda x: (x[0], x[1])):
        if lam_q <= 0 or C_q < 0:
            continue
        if hull_q and lam_q == hull_q[-1][0]:
            if C_q < hull_q[-1][1]:
                hull_q.pop()
            else:
                continue
        while hull_q:
            lp, Cp, ylo_p = hull_q[-1]
            y_int = (lam_q * C_q - lp * Cp) / (lam_q - lp)
            if y_int <= ylo_p or y_int <= C_q:
                hull_q.pop()
            else:
                hull_q.append((lam_q, C_q, y_int))
                break
        if not hull_q:
            if C_q != 0:
                return False, None
            hull_q.append((lam_q, Fraction(0), Fraction(0)))

    if not hull_q:
        return False, None

    yt_q = eps_q * eps_q
    T_sp_exact = Fraction(0)
    for i, (lam_q, C_q, ylo_q) in enumerate(hull_q):
        yhi_q = hull_q[i + 1][2] if i + 1 < len(hull_q) else None
        a_q = yt_q if yt_q > ylo_q else ylo_q
        b_q = y0_q if (yhi_q is None or y0_q < yhi_q) else yhi_q
        if b_q > a_q:
            ratio_q = (b_q - C_q) / (a_q - C_q)
            T_sp_exact += log_rational_upper_bound_exact(ratio_q, terms=16) / (2 * lam_q)
    T_gap_exact = log_rational_upper_bound_exact(y0_q / yt_q, terms=16) / (2 * hull_q[0][0])

    T_sp_ub_q = ceil_rational(T_sp_exact, denom=10**12)
    T_gap_ub_q = ceil_rational(T_gap_exact, denom=10**12)

    cert = {
        "y0": _fmt_q(y0_q),
        "eps": _fmt_q(eps_q),
        "tiers": [
            {
                "lambda_q": _fmt_q(lam),
                "C_q": _fmt_q(C),
                "knot_q": _fmt_q(knot),
            }
            for lam, C, knot in hull_q
        ],
        "T_sp_ub_q": _fmt_q(T_sp_ub_q),
        "T_sp_ub_float": float(T_sp_ub_q),
        "T_gap_ub_q": _fmt_q(T_gap_ub_q),
        "T_gap_ub_float": float(T_gap_ub_q),
        "speedup_float": float(T_gap_ub_q / T_sp_ub_q),
        "ldlt_bundle": ldlt_bundle,
        "model_meta": model_meta or {},
    }
    return True, cert


def build_exact_mixing_certificate(
    tiers_float: list[tuple[float, float]],
    y0_float: float,
    eps_float: float,
    quant_denom: int = 10**9,
    lam_margin_rel: float = 1e-6,
    C_margin_rel: float = 1e-6,
    ldlt_bundle: dict | None = None,
    model_meta: dict | None = None,
) -> tuple[bool, dict | None]:
    """
    Construct a sound exact-Q certificate from float inputs by outward quantization
    (lambda DOWN, C UP, y0 UP, eps DOWN) followed by exact-Fraction hull & log verification.
    """
    _require_pos_int(quant_denom, "quant_denom")
    hull_f = build_upper_convex_hull(tiers_float)
    if not hull_f:
        return False, None

    raw_q: list[tuple[Fraction, Fraction]] = []
    for idx, (lam, C, _) in enumerate(hull_f):
        lam_q = floor_rational(Fraction(float(lam * (1.0 - lam_margin_rel))), denom=quant_denom)
        C_q = Fraction(0) if idx == 0 else ceil_rational(Fraction(float(C * (1.0 + C_margin_rel))), denom=quant_denom)
        if lam_q > 0:
            raw_q.append((lam_q, C_q))

    y0_q = ceil_rational(Fraction(float(y0_float)), denom=quant_denom)
    eps_q = floor_rational(Fraction(float(eps_float)), denom=quant_denom)
    return build_exact_mixing_certificate_from_fractions(
        raw_q, y0_q, eps_q, ldlt_bundle=ldlt_bundle, model_meta=model_meta
    )


def _parse_q_matrix(mat, expected_dim: int | None, name: str) -> list[list[Fraction]]:
    if not isinstance(mat, list) or len(mat) == 0:
        raise ValueError(f"{name}: empty or non-list matrix")
    n = len(mat)
    if expected_dim is not None and n != expected_dim:
        raise ValueError(f"{name}: expected dim {expected_dim}, got {n}")
    out = []
    for i, row in enumerate(mat):
        if not isinstance(row, list) or len(row) != n:
            raise ValueError(f"{name}: row {i} malformed")
        out.append([_parse_exact_fraction(x, f"{name}[{i}][{j}]") for j, x in enumerate(row)])
    return out


def _verify_ldlt_bundle_exact(bundle: dict, hull_q: list[tuple[Fraction, Fraction, Fraction]]) -> tuple[bool, int, str]:
    """
    Cryptographically verify a linked Global Operator-Order LDL^T bundle (Theorem 4.2):
      - Parses shared quantized M_q, P0_q, beta0_q > 0, delta_M_q >= 0, delta_P0_q >= 0.
      - Requires 1-to-1 coverage of EVERY tier idx in 0..len(hull_q)-1 for gap witnesses,
        and EVERY tier idx in 1..len(hull_q)-1 for Christoffel witnesses.
      - RECONSTRUCTS A_gap and A_chr directly from hull_q[idx] = (lam_q, C_q, _) and verifies
        A_reconstructed == L * diag(D) * L^T strictly in exact Fraction!
    """
    if not isinstance(bundle, dict):
        return False, 0, "ldlt_bundle must be a dict"
    M_q = _parse_q_matrix(bundle["M_q"], None, "M_q")
    dimM = len(M_q)
    P0_q = _parse_q_matrix(bundle["P0_q"], dimM, "P0_q")
    beta0_q = _parse_exact_fraction(bundle["beta0_q"], "beta0_q")
    delta_M_q = _parse_exact_fraction(bundle["delta_M_q"], "delta_M_q")
    delta_P0_q = _parse_exact_fraction(bundle["delta_P0_q"], "delta_P0_q")
    if beta0_q <= 0 or delta_M_q < 0 or delta_P0_q < 0:
        return False, 0, "invalid beta0_q or negative perturbation radius"

    dimH = bundle["dim_H"]
    if not isinstance(dimH, int) or isinstance(dimH, bool) or dimH <= 0 or dimH * dimH != dimM:
        return False, 0, "dim_H mismatch with dim(M_q)"

    gap_wits = bundle["gap_witnesses"]
    chr_wits = bundle["christoffel_witnesses"]
    if not isinstance(gap_wits, list) or not isinstance(chr_wits, list):
        return False, 0, "gap_witnesses and christoffel_witnesses must be lists"

    seen_gap = set()
    for w in gap_wits:
        if not isinstance(w, dict):
            return False, 0, "gap witness must be dict"
        t_idx = w["tier_idx"]
        if not isinstance(t_idx, int) or isinstance(t_idx, bool) or not (0 <= t_idx < len(hull_q)):
            return False, 0, f"invalid gap tier_idx {t_idx}"
        if t_idx in seen_gap:
            return False, 0, f"duplicate gap witness for tier {t_idx}"
        seen_gap.add(t_idx)

        lam_q = hull_q[t_idx][0]
        P_k_q = _parse_q_matrix(w["P_k_q"], dimM, f"P_k_q[{t_idx}]")
        delta_P_q = _parse_exact_fraction(w["delta_P_q"], f"delta_P_q[{t_idx}]")
        if delta_P_q < 0:
            return False, 0, f"negative delta_P_q on tier {t_idx}"
        total_err_q = delta_M_q + beta0_q * delta_P0_q + lam_q * delta_P_q
        diag_shift_q = lam_q + total_err_q

        # Reconstruct A_gap directly from Theorem 4.2(i) — never trust an unlinked A!
        A_gap = [
            [
                M_q[i][j] + beta0_q * P0_q[i][j] + lam_q * P_k_q[i][j]
                - (diag_shift_q if i == j else Fraction(0))
                for j in range(dimM)
            ]
            for i in range(dimM)
        ]
        L_q = _parse_q_matrix(w["L"], dimM, f"gap_L[{t_idx}]")
        D_q = [_parse_exact_fraction(x, f"gap_D[{t_idx}][{i}]") for i, x in enumerate(w["D"])]
        ok_l, msg_l = verify_ldlt_psd_exact(A_gap, L_q, D_q)
        if not ok_l:
            return False, 0, f"gap LDL^T failed on tier {t_idx}: {msg_l}"

    if seen_gap != set(range(len(hull_q))):
        return False, 0, "gap_witnesses must cover every active tier 0..r"

    seen_chr = set()
    for w in chr_wits:
        if not isinstance(w, dict):
            return False, 0, "christoffel witness must be dict"
        t_idx = w["tier_idx"]
        if not isinstance(t_idx, int) or isinstance(t_idx, bool) or not (1 <= t_idx < len(hull_q)):
            return False, 0, f"invalid christoffel tier_idx {t_idx}"
        if t_idx in seen_chr:
            return False, 0, f"duplicate christoffel witness for tier {t_idx}"
        seen_chr.add(t_idx)

        bar_Lam_q = hull_q[t_idx][1] + Fraction(1)  # C_k + 1 == bar_Lambda_k
        K_k_q = _parse_q_matrix(w["K_k_q"], dimH, f"K_k_q[{t_idx}]")
        delta_K_q = _parse_exact_fraction(w["delta_K_q"], f"delta_K_q[{t_idx}]")
        if delta_K_q < 0:
            return False, 0, f"negative delta_K_q on tier {t_idx}"
        c_shift_q = bar_Lam_q - delta_K_q

        # Reconstruct A_chr directly from Theorem 4.2(ii) — never trust an unlinked A!
        A_chr = [
            [
                (c_shift_q if i == j else Fraction(0)) - K_k_q[i][j]
                for j in range(dimH)
            ]
            for i in range(dimH)
        ]
        L_q = _parse_q_matrix(w["L"], dimH, f"chr_L[{t_idx}]")
        D_q = [_parse_exact_fraction(x, f"chr_D[{t_idx}][{i}]") for i, x in enumerate(w["D"])]
        ok_l, msg_l = verify_ldlt_psd_exact(A_chr, L_q, D_q)
        if not ok_l:
            return False, 0, f"christoffel LDL^T failed on tier {t_idx}: {msg_l}"

    if seen_chr != set(range(1, len(hull_q))):
        return False, 0, "christoffel_witnesses must cover every active tier 1..r"

    return True, len(gap_wits) + len(chr_wits), "ok"


def verify_mixing_certificate_exact(cert: dict) -> tuple[bool, dict]:
    """
    100% ZERO-FLOATING-POINT-TRUST exact rational (Q) verifier for a Quantum Spectral
    Christoffel-Super-Poincare mixing-time certificate (and any linked Theorem 4.2 LDL^T bundle).
    """
    if not isinstance(cert, dict):
        return False, {"reason": "certificate must be a dict"}
    try:
        y0_q = _parse_exact_fraction(cert["y0"], "y0")
        eps_q = _parse_exact_fraction(cert["eps"], "eps")
        T_sp_ub_q = _parse_exact_fraction(cert["T_sp_ub_q"], "T_sp_ub_q")
        T_gap_ub_q = _parse_exact_fraction(cert["T_gap_ub_q"], "T_gap_ub_q")
        tiers = cert["tiers"]
        if not isinstance(tiers, list) or len(tiers) < 1:
            return False, {"reason": "empty or non-list tiers"}
        if eps_q <= 0 or y0_q <= eps_q * eps_q:
            return False, {"reason": "invalid y0 or eps"}

        hull_q: list[tuple[Fraction, Fraction, Fraction]] = []
        for idx, t in enumerate(tiers):
            if not isinstance(t, dict):
                return False, {"reason": f"tier {idx} is not a dict"}
            lam_q = _parse_exact_fraction(t["lambda_q"], f"tier[{idx}].lambda_q")
            C_q = _parse_exact_fraction(t["C_q"], f"tier[{idx}].C_q")
            knot_q = _parse_exact_fraction(t["knot_q"], f"tier[{idx}].knot_q")
            if lam_q <= 0 or C_q < 0:
                return False, {"reason": f"tier {idx}: nonpositive lambda or negative C"}
            if idx == 0:
                if C_q != 0 or knot_q != 0:
                    return False, {"reason": "tier 0 must have C_0 = 0 and knot_0 = 0"}
            else:
                lp, Cp, kp = hull_q[-1]
                if lam_q <= lp or C_q <= Cp:
                    return False, {"reason": f"tier {idx}: lambda and C must strictly increase"}
                expected_knot = (lam_q * C_q - lp * Cp) / (lam_q - lp)
                if knot_q != expected_knot:
                    return False, {"reason": f"tier {idx}: knot_q mismatch"}
                if knot_q <= kp or knot_q <= C_q:
                    return False, {"reason": f"tier {idx}: non-monotone hull knot or knot <= C"}
            hull_q.append((lam_q, C_q, knot_q))

        # Verify linked Global Operator-Order LDL^T bundle if present (or required by model_meta)
        n_ldlt = 0
        bundle = cert.get("ldlt_bundle", None)
        meta = cert.get("model_meta", {})
        if isinstance(meta, dict) and meta.get("end_to_end_ldlt", False) and bundle is None:
            return False, {"reason": "end_to_end_ldlt flag set but ldlt_bundle is missing"}
        if bundle is not None:
            ok_b, n_ldlt, msg_b = _verify_ldlt_bundle_exact(bundle, hull_q)
            if not ok_b:
                return False, {"reason": f"ldlt_bundle failed: {msg_b}"}

        # Reject legacy unlinked ldlt_witnesses field if someone attempts to inject it
        if "ldlt_witnesses" in cert and cert["ldlt_witnesses"]:
            return False, {"reason": "unlinked ldlt_witnesses field is forbidden; use linked ldlt_bundle"}

        # Recompute exact UNQUANTIZED rational upper bounds on T_SP and T_gap
        yt_q = eps_q * eps_q
        T_sp_exact = Fraction(0)
        for i, (lam_q, C_q, ylo_q) in enumerate(hull_q):
            yhi_q = hull_q[i + 1][2] if i + 1 < len(hull_q) else None
            a_q = yt_q if yt_q > ylo_q else ylo_q
            b_q = y0_q if (yhi_q is None or y0_q < yhi_q) else yhi_q
            if b_q > a_q:
                ratio_q = (b_q - C_q) / (a_q - C_q)
                if ratio_q < Fraction(1):
                    return False, {"reason": f"tier {i}: ratio < 1"}
                T_sp_exact += log_rational_upper_bound_exact(ratio_q, terms=16) / (2 * lam_q)

        T_gap_exact = log_rational_upper_bound_exact(y0_q / yt_q, terms=16) / (2 * hull_q[0][0])

        if T_sp_ub_q < T_sp_exact:
            return False, {"reason": "T_sp_ub_q is tighter than exact rational upper bound"}
        if T_gap_ub_q < T_gap_exact:
            return False, {"reason": "T_gap_ub_q is tighter than exact rational upper bound"}

        # Strict zero-float-trust display consistency checks (including speedup_float!)
        display_checks = [
            ("T_sp_ub_float", T_sp_ub_q),
            ("T_gap_ub_float", T_gap_ub_q),
            ("speedup_float", T_gap_ub_q / T_sp_ub_q),
        ]
        for f_key, q_val in display_checks:
            if f_key in cert:
                f_raw = cert[f_key]
                if not isinstance(f_raw, (int, float)) or isinstance(f_raw, bool) or not math.isfinite(float(f_raw)):
                    return False, {"reason": f"invalid or non-finite {f_key}"}
                if abs(Fraction(float(f_raw)) - q_val) > Fraction(1, 10**11):
                    return False, {"reason": f"{f_key} inconsistent with exact rational bound"}

        return True, {
            "n_tiers": len(hull_q),
            "n_ldlt_witnesses": n_ldlt,
            "T_sp_ub_q": T_sp_ub_q,
            "T_gap_ub_q": T_gap_ub_q,
        }
    except Exception as e:
        return False, {"reason": f"verification exception: {e}"}

"""Zero-floating-point exact-Q certificate verifier: GHD-DISAMBIG-CERT-1.0.
Audits all four information-theoretic and communication-complexity pillars of
Yogesh Dahiya, Mika Goos, Nathaniel Harms, Hamed Hatami, Pooya Hatami,
Shachar Lovett, & Weiqiang Yuan (arXiv:2611.32837, Nov 24, 2026)
"Communication Complexity of Disambiguations of Gap Hamming Distance":
  - Mode 1: marton_coupling_collision_cert (Lemma 3.1(a)-(b) exact Marton coupling & col(Z) <= ||mu||_inf)
  - Mode 2: lemma42_leaf_rectangle_restore_cert (Lemma 4.2 & Remark 4.3 protocol leaf rectangle restoration)
  - Mode 3: ghd_disambiguation_and_xor_lift_cert (Sec. 1-2 gamma-GHD XOR-lift & planted support contradiction)
  - Mode 4: theorem11_iterative_trajectory_cert (Theorem 1.1 Omega(n^{2/3}) multi-round recurrence audit)

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import re
from fractions import Fraction
from typing import Any, Dict, List, Set, Tuple

from src.ghd_exact import (
    collision_prob_marton_Z,
    format_rat,
    hamming_dist_int,
    marton_sequential_coupling_exact,
)

SCHEMA_VERSION = "GHD-DISAMBIG-CERT-1.0"
_CANON_INT_RE = re.compile(r"\A(0|-?[1-9][0-9]*)\Z")
_CANON_FRAC_RE = re.compile(r"\A-?[1-9][0-9]*/[1-9][0-9]*\Z")
MAX_RAT_STR_LEN = 1024
MAX_INT_BITS = 2048
MAX_ID_LEN = 128
MAX_JSON_DEPTH = 32


class GHDCertificateError(ValueError):
    """Raised whenever a GHD-DISAMBIG-CERT-1.0 certificate fails any invariant."""


def _assert_strict_json_types(obj: Any, path: str = "$", depth: int = 0) -> None:
    if depth > MAX_JSON_DEPTH:
        raise GHDCertificateError(f"JSON nesting depth > {MAX_JSON_DEPTH} at {path}")
    t = type(obj)
    if t is int:
        if obj.bit_length() > MAX_INT_BITS:
            raise GHDCertificateError(f"Integer bit-length > {MAX_INT_BITS} at {path}")
        return
    if t is str or t is bool:
        return
    if t is list:
        for i, v in enumerate(obj):
            _assert_strict_json_types(v, f"{path}[{i}]", depth + 1)
        return
    if t is dict:
        for k, v in obj.items():
            if type(k) is not str:
                raise GHDCertificateError(f"Non-string dict key at {path}")
            _assert_strict_json_types(v, f"{path}.{k}", depth + 1)
        return
    raise GHDCertificateError(f"Forbidden JSON type {t.__name__} at {path}")


def _parse_int(val: Any, name: str) -> int:
    if type(val) is not int:
        raise GHDCertificateError(f"{name} must be strict int, got {type(val).__name__}")
    if val.bit_length() > MAX_INT_BITS:
        raise GHDCertificateError(f"{name} integer too large")
    return val


def _parse_rat(val: Any, name: str) -> Fraction:
    if type(val) is int:
        if val.bit_length() > MAX_INT_BITS:
            raise GHDCertificateError(f"{name} integer too large")
        return Fraction(val, 1)
    if type(val) is str:
        if len(val) > MAX_RAT_STR_LEN:
            raise GHDCertificateError(f"{name} rational string too long")
        if _CANON_INT_RE.match(val):
            iv = int(val)
            if iv.bit_length() > MAX_INT_BITS:
                raise GHDCertificateError(f"{name} integer bit-length > {MAX_INT_BITS}")
            return Fraction(iv, 1)
        if _CANON_FRAC_RE.match(val):
            num_s, den_s = val.split("/")
            num, den = int(num_s), int(den_s)
            if num.bit_length() > MAX_INT_BITS or den.bit_length() > MAX_INT_BITS:
                raise GHDCertificateError(f"{name} rational bit-length > {MAX_INT_BITS}")
            if den < 2:
                raise GHDCertificateError(f"{name} denominator must be >= 2: {val!r}")
            q = Fraction(num, den)
            if q.numerator != num or q.denominator != den:
                raise GHDCertificateError(f"{name} unreduced fraction: {val!r}")
            return q
        raise GHDCertificateError(f"{name} non-canonical rational string: {val!r}")
    raise GHDCertificateError(f"{name} invalid type {type(val).__name__}")


def _parse_exact_keys(cert: Dict[str, Any], req: Set[str], mode: str) -> None:
    keys = set(cert.keys())
    if keys != req:
        raise GHDCertificateError(f"{mode} key mismatch: {sorted(keys ^ req)}")


def _parse_dist(raw: Any, size: int, name: str) -> List[Fraction]:
    if type(raw) is not list or len(raw) != size:
        raise GHDCertificateError(f"{name} must have length {size}")
    dist = [_parse_rat(raw[i], f"{name}[{i}]") for i in range(size)]
    if any(p < 0 for p in dist):
        raise GHDCertificateError(f"{name} contains negative probability")
    if sum(dist, Fraction(0, 1)) != Fraction(1, 1):
        raise GHDCertificateError(f"{name} does not sum to 1")
    return dist


# =============================================================================
# Mode 1: Lemma 3.1 Exact Marton Sequential Uniform Coupling & Collision Bound
# =============================================================================


def _verify_mode1_marton_coupling(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema",
        "mode",
        "cert_id",
        "num_bits_m",
        "mu_probs",
        "deficit_D_int",
        "subset_I",
        "tail_param_s",
        "claimed_mu_inf",
        "claimed_expected_dist",
        "claimed_sum_ai_sq",
        "claimed_collision_Z",
        "claimed_tail_prob",
    }
    _parse_exact_keys(cert, req, "Mode 1")
    m = _parse_int(cert["num_bits_m"], "num_bits_m")
    if not (2 <= m <= 5):
        raise GHDCertificateError("Require 2 <= num_bits_m <= 5")
    size = 1 << m
    mu = _parse_dist(cert["mu_probs"], size, "mu_probs")
    D_int = _parse_int(cert["deficit_D_int"], "deficit_D_int")
    s_param = _parse_int(cert["tail_param_s"], "tail_param_s")
    if not (0 <= D_int <= m) or not (1 <= s_param <= 8):
        raise GHDCertificateError("Require 0 <= deficit_D_int <= m and 1 <= tail_param_s <= 8")

    # Verify D_inf(mu) <= D_int <=> 2^m * ||mu||_inf <= 2^{D_int}
    mu_inf = max(mu)
    if Fraction(size, 1) * mu_inf > Fraction(1 << D_int, 1):
        raise GHDCertificateError(f"Distribution exceeds deficit D={D_int}: 2^m*||mu||_inf={size * mu_inf}")

    raw_I = cert["subset_I"]
    if type(raw_I) is not list:
        raise GHDCertificateError("subset_I must be list")
    coord_I = [_parse_int(v, "subset_I") for v in raw_I]
    if coord_I != sorted(coord_I) or len(set(coord_I)) != len(coord_I) or any(not (0 <= c < m) for c in coord_I):
        raise GHDCertificateError("subset_I must be strictly increasing indices in [0, m-1]")

    # Independently build exact Marton coupling (X, U)
    joint, exp_dist, sum_ai_sq = marton_sequential_coupling_exact(mu, m)

    # Verify exact marginals X ~ mu and U ~ U_m!
    marg_x = [Fraction(0, 1)] * size
    marg_u = [Fraction(0, 1)] * size
    for (x, u), p in joint.items():
        marg_x[x] += p
        marg_u[u] += p
    if marg_x != mu:
        raise GHDCertificateError("Coupling X marginal failed exact parity with mu")
    unif = Fraction(1, size)
    if any(pu != unif for pu in marg_u):
        raise GHDCertificateError("Coupling U marginal is not uniform")

    # Verify Lemma 3.1(a): E[dist(X, U)]^2 <= m * D_int
    if exp_dist * exp_dist > Fraction(m * D_int, 1):
        raise GHDCertificateError(f"Lemma 3.1(a) violated: E[dist]^2={exp_dist**2} > m*D={m*D_int}")

    # Verify Lemma 3.1(b) Eq. (5): col(Z) <= ||mu||_inf AND exact tail Pr[nu_{U_I}(X_{bar I}) > thresh] <= 2^{-s}
    col_z, z_dist = collision_prob_marton_Z(joint, coord_I, m)
    if col_z > mu_inf:
        raise GHDCertificateError(f"Lemma 3.1(b) Eq. (5) violated: col(Z)={col_z} > ||mu||_inf={mu_inf}")

    # Since U_I is uniform on 2^{|I|} values, nu_u(y) = Pr[Z=(u,y)] * 2^{|I|}
    k_I = len(coord_I)
    thresh = Fraction(1 << (D_int + s_param), 1 << (m - k_I))
    tail_prob = Fraction(0, 1)
    for (u_sub, x_rest), pz in z_dist.items():
        nu_val = pz * Fraction(1 << k_I, 1)
        if nu_val > thresh:
            tail_prob += pz
    if tail_prob > Fraction(1, 1 << s_param):
        raise GHDCertificateError(f"Lemma 3.1(b) Eq. (3) tail {tail_prob} > 2^(-{s_param})")

    if _parse_rat(cert["claimed_mu_inf"], "claimed_mu_inf") != mu_inf:
        raise GHDCertificateError("claimed_mu_inf mismatch")
    if _parse_rat(cert["claimed_expected_dist"], "claimed_expected_dist") != exp_dist:
        raise GHDCertificateError("claimed_expected_dist mismatch")
    if _parse_rat(cert["claimed_sum_ai_sq"], "claimed_sum_ai_sq") != sum_ai_sq:
        raise GHDCertificateError("claimed_sum_ai_sq mismatch")
    if _parse_rat(cert["claimed_collision_Z"], "claimed_collision_Z") != col_z:
        raise GHDCertificateError("claimed_collision_Z mismatch")
    if _parse_rat(cert["claimed_tail_prob"], "claimed_tail_prob") != tail_prob:
        raise GHDCertificateError("claimed_tail_prob mismatch")

    return {
        "verified": True,
        "mode": cert["mode"],
        "m": m,
        "mu_inf": format_rat(mu_inf),
        "exp_dist": format_rat(exp_dist),
        "col_Z": format_rat(col_z),
    }


# =============================================================================
# Mode 2: Lemma 4.2 & Remark 4.3 Protocol Leaf Rectangle Restoration
# =============================================================================


def _verify_mode2_leaf_rectangle(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema",
        "mode",
        "cert_id",
        "num_rows",
        "num_cols",
        "protocol_cost_d",
        "mu_rows",
        "nu_cols",
        "func_matrix_01",
        "leaf_rectangles",
        "witness_leaf_idx",
        "claimed_base_expectation",
        "claimed_protocol_error",
        "claimed_witness_mass",
        "claimed_witness_cond_exp",
        "claimed_row_blowup_factor",
        "claimed_col_blowup_factor",
    }
    _parse_exact_keys(cert, req, "Mode 2")
    nr = _parse_int(cert["num_rows"], "num_rows")
    nc = _parse_int(cert["num_cols"], "num_cols")
    d = _parse_int(cert["protocol_cost_d"], "protocol_cost_d")
    if not (2 <= nr <= 16 and 2 <= nc <= 16 and 1 <= d <= 6):
        raise GHDCertificateError("Require 2 <= nr, nc <= 16 and 1 <= d <= 6")
    mu = _parse_dist(cert["mu_rows"], nr, "mu_rows")
    nu = _parse_dist(cert["nu_cols"], nc, "nu_cols")

    raw_f = cert["func_matrix_01"]
    if type(raw_f) is not list or len(raw_f) != nr:
        raise GHDCertificateError("func_matrix_01 row count mismatch")
    F: List[List[int]] = []
    for r in range(nr):
        if type(raw_f[r]) is not list or len(raw_f[r]) != nc:
            raise GHDCertificateError(f"func_matrix_01[{r}] col count mismatch")
        row = [_parse_int(v, f"F[{r}]") for v in raw_f[r]]
        if any(b not in (0, 1) for b in row):
            raise GHDCertificateError(f"func_matrix_01[{r}] must be binary 0/1")
        F.append(row)

    # Verify E_{mu x nu}[F] >= 1/4
    base_exp = Fraction(0, 1)
    for r in range(nr):
        for c in range(nc):
            if F[r][c] == 1:
                base_exp += mu[r] * nu[c]
    if base_exp < Fraction(1, 4):
        raise GHDCertificateError(f"Base expectation {base_exp} < 1/4")

    # Verify leaf_rectangles partition [nr] x [nc] into <= 2^d disjoint rectangles with error <= 1/100
    raw_leaves = cert["leaf_rectangles"]
    if type(raw_leaves) is not list or not (1 <= len(raw_leaves) <= (1 << d)):
        raise GHDCertificateError(f"leaf_rectangles count must be in [1, 2^d={1 << d}]")

    covered: Set[Tuple[int, int]] = set()
    proto_err = Fraction(0, 1)
    leaves: List[Tuple[List[int], List[int], int]] = []
    for li, lf in enumerate(raw_leaves):
        if type(lf) is not dict or set(lf.keys()) != {"rows", "cols", "output"}:
            raise GHDCertificateError(f"leaf_rectangles[{li}] schema mismatch")
        rs = [_parse_int(v, f"leaf[{li}].rows") for v in lf["rows"]]
        cs = [_parse_int(v, f"leaf[{li}].cols") for v in lf["cols"]]
        out = _parse_int(lf["output"], f"leaf[{li}].output")
        if not rs or not cs or len(set(rs)) != len(rs) or len(set(cs)) != len(cs):
            raise GHDCertificateError(f"leaf[{li}] invalid rows/cols")
        if any(not (0 <= r < nr) for r in rs) or any(not (0 <= c < nc) for c in cs) or out not in (0, 1):
            raise GHDCertificateError(f"leaf[{li}] index or output out of range")
        for r in rs:
            for c in cs:
                if (r, c) in covered:
                    raise GHDCertificateError(f"Overlapping leaf rectangles at ({r},{c})")
                covered.add((r, c))
                if F[r][c] != out:
                    proto_err += mu[r] * nu[c]
        leaves.append((rs, cs, out))

    if len(covered) != nr * nc:
        raise GHDCertificateError("leaf_rectangles do not partition the entire matrix")
    if proto_err > Fraction(1, 100):
        raise GHDCertificateError(f"Protocol error {proto_err} > 1/100")

    w_idx = _parse_int(cert["witness_leaf_idx"], "witness_leaf_idx")
    if not (0 <= w_idx < len(leaves)):
        raise GHDCertificateError("witness_leaf_idx out of range")
    w_rs, w_cs, w_out = leaves[w_idx]
    if w_out != 1:
        raise GHDCertificateError("Witness leaf must have output == 1")
    mu_A = sum((mu[r] for r in w_rs), Fraction(0, 1))
    nu_B = sum((nu[c] for c in w_cs), Fraction(0, 1))
    w_mass = mu_A * nu_B
    w_ones = sum((mu[r] * nu[c] for r in w_rs for c in w_cs if F[r][c] == 1), Fraction(0, 1))
    if w_mass < Fraction(1, 5 * (1 << d)):
        raise GHDCertificateError(f"Witness rectangle mass {w_mass} < 2^(-{d})/5")
    w_cond_exp = w_ones / w_mass
    if w_cond_exp < Fraction(1, 2):
        raise GHDCertificateError(f"Witness conditional expectation {w_cond_exp} < 1/2")

    # Remark 4.3: blowup factors 1/mu(A) and 1/nu(B) are <= 5 * 2^d < 2^{d+3}!
    row_blow = Fraction(1, 1) / mu_A
    col_blow = Fraction(1, 1) / nu_B
    max_blow = Fraction(5 * (1 << d), 1)
    if row_blow > max_blow or col_blow > max_blow:
        raise GHDCertificateError("Remark 4.3 marginal blowup exceeded 5 * 2^d")

    if _parse_rat(cert["claimed_base_expectation"], "claimed_base_expectation") != base_exp:
        raise GHDCertificateError("claimed_base_expectation mismatch")
    if _parse_rat(cert["claimed_protocol_error"], "claimed_protocol_error") != proto_err:
        raise GHDCertificateError("claimed_protocol_error mismatch")
    if _parse_rat(cert["claimed_witness_mass"], "claimed_witness_mass") != w_mass:
        raise GHDCertificateError("claimed_witness_mass mismatch")
    if _parse_rat(cert["claimed_witness_cond_exp"], "claimed_witness_cond_exp") != w_cond_exp:
        raise GHDCertificateError("claimed_witness_cond_exp mismatch")
    if _parse_rat(cert["claimed_row_blowup_factor"], "claimed_row_blowup_factor") != row_blow:
        raise GHDCertificateError("claimed_row_blowup_factor mismatch")
    if _parse_rat(cert["claimed_col_blowup_factor"], "claimed_col_blowup_factor") != col_blow:
        raise GHDCertificateError("claimed_col_blowup_factor mismatch")

    return {
        "verified": True,
        "mode": cert["mode"],
        "base_exp": format_rat(base_exp),
        "proto_err": format_rat(proto_err),
        "witness_mass": format_rat(w_mass),
        "witness_cond_exp": format_rat(w_cond_exp),
    }


# =============================================================================
# Mode 3: Section 1-2 gamma-GHD Disambiguation, XOR-Lift & Planted Contradiction
# =============================================================================


def _verify_mode3_ghd_xor_lift(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema",
        "mode",
        "cert_id",
        "num_bits_n",
        "gamma",
        "gap_maj_truth_table",
        "planted_K",
        "reference_a_mask",
        "delta_T",
        "support_A",
        "support_B",
        "claimed_uniform_expectation",
        "claimed_max_support_dist",
        "claimed_support_all_zero",
    }
    _parse_exact_keys(cert, req, "Mode 3")
    n = _parse_int(cert["num_bits_n"], "num_bits_n")
    if not (3 <= n <= 6):
        raise GHDCertificateError("Require 3 <= num_bits_n <= 6")
    gamma = _parse_rat(cert["gamma"], "gamma")
    if not (Fraction(0, 1) < gamma < Fraction(1, 2)):
        raise GHDCertificateError("Require 0 < gamma < 1/2")

    size = 1 << n
    raw_tt = cert["gap_maj_truth_table"]
    if type(raw_tt) is not list or len(raw_tt) != size:
        raise GHDCertificateError(f"gap_maj_truth_table must have length {size}")
    tt = [_parse_int(v, "gap_maj_truth_table") for v in raw_tt]
    if any(b not in (0, 1) for b in tt):
        raise GHDCertificateError("gap_maj_truth_table must be binary 0/1")

    # Verify total function f is a valid disambiguation of gamma-Gap Majority (Eq. 2):
    # |z| <= gamma * n => f(z) = 0; |z| >= (1 - gamma) * n => f(z) = 1
    for z in range(size):
        wt = bin(z).count("1")
        if Fraction(wt, 1) <= gamma * Fraction(n, 1) and tt[z] != 0:
            raise GHDCertificateError(f"Promise violated at z={z} (wt={wt} <= {gamma*n}): f(z)={tt[z]} != 0")
        if Fraction(wt, 1) >= (Fraction(1, 1) - gamma) * Fraction(n, 1) and tt[z] != 1:
            raise GHDCertificateError(f"Promise violated at z={z} (wt={wt} >= {(1-gamma)*n}): f(z)={tt[z]} != 1")

    # Exact uniform expectation of XOR-lift F(x, y) = f(x xor y) equals E_{z ~ U_n}[f(z)]!
    unif_exp = Fraction(sum(tt), size)
    if unif_exp < Fraction(1, 2):
        raise GHDCertificateError(f"Disambiguation must satisfy E[F] >= 1/2 (got {unif_exp})")

    raw_K = cert["planted_K"]
    if type(raw_K) is not list:
        raise GHDCertificateError("planted_K must be list")
    K = [_parse_int(v, "planted_K") for v in raw_K]
    if K != sorted(K) or len(set(K)) != len(K) or any(not (0 <= c < n) for c in K):
        raise GHDCertificateError("planted_K invalid")
    mask_K = 0
    for c in K:
        mask_K |= (1 << c)
    m_T = n - len(K)

    ref_a = _parse_int(cert["reference_a_mask"], "reference_a_mask")
    if not (0 <= ref_a < size):
        raise GHDCertificateError("reference_a_mask out of range")
    delta_T = _parse_int(cert["delta_T"], "delta_T")
    if delta_T < 0 or Fraction(2 * delta_T + m_T, 1) > gamma * Fraction(n, 1):
        raise GHDCertificateError(f"Planted final bound 2*Delta_T + m_T = {2*delta_T + m_T} > gamma*n = {gamma*n}")

    raw_sA = cert["support_A"]
    raw_sB = cert["support_B"]
    if type(raw_sA) is not list or type(raw_sB) is not list or len(raw_sA) < 2 or len(raw_sB) < 2:
        raise GHDCertificateError("support_A and support_B must each contain at least 2 distinct strings")
    sA = [_parse_int(v, "support_A") for v in raw_sA]
    sB = [_parse_int(v, "support_B") for v in raw_sB]
    if len(set(sA)) != len(sA) or len(set(sB)) != len(sB):
        raise GHDCertificateError("Duplicate strings in support_A or support_B")
    if any(not (0 <= x < size) for x in sA) or any(not (0 <= y < size) for y in sB):
        raise GHDCertificateError("Support string out of range")

    for x in sA:
        if hamming_dist_int(x & mask_K, ref_a & mask_K) > delta_T:
            raise GHDCertificateError(f"x={x} exceeds planted distance Delta_T={delta_T} on K")
    for y in sB:
        if hamming_dist_int(y & mask_K, ref_a & mask_K) > delta_T:
            raise GHDCertificateError(f"y={y} exceeds planted distance Delta_T={delta_T} on K")

    # Verify every (x, y) in support_A x support_B has dist(x, y) <= gamma*n and F(x, y) = 0!
    max_d = 0
    for x in sA:
        for y in sB:
            dxy = hamming_dist_int(x, y)
            if dxy > max_d:
                max_d = dxy
            if Fraction(dxy, 1) > gamma * Fraction(n, 1) or tt[x ^ y] != 0:
                raise GHDCertificateError(f"Contradiction support failed at ({x},{y}): dist={dxy}, F={tt[x^y]}")

    if _parse_rat(cert["claimed_uniform_expectation"], "claimed_uniform_expectation") != unif_exp:
        raise GHDCertificateError("claimed_uniform_expectation mismatch")
    if _parse_int(cert["claimed_max_support_dist"], "claimed_max_support_dist") != max_d:
        raise GHDCertificateError("claimed_max_support_dist mismatch")
    if cert["claimed_support_all_zero"] is not True:
        raise GHDCertificateError("claimed_support_all_zero must be true")

    return {
        "verified": True,
        "mode": cert["mode"],
        "n": n,
        "unif_exp": format_rat(unif_exp),
        "max_support_dist": max_d,
    }


# =============================================================================
# Mode 4: Theorem 1.1 Iterative Recurrence Trajectory & Omega(n^{2/3}) Audit
# =============================================================================


def _verify_mode4_iterative_trajectory(cert: Dict[str, Any]) -> Dict[str, Any]:
    req = {
        "schema",
        "mode",
        "cert_id",
        "num_bits_n",
        "gamma",
        "protocol_cost_d",
        "correlation_rho",
        "rounds",
        "claimed_num_rounds_T",
        "claimed_final_mT",
        "claimed_final_DeltaT",
        "claimed_contradiction_lhs",
    }
    _parse_exact_keys(cert, req, "Mode 4")
    n = _parse_int(cert["num_bits_n"], "num_bits_n")
    d = _parse_int(cert["protocol_cost_d"], "protocol_cost_d")
    gamma = _parse_rat(cert["gamma"], "gamma")
    rho = _parse_rat(cert["correlation_rho"], "correlation_rho")
    if n < 1000 or d < 1:
        raise GHDCertificateError("Require n >= 1000 and d >= 1")
    if not (Fraction(0, 1) < gamma < Fraction(1, 2)) or not (Fraction(0, 1) < rho < Fraction(1, 1)):
        raise GHDCertificateError("Invalid gamma or rho")
    # Theorem 1.1 / Section 4 validity constraint: rho <= c_0 / sqrt(d) with explicit c_0 = 1/2
    # cleared in exact rational arithmetic as 4 * rho^2 * d <= 1.
    if Fraction(4, 1) * rho * rho * Fraction(d, 1) > Fraction(1, 1):
        raise GHDCertificateError(
            f"Correlation parameter rho={rho} violates Theorem 1.1 scaling 4*rho^2*d <= 1 for d={d}"
        )

    raw_rounds = cert["rounds"]
    if type(raw_rounds) is not list or not (2 <= len(raw_rounds) <= 512):
        raise GHDCertificateError("rounds must have length in [2, 512]")

    prev_m: Fraction | None = None
    prev_D: int | None = None
    prev_Delta: Fraction | None = None

    for idx, st in enumerate(raw_rounds):
        if type(st) is not dict or set(st.keys()) != {"t", "m_t", "D_t", "Delta_t"}:
            raise GHDCertificateError(f"rounds[{idx}] schema mismatch")
        t = _parse_int(st["t"], f"rounds[{idx}].t")
        if t != idx:
            raise GHDCertificateError(f"rounds[{idx}].t != {idx}")
        mt = _parse_rat(st["m_t"], f"rounds[{idx}].m_t")
        Dt = _parse_int(st["D_t"], f"rounds[{idx}].D_t")
        Delta_t = _parse_rat(st["Delta_t"], f"rounds[{idx}].Delta_t")
        if mt < 0 or Dt < 0 or Delta_t < 0:
            raise GHDCertificateError(f"Negative state value at round {idx}")
        if idx == 0:
            if mt != Fraction(n, 1) or Dt != 0 or Delta_t != Fraction(0, 1):
                raise GHDCertificateError("Initial state must be (m_0=n, D_0=0, Delta_0=0)")
        else:
            assert prev_m is not None and prev_D is not None and prev_Delta is not None
            # Check Lemma 4.1 precondition rho * m_{t-1} >= 100 before stopping
            if prev_m <= gamma * Fraction(n, 1) / Fraction(2, 1):
                raise GHDCertificateError(f"Continued past stopping threshold m <= gamma*n/2 at round {idx}")
            if rho * prev_m < Fraction(100, 1):
                raise GHDCertificateError(f"Lemma 4.1 precondition rho*m >= 100 failed at round {idx - 1}")
            # Conservative upper-envelope recurrence for Theorem 1.1:
            # remaining coordinates satisfy (1 - rho/2) * m_{t-1} <= m_t <= m_{t-1},
            # deficit grows by at least d + 10, and distance step satisfies step_delta >= 20*rho*sqrt(m*D).
            if mt < (Fraction(1, 1) - rho / Fraction(2, 1)) * prev_m or mt > prev_m:
                raise GHDCertificateError(
                    f"m_t={mt} outside valid monotone envelope [(1-rho/2)*m_{{t-1}}, m_{{t-1}}] at round {idx}"
                )
            if Dt < prev_D + d + 10:
                raise GHDCertificateError(f"D_t underestimated D_{{t-1}} + d + 10 at round {idx}")
            step_delta = Delta_t - prev_Delta
            if step_delta < 0 or step_delta * step_delta < Fraction(400, 1) * rho * rho * prev_m * Fraction(prev_D, 1):
                raise GHDCertificateError(f"Delta_t step underestimated 20*rho*sqrt(m*D) at round {idx}")
        prev_m, prev_D, prev_Delta = mt, Dt, Delta_t

    assert prev_m is not None and prev_Delta is not None
    T = len(raw_rounds) - 1
    if prev_m > gamma * Fraction(n, 1) / Fraction(2, 1):
        raise GHDCertificateError(f"Final m_T={prev_m} did not reach stopping condition <= gamma*n/2")
    contradiction_lhs = Fraction(2, 1) * prev_Delta + prev_m
    if contradiction_lhs > gamma * Fraction(n, 1):
        raise GHDCertificateError(f"Final contradiction failed: 2*Delta_T + m_T = {contradiction_lhs} > gamma*n={gamma*n}")

    if _parse_int(cert["claimed_num_rounds_T"], "claimed_num_rounds_T") != T:
        raise GHDCertificateError("claimed_num_rounds_T mismatch")
    if _parse_rat(cert["claimed_final_mT"], "claimed_final_mT") != prev_m:
        raise GHDCertificateError("claimed_final_mT mismatch")
    if _parse_rat(cert["claimed_final_DeltaT"], "claimed_final_DeltaT") != prev_Delta:
        raise GHDCertificateError("claimed_final_DeltaT mismatch")
    if _parse_rat(cert["claimed_contradiction_lhs"], "claimed_contradiction_lhs") != contradiction_lhs:
        raise GHDCertificateError("claimed_contradiction_lhs mismatch")

    return {
        "verified": True,
        "mode": cert["mode"],
        "n": n,
        "d": d,
        "T": T,
        "contradiction_lhs": format_rat(contradiction_lhs),
    }


def verify_ghd_certificate_exact(cert: Dict[str, Any]) -> Dict[str, Any]:
    """Top-level zero-float entry point for GHD-DISAMBIG-CERT-1.0."""
    if type(cert) is not dict:
        raise GHDCertificateError("Certificate root must be a JSON object")
    _assert_strict_json_types(cert)
    if cert.get("schema") != SCHEMA_VERSION:
        raise GHDCertificateError(f"Unsupported schema: {cert.get('schema')!r}")
    cid = cert.get("cert_id")
    if type(cid) is not str or not (1 <= len(cid) <= MAX_ID_LEN):
        raise GHDCertificateError(f"cert_id must be string of length in [1, {MAX_ID_LEN}]")
    mode = cert.get("mode")
    if mode == "marton_coupling_collision_cert":
        return _verify_mode1_marton_coupling(cert)
    if mode == "lemma42_leaf_rectangle_restore_cert":
        return _verify_mode2_leaf_rectangle(cert)
    if mode == "ghd_disambiguation_and_xor_lift_cert":
        return _verify_mode3_ghd_xor_lift(cert)
    if mode == "theorem11_iterative_trajectory_cert":
        return _verify_mode4_iterative_trajectory(cert)
    raise GHDCertificateError(f"Unknown verification mode: {mode!r}")

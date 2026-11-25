"""Generate all 16 canonical GHD-DISAMBIG-CERT-1.0 certificates and 4 exact-Q
experimental studies for Paper 42: Dahiya, Goos, Harms, Hatami, Hatami, Lovett, & Yuan
(arXiv:2611.32837).

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import json
import sys
import time
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, List, Sequence

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.ghd_certifier import SCHEMA_VERSION, verify_ghd_certificate_exact
from src.ghd_exact import (
    collision_prob_marton_Z,
    format_rat,
    hamming_dist_int,
    marton_sequential_coupling_exact,
)

CERT_DIR = ROOT / "certificates"
DATA_DIR = ROOT / "data"


def _isqrt_ceil(n: int) -> int:
    """Exact integer ceil(sqrt(n)) for n >= 0 (zero floats)."""
    if n <= 0:
        return 0
    r = int(n)
    # Newton's method for floor(sqrt(n))
    x = 1 << ((n.bit_length() + 1) // 2)
    while True:
        y = (x + n // x) // 2
        if y >= x:
            break
        x = y
    return x if x * x == n else x + 1


def _rat_sqrt_upper(q: Fraction, scale_den: int = 16) -> Fraction:
    """Exact conservative rational upper bound >= sqrt(q) with denominator scale_den."""
    # Find smallest integer k such that (k / scale_den)^2 >= q = a / b <=> k^2 * b >= a * scale_den^2
    lhs_target = q.numerator * (scale_den * scale_den)
    # Need k^2 >= ceil(lhs_target / q.denominator)
    num_ceil = (lhs_target + q.denominator - 1) // q.denominator
    k = _isqrt_ceil(num_ceil)
    return Fraction(k, scale_den)


def _make_mode1(
    cert_id: str,
    m: int,
    mu: List[Fraction],
    D_int: int,
    subset_I: List[int],
    s_param: int,
) -> Dict[str, Any]:
    mu_inf = max(mu)
    joint, exp_dist, sum_ai_sq = marton_sequential_coupling_exact(mu, m)
    col_z, z_dist = collision_prob_marton_Z(joint, subset_I, m)
    k_I = len(subset_I)
    thresh = Fraction(1 << (D_int + s_param), 1 << (m - k_I))
    tail_prob = sum(
        (pz for (_, _), pz in z_dist.items() if pz * Fraction(1 << k_I, 1) > thresh),
        Fraction(0, 1),
    )
    return {
        "schema": SCHEMA_VERSION,
        "mode": "marton_coupling_collision_cert",
        "cert_id": cert_id,
        "num_bits_m": m,
        "mu_probs": [format_rat(p) for p in mu],
        "deficit_D_int": D_int,
        "subset_I": subset_I,
        "tail_param_s": s_param,
        "claimed_mu_inf": format_rat(mu_inf),
        "claimed_expected_dist": format_rat(exp_dist),
        "claimed_sum_ai_sq": format_rat(sum_ai_sq),
        "claimed_collision_Z": format_rat(col_z),
        "claimed_tail_prob": format_rat(tail_prob),
    }


def _make_mode2(
    cert_id: str,
    nr: int,
    nc: int,
    d: int,
    mu: List[Fraction],
    nu: List[Fraction],
    F: List[List[int]],
    leaves: List[Dict[str, Any]],
    w_idx: int,
) -> Dict[str, Any]:
    base_exp = sum((mu[r] * nu[c] for r in range(nr) for c in range(nc) if F[r][c] == 1), Fraction(0, 1))
    proto_err = Fraction(0, 1)
    for lf in leaves:
        for r in lf["rows"]:
            for c in lf["cols"]:
                if F[r][c] != lf["output"]:
                    proto_err += mu[r] * nu[c]
    wlf = leaves[w_idx]
    mu_A = sum((mu[r] for r in wlf["rows"]), Fraction(0, 1))
    nu_B = sum((nu[c] for c in wlf["cols"]), Fraction(0, 1))
    w_mass = mu_A * nu_B
    w_ones = sum((mu[r] * nu[c] for r in wlf["rows"] for c in wlf["cols"] if F[r][c] == 1), Fraction(0, 1))
    return {
        "schema": SCHEMA_VERSION,
        "mode": "lemma42_leaf_rectangle_restore_cert",
        "cert_id": cert_id,
        "num_rows": nr,
        "num_cols": nc,
        "protocol_cost_d": d,
        "mu_rows": [format_rat(p) for p in mu],
        "nu_cols": [format_rat(p) for p in nu],
        "func_matrix_01": F,
        "leaf_rectangles": leaves,
        "witness_leaf_idx": w_idx,
        "claimed_base_expectation": format_rat(base_exp),
        "claimed_protocol_error": format_rat(proto_err),
        "claimed_witness_mass": format_rat(w_mass),
        "claimed_witness_cond_exp": format_rat(w_ones / w_mass),
        "claimed_row_blowup_factor": format_rat(Fraction(1, 1) / mu_A),
        "claimed_col_blowup_factor": format_rat(Fraction(1, 1) / nu_B),
    }


def _make_mode3(
    cert_id: str,
    n: int,
    gamma: Fraction,
    tt: List[int],
    planted_K: List[int],
    ref_a: int,
    delta_T: int,
    sA: List[int],
    sB: List[int],
) -> Dict[str, Any]:
    unif_exp = Fraction(sum(tt), 1 << n)
    max_d = max(hamming_dist_int(x, y) for x in sA for y in sB)
    return {
        "schema": SCHEMA_VERSION,
        "mode": "ghd_disambiguation_and_xor_lift_cert",
        "cert_id": cert_id,
        "num_bits_n": n,
        "gamma": format_rat(gamma),
        "gap_maj_truth_table": tt,
        "planted_K": planted_K,
        "reference_a_mask": ref_a,
        "delta_T": delta_T,
        "support_A": sA,
        "support_B": sB,
        "claimed_uniform_expectation": format_rat(unif_exp),
        "claimed_max_support_dist": max_d,
        "claimed_support_all_zero": True,
    }


def _make_mode4(
    cert_id: str,
    n: int,
    gamma: Fraction,
    d: int,
    rho: Fraction,
) -> Dict[str, Any]:
    rounds = []
    mt = Fraction(n, 1)
    Dt = 0
    Delta_t = Fraction(0, 1)
    t = 0
    rounds.append({"t": 0, "m_t": format_rat(mt), "D_t": 0, "Delta_t": "0"})
    stop_thresh = gamma * Fraction(n, 1) / Fraction(2, 1)
    while mt > stop_thresh:
        # Exact conservative upper step: Delta_{t+1} = Delta_t + ceil_rat(20 * rho * sqrt(m_t * D_t))
        rad_sq = Fraction(400, 1) * rho * rho * mt * Fraction(Dt, 1)
        step = _rat_sqrt_upper(rad_sq, scale_den=8)
        Delta_t = Delta_t + step
        mt = (Fraction(1, 1) - rho / Fraction(2, 1)) * mt
        Dt = Dt + d + 10
        t += 1
        rounds.append({"t": t, "m_t": format_rat(mt), "D_t": Dt, "Delta_t": format_rat(Delta_t)})
    lhs = Fraction(2, 1) * Delta_t + mt
    return {
        "schema": SCHEMA_VERSION,
        "mode": "theorem11_iterative_trajectory_cert",
        "cert_id": cert_id,
        "num_bits_n": n,
        "gamma": format_rat(gamma),
        "protocol_cost_d": d,
        "correlation_rho": format_rat(rho),
        "rounds": rounds,
        "claimed_num_rounds_T": t,
        "claimed_final_mT": format_rat(mt),
        "claimed_final_DeltaT": format_rat(Delta_t),
        "claimed_contradiction_lhs": format_rat(lhs),
    }


def build_all_certificates() -> List[Dict[str, Any]]:
    certs: List[Dict[str, Any]] = []

    # =========================================================================
    # Mode 1: 4 canonical Lemma 3.1 Marton Coupling & Collision certificates
    # =========================================================================
    # 1a: m=3, D=1 biased product-like distribution, subset I=[0, 2]
    mu1a = [Fraction(1, 4), Fraction(1, 8), Fraction(1, 4), Fraction(1, 8),
            Fraction(1, 16), Fraction(1, 16), Fraction(1, 16), Fraction(1, 16)]
    certs.append(_make_mode1("m1_marton_m3_D1_biased", 3, mu1a, 1, [0, 2], 2))

    # 1b: m=4, D=2 correlated Markov-chain-like distribution, subset I=[1, 3]
    mu1b = [Fraction(1, 4) if x in (0, 15) else Fraction(1, 28) for x in range(16)]
    # Sum: 2/4 + 14/28 = 1! ||mu||_inf = 1/4 -> 16 * 1/4 = 4 = 2^2 (exact D=2!)
    certs.append(_make_mode1("m1_marton_m4_D2_correlated", 4, mu1b, 2, [1, 3], 3))

    # 1c: m=4, D=1 half-cube uniform (exact support size 8!), subset I=[0, 1]
    mu1c = [Fraction(1, 8) if bin(x).count("1") % 2 == 0 else Fraction(0, 1) for x in range(16)]
    certs.append(_make_mode1("m1_marton_m4_D1_even_parity", 4, mu1c, 1, [0, 1], 2))

    # 1d: m=5, D=2 skewed Hamming-ball distribution, subset I=[0, 2, 4]
    # Give weight 1/8 to x=0, 1/16 to weight-1 (5 strings -> 5/16), remaining 26 strings share 9/16 -> 9/416 each
    mu1d = []
    for x in range(32):
        w = bin(x).count("1")
        if w == 0:
            mu1d.append(Fraction(1, 8))
        elif w == 1:
            mu1d.append(Fraction(1, 16))
        else:
            mu1d.append(Fraction(9, 416))
    certs.append(_make_mode1("m1_marton_m5_D2_hamming_ball", 5, mu1d, 2, [0, 2, 4], 3))

    # =========================================================================
    # Mode 2: 4 canonical Lemma 4.2 & Remark 4.3 Protocol Leaf Rectangle certs
    # =========================================================================
    # 2a: 4x4, cost d=2 (4 leaves), exact zero-error protocol, base_exp = 3/8 >= 1/4
    mu2a = [Fraction(1, 4)] * 4
    nu2a = [Fraction(1, 4)] * 4
    F2a = [
        [1, 1, 0, 0],
        [1, 1, 0, 0],
        [0, 0, 1, 1],
        [0, 0, 0, 0],
    ]
    lf2a = [
        {"rows": [0, 1], "cols": [0, 1], "output": 1},
        {"rows": [0, 1], "cols": [2, 3], "output": 0},
        {"rows": [2], "cols": [2, 3], "output": 1},
        {"rows": [2], "cols": [0, 1], "output": 0},
    ]
    # Add row 3! Make 4 exact covering leaves:
    F2a = [
        [1, 1, 0, 0],
        [1, 1, 0, 0],
        [0, 0, 0, 0],
        [0, 0, 1, 1],
    ]
    lf2a = [
        {"rows": [0, 1], "cols": [0, 1], "output": 1},
        {"rows": [0, 1], "cols": [2, 3], "output": 0},
        {"rows": [2, 3], "cols": [0, 1], "output": 0},
        {"rows": [2, 3], "cols": [2, 3], "output": 1},  # has 2 ones + 2 zeros -> use row 2=1 too!
    ]
    F2a = [
        [1, 1, 0, 0],
        [1, 1, 0, 0],
        [0, 0, 1, 1],
        [0, 0, 1, 1],
    ]
    certs.append(_make_mode2("m2_leaf_4x4_d2_exact", 4, 4, 2, mu2a, nu2a, F2a, lf2a, 0))

    # 2b: 4x4, cost d=2, NON-ZERO protocol error = 1/100 (sharp boundary!), skewed mu x nu!
    # Put tiny mass 1/100 on (3,3) where F[3][3]=0 inside a 1-leaf!
    mu2b = [Fraction(3, 10), Fraction(3, 10), Fraction(3, 10), Fraction(1, 10)]
    nu2b = [Fraction(3, 10), Fraction(3, 10), Fraction(3, 10), Fraction(1, 10)]
    F2b = [
        [1, 1, 0, 0],
        [1, 1, 0, 0],
        [0, 0, 1, 1],
        [0, 0, 1, 0],  # single error cell (3,3) with mass 1/10 * 1/10 = 1/100 EXACT!
    ]
    certs.append(_make_mode2("m2_leaf_4x4_d2_sharp_err_1_100", 4, 4, 2, mu2b, nu2b, F2b, lf2a, 0))

    # 2c: 6x6, cost d=3 (6 leaves <= 8), base_exp just above 1/4!
    mu2c = [Fraction(1, 6)] * 6
    nu2c = [Fraction(1, 6)] * 6
    F2c = [[1 if (r < 3 and c < 3) or (r == 5 and c >= 4) else 0 for c in range(6)] for r in range(6)]
    # base_exp = (9 + 2)/36 = 11/36 > 1/4!
    lf2c = [
        {"rows": [0, 1, 2], "cols": [0, 1, 2], "output": 1},
        {"rows": [0, 1, 2], "cols": [3, 4, 5], "output": 0},
        {"rows": [3, 4], "cols": [0, 1, 2, 3, 4, 5], "output": 0},
        {"rows": [5], "cols": [0, 1, 2, 3], "output": 0},
        {"rows": [5], "cols": [4, 5], "output": 1},
    ]
    certs.append(_make_mode2("m2_leaf_6x6_d3_near_quarter", 6, 6, 3, mu2c, nu2c, F2c, lf2c, 0))

    # 2d: 8x8, cost d=3 (4 leaves), asymmetric rectangular partition
    mu2d = [Fraction(1, 8)] * 8
    nu2d = [Fraction(1, 8)] * 8
    F2d = [[1 if (r < 4 and c < 4) or (r >= 6 and c >= 6) else 0 for c in range(8)] for r in range(8)]
    lf2d = [
        {"rows": [0, 1, 2, 3], "cols": [0, 1, 2, 3], "output": 1},
        {"rows": [0, 1, 2, 3], "cols": [4, 5, 6, 7], "output": 0},
        {"rows": [4, 5], "cols": [0, 1, 2, 3, 4, 5, 6, 7], "output": 0},
        {"rows": [6, 7], "cols": [0, 1, 2, 3, 4, 5], "output": 0},
        {"rows": [6, 7], "cols": [6, 7], "output": 1},
    ]
    certs.append(_make_mode2("m2_leaf_8x8_d3_asymmetric", 8, 8, 3, mu2d, nu2d, F2d, lf2d, 0))

    # =========================================================================
    # Mode 3: 4 canonical Sec. 1-2 gamma-GHD XOR-Lift & Planted Contradiction certs
    # =========================================================================
    # Helper: standard threshold disambiguation f(z) = 1 iff |z| >= ceil(n/2) (E[f] >= 1/2!)
    def _thresh_tt(n: int) -> List[int]:
        thr = (n + 1) // 2
        return [1 if bin(z).count("1") >= thr else 0 for z in range(1 << n)]

    # 3a: n=4, gamma=1/3 (wt <= 4/3 -> 0, wt >= 8/3 -> 1), planted K=[0,1,2], m_T=1, Delta_T=0 -> 2*0+1=1 <= 4/3!
    certs.append(_make_mode3("m3_ghd_n4_gam1_3_planted", 4, Fraction(1, 3), _thresh_tt(4), [0, 1, 2], 0, 0, [0, 8], [0, 8]))

    # 3b: n=5, gamma=1/3 (wt <= 5/3 -> 0), K=[0,1,2,3], m_T=1, Delta_T=0 -> 1 <= 5/3!
    certs.append(_make_mode3("m3_ghd_n5_gam1_3_planted", 5, Fraction(1, 3), _thresh_tt(5), [0, 1, 2, 3], 5, 0, [5, 21], [5, 21]))

    # 3c: n=6, gamma=1/3 (wt <= 2 -> 0, wt >= 4 -> 1), K=[0,1,2,3,4,5], m_T=0, Delta_T=1 -> 2*1+0 = 2 <= 2 EXACT!
    sA3c = [0, 1, 2, 4, 8, 16, 32]  # all strings within Hamming ball radius 1 around 0!
    certs.append(_make_mode3("m3_ghd_n6_gam1_3_ball_radius1", 6, Fraction(1, 3), _thresh_tt(6), [0, 1, 2, 3, 4, 5], 0, 1, sA3c, sA3c))

    # 3d: n=6, gamma=2/5 (wt <= 12/5 = 2.4 -> 0, wt >= 18/5 = 3.6 -> 1), custom non-symmetric disambiguation
    # with E[f] > 1/2 (sets all wt=3 to 1!), K=[0,1,2,3,4,5], Delta_T=1 -> max dist 2 <= 12/5!
    tt3d = [1 if bin(z).count("1") >= 3 else 0 for z in range(64)]
    certs.append(_make_mode3("m3_ghd_n6_gam2_5_nonsym_disambig", 6, Fraction(2, 5), tt3d, [0, 1, 2, 3, 4, 5], 63, 1, [63, 62, 61, 59], [63, 62, 55, 47]))

    # =========================================================================
    # Mode 4: 4 canonical Theorem 1.1 Omega(n^{2/3}) Iterative Trajectory certs
    # =========================================================================
    # Check parameters so rho*m >= 100 before stopping AND 2*Delta_T + m_T <= gamma*n!
    # At d=4, rho=1/4, gamma=1/3: T ~ 14 rounds; Delta_T ~ 20*(1/4)*sqrt(n*14*14)*14 ~ 5*14*14*sqrt(n) ~ 980*sqrt(n)!
    # Need 2*Delta_T <= n/6 => 1960*sqrt(n) <= n/6 => sqrt(n) >= 12000 => n >= 1.5e8!
    # Exact Fractions handle n = 10^9 effortlessly in < 1 ms!
    certs.append(_make_mode4("m4_traj_gam1_3_d4_n5e8", 500_000_000, Fraction(1, 3), 4, Fraction(1, 4)))
    certs.append(_make_mode4("m4_traj_gam1_3_d9_n2e9", 2_000_000_000, Fraction(1, 3), 9, Fraction(1, 6)))
    certs.append(_make_mode4("m4_traj_gam1_4_d4_n2e9", 2_000_000_000, Fraction(1, 4), 4, Fraction(1, 4)))
    certs.append(_make_mode4("m4_traj_gam2_5_d16_n5e9", 5_000_000_000, Fraction(2, 5), 16, Fraction(1, 8)))

    return certs


def run_experiments() -> None:
    CERT_DIR.mkdir(parents=True, exist_ok=True)
    DATA_DIR.mkdir(parents=True, exist_ok=True)

    certs = build_all_certificates()
    replay_rows: List[Dict[str, Any]] = []
    for cert in certs:
        out_path = CERT_DIR / f"{cert['cert_id']}.json"
        out_path.write_text(json.dumps(cert, indent=2) + "\n", encoding="utf-8")
        verify_ghd_certificate_exact(cert)
        times_ms: List[float] = []
        res: Dict[str, Any] = {}
        for _ in range(5):
            t0 = time.perf_counter()
            res = verify_ghd_certificate_exact(cert)
            times_ms.append((time.perf_counter() - t0) * 1000.0)
        times_ms.sort()
        replay_rows.append(
            {
                "cert_id": cert["cert_id"],
                "mode": cert["mode"],
                "verify_ms": round(times_ms[2], 3),
                "summary": res,
            }
        )

    (DATA_DIR / "certificate_replay_summary.json").write_text(
        json.dumps({"count": len(replay_rows), "certificates": replay_rows}, indent=2) + "\n",
        encoding="utf-8",
    )

    # Exp 1: Marton Coupling Collision Headroom col(Z) / ||mu||_inf across Mode 1 certs
    exp1_rows = []
    for c in certs:
        if c["mode"] == "marton_coupling_collision_cert":
            mu_inf = Fraction(c["claimed_mu_inf"])
            col_z = Fraction(c["claimed_collision_Z"])
            exp_d = Fraction(c["claimed_expected_dist"])
            m = c["num_bits_m"]
            D = c["deficit_D_int"]
            exp1_rows.append(
                {
                    "cert_id": c["cert_id"],
                    "m": m,
                    "D": D,
                    "col_to_muinf_ratio": round(float(col_z / mu_inf), 6),
                    "dist_sq_to_mD_ratio": round(float((exp_d * exp_d) / Fraction(m * D, 1)), 6),
                }
            )
    (DATA_DIR / "exp1_marton_coupling_headroom.json").write_text(
        json.dumps({"rows": exp1_rows}, indent=2) + "\n", encoding="utf-8"
    )

    # Exp 2: Theorem 1.1 Iterative Round Profile for m4_traj_gam1_3_d4_n5e8
    c4a = next(c for c in certs if c["cert_id"] == "m4_traj_gam1_3_d4_n5e8")
    n4a = c4a["num_bits_n"]
    exp2_rows = []
    for st in c4a["rounds"]:
        mt_f = float(Fraction(st["m_t"])) / n4a
        dt_f = float(Fraction(st["Delta_t"])) / n4a
        exp2_rows.append(
            {
                "t": st["t"],
                "m_over_n": round(mt_f, 6),
                "two_Delta_over_n": round(2.0 * dt_f, 6),
                "sum_over_n": round(mt_f + 2.0 * dt_f, 6),
                "D_t": st["D_t"],
            }
        )
    (DATA_DIR / "exp2_iterative_round_trajectory.json").write_text(
        json.dumps({"n": n4a, "gamma": "1/3", "d": 4, "rho": "1/4", "rows": exp2_rows}, indent=2) + "\n",
        encoding="utf-8",
    )

    # Exp 3: Communication Complexity Separation: O(1) vs Gavinsky n^{1/2} vs Dahiya et al. n^{2/3}
    exp3_rows = []
    for p in range(1, 7):
        n_val = 64 ** p  # exact 6th power so n^{1/2} and n^{2/3} are exact integers!
        exp3_rows.append(
            {
                "n": n_val,
                "randomized_O1": 1,
                "gavinsky_sqrt_n": 8 ** p,
                "dahiya_n_2_3": 16 ** p,
                "gain_factor": 2 ** p,
            }
        )
    (DATA_DIR / "exp3_pseudodet_comm_separation.json").write_text(
        json.dumps({"rows": exp3_rows}, indent=2) + "\n", encoding="utf-8"
    )

    # Exp 4: Lemma 4.2 Witness Rectangle Mass vs 2^{-d}/5 Floor
    exp4_rows = []
    for c in certs:
        if c["mode"] == "lemma42_leaf_rectangle_restore_cert":
            d_val = c["protocol_cost_d"]
            w_mass = float(Fraction(c["claimed_witness_mass"]))
            floor_val = 1.0 / (5 * (1 << d_val))
            exp4_rows.append(
                {
                    "cert_id": c["cert_id"],
                    "d": d_val,
                    "witness_mass": round(w_mass, 6),
                    "lemma42_floor": round(floor_val, 6),
                    "cond_exp": round(float(Fraction(c["claimed_witness_cond_exp"])), 6),
                }
            )
    (DATA_DIR / "exp4_leaf_rectangle_headroom.json").write_text(
        json.dumps({"rows": exp4_rows}, indent=2) + "\n", encoding="utf-8"
    )

    print(f"Generated {len(certs)} canonical GHD-DISAMBIG-CERT-1.0 certificates and 4 experiment JSONs.")
    for r in replay_rows:
        print(f"  {r['cert_id']:38s}  {r['verify_ms']:6.3f} ms  ({r['mode']})")


if __name__ == "__main__":
    run_experiments()

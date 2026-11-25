"""Pure-stdlib zero-floating-point exact-Q primitives for Paper 42:
Yogesh Dahiya, Mika Goos, Nathaniel Harms, Hamed Hatami, Pooya Hatami,
Shachar Lovett, & Weiqiang Yuan (arXiv:2611.32837, Nov 24, 2026)
"Communication Complexity of Disambiguations of Gap Hamming Distance".

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

from fractions import Fraction
from typing import Dict, List, Sequence, Tuple


def format_rat(q: Fraction) -> str:
    """Canonical reduced rational string ('n' if denominator == 1 else 'n/d')."""
    if q.denominator == 1:
        return str(q.numerator)
    return f"{q.numerator}/{q.denominator}"


def hamming_dist_int(x: int, y: int) -> int:
    """Exact Hamming distance between two bitmasks x, y."""
    return bin(x ^ y).count("1")


def marton_sequential_coupling_exact(
    mu: Sequence[Fraction],
    m: int,
) -> Tuple[Dict[Tuple[int, int], Fraction], Fraction, Fraction]:
    """Exact rational construction of Marton's sequential maximal coupling (Lemma 3.1)
    of distribution mu on {0,1}^m (representing {+1,-1}^m) with uniform U_m!
    At coordinate i (0..m-1, LSB-first prefix):
      Given prefix x_{<i} with conditional Pr[X_i = 0 | x_{<i}] = p0 and p1 = 1 - p0,
      Marton's threshold coupling T_i ~ Unif[-1,1] yields exact joint bit probabilities:
        P(X_i=0, U_i=0 | x_{<i}) = min(p0, 1/2)
        P(X_i=1, U_i=1 | x_{<i}) = min(p1, 1/2)
        P(X_i=0, U_i=1 | x_{<i}) = max(0, p0 - 1/2)
        P(X_i=1, U_i=0 | x_{<i}) = max(0, p1 - 1/2)
    Returns (joint_dict {(x, u): prob}, expected_hamming_dist, sum_E_ai_sq)."""
    size = 1 << m
    assert len(mu) == size

    # Precompute prefix probabilities P(X_{<i} = pref)
    joint: Dict[Tuple[int, int], Fraction] = {(0, 0): Fraction(1, 1)}
    exp_dist = Fraction(0, 1)
    sum_ai_sq = Fraction(0, 1)

    for i in range(m):
        # Compute prefix marginal mass for each prefix of length i
        pref_mass: Dict[int, Fraction] = {}
        pref_bit0: Dict[int, Fraction] = {}
        mask_pref = (1 << i) - 1
        for x in range(size):
            px = mu[x]
            if px == 0:
                continue
            pr = x & mask_pref
            pref_mass[pr] = pref_mass.get(pr, Fraction(0, 1)) + px
            if ((x >> i) & 1) == 0:
                pref_bit0[pr] = pref_bit0.get(pr, Fraction(0, 1)) + px

        # Compute E[|a_i|]/2 and E[a_i^2] at coordinate i
        for pr, pm in pref_mass.items():
            p0 = pref_bit0.get(pr, Fraction(0, 1)) / pm
            ai = Fraction(2, 1) * p0 - Fraction(1, 1)  # in [-1, 1]
            exp_dist += pm * abs(ai) / Fraction(2, 1)
            sum_ai_sq += pm * ai * ai

        next_joint: Dict[Tuple[int, int], Fraction] = {}
        half = Fraction(1, 2)
        for (x_pr, u_pr), prob in joint.items():
            if prob == 0:
                continue
            pm = pref_mass.get(x_pr, Fraction(0, 1))
            if pm == 0:
                continue
            p0 = pref_bit0.get(x_pr, Fraction(0, 1)) / pm
            p1 = Fraction(1, 1) - p0
            trans = [
                (0, 0, min(p0, half)),
                (1, 1, min(p1, half)),
                (0, 1, max(Fraction(0, 1), p0 - half)),
                (1, 0, max(Fraction(0, 1), p1 - half)),
            ]
            for bx, bu, tp in trans:
                if tp > 0:
                    key = (x_pr | (bx << i), u_pr | (bu << i))
                    next_joint[key] = next_joint.get(key, Fraction(0, 1)) + prob * tp
        joint = next_joint

    return joint, exp_dist, sum_ai_sq


def collision_prob_marton_Z(
    joint: Dict[Tuple[int, int], Fraction],
    coord_I: Sequence[int],
    m: int,
) -> Tuple[Fraction, Dict[Tuple[int, int], Fraction]]:
    """Compute exact distribution & collision probability col(Z) of Z = (U_I, X_{bar I})."""
    mask_I = 0
    for idx in coord_I:
        mask_I |= (1 << idx)
    mask_not_I = ((1 << m) - 1) ^ mask_I

    z_dist: Dict[Tuple[int, int], Fraction] = {}
    for (x, u), p in joint.items():
        if p == 0:
            continue
        key = (u & mask_I, x & mask_not_I)
        z_dist[key] = z_dist.get(key, Fraction(0, 1)) + p

    col = sum((p * p for p in z_dist.values()), Fraction(0, 1))
    return col, z_dist

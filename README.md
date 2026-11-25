# Certified Verification of Communication Complexity Disambiguations of Gap Hamming Distance

[![License: MIT](https://img.shields.io/badge/Code%20%26%20Lean-MIT-blue.svg)](LICENSE)
[![Paper License: CC-BY-4.0](https://img.shields.io/badge/Paper-CC--BY--4.0-green.svg)](paper/main.tex)

**Author:** Lluis Eriksson

Machine-checked **Lean 4.35.0** formalization and zero-floating-point exact-$\mathbb{Q}$ certificate audit (`GHD-DISAMBIG-CERT-1.0`) for the breakthrough $\Omega(n^{2/3})$ randomized vs. pseudo-deterministic communication complexity separation for disambiguations of Gap Hamming Distance by **Yogesh Dahiya, Mika Göös, Nathaniel Harms, Hamed Hatami, Pooya Hatami, Shachar Lovett, & Weiqiang Yuan** ([arXiv:2611.32837](https://arxiv.org/abs/2611.32837), Nov 24, 2026).

---

## Key Verified Artifacts

| Artifact | Verification Metric | Result |
| :--- | :--- | :--- |
| **Lean 4.35.0 Kernel** (`lean/GapHammingDisambig.lean`) | 18 theorems, zero `sorry`, zero warnings, zero `Classical.choice` | **18 / 18 PASS** (`4` `none`, `2` `[propext]`, `12` `[propext, Quot.sound]`) |
| **Exact-$\mathbb{Q}$ Verifier** (`src/ghd_certifier.py`) | Zero `float()`, `math`, or `numpy`; 4-mode `GHD-DISAMBIG-CERT-1.0` | **16 / 16 PASS** (`0.104–2.537 ms`) |
| **Adversarial Red-Team Suite** (`tests/test_suite.py`) | 63 live forged payloads (13 global + 12–13/mode) | **63 / 63 REJECTED** |
| **SHA-256 Integrity Manifest** (`SHA256_MANIFEST.json`) | Full deterministic replay check (`scripts/verify_all.py`) | **41 / 41 MATCH** |
| **Manuscript** (`paper/main.pdf`) | 3 pages, 3 publication figures (`300 DPI`) | **0 warnings, 0 overfulls** |

---

## Four Certificate Modes (`GHD-DISAMBIG-CERT-1.0`)

1. **`marton_coupling_collision_cert` (Mode 1 — Lemma 3.1):** Independently constructs Marton's sequential uniform coupling $(X, U)$ over $\mathbb{Q}$, verifies exact marginals $X \sim \mu$ and $U \sim U_m$, $\mathbb{E}[\operatorname{dist}(X, U)]^2 \le m D$, exact collision inequality $\operatorname{col}(Z) \le \|\mu\|_\infty$ (Eq. 5), and Markov tail $\Pr[\nu_{U_I}(X_{\bar{I}}) > 2^{D+s}/2^{m-|I|}] \le 2^{-s}$.
2. **`lemma42_leaf_rectangle_restore_cert` (Mode 2 — Lemma 4.2 & Remark 4.3):** Audits exact $2^d$-leaf rectangle partitions of binary matrices with $\mathbb{E}_{\mu\times\nu}[F] \ge 1/4$ and protocol error $\le 1/100$, certifying a witness leaf $A^* \times B^*$ with mass $\ge 2^{-d}/5$, conditional expectation $\ge 1/2$, and Remark 4.3 marginal blowups $1/\mu(A^*), 1/\nu(B^*) \le 5 \cdot 2^d < 2^{d+3}$.
3. **`ghd_disambiguation_and_xor_lift_cert` (Mode 3 — Sec. 1–2):** Certifies total Boolean disambiguations of $\gamma$-Gap Majority / XOR-lift $\gamma$-GHD with $\mathbb{E}[F] \ge 1/2$ and exact planted-coordinate contradiction supports $A \times B$ where every pair $(x,y)$ satisfies $\operatorname{dist}(x,y) \le 2\Delta_T + m_T \le \gamma n$ and $F(x,y) = 0$.
4. **`theorem11_iterative_trajectory_cert` (Mode 4 — Theorem 1.1):** Replays exact rational multi-round planting recurrences $(m_t, D_t, \Delta_t)$ with step shrinkage $(1 - \rho/2)$, deficit growth $D_{t+1} = D_t + d + 10$, and exact terminal contradiction $2\Delta_T + m_T \le \gamma n$ certifying the $\Omega(n^{2/3})$ exponent balance.

---

## Quick Reproduction

```bash
# 1. Verify Lean 4.35.0 kernel & axioms
cd lean && lake build && lake env lean AuditAxioms.lean && cd ..

# 2. Regenerate certificates, data, figures, and run full verification + 60-attack red team
python scripts/run_all_experiments.py
python scripts/make_figures.py
python scripts/verify_all.py
```

---

## Licenses & Transparency Disclosure

- **Code, Lean proofs, certificates, and scripts:** [MIT License](LICENSE).
- **Manuscript (`paper/main.tex`, `paper/main.pdf`) and figures:** CC-BY-4.0.
- **AI Assistance Disclosure:** Prepared by sole author Lluis Eriksson with AI coding, formalization, and drafting assistance from Google Antigravity; all Lean proofs, exact-$\mathbb{Q}$ certificates, and adversarial tests were independently compiled and machine-verified locally.

"""Comprehensive pytest & 60-attack live adversarial red-team suite for Paper 42:
GHD-DISAMBIG-CERT-1.0 (Dahiya et al., arXiv:2611.32837).

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import copy
import json
import sys
from pathlib import Path
from typing import Any, Callable, Dict, List, Tuple

ROOT = Path(__file__).resolve().parent.parent
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.ghd_certifier import GHDCertificateError, verify_ghd_certificate_exact

CERT_DIR = ROOT / "certificates"


def _load(name: str) -> Dict[str, Any]:
    return json.loads((CERT_DIR / f"{name}.json").read_text(encoding="utf-8"))


def test_all_16_canonical_certificates_verify() -> None:
    paths = sorted(CERT_DIR.glob("*.json"))
    assert len(paths) == 16, f"Expected 16 certificates, found {len(paths)}"
    for p in paths:
        res = verify_ghd_certificate_exact(json.loads(p.read_text(encoding="utf-8")))
        assert res["verified"] is True


def _mut(base: Dict[str, Any], fn: Callable[[Dict[str, Any]], None]) -> Dict[str, Any]:
    c = copy.deepcopy(base)
    fn(c)
    return c


def build_60_adversarial_attacks() -> List[Tuple[str, Any]]:
    m1 = _load("m1_marton_m3_D1_biased")
    m2 = _load("m2_leaf_4x4_d2_sharp_err_1_100")
    m3 = _load("m3_ghd_n6_gam1_3_ball_radius1")
    m4 = _load("m4_traj_gam1_3_d4_n5e8")

    attacks: List[Tuple[str, Any]] = [
        # --- Global Schema / Type / Rational Hardening (12 attacks) ---
        ("g01_non_dict_root", [1, 2, 3]),
        ("g02_wrong_schema", _mut(m1, lambda c: c.__setitem__("schema", "GHD-DISAMBIG-CERT-2.0"))),
        ("g03_empty_cert_id", _mut(m1, lambda c: c.__setitem__("cert_id", ""))),
        ("g04_unknown_mode", _mut(m1, lambda c: c.__setitem__("mode", "bogus"))),
        ("g05_float_leak", _mut(m1, lambda c: c["mu_probs"].__setitem__(0, 0.25))),
        ("g06_none_injection", _mut(m1, lambda c: c.__setitem__("num_bits_m", None))),
        ("g07_bool_as_int", _mut(m1, lambda c: c.__setitem__("deficit_D_int", True))),
        ("g08_unreduced_fraction", _mut(m1, lambda c: c["mu_probs"].__setitem__(0, "2/8"))),
        ("g09_den_one_fraction", _mut(m4, lambda c: c["rounds"][0].__setitem__("Delta_t", "0/1"))),
        ("g10_neg_zero_rat", _mut(m4, lambda c: c["rounds"][0].__setitem__("Delta_t", "-0"))),
        ("g11_oversized_rat_str", _mut(m3, lambda c: c.__setitem__("gamma", "1/" + "9" * 1200))),
        ("g12_huge_int_bitlen", _mut(m4, lambda c: c.__setitem__("num_bits_n", 1 << 3000))),
        ("g13_json_depth_dos", _mut(m1, lambda c: c.__setitem__("mu_probs", eval("[" * 40 + "0" + "]" * 40)))),
        # --- Mode 1: Lemma 3.1 Marton Coupling & Collision (12 attacks) ---
        ("m1_01_extra_key", _mut(m1, lambda c: c.__setitem__("extra", 1))),
        ("m1_02_mu_not_sum_one", _mut(m1, lambda c: c["mu_probs"].__setitem__(0, "1/2"))),
        ("m1_03_mu_negative", _mut(m1, lambda c: (c["mu_probs"].__setitem__(0, "-1/4"), c["mu_probs"].__setitem__(1, "5/8")))),
        ("m1_04_deficit_too_small", _mut(m1, lambda c: c.__setitem__("deficit_D_int", 0))),
        ("m1_05_unsorted_subset_I", _mut(m1, lambda c: c.__setitem__("subset_I", [2, 0]))),
        ("m1_06_subset_I_out_of_range", _mut(m1, lambda c: c.__setitem__("subset_I", [0, 5]))),
        ("m1_07_tail_s_zero", _mut(m1, lambda c: c.__setitem__("tail_param_s", 0))),
        ("m1_08_wrong_mu_inf", _mut(m1, lambda c: c.__setitem__("claimed_mu_inf", "1/8"))),
        ("m1_09_wrong_exp_dist", _mut(m1, lambda c: c.__setitem__("claimed_expected_dist", "0"))),
        ("m1_10_wrong_sum_ai_sq", _mut(m1, lambda c: c.__setitem__("claimed_sum_ai_sq", "0"))),
        ("m1_11_wrong_collision_Z", _mut(m1, lambda c: c.__setitem__("claimed_collision_Z", "3/16"))),
        ("m1_12_wrong_tail_prob", _mut(m1, lambda c: c.__setitem__("claimed_tail_prob", "1/2"))),
        # --- Mode 2: Lemma 4.2 & Remark 4.3 Protocol Leaf Rectangle (12 attacks) ---
        ("m2_01_extra_key", _mut(m2, lambda c: c.__setitem__("extra", 1))),
        ("m2_02_base_exp_below_quarter", _mut(m2, lambda c: c.__setitem__("func_matrix_01", [[0] * 4 for _ in range(4)]))),
        ("m2_03_too_many_leaves", _mut(m2, lambda c: c.__setitem__("protocol_cost_d", 1))),
        ("m2_04_overlapping_leaves", _mut(m2, lambda c: c["leaf_rectangles"][1]["cols"].append(0))),
        ("m2_05_incomplete_partition", _mut(m2, lambda c: c["leaf_rectangles"][3]["cols"].pop())),
        ("m2_06_proto_error_gt_1_100", _mut(m2, lambda c: c["func_matrix_01"][0].__setitem__(0, 0))),
        ("m2_07_witness_zero_output", _mut(m2, lambda c: c.__setitem__("witness_leaf_idx", 1))),
        ("m2_08_wrong_base_exp", _mut(m2, lambda c: c.__setitem__("claimed_base_expectation", "1/2"))),
        ("m2_09_wrong_proto_err", _mut(m2, lambda c: c.__setitem__("claimed_protocol_error", "0"))),
        ("m2_10_wrong_witness_mass", _mut(m2, lambda c: c.__setitem__("claimed_witness_mass", "1/4"))),
        ("m2_11_wrong_cond_exp", _mut(m2, lambda c: c.__setitem__("claimed_witness_cond_exp", "1/2"))),
        ("m2_12_wrong_row_blowup", _mut(m2, lambda c: c.__setitem__("claimed_row_blowup_factor", "1"))),
        # --- Mode 3: Sec. 1-2 gamma-GHD XOR-Lift & Planted Contradiction (12 attacks) ---
        ("m3_01_extra_key", _mut(m3, lambda c: c.__setitem__("extra", 1))),
        ("m3_02_gamma_half", _mut(m3, lambda c: c.__setitem__("gamma", "1/2"))),
        ("m3_03_promise_zero_violated", _mut(m3, lambda c: c["gap_maj_truth_table"].__setitem__(0, 1))),
        ("m3_04_promise_one_violated", _mut(m3, lambda c: c["gap_maj_truth_table"].__setitem__(63, 0))),
        ("m3_05_unif_exp_below_half", _mut(m3, lambda c: c.__setitem__("gap_maj_truth_table", [1 if bin(z).count("1") >= 4 else 0 for z in range(64)]))),
        ("m3_06_planted_bound_exceeded", _mut(m3, lambda c: c.__setitem__("delta_T", 2))),
        ("m3_07_support_exceeds_delta", _mut(m3, lambda c: c["support_A"].append(63))),
        ("m3_08_empty_support_A", _mut(m3, lambda c: c.__setitem__("support_A", []))),
        ("m3_09_duplicate_support_B", _mut(m3, lambda c: c["support_B"].append(0))),
        ("m3_10_wrong_unif_exp", _mut(m3, lambda c: c.__setitem__("claimed_uniform_expectation", "1/2"))),
        ("m3_11_wrong_max_dist", _mut(m3, lambda c: c.__setitem__("claimed_max_support_dist", 1))),
        ("m3_12_all_zero_false", _mut(m3, lambda c: c.__setitem__("claimed_support_all_zero", False))),
        ("m3_13_singleton_support", _mut(m3, lambda c: (c.__setitem__("support_A", [0]), c.__setitem__("support_B", [0]), c.__setitem__("claimed_max_support_dist", 0)))),
        # --- Mode 4: Theorem 1.1 Iterative Recurrence Trajectory (12 attacks) ---
        ("m4_01_extra_key", _mut(m4, lambda c: c.__setitem__("extra", 1))),
        ("m4_02_n_too_small", _mut(m4, lambda c: c.__setitem__("num_bits_n", 100))),
        ("m4_03_bad_init_m0", _mut(m4, lambda c: c["rounds"][0].__setitem__("m_t", "100"))),
        ("m4_04_round_index_skip", _mut(m4, lambda c: c["rounds"][1].__setitem__("t", 2))),
        ("m4_05_m_shrunk_too_fast", _mut(m4, lambda c: c["rounds"][1].__setitem__("m_t", "1"))),
        ("m4_06_D_underestimated", _mut(m4, lambda c: c["rounds"][1].__setitem__("D_t", 1))),
        ("m4_07_Delta_underestimated", _mut(m4, lambda c: c["rounds"][2].__setitem__("Delta_t", "0"))),
        ("m4_08_stopped_too_early", _mut(m4, lambda c: (c["rounds"].pop(), c.__setitem__("claimed_num_rounds_T", c["claimed_num_rounds_T"] - 1)))),
        ("m4_09_wrong_T", _mut(m4, lambda c: c.__setitem__("claimed_num_rounds_T", 1))),
        ("m4_10_wrong_final_mT", _mut(m4, lambda c: c.__setitem__("claimed_final_mT", "0"))),
        ("m4_11_wrong_final_DeltaT", _mut(m4, lambda c: c.__setitem__("claimed_final_DeltaT", "0"))),
        ("m4_12_wrong_contradiction_lhs", _mut(m4, lambda c: c.__setitem__("claimed_contradiction_lhs", "0"))),
        ("m4_13_rho_violates_inv_sqrt_d", _mut(m4, lambda c: c.__setitem__("correlation_rho", "9/10"))),
    ]
    assert len(attacks) == 63
    return attacks


def test_63_live_adversarial_attacks_rejected() -> None:
    attacks = build_60_adversarial_attacks()
    rejected = 0
    for name, payload in attacks:
        try:
            verify_ghd_certificate_exact(payload)
        except GHDCertificateError:
            rejected += 1
        else:
            raise AssertionError(f"Adversarial attack {name!r} was NOT rejected!")
    assert rejected == 63


def test_exact_no_float_source_audit() -> None:
    for rel in ["src/ghd_exact.py", "src/ghd_certifier.py"]:
        src = (ROOT / rel).read_text(encoding="utf-8")
        assert "float(" not in src, f"float() found in {rel}"
        assert "math." not in src, f"math. found in {rel}"
        assert "numpy" not in src, f"numpy found in {rel}"

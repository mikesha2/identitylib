/- 
Written by Congzhou M Sha (cms6712@psu.edu)

Copyright 2022 Congzhou M Sha

Permission is hereby granted, free of charge, to any person obtaining a copy 
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell 
copies of the Software, and to permit persons to whom the Software is 
furnished to do so, subject to the following conditions:

-/
import tactic
import data.real.basic
import lemmas0

open_locale big_operators

/- Chapter 0.1: Finite sums -/
namespace chapter0_1
  @[simp] theorem arithmetic_progression_0_111 (n : ℕ) (a r : ℝ) : 
    ∑ (k : ℕ) in finset.range n, (a + k * r) = n * (a + (n - 1) * r / 2) :=
  begin
    induction n with n ih,
    { simp, },
    {
      rw [finset.sum_range_succ, ih, nat.succ_eq_add_one, 
        mul_sub_right_distrib, one_mul],
      simp,
      repeat {rw left_distrib},
      rw [right_distrib, right_distrib, add_assoc,
        one_mul, one_mul, div_eq_mul_inv, div_eq_mul_inv, 
        mul_sub_right_distrib, mul_sub_left_distrib],
      repeat {rw right_distrib},
      repeat {rw left_distrib},
      ring_nf,
    },
  end

  @[simp] theorem geometric_progression_0_112 (n : ℕ) (a q : ℝ) (h : q ≠ 1) :
    ∑ (k : ℕ) in finset.range n, a * q ^ k = a * (q ^ n - 1) / (q - 1) :=
  begin
    induction n with n ih,
    { simp, },
    {
      rw [finset.sum_range_succ, ih, pow_succ],
      repeat {rw div_eq_mul_inv},
      repeat {rw mul_sub_left_distrib},
      repeat {rw mul_sub_right_distrib},
      repeat {rw mul_one},
      rw ne_zero_iff_sub_ne_zero at h,
      have := mul_inv_cancel h,
      nth_rewrite_lhs 1 ← mul_one (a * q ^ n),
      nth_rewrite_lhs 2 ← this,
      rw ← mul_assoc (a * q ^ n),
      repeat {rw mul_sub_left_distrib},
      repeat {rw mul_sub_right_distrib},
      ring_nf,
    },
  end

  @[simp] lemma pure_geometric_progression (n : ℕ) (q : ℝ) (h : q ≠ 1) : 
    ∑ (k : ℕ) in finset.range n, q ^ k = (q ^ n - 1) / (q - 1) := 
  begin
    have := geometric_progression_0_112 n 1 q h,
    simp at this,
    exact this,
  end


  @[simp] lemma deriv_except_at_one (n : ℕ) (q : ℝ) (h : q ≠ 1) :
      has_deriv_at (λ (x : ℝ), (finset.range n).sum (pow x)) 
        (∑ (k : ℕ) in finset.range n, power_rule.x_to_n' k q) q
      ↔ has_deriv_at (λ (x : ℝ), (x ^ n - 1) / (x - 1)) 
        (∑ (k : ℕ) in finset.range n, power_rule.x_to_n' k q) q :=
  begin
    split,
    {
      intro p,
      rw [has_deriv_at, has_deriv_at_filter, has_fderiv_at_filter,
      asymptotics.is_o_iff] at *,
      intros c r,
      have := (ne_zero_iff_sub_ne_zero q 1).1 h,
      rw ← abs_pos at this,
      replace : 0 < |q - 1| / 2, by linarith,
      specialize p r,
      rw metric.eventually_nhds_iff_ball at *,
      cases p with ε h₁,
      cases h₁ with h₁ h₂,
      use min ε (|q - 1| / 2),
      split,
      { 
        rw [gt_iff_lt, lt_min_iff],
        split,
        repeat {linarith},
      },
      {
        intros x' q₁,
        simp at q₁,
        unfold dist at q₁,
        have : x' ≠ 1 := begin
          by_contra,
          rw h at q₁,
          have q₂ := q₁.2,
          rw abs_sub_comm at q₂,
          linarith,
        end,
        specialize h₂ x' q₁.1,
        rw ← pure_geometric_progression n q h,
        rw ← pure_geometric_progression n x' this,
        assumption,
      },
    },
    {
      intro p,
      rw [has_deriv_at, has_deriv_at_filter, has_fderiv_at_filter,
      asymptotics.is_o_iff] at *,
      intros c r,
      have := (ne_zero_iff_sub_ne_zero q 1).1 h,
      rw ← abs_pos at this,
      replace : 0 < |q - 1| / 2, by linarith,
      specialize p r,
      rw metric.eventually_nhds_iff_ball at *,
      cases p with ε h₁,
      cases h₁ with h₁ h₂,
      use min ε (|q - 1| / 2),
      split,
      { 
        rw [gt_iff_lt, lt_min_iff],
        split,
        repeat {linarith},
      },
      {
        intros x' q₁,
        simp at q₁,
        unfold dist at q₁,
        have : x' ≠ 1 := begin
          by_contra,
          rw h at q₁,
          have q₂ := q₁.2,
          rw abs_sub_comm at q₂,
          linarith,
        end,
        specialize h₂ x' q₁.1,
        rw pure_geometric_progression n q h,
        rw pure_geometric_progression n x' this,
        assumption,
      },
    },
  end

  theorem arithmetic_geometric_progression_0_113 (n : ℕ) (a q r : ℝ) (h : q ≠ 1) :
    ∑ (k : ℕ) in finset.range (n + 1), ((a + k * r) * q ^ k) = 
      (a - (a + n * r) * q ^ (n + 1)) / (1 - q) + r * q * (1 - q ^ n) / (1 - q) ^ 2 :=
  begin
    rw arith_geom_progression_split_sum (n + 1) a q r,
    rw geometric_progression_0_112 (n + 1) a q h,
    rw ← deriv_sub_geom_eq_sum,
    have p₁ := deriv_sum_powers (n + 1 + 1) q,
    replace p₁ := (deriv_except_at_one (n + 1 + 1) q h).1 p₁,
    have p₂ := deriv_geom_at_ne_one (n + 1) q h,
    rename_var x y at p₁,
    replace p₁ := has_deriv_at.unique p₁ p₂,
    clear p₂,
    rw sum_x_to_n'_eq_deriv_sum (n + 1) q at p₁,
    rw p₁,
    rw pure_geometric_progression (n + 1) q h,
    rw ← neg_sub 1 q,
    have q₁ : (-(1 - q)) ^ 2 = (1 - q) ^ 2, by ring_nf,
    rw q₁,
    simp only [nat.cast_add, nat.cast_one, div_eq_mul_inv, left_distrib, right_distrib,
      mul_sub_left_distrib, mul_sub_right_distrib, mul_one, one_mul],
    rw [sub_eq_neg_add, mul_comm, ← neg_inv, neg_mul, neg_neg, mul_comm,
      sub_eq_add_neg (a * (1 - q)⁻¹)],
    nth_rewrite_lhs 0 add_assoc,
    nth_rewrite_rhs 0 add_assoc,
    rw [add_right_inj, mul_neg, neg_add],
    nth_rewrite_rhs 0 add_assoc,
    simp only [mul_neg, neg_mul],
    rw [add_right_inj],
    rw ne_zero_iff_sub_ne_zero at h,
    repeat {rw mul_assoc},
    have := (sub_ne_zero_iff_sub_ne_zero q 1).1 h,
    rw [mul_comm (1 - q), inv_mul_eq_div, 
      cancel_power (1 - q) this, pow_one, mul_div, mul_one],
    repeat {rw ← mul_comm (1 - q)⁻¹},
    repeat {rw inv_mul_eq_div},
    rw ← mul_assoc,
    nth_rewrite_rhs 0 ← mul_assoc,
    rw [mul_comm r (↑n), add_assoc, add_sub_assoc, add_sub_assoc, add_right_inj],
    repeat {rw sub_eq_add_neg},
    rw [neg_neg, add_assoc (-(r * (q ^ (n + 1) / (1 + -q))) + -(r * (q ^ (n + 1) / (1 + -q)))),
      add_comm (-(r * (q ^ (n + 1 + 1) * ((1 + -q) ^ 2)⁻¹) + -(r * ((1 + -q) ^ 2)⁻¹))),
      ← add_assoc (-(r * (q ^ (n + 1) / (1 + -q))) + -(r * (q ^ (n + 1) / (1 + -q)))),
      neg_add, neg_neg, ← add_assoc, add_assoc (-(r * (q ^ (n + 1) / (1 + -q)))), 
      neg_add_self, add_zero, neg_add, neg_neg, add_comm (-(r * (q ^ (n + 1 + 1) * ((1 + -q) ^ 2)⁻¹))),
      ← add_assoc, add_comm (-(r * (q ^ (n + 1) / (1 + -q))) + -(r / (1 + -q)))],
    
    
    have m₁ := mul_ne_zero this this,
    have m₂ := mul_inv_cancel m₁,
    
    rw mul_self_eq_square at m₁,
    rw mul_self_eq_square at m₂,
    have m₃ := mul_self_pos.2 this,
    rw mul_self_eq_square at m₃,
    have m₄ : (r * ((1 + -q) ^ 2)⁻¹ + (-(r * (q ^ (n + 1) / (1 + -q))) + -(r / (1 + -q))) +
      -(r * (q ^ (n + 1 + 1) * ((1 + -q) ^ 2)⁻¹))) * (1 - q) ^ 2 = (r * (q * ((1 + -q) ^ 2)⁻¹) + -(r * (q * (q ^ n * ((1 + -q) ^ 2)⁻¹)))) * (1 - q) ^ 2 ↔
      (r * ((1 + -q) ^ 2)⁻¹ + (-(r * (q ^ (n + 1) / (1 + -q))) + -(r / (1 + -q))) +
      -(r * (q ^ (n + 1 + 1) * ((1 + -q) ^ 2)⁻¹)) =
      r * (q * ((1 + -q) ^ 2)⁻¹) + -(r * (q * (q ^ n * ((1 + -q) ^ 2)⁻¹))))
      := (mul_right_cancel_iff_of_pos m₃),
    rw ← m₄,
    clear m₄,
    repeat {rw right_distrib},
    repeat {rw tactic.ring.add_neg_eq_sub},
    rw mul_comm at m₂,
    rw [mul_assoc r, m₂, mul_one, neg_mul, mul_assoc r, div_mul, 
      cancel_power (1 - q) this, pow_one, ← div_mul, div_one, neg_mul,
      div_mul, cancel_power (1 - q) this, 
      pow_one, ← div_mul, div_one, ← neg_add, ← sub_eq_add_neg,
      sub_add_eq_sub_sub, neg_mul, mul_assoc, mul_assoc, m₂, mul_one,
      mul_assoc r, mul_assoc q, m₂, ← mul_assoc, ← mul_assoc, ← mul_assoc, 
      ← mul_assoc, ← neg_mul, ← neg_mul, ← neg_mul, mul_assoc (-(r * q) * q ^ n), m₂,
      sub_eq_add_neg, pow_succ q (n + 1)],
    simp only [left_distrib, right_distrib, mul_one, mul_sub_right_distrib, mul_sub_left_distrib],
    ring_nf,
    simp only [left_distrib, right_distrib],
    rw [one_mul, add_left_inj, mul_comm (-q ^ n), pow_succ, ← mul_neg],
  end

  theorem k_squared_geometric_progression_0_114 (n : ℕ) (x : ℝ) :
    ∑ (k : ℕ) in finset.range n, ↑k ^ 2 * x ^ k =
    ((-n ^ 2 + 2 * n - 1) * x ^ (n + 2) + (2 * n ^ 2 - 2 * n - 1) * x ^ (n + 1) 
    - n ^ 2 * x ^ n + x ^ 2 + x) / (1 - x) ^ 3 :=
  begin
    
  end


end chapter0_1
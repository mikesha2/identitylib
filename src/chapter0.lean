/- 
Written by Congzhou M Sha (cms6712@psu.edu)

Copyright 2022 Congzhou M Sha

Permission is hereby granted, free of charge, to any person obtaining a copy 
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell 
copies of the Software, and to permit persons to whom the Software is 
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

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

  /-
    An inelegant method of proving the derivatives except at 1 are equal for two functions
    which agree except at 1.
    TODO: I've written helper theorems in lemma0.lean which can simplify this argument.
  -/
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
        rw abs_sub_comm at this,
        have q₁' := q₁.2,
        nth_rewrite_rhs 0 abs_sub_comm at q₁',
        have := half_bound q x' q₁' h,
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
        rw abs_sub_comm at this,
        have q₁' := q₁.2,
        nth_rewrite_rhs 0 abs_sub_comm at q₁',
        have := half_bound q x' q₁' h,
        specialize h₂ x' q₁.1,
        rw pure_geometric_progression n q h,
        rw pure_geometric_progression n x' this,
        assumption,
      },
    },
  end

  lemma deriv_of_geometric (n : ℕ) (x : ℝ) (h : x ≠ 1):
    ∑ (k : ℕ) in finset.range n, (↑k + 1) * x ^ k = 
    ((↑n + 1) * x ^ n * (x - 1) - (x ^ (n + 1) - 1)) / (x - 1) ^ 2 :=
  begin
    have p₁ := deriv_sum_powers (n + 1) x,
    replace p₁ := (deriv_except_at_one (n + 1) x h).1 p₁,
    have p₂ := deriv_geom_at_ne_one n x h,
    rename_var x y at p₁,
    replace p₁ := has_deriv_at.unique p₁ p₂,
    clear p₂,
    rw sum_x_to_n'_eq_deriv_sum n x at p₁,
    assumption,
  end

  lemma deriv_of_geometric_rv (n : ℕ) (x : ℝ) (h : x ≠ 1):
    ((↑n + 1) * x ^ n * (x - 1) - (x ^ (n + 1) - 1)) / (x - 1) ^ 2 =
    ∑ (k : ℕ) in finset.range n, (↑k + 1) * x ^ k :=
  begin
    have := deriv_of_geometric n x h,
    symmetry,
    exact this,
  end

  /- 
    Proof through linearity of sums and differentiating both sides of the geometric series
    equation. "Differentiating both sides" is equivalent to "the derivative is unique"
  -/
  theorem arithmetic_geometric_progression_0_113 (n : ℕ) (a q r : ℝ) (h : q ≠ 1) :
    ∑ (k : ℕ) in finset.range (n + 1), ((a + k * r) * q ^ k) = 
      (a - (a + n * r) * q ^ (n + 1)) / (1 - q) + r * q * (1 - q ^ n) / (1 - q) ^ 2 :=
  begin
    rw arith_geom_progression_split_sum (n + 1) a q r,
    rw geometric_progression_0_112 (n + 1) a q h,
    rw ← deriv_sub_geom_eq_sum,
    have p₁ := deriv_of_geometric (n + 1) q h,
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

  /- Some weird combinations of casting natural numbers and 
  multiplying that ring_nf has difficulty solving -/
  lemma k_squared_geometric_progression_algebra (x : ℝ) (n : ℕ) :
    -x ^ (n + 2) * ↑n * ↑n +
        (2 * x ^ (n + 1) * ↑n * ↑n +
          (-x * x * x * x ^ n * ↑n * ↑n + 3 * x * x * x ^ n * ↑n * ↑n -
              3 * x * x ^ n * ↑n * ↑n)) =
      2 * x ^ (n + 2) * ↑n * ↑n +
        (-x ^ (n + 1) * ↑n * ↑n - x ^ (n + 3) * ↑n * ↑n) :=
  begin
    have : -x ^ (n + 2) * ↑n * ↑n = -(↑n) ^ 2 * x ^ (n + 2), by ring_nf,
    rw this, clear this,
    have : 2 * x ^ (n + 1) * ↑n * ↑n = 2 * (↑n) ^ 2 * x ^ (n + 1), by ring_nf,
    rw this, clear this,
    have : -x * x * x * x ^ n * ↑n * ↑n = -(↑n) ^ 2 * x ^ (n + 3) :=
    begin
      repeat {rw pow_succ},
      ring_nf,
    end,
    rw this, clear this,
    have : 3 * x * x * x ^ n * ↑n * ↑n = 3 * (↑n) ^ 2 * x ^ (n + 2) :=
    begin
      repeat {rw pow_succ},
      ring_nf,
    end,
    rw this, clear this,
    have : 3 * x * x ^ n * ↑n * ↑n = 3 * (↑n) ^ 2 * x ^ (n + 1) :=
    begin
      rw [mul_assoc, mul_assoc, mul_assoc, ← mul_assoc x, ← pow_succ],
      ring_nf,
    end,
    rw this, clear this,
    ring_nf,
  end

  /-
    Surprisingly, though the calculus proof (differentiating the geometric series twice)
    is easier to follow on paper, the induction proof has far less tedious algebra.
  -/
  theorem k_squared_geometric_progression_0_114 (n : ℕ) (x : ℝ) (h : x ≠ 1) :
    ∑ (k : ℕ) in finset.range n, ↑k ^ 2 * x ^ k =
    ((-n ^ 2 + 2 * n - 1) * x ^ (n + 2) + (2 * n ^ 2 - 2 * n - 1) * x ^ (n + 1) 
    - n ^ 2 * x ^ n + x ^ 2 + x) / (1 - x) ^ 3 :=
  begin
    induction n with n ih,
    { simp, },
    {
      rw [finset.sum_range_succ, nat.succ_eq_add_one, ih],
      have h':= (ne_zero_iff_sub_ne_zero x 1).mp h,
      replace h' := (sub_ne_zero_iff_sub_ne_zero x 1).mp h',
      have trip := mul_ne_zero (mul_ne_zero h' h') h',
      rw mul_self_twice_eq_cube at trip,

      -- Multiply both sides by (1 - x) ^ 3 (nonzero). 
      -- TODO: replace this with easier to use multiply_both_sides_by_ne_zero (lemma0.lean)
      have :
      (((-↑n ^ 2 + 2 * ↑n - 1) * x ^ (n + 2) + (2 * ↑n ^ 2 - 2 * ↑n - 1) * x ^ (n + 1) - ↑n ^ 2 * x ^ n + x ^ 2 +
         x) /
      (1 - x) ^ 3 +
      ↑n ^ 2 * x ^ n) * (1 - x) ^ 3 =
      (((-↑(n + 1) ^ 2 + 2 * ↑(n + 1) - 1) * x ^ (n + 1 + 2) +
              (2 * ↑(n + 1) ^ 2 - 2 * ↑(n + 1) - 1) * x ^ (n + 1 + 1) -
            ↑(n + 1) ^ 2 * x ^ (n + 1) +
          x ^ 2 +
        x) /
      (1 - x) ^ 3) * (1 - x) ^ 3 ↔
      ((-↑n ^ 2 + 2 * ↑n - 1) * x ^ (n + 2) + (2 * ↑n ^ 2 - 2 * ↑n - 1) * x ^ (n + 1) - ↑n ^ 2 * x ^ n + x ^ 2 +
          x) /
        (1 - x) ^ 3 +
      ↑n ^ 2 * x ^ n =
      ((-↑(n + 1) ^ 2 + 2 * ↑(n + 1) - 1) * x ^ (n + 1 + 2) +
              (2 * ↑(n + 1) ^ 2 - 2 * ↑(n + 1) - 1) * x ^ (n + 1 + 1) -
            ↑(n + 1) ^ 2 * x ^ (n + 1) +
          x ^ 2 +
        x) /
      (1 - x) ^ 3
        := mul_right_cancel_iff_ne_zero trip,
      rw ← this, clear this,
      have cancel := mul_inv_cancel trip,
      rw mul_comm at cancel,
      rw [right_distrib, div_eq_mul_inv, mul_assoc, cancel, mul_one, div_eq_mul_inv],
      nth_rewrite_rhs 0 mul_assoc,
      rw [cancel],
      simp only [right_distrib, left_distrib, mul_sub_right_distrib, 
        mul_sub_left_distrib, one_mul, mul_one, ← mul_self_eq_square, nat.cast_add, nat.cast_one],
      rw [add_right_comm (-(↑n * ↑n) * x ^ (n + 2) + 2 * ↑n * x ^ (n + 2) - x ^ (n + 2) +
        (2 * (↑n * ↑n) * x ^ (n + 1) - 2 * ↑n * x ^ (n + 1) - x ^ (n + 1)) -
        ↑n * ↑n * x ^ n +
        x * x), add_left_inj, add_right_comm (-(↑n * ↑n) * x ^ (n + 2) + 2 * ↑n * x ^ (n + 2) - x ^ (n + 2) +
        (2 * (↑n * ↑n) * x ^ (n + 1) - 2 * ↑n * x ^ (n + 1) - x ^ (n + 1)) -
        ↑n * ↑n * x ^ n), add_left_inj],
      have : n + 1 + 1 = n + 2, by linarith,
      rw this, clear this,
      have : n + 1 + 2 = n + 3, by linarith,
      rw this, clear this,
      ring_nf,
      rw add_left_inj,
      simp only [right_distrib, left_distrib, mul_sub_right_distrib, 
        mul_sub_left_distrib],
      rw add_left_inj,
      exact k_squared_geometric_progression_algebra x n,
    }
  end

  -- TODO: The general case sum_integers_0_121 with Bernoulli numbers

  theorem sum_integers_0_121_1 (n : ℕ) :
    ∑ (k : ℕ) in finset.range (n + 1), (↑k : ℝ) = ↑n * (n + 1) / 2 :=
  begin
    induction n with n ih,
    { simp, },
    {
      rw [finset.sum_range_succ, nat.succ_eq_add_one, ih],
      cancel_denoms,
      simp only [right_distrib, left_distrib, div_eq_mul_inv, nat.cast_add, nat.cast_one],
      ring_nf,
    },
  end

  theorem sum_integers_0_121_2 (n : ℕ) :
    ∑ (k : ℕ) in finset.range (n + 1), (↑k : ℝ) ^ 2 = (↑n * (n + 1) * (2 * n + 1)) / 6 :=
  begin
    induction n with n ih,
    { simp, },
    {
      rw [finset.sum_range_succ, nat.succ_eq_add_one, ih],
      cancel_denoms,
      simp only [right_distrib, left_distrib, div_eq_mul_inv, nat.cast_add, nat.cast_one, 
        one_mul, mul_one],
      ring_nf,
    },
  end

  theorem sum_integers_0_121_3 (n : ℕ) :
    ∑ (k : ℕ) in finset.range (n + 1), (↑k : ℝ) ^ 3 = (n * (n + 1) / 2) ^ 2 :=
  begin
    induction n with n ih,
    { simp, },
    {
      rw [finset.sum_range_succ, nat.succ_eq_add_one, ih],
      cancel_denoms,
      simp only [right_distrib, left_distrib, div_eq_mul_inv, nat.cast_add, nat.cast_one, 
        one_mul, mul_one],
      ring_nf,
    },
  end

  theorem sum_integers_0_121_4 (n : ℕ) :
    ∑ (k : ℕ) in finset.range (n + 1), (↑k : ℝ) ^ 4 = n * (n + 1) * (2 * n + 1) * (3 * n ^ 2 + 3 * n - 1) / 30 :=
  begin
    induction n with n ih,
    { simp, },
    {
      rw [finset.sum_range_succ, nat.succ_eq_add_one, ih],
      cancel_denoms,
      simp only [right_distrib, left_distrib, div_eq_mul_inv, nat.cast_add, nat.cast_one, 
        one_mul, mul_one],
      ring_nf,
    },
  end

  theorem sum_integers_0_121_5 (n : ℕ) :
    ∑ (k : ℕ) in finset.range (n + 1), (↑k : ℝ) ^ 5 = n ^ 2 * (n + 1) ^ 2 * (2 * n ^ 2 + 2 * n - 1) / 12 :=
  begin
    induction n with n ih,
    { simp, },
    {
      rw [finset.sum_range_succ, nat.succ_eq_add_one, ih],
      cancel_denoms,
      simp only [right_distrib, left_distrib, div_eq_mul_inv, nat.cast_add, nat.cast_one, 
        one_mul, mul_one],
      ring_nf,
    },
  end
  
  theorem sum_integers_0_121_6 (n : ℕ) :
    ∑ (k : ℕ) in finset.range (n + 1), (↑k : ℝ) ^ 6 = n * (n + 1) * (2 * n + 1) * (3 * n ^ 4 + 6 * n ^ 3 - 3 * n + 1) / 42 :=
  begin
    induction n with n ih,
    { simp, },
    {
      rw [finset.sum_range_succ, nat.succ_eq_add_one, ih],
      cancel_denoms,
      simp only [right_distrib, left_distrib, div_eq_mul_inv, nat.cast_add, nat.cast_one, 
        one_mul, mul_one],
      ring_nf,
    },
  end

  theorem sum_integers_0_121_7 (n : ℕ) :
    ∑ (k : ℕ) in finset.range (n + 1), (↑k : ℝ) ^ 7 = n ^ 2 * (n + 1) ^ 2 * (3 * n ^ 4 + 6 * n ^ 3 - n ^ 2 - 4 * n + 2) / 24 :=
  begin
    induction n with n ih,
    { simp, },
    {
      rw [finset.sum_range_succ, nat.succ_eq_add_one, ih],
      cancel_denoms,
      simp only [right_distrib, left_distrib, div_eq_mul_inv, nat.cast_add, nat.cast_one, 
        one_mul, mul_one],
      ring_nf,
    },
  end
end chapter0_1

namespace chapter0_2

end chapter0_2
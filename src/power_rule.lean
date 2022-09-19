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
import data.real.basic
import tactic
import analysis.normed.group.basic
import algebra.order.absolute_value
import algebra.order.group
import algebra.group_power.basic
import data.nat.choose.basic
import data.nat.choose.sum
import algebra.big_operators.basic
import tactic.linarith
import analysis.calculus.fderiv
import analysis.special_functions.pow
import analysis.calculus.cont_diff
import data.num.lemmas

open polynomial nat finset filter asymptotics set metric
open_locale topological_space big_operators
namespace power_rule

  @[simp] def x_to_n : (ℕ → ℝ → ℝ) := (λ (n : ℕ) (x : ℝ), x ^ n)
  @[simp] def x_to_n' : (ℕ → ℝ → ℝ)
  | 0 := λ (x : ℝ), (0 : ℝ)
  | (n + 1) := λ (x : ℝ), (n + 1 : ℝ) * x ^ n

  theorem geometric_series_no_division (x : ℝ) (n : ℕ) : 
    finset.sum (range n) (λ k, (x-1) * x ^ (k : ℝ)) = x ^ n - 1 := 
  begin
    apply sum_range_induction,
    simp,
    intro m,
    simp,
    ring_nf,
  end

  lemma mul_sum_left_distrib (f : ℝ → ℝ → ℝ) (g : ℕ → ℝ) (x : ℝ) (y : ℝ) (n : ℕ) :
    (f x y) * (range n).sum g = (range n).sum (λ k, (f x y) * (g k)) :=
  begin
    induction n with n h,
    { simp, },
    {
      rw finset.sum_range_succ,
      rw left_distrib,
      dsimp,
      rw h,
      rw finset.sum_range_succ,
    }
  end

  lemma unfold_last_term : ∀ (x y : ℝ) (n : ℕ) (f : ℕ → ℝ), 
    (n > 0) → (range n).sum f = (range (n - 1)).sum (λ k, f k) + f (n-1) :=
  begin
    intros x y n f p,
    induction n with n ih,
    { simp, linarith,},
    {
      rw range_succ,
      simp,
      ring,
    },
  end

  lemma unfold_first_term : ∀ (x y : ℝ) (n : ℕ) (f : ℕ → ℝ),
    (n > 0) → (range n).sum f = f 0 + (range (n-1)).sum (λ k, f (k + 1)) :=
  begin
    intros x y n f p,
    induction n with n ih,
    { simp, linarith, },
    {
      induction n with n₁ ih₁,
      { norm_num, },
      {
        rw range_succ,
        simp,
        have q : n₁.succ > 0, by simp,
        have r := ih q,
        rw r,
        clear ih ih₁ p,
        have s := (unfold_last_term x y n₁.succ f) q,
        rename_var x k,
        simp,
        rw range_succ,
        simp,
        rw nat.succ_eq_add_one,
        linarith,
      },
    }
  end

  theorem x_to_n_sub_y_to_n_factor (x y : ℝ) (n : ℕ) : x^n-y^n = (x-y) * (range n).sum (λ k, x ^ (n - 1 - k) * y ^ k) := begin
    rw finset.mul_sum,
    induction n with n ih,
    { simp, },
    {
      rw [pow_succ, pow_succ, finset.sum_range_succ],
      simp,
      rw [mul_sub_right_distrib, ← add_sub_assoc, sub_left_inj],
      rw sub_eq_iff_eq_add at ih,
      rw [ih, left_distrib, finset.mul_sum, add_left_inj, finset.sum_congr rfl],
      intros k p,
      rw [← mul_assoc, ← mul_assoc, mul_comm, mul_comm x (x-y),
        mul_assoc (x-y) x (x ^ (n - 1 - k)), ← pow_succ],
      
      have q : n - 1 - k + 1 = n - k, begin
        rw nat.sub.right_comm,
        rw finset.mem_range at p,
        have q₁ : 0 < n - k, begin
          exact nat.sub_pos_of_lt p,
        end,
        have q₂ : 1 ≤ n - k, by linarith,
        rw nat.sub_add_cancel q₂,
      end,

      rw q,
      ring_nf,
    }
  end

  lemma pos_mul_ge_one_ge_one (a b : ℝ) (h₁ : a ≥ 1) (h₂ : b > 0) : (a * b ≥ b) := begin
    nlinarith,
  end

  lemma weaken_le (a b c : ℝ) (h : a ≤ b ∧ 0 < c) : (a ≤ b + c) :=
  begin
    have h₁ := h.1,
    have h₂ := h.2,
    nlinarith,
  end

  lemma deriv_power_ineq_helper_1 (x y : ℝ) (n k : ℕ)
  (h : -1 < y - x ∧ y - x < 1)
  (p : k ≤ n) :
  |x| ^ k ≤ (|x| + 1) ^ k :=
  begin
    have v₁ : |x| ≤ |x| + 1,
      begin
        have w₁ := le_abs_self x,
        linarith,
      end,
      induction k with k ih,
      {
        simp,
      },
      {
        have : k ≤ n, begin
          rw succ_eq_add_one at p,
          linarith,
        end,
        rw [pow_succ, pow_succ],
        have w₁ := le_abs_self x,
        have w₂ := ih this,
        have w₃ : |x| + 1 ≥ 1 :=
        begin
          have := abs_nonneg x,
          linarith,
        end,
        rw [right_distrib, one_mul],
        have w₄ : 0 < (|x| + 1), by nlinarith,
        have w₅ := pow_pos w₄,
        apply weaken_le,
        split,
        {
          nlinarith,
        },
        {
          specialize w₅ k,
          exact w₅,
        },
      },
  end

  lemma deriv_power_ineq_helper_2
    (x y : ℝ) (n k : ℕ)
    (h : -1 < y - x ∧ y - x < 1)
    (p : k ≤ n) : |y| ^ (n - k) ≤ (|x| + 1) ^ (n - k) :=
  begin
    have h₁ := h.1,
    have h₂ := h.2,
    clear h,
    have h₃ : |y| < |x| + 1,
    begin
      have q := le_abs_self x,
      rw abs_lt,
      split,
      {
        rw [neg_eq_zero_sub, sub_add_eq_sub_sub, sub_lt_iff_lt_add, 
          ← neg_eq_zero_sub, neg_lt, lt_abs],
        right,
        linarith,
      },
      {
        linarith,
      },
    end,
    induction (n-k) with n ih,
    { simp, },
    {
      rw [pow_succ, pow_succ],
      have w₁ := le_abs_self x,
      have w₂ := ih,
      have w₃ : |x| + 1 ≥ 1 :=
      begin
        have := abs_nonneg x,
        linarith,
      end,
      have w₄ : |y| ≤ |x| + 1, by linarith,
      have w₅ := abs_nonneg y,
      have w₆ : 0 < |x| + 1, by linarith,
      have w₇ := pow_pos w₆,
      have w₈ := pow_nonneg w₅,
      specialize w₈ n,
      replace w₆ : 0 ≤ |x| + 1, by linarith,
      exact mul_le_mul w₄ ih w₈ w₆,
    },
  end


  lemma deriv_power_ineq'
    (x y : ℝ) (n k : ℕ)
    (h : -1 < y - x ∧ y - x < 1)
    (p : k ≤ n) :
    |y ^ (n - k) * x ^ k| ≤ (|x| + 1) ^ n :=
  begin
    have u₁ := deriv_power_ineq_helper_1 x y n k h p,
    have u₂ := deriv_power_ineq_helper_2 x y n k h p,
    rw abs_mul,
    repeat {rw abs_pow},
    have u₃ := pow_nonneg (abs_nonneg y),
    have u₄ : 0 ≤ (|x| + 1), begin
      have := abs_nonneg x,
      linarith,
    end,
    specialize u₃ (n-k),
    replace u₄ := pow_nonneg u₄,
    specialize u₄ k,
    have q := mul_le_mul u₁ u₂ u₃ u₄,
    rw ← pow_add at q,
    rw ← nat.add_sub_assoc at q,
    rw (nat.add_sub_cancel_left k n) at q,
    rw mul_comm,
    exact q,
    exact p,
  end

  lemma sum_cons_simp (x y : ℝ) (n : ℕ) : ∑ (x_1 : ℕ) in range (n + 1), (|x| + 1) ^ n = (n + 1) * (|x| + 1) ^ n :=
  begin
    simp,
  end

  lemma sum_one_plus_abs_pos (x : ℝ) (n : ℕ) :  ∀ i ∈ range (n+1), 0 < (|x| + 1) ^ n := 
  begin
    intros i p,
    have := abs_nonneg x,
    have h₁ : 0 < |x| + 1, by linarith,
    have h₂ := pow_pos h₁,
    specialize h₂ n,
    exact h₂,
  end

    lemma sum_one_plus_abs_nonneg (x : ℝ) (n : ℕ) : ∀ i ∈ range (n + 1), 0 ≤ (|x| + 1) ^ n := 
  begin
    intros i p,
    have := abs_nonneg x,
    have h₁ : 0 ≤ |x| + 1, by linarith,
    have h₂ := pow_nonneg h₁,
    specialize h₂ n,
    exact h₂,
  end
  lemma sum_power_bound_constant (x : ℝ) (n : ℕ) : ∑ (x_1 : ℕ) in range (n + 1), (|x| + 1) ^ n = (n+1) * (|x| + 1) ^ n :=
  begin
    simp,
  end

  lemma one_plus_abs_pos (x : ℝ) : 0 < 1 + |x| := begin
    have := abs_nonneg x,
    linarith,
  end
  
  lemma one_plus_abs_nonneg (x : ℝ) : 0 ≤ 1 + |x| := begin
    have := abs_nonneg x,
    linarith,
  end

  lemma one_plus_abs_pow_pos (x : ℝ) : ∀ (n:ℕ), 0 < (1 + |x|) ^ n := pow_pos (one_plus_abs_pos x)
  
  lemma one_plus_abs_pow_nonneg (x : ℝ) (n : ℕ) : 0 ≤ (1 + |x|) ^ n := 
  begin
    have := one_plus_abs_pow_pos x n,
    linarith,
  end

  lemma bound_xy_y (x y : ℝ) (r : |y - x| < 1) : |y| < 1 + |x| := begin
    have := abs_abs_sub_abs_le_abs_sub y x,
    have : | |y| - |x| | < 1, by linarith,
    rw abs_lt at this,
    linarith,
  end

  lemma bound_x (x : ℝ) : |x| ≤ 1 + |x| := begin linarith, end

  lemma bound_x_pow_one (x : ℝ) (n : ℕ) : 1 ≤ (1 + |x|) ^ n :=
  begin
    induction n with n ih,
    { simp, },
    {
      rw pow_succ,
      have a := abs_nonneg x,
      have b : 1 ≤ 1 + |x|, by linarith,
      have c : (0 : ℝ) ≤ 1, by norm_num,
      have := mul_le_mul b ih c (one_plus_abs_nonneg x),
      rw one_mul at this,
      exact this,
    },
  end

  lemma bound_x_pow (x : ℝ) (n : ℕ) : |x| ^ n ≤ (1 + |x|) ^ n :=
  begin
    induction n with n ih,
    {
      have := bound_x x, 
      linarith,
    },
    {
      rw [pow_succ, pow_succ],
      have a := one_plus_abs_pos x,
      have b := one_plus_abs_pow_pos x n,
      have := abs_nonneg x,
      have f := pow_nonneg this,
      specialize f n,
      have e : 0 ≤ (1 + |x|) ^ n, by linarith,
      have c : |x| ≤ |x|, by linarith,
      have d : |x| ≤ 1 + |x|, by linarith,
      have : 0 ≤ 1 + |x|, by linarith,
      exact mul_le_mul d ih f this,
    },
  end

  lemma pow_abs_nonneg (x : ℝ) (n : ℕ) : 0 ≤ (|x|) ^ n :=
  begin
    have := abs_nonneg x,
    have := pow_nonneg this,
    specialize this n,
    exact this,
  end

  lemma power_abs_y_bound (x y : ℝ) (q : |y| ≤ 1 + |x|) (k : ℕ) : |y| ^ k ≤ (1 + |x|) ^ k := 
  begin
    induction k with k ih,
    { simp, },
    {
      rw [pow_succ, pow_succ],
      have a := pow_abs_nonneg y k,
      have := abs_nonneg x,
      have b : 0 ≤ 1 + |x|, by linarith,
      exact mul_le_mul q ih a b,
    },
  end

  lemma power_abs_x_bound (x y : ℝ) (k : ℕ)  : |x| ^ k ≤ (1 + |x|) ^ k :=
  begin
    induction k with k ih,
    { simp, },
    {
      rw [pow_succ, pow_succ],
      have a := pow_abs_nonneg x k,
      have := abs_nonneg x,
      have f : 0 ≤ 1 + |x|, by linarith,
      have b := bound_x x,
      exact mul_le_mul b ih a f,
    },
  end

  lemma function_bound (x y : ℝ) (q : |y| ≤ 1 + |x|) (n : ℕ): 
    ∀ (x_1 : ℕ), x_1 ∈ range (n + 1) → |y ^ (n - x_1) * x ^ x_1| ≤ |(1+|x|) ^ n| := 
  begin
    intros k p,
    rw abs_mul,
    repeat {rw abs_pow},
    have a : ∀ (k : ℕ), |y| ^ k ≤ (1 + |x|) ^ k := 
    begin
      intro k,
      clear p,
      induction k with k ih,
      { simp, },
      {
        rw [pow_succ, pow_succ],
        have a := pow_abs_nonneg y k,
        have := abs_nonneg x,
        have b : 0 ≤ 1 + |x|, by linarith,
        exact mul_le_mul q ih a b,
      },
    end,
    specialize a (n-k),
    
    have b := bound_x x,
    have c : ∀ (k : ℕ), |x| ^ k ≤ (1 + |x|) ^ k :=
    begin
      intro k,
      clear p,
      induction k with k ih,
      { simp, },
      {
        rw [pow_succ, pow_succ],
        have a := pow_abs_nonneg x k,
        have := abs_nonneg x,
        have f : 0 ≤ 1 + |x|, by linarith,
        exact mul_le_mul b ih a f,
      },
    end,
    specialize c k,

    have := abs_nonneg x,
    have q : 0 ≤ 1 + |x|, by linarith,
    have := pow_nonneg q,
    specialize this (n - k),

    have d := mul_le_mul a c (pow_abs_nonneg x k) this,
    rw finset.mem_range_succ_iff at p,
    rw pow_sub_mul_pow (1 + |x|) p at d,
    rw ← abs_of_nonneg q at d,
    exact d,
  end
    
  lemma sum_ineq (x y c : ℝ) (h : |y| ≤ 1 + |x|) (n : ℕ) : 
    |∑ (x_1 : ℕ) in range (n + 1), y ^ (n - x_1) * x ^ x_1|
    ≤ |∑ (x_1 : ℕ) in range (n + 1), (1 + |x|) ^ n| :=
  begin
    have q₁ := bound_x x,
    have q₂ := finset.abs_sum_le_sum_abs (λ x_1, y ^ (n - x_1) * x ^ x_1) (range (n + 1)),
    simp at q₂,
    have q₃ := function_bound x y h n,
    have q₄ := finset.sum_le_sum q₃,
    simp at q₄,
    simp,
    have := one_plus_abs_pow_pos x n,
    have a : 0 ≤ (1 + |x|) ^ n, by linarith,
    have : (0 : ℝ) ≤ ↑n := nat.cast_nonneg n,
    have : (0 : ℝ) ≤ ↑n + 1, by linarith,
    have : 0 ≤ (↑n + 1) * (1 + |x|) ^ n := mul_nonneg this a,
    rw abs_of_nonneg this,
    clear this this this,
    rw ← abs_of_pos (one_plus_abs_pos x),
    linarith,
  end

  lemma power_limit_denom_pos (x : ℝ) (n : ℕ) :
    0 < ((↑n + 2) * (↑n + 1) * (1 + |x|) ^ n) :=
  begin
    have a : (0 : ℝ) ≤ ↑n := nat.cast_nonneg n,
    have b : (0 : ℝ) < 2, by norm_num,
    have c := add_pos_of_nonneg_of_pos a b,
    have b : (0 : ℝ) < 1, by norm_num,
    have d := add_pos_of_nonneg_of_pos a b,
    have e := one_plus_abs_pow_pos x n,
    have := mul_pos c (mul_pos d e),
    rw ← mul_assoc at this,
    exact this,
  end

  lemma power_limit_div_pos (x : ℝ) (n : ℕ) (c : ℝ) (r : 0 < c) :
    0 < c / ((↑n + 2) * (↑n + 1) * (1 + |x|) ^ n) :=
  begin
    have a := power_limit_denom_pos x n,
    exact div_pos r a,
  end

  lemma ineq_1 (x : ℝ) (n : ℕ) : |(x ^ n * ↑n + x ^ n)| ≤ |2 * (↑n+2) * (1+|x|)^(n+1)| := begin
    have := one_plus_abs_pow_pos x (n + 1),
    have := le_abs_self x,

    have a : 1*|x ^ n| ≤ (↑n + 2) * (1 + |x|) ^ (n + 1) := begin
      have a := bound_x_pow x n,
      have f : (0 : ℝ) ≤ ↑n := nat.cast_nonneg n,
      have : (0 : ℝ) < (1 : ℝ), by norm_num,
      have b: (0 : ℝ) ≤ ↑n + 1, by linarith,
      have g : (1 : ℝ) ≤ ↑n + 2, by linarith,
      have h : (0 : ℝ) ≤ ↑n + 2, by linarith,
      have := abs_nonneg x,
      have i := pow_nonneg this,
      specialize i n,
      have c : 1 ≤ 1 + |x|, by linarith,
      have d : 0 ≤ 1 + |x|, by linarith,
      have e := mul_le_mul c a (pow_abs_nonneg x n) d,
      simp at e,
      rw ← pow_succ at e,
      rw ← pow_abs,
      exact mul_le_mul g e i h,
    end,
    have b : (|x| ^ n * ↑n) ≤ (n + 2) * (1 + |x|) ^ (n+1) := begin
      rw mul_comm,
      have a := bound_x_pow x n,
      have b : ↑n ≤ ↑n + (1 : ℝ), by linarith,
      refine mul_le_mul _ _ _ _,
      linarith,
      have := abs_nonneg x,
      have c : 1 ≤ 1 + |x|, by linarith,
      have d : 0 ≤ 1 + |x|, by linarith,
      have e := mul_le_mul c a (pow_abs_nonneg x n) d,
      rw one_mul at e,
      rw pow_succ,
      exact e,
      exact pow_abs_nonneg x n,
      have f := nat.cast_nonneg n,
      have g : (0 : ℝ) ≤ 1, by norm_num,
      have : (0 : ℝ) ≤ 2, by linarith,
      have := add_le_add f this,
      linarith,
    end,

    rw one_mul at a,
    have c : (↑n + (1:ℝ) ≤ ↑n + 2), by linarith,
    have d := one_plus_abs_pow_pos x (n + 1),
    replace d : 0 ≤ (1 + |x|) ^ (n + 1), by linarith,
    have e := abs_add (x ^ n * ↑n) (x ^ n),
    have g := one_plus_abs_pow_pos x (n + 1),
    have g' : 0 ≤ (1 + |x|) ^ (n+1), by linarith,
    have f : (0 : ℝ) ≤ ↑n := nat.cast_nonneg n,
    have h : (0 : ℝ) ≤ ↑n + 2, by linarith,
    have j : (0 : ℝ) ≤ 2, by norm_num,
    have i := mul_nonneg h g',
    replace j := mul_nonneg j i,
    rw ← mul_assoc at j,
    rw abs_of_nonneg j,
    have : (2 : ℝ) = 1 + 1, by norm_num,
    rw [this, right_distrib, one_mul, ← this, right_distrib],
    rw ← abs_pow at b,
    rw ← abs_of_nonneg f at b,
    rw ← abs_mul at b,
    rw abs_of_nonneg f at *,
    linarith,
  end

  lemma expr_nonneg (x y : ℝ) (n : ℕ) (h : 0 < |y-x|): 0 ≤ |y - x| * ((↑n + 3) * (↑n + 2) * (1 + |x|) ^ (n + 1)) :=
  begin
    have p₂ := one_plus_abs_pow_pos x (n + 1),
    have p₃ : (0 : ℝ) ≤ ↑n := nat.cast_nonneg n,
    have p₄ : (0 : ℝ) < ↑n + 2, by linarith,
    have p₅ : (0 : ℝ) < ↑n + 3, by linarith,
    have p₆ := mul_pos p₅ p₄,
    have p₇ := mul_pos p₆ p₂,
    have p₈ := mul_pos h p₇,
    linarith,
  end
  
  lemma one_plus_abs_mono_inc (x : ℝ) (n : ℕ) : (1 + |x|) ^ n ≤ (1 + |x|) ^ (n + 1) :=
  begin
    induction n with n ih,
    { simp, },
    {
      rw pow_succ,
      rw pow_succ,
      have a : 1 + |x| ≤ 1 + |x|, by linarith,
      refine mul_le_mul _ _ _ _,
      exact a,
      exact ih,
      have := one_plus_abs_pow_pos x n,
      linarith,
      have := one_plus_abs_pos x,
      linarith,
    },
  end

  lemma one_plus_abs_mono_inc_pair (x : ℝ) (m n : ℕ) : (1 + |x|) ^ m ≤ (1 + |x|) ^ (m + n) :=
  begin
    induction m with m ih,
    { simp, exact bound_x_pow_one x n, },
    {
      rw [pow_succ, nat.succ_add, pow_succ],
      have : 1 + |x| ≤ 1 + |x|, by linarith,
      exact mul_le_mul this ih (one_plus_abs_pow_nonneg x m) (one_plus_abs_nonneg x),
    }
  end

  lemma one_plus_abs_mono_inc_le (x : ℝ) (m n : ℕ) (h : m ≤ n) : (1 + |x|) ^ m ≤ (1 + |x|) ^ n :=
  begin
    have a := one_plus_abs_mono_inc_pair x m (n - m),
    rw nat.add_sub_of_le h at a,
    assumption,
  end

  lemma expr_lt (x : ℝ) (n : ℕ) : (↑n + 1) * (1 + |x|) ^ n ≤ (↑n + 2) * (1 + |x|) ^ (n + 1) := 
  begin
    have a := one_plus_abs_mono_inc x n,
    have a' := one_plus_abs_pow_nonneg x n,
    have b : 1 ≤ 2, by norm_num,
    have c : (↑n + (1:ℝ)) ≤ (↑n + (2 : ℝ)), by linarith,
    have c' : (0 : ℝ) ≤ ↑n := nat.cast_nonneg n,
    
    refine mul_le_mul _ _ _ _,
    repeat {linarith},
  end

  lemma ineq_1_pos (x : ℝ) (n : ℕ) : 0 < (↑n + 1) * (1 + |x|) ^ n :=
  begin
    have a' := one_plus_abs_pow_pos x n,
    have c' : (0 : ℝ) ≤ ↑n := nat.cast_nonneg n,
    have c : (0:ℝ) < ↑n + 1, by linarith,
    exact mul_pos c a',
  end

  lemma ineq_2_pos (x : ℝ) (n : ℕ) : 0 < 2 * (↑n + 2) * (1 + |x|) ^ (n + 1) :=
  begin
    have a' := one_plus_abs_pow_pos x (n+1),
    have c' : (0 : ℝ) ≤ ↑n := nat.cast_nonneg n,
    have c : (0:ℝ) < ↑n + 2, by linarith,
    have d := mul_pos c a',
    have : (0:ℝ) < 2, by norm_num,
    have := mul_pos this d,
    linarith,
  end

  lemma ineq_3 (x : ℝ) (n : ℕ) : 3 * (↑n + 2) * (1 + |x|) ^ (n + 1) ≤ (↑n + 3) * (↑n + 2) * (1 + |x|) ^ (n + 1) :=
  begin
    have a : (0 : ℝ) ≤ ↑n := nat.cast_nonneg n,
    have a' : (0 : ℝ) ≤ ↑n + 2, by linarith,
    have a'' : (0 : ℝ) ≤ ↑n + 3, by linarith,
    have a₁ : (3 : ℝ) ≤ ↑n + 3, by linarith,
    have a₂ : (↑n + (2 : ℝ)) ≤ ↑n + 2, by linarith,
    have b := one_plus_abs_pow_nonneg x (n + 1),
    refine mul_le_mul _ _ _ _,
    repeat {linarith},
    refine mul_le_mul _ _ _ _,
    repeat {linarith},
    refine mul_nonneg _ _,
    repeat {linarith},
  end

  lemma individual_to_sum (x : ℝ) (n : ℕ) : x ^ n * ↑n + x ^ n = ∑ (x_1 : ℕ) in range (n+1), x ^ n :=
  begin
    simp,
    rw right_distrib,
    rw one_mul,
    rw mul_comm,
  end
  lemma sub_sum_eq_sum_sub (x : ℝ) (n : ℕ) (f : ℕ → ℝ) (g : ℕ → ℝ) : 
  ∑ (x_1 : ℕ) in range n, (f x_1 - g x_1) = (∑ (x_1 : ℕ) in range n, f x_1) - (∑ (x_1 : ℕ) in range n, g x_1) :=
  begin
    simp,
  end

  lemma factor_out (x y : ℝ) (n : ℕ) :
    ∑ (x_1 : ℕ) in range (n + 1), (y ^ (n - x_1) * x ^ x_1 - x ^ n) =
    ∑ (x_1 : ℕ) in range (n + 1), x ^ x_1 * (y ^ (n - x_1) - x ^ (n - x_1)) :=
  begin
    apply finset.sum_congr rfl,
    intros k p,
    rw finset.mem_range at p,
    have : k ≤ n, by linarith,
    rw mul_sub_left_distrib,
    rw mul_comm,
    rw pow_mul_pow_sub x this,
  end

  lemma rw_inner_expr (x y : ℝ) (n : ℕ) :
    ∑ (x_1 : ℕ) in range (n + 1), x ^ x_1 * (y ^ (n - x_1) - x ^ (n - x_1)) =
    ∑ (x_1 : ℕ) in range (n + 1), x ^ x_1 * (y - x) * ∑ (x_2 : ℕ) in range (n - x_1), y ^ (n - x_1 - 1 - x_2) * x ^ x_2 :=
  begin
    apply finset.sum_congr rfl,
    intros k p,
    rw mul_assoc,
    rw x_to_n_sub_y_to_n_factor y x (n - k),
  end

  lemma ineq_inner_sum (x y : ℝ) (n : ℕ) (h : |y| ≤ 1 + |x|):
    |∑ (k : ℕ) in range (n + 1), y ^ (n - k) * x ^ k| ≤ (n + 1) * (1 + |x|) ^ n :=
  begin
    have a := sum_ineq x y n h n,
    simp at a,
    have b := one_plus_abs_pow_nonneg x n,
    have : (0 : ℝ) ≤ ↑n := nat.cast_nonneg n,
    have c : (0 : ℝ) ≤ ↑n + 1, by linarith,
    have d := mul_nonneg c b,
    have := abs_of_nonneg d,
    rw this at a,
    assumption,
  end

  lemma function_bound_2 (x y : ℝ) (n : ℕ) : ∀ (i : ℕ), i ∈ range (n + 1) → 
    |x ^ i * (y - x) * ∑ (x_2 : ℕ) in range (n - i), y ^ (n - i - 1 - x_2) * x ^ x_2|
    ≤ |x ^ i * (y - x)| * |∑ (x_2 : ℕ) in range (n - i), y ^ (n - i - 1 - x_2) * x ^ x_2| :=
  begin
    intros i p,
    rw abs_mul,
  end

  lemma coe_nat_ineq (n i : ℕ) (h : i < n) : ↑(n - i - 1) + (1 : ℝ) = ↑(n-i) :=
  begin
    have : n ≥ i + 1, by linarith,
    have : n - i ≥ 1 := le_tsub_of_add_le_left this,
    have : 1 ≤ n - i, by linarith,
    rw nat.cast_sub this,
    simp,
  end

  lemma weird_nat_ineq_1 (n i : ℕ) : n - i - 1 ≤ n - i := nat.sub_le (n - i) 1
  /-
  lemma function_bound_2_5 (x : ℝ) (n i : ℕ) :
    ∑ (x_2 : ℕ) in range (n - i), |(1 + |x|) ^ (n - i - 1 - x_2) * (1 + |x|) ^ x_2|
    = ∑ (x_2 : ℕ) in range (n - i), (1 + |x|) ^ (n - i - 1) :=
  begin
    rw finset.sum_congr rfl,
    intros k p,
    rw finset.mem_range at p,

    have a := weird_nat_ineq_1 n i,

    rw ← abs_of_pos (one_plus_abs_pow_pos x (n - i - 1)),
    rw ← pow_add,
    rw nat.sub_add_cancel this,
  end
  -/

  lemma function_bound_3_pos (x y : ℝ) (n i : ℕ) : 0 ≤ ↑(n - i) * (1 + |x|) ^ (n - i - 1) :=
  begin
    have a : (0 : ℝ) ≤ ↑(n - i) := nat.cast_nonneg (n - i),
    have b := one_plus_abs_pow_nonneg x (n - i - 1),
    exact mul_nonneg a b,
  end

  lemma function_bound_3 (x y : ℝ) (n i : ℕ) (h : |y| ≤ 1 + |x|) : ∀ (k : ℕ), k ∈ range(n - i) →
    |y ^ (n - i - 1 - k) * x ^ k|
    ≤ (1 + |x|) ^ (n - i - 1) :=
  begin
    intros k p,
    rw finset.mem_range at p,
    have p := le_pred_of_lt p,
    rw ← abs_of_pos (one_plus_abs_pow_pos x (n - i - 1)),
    rw abs_mul,
    repeat {rw abs_pow},
    have a := power_abs_x_bound x y k,
    have b := power_abs_y_bound x y h (n - i - 1 - k),

    have := abs_nonneg x,
    have q : 0 ≤ 1 + |x|, by linarith,
    have q₁ := pow_nonneg q (n - i - 1 - k),
    have q₂ := pow_nonneg this k,

    have d := mul_le_mul b a q₂ q₁,
    rw pow_sub_mul_pow (1 + |x|) p at d,
    rw ← abs_of_nonneg q at d,
    exact d,
  end

  @[simp] lemma rw_abs_sum (x : ℝ) (n : ℕ) : 
    ∑ (i : ℕ) in range (n + 1), |x| ^ i * |↑(n - i) * (1 + |x|) ^ (n - i - 1)|
    = ∑ (i : ℕ) in range (n + 1), |x| ^ i * (↑(n - i) * (1 + |x|) ^ (n - i - 1)) :=
  begin
    rw finset.sum_congr rfl,
    intros i p,
    have a := one_plus_abs_pow_nonneg x (n - i - 1),
    have b : (0 : ℝ) ≤ ↑(n - i) := nat.cast_nonneg (n - i),
    have c := mul_nonneg b a,
    rw ← abs_of_nonneg c,
    rw abs_abs,
  end

  lemma rw_abs_sum_2 (x y : ℝ) (n : ℕ ) :
    ∑ (i : ℕ) in range (n + 1), |x| ^ i * (↑(n - i) * (1 + |x|) ^ (n - i - 1))
    = ∑ (x_1 : ℕ) in range (n + 1), |x| ^ x_1 * ((↑n - ↑x_1) * (1 + |x|) ^ (n - x_1 - 1)) :=
  begin
    rw finset.sum_congr rfl,
    intros i p,
    rw finset.mem_range at p,
    have : i ≤ n, by linarith,
    rw nat.cast_sub this,
  end

  lemma ineq_5 (x y : ℝ) (n : ℕ) (h : |y| ≤ 1 + |x|): ∑ (i : ℕ) in range (n + 1), |x ^ i| * |∑ (x_2 : ℕ) in range (n - i), y ^ (n - i - 1 - x_2) * x ^ x_2| ≤ 
  ∑ (i : ℕ) in range (n + 1), |x ^ i| * |∑ (x_2 : ℕ) in range (n - i), (1 + |x|) ^ (n - i - 1)| :=
  begin
    refine finset.sum_le_sum _,
    intros i p,
    rw finset.mem_range at p,
    refine mul_le_mul _ _ _ _,
    { linarith, },
    { 
      simp,
      have a := finset.abs_sum_le_sum_abs (λ x_2, y ^ (n - i - 1 - x_2) * x ^ x_2) (range (n - i)),
      rw abs_of_nonneg (function_bound_3_pos x y n i),

      have b := function_bound_3 x y n i h,
      have c := finset.sum_le_sum b,
      simp at c,
      rename_var x_1 i_1,
      linarith,
    },
    {
      exact abs_nonneg (∑ (x_2 : ℕ) in range (n - i), y ^ (n - i - 1 - x_2) * x ^ x_2),
    },
    {
      exact abs_nonneg (x ^ i),
    },
  end

  lemma rw_inner_sum (x y : ℝ) (n : ℕ) : ∑ (i : ℕ) in range (n + 1), 
  |x ^ i * ∑ (x_2 : ℕ) in range (n - i), 
    y ^ (n - i - 1 - x_2) * x ^ x_2|
      = ∑ (x_1 : ℕ) in range (n + 1), 
        |x ^ x_1| * |∑ (x_2 : ℕ) in range (n - x_1), 
          y ^ (n - x_1 - 1 - x_2) * x ^ x_2| :=
  begin
    rw finset.sum_congr rfl,
    intros k p,
    rw finset.mem_range at p,
    rw abs_mul,
  end

  lemma ineq_6 (x y : ℝ) (n : ℕ) (h : |y| ≤ 1 + |x|) : 
    |y - x| * ∑ (i : ℕ) in range (n + 1), |x ^ i| * |∑ (x_2 : ℕ) in range (n - i), y ^ (n - i - 1 - x_2) * x ^ x_2|
      ≤ |y - x| * ∑ (i : ℕ) in range (n + 1), |x ^ i| * ((n - i) * (1 + |x|) ^ (n - i - 1)) :=
  begin
    have d := eq_zero_or_ne_zero (|y-x|),
    cases d,
    { rw d, simp, },
    {
      have : 0 < |y-x| :=
      begin
        have := abs_nonneg (y-x),
        by_contra,
        apply d.out,
        linarith,
      end,

      have h := ineq_5 x y n h,
      simp at h,
      simp,
      refine mul_le_mul _ _ _ _,
      { linarith, },
      {
        rw ← rw_abs_sum_2 x y n,
        linarith,
      },
      {
        have a := rw_inner_sum x y n,
        simp at a,
        rw ← a,
        have := finset.abs_sum_le_sum_abs (λ i, x ^ i * ∑ (x_2 : ℕ) in range (n - i), y ^ (n - i - 1 - x_2) * x ^ x_2) (range (n + 1)),
        simp at this,
        have := abs_nonneg (∑ (i : ℕ) in range (n + 1), x ^ i * ∑ (x_2 : ℕ) in range (n - i), y ^ (n - i - 1 - x_2) * x ^ x_2),
        linarith,
      },
      {
        exact abs_nonneg (y - x),
      },
    },
  end

  lemma sum_abs_pos (f : ℕ → ℝ) (n : ℕ) :
    0 ≤ ∑ (i : ℕ) in range n, |f i| :=
  begin
    induction n with n ih,
    simp,
    rw finset.sum_range_succ,
    have := abs_nonneg (f n),
    linarith,
  end

  lemma abs_pow_nonneg (x : ℝ) (n : ℕ) : 0 ≤ |x| ^ n :=
  begin
    exact pow_nonneg (abs_nonneg x) n,
  end


  lemma function_bound_4_1 (x y : ℝ) (n : ℕ) (h : |y| ≤ 1 + |x|) : ∀ (i : ℕ), i ∈ range (n + 1) → 
  |x ^ i * (y - x) * ∑ (x_2 : ℕ) in range (n - i), y ^ (n - i - 1 - x_2) * x ^ x_2| ≤ |(1 + |x|) ^ i| * |y - x| * ((n - i) * (1 + |x|) ^ (n - i - 1)) :=
  begin
    intros i p,
    repeat {rw abs_mul},
    repeat {rw abs_pow},
    have := one_plus_abs_nonneg x,
    have a := power_abs_x_bound x y i,
    have b : |y-x| ≤ |y-x|, by linarith,
    have c := finset.abs_sum_le_sum_abs (λ x_2, y ^ (n - i - 1 - x_2) * x ^ x_2) (range (n - i)),
    rw finset.mem_range at p,
    have : i ≤ n, by linarith,
    rw ← nat.cast_sub this,
    have c' := abs_of_nonneg (function_bound_3_pos x y n i),
    have d := function_bound_3 x y n i h,
    have e := finset.sum_le_sum d,
    simp at e,
    have := mul_le_mul b e (sum_abs_pos (λ i_1, y ^ (n - i - 1 - i_1) * x ^ i_1) (n-i)) (abs_nonneg (y-x)),
    have := mul_le_mul a this (mul_nonneg (abs_nonneg (y - x)) (sum_abs_pos (λ i_1, y ^ (n - i - 1 - i_1) * x ^ i_1) (n-i))) (one_plus_abs_pow_nonneg x i),
    repeat {rw ← mul_assoc},
    repeat {rw ← mul_assoc at this},
    rw abs_of_nonneg (one_plus_abs_nonneg x),
    have f : |x| ^ i ≤ |x| ^ i, by linarith,
    have := mul_le_mul b c (abs_nonneg ∑ (i_1 : ℕ) in range (n - i), y ^ (n - i - 1 - i_1) * x ^ i_1) (abs_nonneg (y-x)),
    have := mul_le_mul f this (mul_nonneg (abs_nonneg (y - x)) (abs_nonneg ∑ (i_1 : ℕ) in range (n - i), y ^ (n - i - 1 - i_1) * x ^ i_1)) (abs_pow_nonneg x i),
    simp at *,
    repeat {rw ← mul_assoc at this},
    linarith,
  end
    

  lemma function_bound_4 (x y : ℝ) (n : ℕ) (h : |y| ≤ 1 + |x|) :
  ∑ (i : ℕ) in range (n + 1), |x ^ i * (y - x) * ∑ (x_2 : ℕ) in range (n - i), y ^ (n - i - 1 - x_2) * x ^ x_2| ≤
  ∑ (i : ℕ) in range (n + 1), |(1 + |x|) ^ i| * |y - x| * ((n - i) * (1 + |x|) ^ (n - i - 1)) :=
  begin
    have a := function_bound_4_1 x y n h,
    have b := finset.sum_le_sum a,
    assumption,
  end

  lemma ineq_constants (x y : ℝ) (n : ℕ) : ∀ (i : ℕ), i ∈ range (n + 1) →
    (λ i, |(1 + |x|) ^ i| * |y - x| * ((↑n - ↑i) * (1 + |x|) ^ (n - i - 1))) i ≤ (λ i, |y - x| * (↑n + 1) * (1 + |x|) ^ n) i :=
  begin
    intros i p,
    dsimp,
    rw finset.mem_range at p,
    have q : i ≤ n, by linarith,
    rw abs_of_nonneg (one_plus_abs_pow_nonneg x i),
    rw [mul_comm ((1 + |x|) ^ i), ← mul_assoc],
    have := nat.sub.right_comm n i 1,
    have := weird_nat_ineq_1 n i,
    rw [mul_comm, ← mul_assoc, ← mul_assoc, 
      mul_comm ((1 + |x|) ^ (n - i - 1)),
      mul_assoc (|y-x|), ← pow_add (1 + |x|) (n - i - 1) i,
      mul_assoc, mul_comm ((1 + |x|) ^ (n - i - 1 + i)), ← mul_assoc],
    have : n - i - 1 + i ≤ n, by linarith,
    have a := one_plus_abs_mono_inc_le x (n - i - 1 + i) n this,
    have : (0 : ℝ) ≤ i := nat.cast_nonneg i,
    have a' : (↑n - ↑i : ℝ) ≤ ↑n + 1, by linarith,
    have : (0 : ℝ) ≤ n := nat.cast_nonneg n,
    have : (0 : ℝ) ≤ n + 1, by linarith,
    have b := mul_le_mul a' a (one_plus_abs_pow_nonneg x (n - i - 1 + i)) this,
    have c := abs_nonneg (y-x),
    have d: |y-x| ≤ |y-x|, by linarith,
    rw [mul_assoc, mul_assoc],
    refine mul_le_mul d b _ _,
    {
      have a: (0 : ℝ) ≤ ↑(n - i) := nat.cast_nonneg (n - i),
      have := nat.cast_sub q,
      rw ← this,
      exact mul_nonneg a (one_plus_abs_pow_nonneg x (n - i - 1 + i)),
    },
    {
      exact abs_nonneg (y - x),
    },
  end

  lemma final (x y c : ℝ) (n : ℕ) (h₁ : 0 < c) (d : 0 < |y - x|) (h₂ : |y - x| < c / ((↑n + 2) * (↑n + 1) * (1 + |x|) ^ n)) :
    (↑n + 1) * (|y - x| * (↑n + 1) * (1 + |x|) ^ n) ≤ c :=
  begin
    have h₁' : 0 ≤ c, by linarith,
    have h₂' : |y - x| ≤ c / ((↑n + 2) * (↑n + 1) * (1 + |x|) ^ n), by linarith,
    have p := power_limit_denom_pos x n,
    have p' : 0 ≤ (↑n + 2) * (↑n + 1) * (1 + |x|) ^ n, by linarith,
    have : |y - x| ≤ c / ((↑n + 2) * (↑n + 1) * (1 + |x|) ^ n) ↔ |y - x| * ((↑n + 2) * (↑n + 1) * (1 + |x|) ^ n) ≤ c :=
    begin
      exact le_div_iff p,
    end,
    replace h₂' := this.mp h₂',
    rw [← mul_assoc, ← mul_assoc] at h₂',
    rw [← mul_assoc, ← mul_assoc, mul_comm (↑n + 1) (|y-x|)],
    have : (0 : ℝ) ≤ ↑n := nat.cast_nonneg n,
    have c : ↑n + (1 : ℝ) ≤ ↑n + 2, by linarith,
    have a' : 0 ≤ (↑n +(1 : ℝ)), by linarith,
    have a'' := one_plus_abs_pow_nonneg x n,
    have a''' := mul_nonneg a' a'',
    have b' : (0 : ℝ) ≤ ↑n + (2:ℝ), by linarith,

    have a : (↑n + (1 : ℝ)) * (1 + |x|) ^ n ≤ (↑n + (1 : ℝ)) * (1 + |x|) ^ n, by linarith,
    have b := mul_le_mul c a a''' b',
    have d': |y - x| ≤ |y - x|, by linarith,
    have d'' : (0 : ℝ) ≤ ↑n + 1, by linarith,
    have d''' := mul_nonneg d'' a''',
    have d := mul_le_mul d' b d''' (abs_nonneg (y-x)),
    linarith,
  end

  lemma ineq_inner_sum_2 (x : ℝ) (n : ℕ) ⦃c : ℝ⦄ (y : ℝ)
  (r : 0 < c)
  (p₁ : |y - x| < 1)
  (p₂ : |y - x| < c / ((↑n + 2) * (↑n + 1) * (1 + |x|) ^ n))
  (d : 0 < |y - x|) :
  |∑ (x_1 : ℕ) in
        range (n + 1),
        x ^ x_1 * (y - x) *
          ∑ (x_2 : ℕ) in
            range (n - x_1),
            y ^ (n - x_1 - 1 - x_2) * x ^ x_2| ≤
    c :=
  begin
    have h₁' := bound_xy_y x y p₁,
    replace h₁' : |y| ≤ 1 + |x|, by linarith,
    have a := function_bound_4 x y n h₁',
    have b := finset.sum_le_sum (ineq_constants x y n),
    have c' := finset.abs_sum_le_sum_abs (λ x_1, x ^ x_1 * (y - x) * ∑ (x_2 : ℕ) in range (n - x_1), y ^ (n - x_1 - 1 - x_2) * x ^ x_2) (range (n + 1)),
    
    simp at a,
    simp at b,
    simp at c',

    have d' : |∑ (x_1 : ℕ) in range (n + 1), x ^ x_1 * (y - x) * ∑ (x_2 : ℕ) in range (n - x_1), y ^ (n - x_1 - 1 - x_2) * x ^ x_2| ≤
      (↑n + 1) * (|y - x| * (↑n + 1) * (1 + |x|) ^ n), by linarith,
    have e := final x y c n r d p₂,
    linarith,
  end

  lemma inequality_chasing_deriv_of_power (x : ℝ) (n : ℕ) ⦃c : ℝ⦄ (y : ℝ)
  (r : 0 < c)
  (p : dist y x < min 1 (c / (((n+2) * (n+1) * (1 + |x|) ^ n)))) :
  |(y - x) * ∑ (x_1 : ℕ) in range (n + 1), y ^ (n - x_1) * x ^ x_1 +
        (x - y) * (x ^ n * ↑n + x ^ n)| ≤
    c * |y - x| :=
  begin
    unfold dist at p,
    rw lt_min_iff at p,
    have p₁ := p.1,
    have p₂ := p.2,
    clear p,
    rw ← neg_sub y x,
    rw neg_mul,
    rw ← sub_eq_add_neg ((y - x) * ∑ (x_1 : ℕ) in range (n + 1), y ^ (n - x_1) * x ^ x_1) ((y - x) * (x ^ n * ↑n + x ^ n)),
    rw ← mul_sub_left_distrib,
    rw abs_mul,
    rw mul_comm,

    have := bound_xy_y x y p₁,
    have : |y| ≤ 1 + |x|, by linarith,
    have a := sum_ineq x y c this n,
    clear this this,
    simp at a,
    have d := eq_zero_or_ne_zero (|y-x|),
    cases d,
    {
      repeat {rw d},
      rw [mul_zero, mul_zero], 
    },
    {
      have := abs_nonneg (y-x),
      replace d := d.out,
      replace d : 0 < |y-x| := begin
        by_contra,
        apply d,
        linarith,
      end,
      rw mul_le_mul_right d,
      rw individual_to_sum x n,
      have b := sub_sum_eq_sum_sub x (n + 1) (λ (x_1 : ℕ), y ^ (n - x_1) * x ^ x_1) (λ (x_1 : ℕ), x ^ n),
      dsimp at b,
      rw ← b,
      clear b,
      have g := bound_xy_y x y p₁,
      have : |y| ≤ 1 + |x|, by linarith,
      have f := function_bound x y this n,
      clear g this,
      rw factor_out x y n,
      rw rw_inner_expr x y n,
      exact ineq_inner_sum_2 x n y r p₁ p₂ d,
    },
  end

  theorem deriv_of_power : ∀ (n : ℕ), ∀ (x : ℝ), has_deriv_at (x_to_n n) (x_to_n' n x) x :=
  begin
    intros n x,
    rw has_deriv_at,
    rw has_deriv_at_filter,
    rw has_fderiv_at_filter,
    dsimp,
    induction n with n ih,
    { simp, },
    {
      clear ih,
      induction n with n ih,
      { simp, },
      {
        rw x_to_n',
        dsimp,
        ring_nf,
        refine asymptotics.is_o_iff.mpr _,
        intros c r,
        refine eventually_nhds_iff_ball.mpr _,
        unfold ball,
        simp,
        use min 1 (c / ((n.succ+2) * (n.succ+1) * (1 + |x|) ^ n.succ)),
        split,
        {
          rw lt_min_iff,
          split,
          { norm_num, },
          {
            exact power_limit_div_pos x n.succ c r,
          }
        },
        {
          intros y p,
          rw [← add_assoc, tactic.ring.add_neg_eq_sub, x_to_n_sub_y_to_n_factor y x (n.succ+1)],
          rw [← tactic.ring.add_neg_eq_sub (-(x ^ n.succ * (↑n+1))), ← neg_add, neg_mul, 
            mul_comm (x ^ (n.succ) * (↑n+1) + x ^ n.succ), ← neg_mul, 
            mul_comm (x ^ n.succ * (↑n+1) + x ^ n.succ) x],
          rw [add_comm (-y * (x ^ n.succ * (↑n+1) + x ^ n.succ)), neg_mul, tactic.ring.add_neg_eq_sub,
            ← mul_sub_right_distrib],
          have q := abs_add ((y - x) * ∑ (x_1 : ℕ) in range (n + 1), y ^ (n - x_1) * x ^ x_1) ((x - y) * (x ^ n * ↑n + x ^ n)),
          simp,
          have := inequality_chasing_deriv_of_power x n.succ y r p,
          simp at this,
          linarith,
        }
      }
    }

  end
end power_rule

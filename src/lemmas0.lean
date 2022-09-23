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
import analysis.calculus.deriv
import power_rule

open_locale big_operators

lemma ne_zero_iff_sub_ne_zero (a b : ℝ) : a ≠ b ↔ a - b ≠ 0 :=
begin
  split;
  intro p,
  {
    have := lt_or_gt_of_ne p,
    cases this,
    intro q,
    repeat {linarith},
  },
  {
    have := lt_or_gt_of_ne p,
    cases this,
    repeat {linarith},
  },
end

lemma sub_ne_zero_iff_sub_ne_zero (a b : ℝ) : a - b ≠ 0 ↔ b - a ≠ 0 :=
begin
  split;
  intro h₁;
  by_contra;
  apply h₁;
  linarith,
end

lemma mul_self_eq_square (a : ℝ) : a * a = a ^ 2 := begin ring_nf, end

lemma mul_self_twice_eq_cube (a : ℝ) : a * a * a = a ^ 3 := begin ring_nf, end

lemma ne_zero_iff_sub_comm_ne_zero (a b : ℝ) : a ≠ b ↔ b - a ≠ 0 :=
begin
  split;
  intro p,
  {
    have := lt_or_gt_of_ne p,
    cases this,
    intro q,
    repeat {linarith},
  },
  {
    have := lt_or_gt_of_ne p,
    cases this,
    repeat {linarith},
  },
end

lemma half_bound (x y : ℝ) {c : ℝ} : (|y - x| < |c - x| / 2) → (x ≠ c) → (y ≠ c) :=
begin
  intros p q,
  have := abs_nonneg (y - x),
  have := abs_nonneg (c - x),
  have : 0 < |c - x| / 2, by linarith,
  by_contra,
  apply q,
  rw h at p,
  linarith,
end

lemma add_sum_sum_same_range_eq_sum_add (n : ℕ) (f : ℕ → ℝ) (g : ℕ → ℝ) :
  (∑ (x : ℕ) in finset.range n, f x) + (∑ (x : ℕ) in finset.range n, g x) =
  ∑ (x : ℕ) in finset.range n, (f x + g x) :=
begin
  induction n with n ih,
  { simp, },
  {
    repeat {rw finset.sum_range_succ},
    rw [add_add_add_comm, ih],
  },
end

lemma add_sub_sum_same_range_eq_sum_sub (n : ℕ) (f : ℕ → ℝ) (g : ℕ → ℝ) :
  (∑ (x : ℕ) in finset.range n, f x) - (∑ (x : ℕ) in finset.range n, g x) =
  ∑ (x : ℕ) in finset.range n, (f x - g x) :=
begin
  induction n with n ih,
  { simp, },
  {
    repeat {rw finset.sum_range_succ},
    rw [← add_sub_assoc, ← ih],
    ring_nf,
  },
end

lemma arith_geom_progression_split_sum (n : ℕ) (a q r : ℝ) :
  ∑ (k : ℕ) in finset.range n, (a + k * r) * q ^ k = 
  (∑ (k : ℕ) in finset.range n, a * q ^ k) +
  (r * ∑ (k : ℕ) in finset.range n, k * q ^ k) :=
begin
  rw finset.mul_sum,
  have := add_sum_sum_same_range_eq_sum_add n 
    (λ (x : ℕ), a * q ^ x) (λ (x : ℕ), r * (↑x * q ^ x)),
  simp at this,
  rw this,
  rw finset.sum_congr rfl,
  
  intros x p,
  rw [right_distrib, add_right_inj, ← mul_assoc],
  nth_rewrite_rhs 0 mul_comm r,
end

lemma sub_sum_sum_same_range_eq_sum_sub (n : ℕ) (x y : ℝ) (f : ℕ → ℝ → ℝ) (g : ℕ → ℝ → ℝ) :
  (∑ (k : ℕ) in finset.range n, f k y) - (∑ (k : ℕ) in finset.range n, g k x) =
  ∑ (k : ℕ) in finset.range n, (f k y - g k x) :=
begin
  induction n with n ih,
  { simp, },
  {
    repeat {rw finset.sum_range_succ},
    rw [add_sub_add_comm, ih],
  },
end

lemma deriv_add_eq_add_deriv (f : ℝ → ℝ) (f' : ℝ → ℝ) (g : ℝ → ℝ) (g' : ℝ → ℝ) (x : ℝ) :
  has_deriv_at f (f' x) x → has_deriv_at g (g' x) x → has_deriv_at (λ y, f y + g y) (f' x + g' x) x :=
begin
  intros a b,
  rw has_deriv_at_iff_is_o at *,
  have := asymptotics.is_o.add a b,
  clear a b,
  dsimp at this,
  ring_nf at this,

  rw asymptotics.is_o_iff at *,
  intros c r,
  specialize this r,
  rw metric.eventually_nhds_iff_ball at *,
  cases this with a b,
  cases b with a' b',
  use a,
  split,
  { exact a', },
  {
    intros y q,
    specialize b' y q,
    clear q,
    simp at *,
    repeat {rw ← add_assoc at b'},
    rw [add_sub, add_comm, ← add_assoc, ← add_assoc, ← add_assoc,
      add_comm (g y) (f y), neg_sub_left, add_comm (g' x), neg_mul, ← mul_neg,
      add_assoc (f y + g y + -f x), ← left_distrib (f' x + g' x) (-y) x,
      add_sub_right_comm (f y + g y + -f x), ← add_sub, neg_sub_left, 
      tactic.ring.add_neg_eq_sub, add_comm (g x) (f x)] at b',
    have : -y + x = -(y - x), by linarith,
    rw [this, mul_comm (f' x + g' x), neg_mul, tactic.ring.add_neg_eq_sub] at b',
    exact b',
  },
end

lemma deriv_sum_extension (n : ℕ) (x : ℝ) (f : ℕ → ℝ → ℝ) (f' : ℕ → ℝ → ℝ) :
  has_deriv_at (λ (x : ℝ), ∑ (k : ℕ) in finset.range (n + 1), f k x) (∑ (k : ℕ) in finset.range (n + 1), f' k x) x
  = has_deriv_at (λ (x : ℝ), (∑ (k : ℕ) in finset.range n, f k x) + f n x)
    ((∑ (k : ℕ) in finset.range n, f' k x) + f' n x) x :=
begin
  repeat {rw [has_deriv_at, has_deriv_at_filter, has_fderiv_at_filter,
    asymptotics.is_o_iff]},
  simp,
  split,
  {
    intros q c p,
    specialize q p,
    rw metric.eventually_nhds_iff_ball at *,
    cases q with ε q₁,
    cases q₁ with q₁ q₂,
    use ε,
    split,
    { exact q₁, },
    {
      intros y r,
      specialize q₂ y r,
      repeat {rw finset.sum_range_succ at *},
      repeat {rw nat.succ_eq_add_one at q₂},
      exact q₂,
    }
  },
  {
    intros q c p,
    specialize q p,
    rw metric.eventually_nhds_iff_ball at *,
    cases q with ε q₁,
    cases q₁ with q₁ q₂,
    use ε,
    split,
    { exact q₁, },
    {
      intros y r,
      specialize q₂ y r,
      repeat {rw finset.sum_range_succ at *},
      repeat {rw nat.succ_eq_add_one at q₂},
      exact q₂,
    }
  }
end

lemma deriv_sum_linearity (n : ℕ) (x : ℝ) (f : ℕ → ℝ → ℝ) (f' : ℕ → ℝ → ℝ) :
  (∀ (k : ℕ), has_deriv_at (f k) (f' k x) x) →
  has_deriv_at (λ (x : ℝ), ∑ (k : ℕ) in finset.range n, f k x)
    (∑ (k : ℕ) in finset.range n, f' k x) x :=
begin
  intro p,
  induction n with n ih,
  {
    specialize p 0,
    simp,
    rw [has_deriv_at, has_deriv_at_filter, has_fderiv_at_filter,
    asymptotics.is_o_iff],
    intros c r,
    rw metric.eventually_nhds_iff_ball,
    use c,
    split,
    { linarith, },
    {
      intros y q,
      simp,
      have a : 0 ≤ c, by linarith,
      have b := abs_nonneg (y - x),
      exact mul_nonneg a b,
    }
  },
  {
    rw deriv_sum_extension n x f f',
    specialize p n,
    exact deriv_add_eq_add_deriv (λ (x : ℝ), ∑ (k : ℕ) in finset.range n, f k x)
      (λ (x : ℝ), (∑ (k : ℕ) in finset.range n, f' k x)) (f n) ( f' n) x ih p,
  },
end

def deriv_sum_powers (n : ℕ) (q : ℝ) := deriv_sum_linearity n q power_rule.x_to_n power_rule.x_to_n' (λ (k : ℕ), power_rule.deriv_of_power k q)

lemma sum_x_to_n'_eq_deriv_sum (n : ℕ) (q : ℝ) : 
  ∑ (k : ℕ) in finset.range (n + 1), power_rule.x_to_n' k q = ∑ (k : ℕ) in finset.range n, (k + 1) * q ^ k :=
begin
  induction n with n ih,
  { simp, },
  {
    rw [finset.sum_range_succ, nat.succ_eq_add_one, ih],
    unfold power_rule.x_to_n',
    rw [← finset.sum_range_succ],
  },
end

lemma deriv_sum_eq_sum_sum (n : ℕ) (q : ℝ) :
  ∑ (k : ℕ) in finset.range n, (↑k + 1) * q ^ k = 
  (∑ (k : ℕ) in finset.range n, k * q ^ k) +
  ∑ (k : ℕ) in finset.range n, q ^ k :=
begin
  rw add_sum_sum_same_range_eq_sum_add,
  rw finset.sum_congr rfl,
  intros k p,
  ring_nf,
end

lemma second_deriv_geometric_series (n : ℕ) (x : ℝ) : 
  deriv (λ y', deriv (λ y, ∑ (k : ℕ) in finset.range n, y ^ (k + 2)) y') x = 
    (∑ (k : ℕ) in finset.range n, ↑(k + 2) * (↑k + 1) * x ^ k) :=
begin
  induction n with n ih,
  {
    simp,
    repeat {rw finset.sum_range_succ},
  },
  {
    induction n with n ih,
    {
      simp,
      repeat {rw finset.sum_range_succ},
    },
    {
      simp,
      rw finset.sum_range_succ,
      nth_rewrite_rhs 0 finset.sum_range_succ,
      simp,
      nth_rewrite_rhs 0 mul_assoc,
      rw [add_left_inj],
      simp at ih,
      rw ih,
    },
  },
end

lemma has_second_deriv_at_geometric_series (n : ℕ) (x : ℝ) :
  has_deriv_at (λ (y : ℝ), ∑ (k : ℕ) in finset.range n, (↑k + 2) * y ^ (k + 1))
  (∑ (k : ℕ) in finset.range n, (↑k + 2) * ((↑k + 1) * x ^ k))
  x :=
begin
  refine has_deriv_at.sum _,
  intros k p,
  have a := power_rule.deriv_of_power (k + 1) x,
  rw [power_rule.x_to_n, power_rule.x_to_n'] at a,
  simp at a,
  rename_var x y at a,
  have b := has_deriv_at_const x (↑k + (2 : ℝ)),
  have := has_deriv_at.mul b a,
  simp at this,
  exact this,
end

lemma expand_second_deriv_geometric_series (n : ℕ) (x : ℝ) :
  ∑ (k : ℕ) in finset.range n, ↑(k + 2) * (↑k + 1) * x ^ k = 
  ∑ (k : ℕ) in finset.range n, ↑k ^ 2 * x ^ k +
  ∑ (k : ℕ) in finset.range n, ↑3 * k * x ^ k +
  ∑ (k : ℕ) in finset.range n, 2 * x ^ k :=
begin
  repeat {rw add_sum_sum_same_range_eq_sum_add},
  rw finset.sum_congr rfl,
  intros a b,
  ring_nf,
  rw nat.cast_add a 2,
  simp only [left_distrib, right_distrib],
  ring_nf,
  have : ↑2 + 1 = (3 : ℝ), by norm_num,
  rw this,
  simp,
end

lemma reverse_second_deriv_geometric_series (n : ℕ) (x : ℝ) :
  ∑ (k : ℕ) in finset.range n, ↑k ^ 2 * x ^ k = 
  ∑ (k : ℕ) in finset.range n, ↑(k + 2) * (↑k + 1) * x ^ k -
  ∑ (k : ℕ) in finset.range n, ↑3 * k * x ^ k -
  ∑ (k : ℕ) in finset.range n, 2 * x ^ k :=
begin
  have := expand_second_deriv_geometric_series n x,
  rw this,
  ring_nf,
end

lemma second_deriv_geometric_sum_advanced_twice (n : ℕ) (x : ℝ) (h : x ≠ 1) :
  deriv (λ y', deriv (λ y, ∑ (k : ℕ) in finset.range n, y ^ (k + 2)) y') x =
  deriv (λ y', deriv (λ y, ∑ (k : ℕ) in finset.range (n + 2), y ^ k) y') x :=
begin
  simp,
  nth_rewrite_rhs 0 finset.sum_range_succ',
  nth_rewrite_rhs 0 finset.sum_range_succ',
  simp,
  rw finset.sum_congr rfl,
  intros x p,
  simp,
  left,
  ring_nf,
end

theorem second_derivative_offset_geometric (n : ℕ) (x : ℝ) (h : x ≠ 1) : 
  ∑ (x_1 : ℕ) in finset.range n, (↑x_1 + 2) * ((↑x_1 + 1) * x ^ x_1)
  = deriv (λ y, ∑ (x_1 : ℕ) in finset.range n, (↑x_1 + 2) * y ^ (x_1 + 1)) x :=
begin
  simp,
end

lemma second_derivative_uniqueness_term_1 (n : ℕ) (x : ℝ) :
  has_deriv_at (λ (y : ℝ), y ^ n) (n * x ^ (n - 1)) x :=
begin
  induction n with n ih,
  {
    simp,
    exact has_deriv_at_const x 1,
  },
  {
    rw [nat.succ_eq_add_one, nat.add_sub_cancel],
    have := power_rule.deriv_of_power (n + 1) x,
    rw [power_rule.x_to_n, power_rule.x_to_n'] at this,
    simp at this,
    rename_var y x,
    rw [nat.cast_add, nat.cast_one],
    exact this,
  }
end

lemma second_derivative_uniqueness_term_2 (n : ℕ) (x : ℝ) :
  has_deriv_at (λ (y : ℝ), y - 1) 1 x :=
begin
  have := power_rule.deriv_of_power 1 x,
  rw [power_rule.x_to_n, power_rule.x_to_n'] at this,
  simp at this,
  rename_var x y at this,
  exact has_deriv_at.sub_const this 1,
end

lemma second_derivative_uniqueness_term_3 (n : ℕ) (x : ℝ) :
  has_deriv_at (λ (y : ℝ), y ^ n * (y - 1)) (↑n * x ^ (n - 1) * (x - 1) + x ^ n * 1) x :=
begin
  have a := second_derivative_uniqueness_term_1 n x,
  have b := second_derivative_uniqueness_term_2 n x,
  exact has_deriv_at.mul a b,
end

lemma second_derivative_uniqueness_term_4 (n : ℕ) (x : ℝ) :
  has_deriv_at (λ (y : ℝ), (y ^ (n + 1) - 1)) ((↑n + 1) * x ^ n) x :=
begin
  have a := second_derivative_uniqueness_term_1 (n + 1) x,
  rw [nat.add_sub_cancel, nat.cast_add, nat.cast_one] at a,
  exact has_deriv_at.sub_const a 1,
end

lemma second_derivative_uniqueness_term_5 (n : ℕ) (x : ℝ) :
  has_deriv_at (λ (y : ℝ), (y - 1) ^ 2) (2 * (x - 1)) x :=
begin
  have := second_derivative_uniqueness_term_2 n x,
  have := has_deriv_at.mul this this,
  simp at this,
  ring_nf at this,
  ring_nf,
  exact this,
end

lemma second_derivative_uniqueness_equality (n : ℕ) (x : ℝ) (h : x ≠ 1) :
  (((↑n + 1) * (↑n * x ^ (n - 1) * (x - 1) + x ^ n) - (↑n + 1) * x ^ n) * (x - 1) ^ 2 -
     ((↑n + 1) * (x ^ n * (x - 1)) - (x ^ (n + 1) - 1)) * (2 * (x - 1))) /
  ((x - 1) ^ 2) ^ 2 = 
  (↑n * ↑(n + 1) * (x - 1) ^ 2 * x ^ (n - 1) - 2 * (-x ^ (n + 1) + 
  (↑n + 1) * (x - 1) * x ^ n + 1)) / (x - 1) ^ 3 :=
begin
  rw ne_zero_iff_sub_ne_zero at h,
  have h' := h,
  rw ← mul_self_pos at h,
  replace h := mul_pos h h,
  repeat {rw mul_self_eq_square at h},
  have : ((((↑n + 1) * (↑n * x ^ (n - 1) * (x - 1) + x ^ n) - (↑n + 1) * x ^ n) * (x - 1) ^ 2 -
       ((↑n + 1) * (x ^ n * (x - 1)) - (x ^ (n + 1) - 1)) * (2 * (x - 1))) /
    ((x - 1) ^ 2) ^ 2) * ((x - 1) ^ 2) ^ 2 =
  ((↑n * ↑(n + 1) * (x - 1) ^ 2 * x ^ (n - 1) - 
  2 * (-x ^ (n + 1) + (↑n + 1) * (x - 1) * x ^ n + 1)) / (x - 1) ^ 3) * ((x - 1) ^ 2) ^ 2 ↔
  (((↑n + 1) * (↑n * x ^ (n - 1) * (x - 1) + x ^ n) - (↑n + 1) * x ^ n) * (x - 1) ^ 2 -
       ((↑n + 1) * (x ^ n * (x - 1)) - (x ^ (n + 1) - 1)) * (2 * (x - 1))) /
    ((x - 1) ^ 2) ^ 2 =
  (↑n * ↑(n + 1) * (x - 1) ^ 2 * x ^ (n - 1) - 2 * (-x ^ (n + 1) + (↑n + 1) * (x - 1) * x ^ n + 1)) / (x - 1) ^ 3
  := mul_right_cancel_iff_of_pos h,
  rw ← this,
  clear this,
  rw div_mul,
  repeat {rw div_eq_mul_inv},
  have m₁ := mul_ne_zero h' h',
  replace m₁ := mul_ne_zero m₁ m₁,
  have m₂ := mul_inv_cancel m₁,
  repeat {rw mul_self_eq_square at m₂},
  have : 2 * 2 = 4, by norm_num,
  rw [m₂, ← div_eq_mul_inv, div_one, ← pow_mul, this, 
    mul_assoc (↑n * ↑(n + 1) * (x - 1) ^ 2 * x ^ (n - 1) - 2 * 
    (-x ^ (n + 1) + (↑n + 1) * (x - 1) * x ^ n + 1)),
    mul_comm ((x - 1) ^ 3)⁻¹],

  have : 3 ≤ 4, by norm_num,
  rw [← pow_sub₀ (x - 1) h' this],
  simp,
  simp only [left_distrib, right_distrib, mul_sub_left_distrib, mul_sub_right_distrib,
    one_mul, mul_one],
  ring_nf,
end

theorem second_derivative_uniqueness_geometric (n : ℕ) (x : ℝ) (h : x ≠ 1) :
  has_deriv_at (λ (y : ℝ), ((↑n + 1) * y ^ n * (y - 1) - (y ^ (n + 1) - 1)) / (y - 1) ^ 2)
    ((↑n * ↑(n + 1) * (x - 1) ^ 2 * (x ^ (n - 1)) - 2 * (-x ^ (n + 1) + (↑n + 1) * (x - 1) * x ^ n + 1)) / (x - 1) ^ 3) x :=
begin
  have a := second_derivative_uniqueness_term_3 n x,
  replace a := has_deriv_at.const_mul (↑n + (1 : ℝ)) a,
  have b := second_derivative_uniqueness_term_4 n x,
  replace a := has_deriv_at.sub a b,
  replace b := second_derivative_uniqueness_term_5 n x,
  have := (ne_zero_iff_sub_ne_zero x 1).1 h,
  replace := mul_ne_zero this this,
  rw mul_self_eq_square at this,
  have := has_deriv_at.div a b this,
  simp at this,
  rw second_derivative_uniqueness_equality n x h at this,
  ring_nf at *,
  assumption,
end

theorem inner_derivs_match (n : ℕ) (x : ℝ) : ∀ (k : ℕ), k ∈ finset.range(n) → 
  has_deriv_at (λ (y : ℝ), (↑k + 2) * y ^ (k + 1)) ((↑k + 2) * ((↑k + 1) * x ^ k)) x :=
begin
  intros k p,
  refine has_deriv_at.const_mul _ _,
  exact power_rule.deriv_of_power (k + 1) x,
end

theorem deriv_of_functions_eq (x f' : ℝ)
  (f g : ℝ → ℝ) (h' : ∀ (y : ℝ), f y = g y) :
  has_deriv_at f f' x → has_deriv_at g f' x :=
begin
  intro p,
  rw [has_deriv_at, has_deriv_at_filter, has_fderiv_at_filter,
    asymptotics.is_o_iff] at *,
  intros c r,
  specialize p r,
  rw metric.eventually_nhds_iff_ball at *,
  simp at p, simp,
  cases p with d q,
  cases q with q q',
  use d,
  split,
  { exact q, },
  {
    intros y m,
    have m₁ := h' y,
    have m₂ := h' x,
    rw [← m₁, ← m₂],
    exact q' y m,
  },
end

theorem deriv_of_functions_eq_add_const (x f' : ℝ) {c : ℝ}
  (f g : ℝ → ℝ) (h' : ∀ (y : ℝ), f y + c = g y) :
  has_deriv_at f f' x → has_deriv_at g f' x :=
begin
  intro p,
  rw [has_deriv_at, has_deriv_at_filter, has_fderiv_at_filter,
    asymptotics.is_o_iff] at *,
  intros c r,
  specialize p r,
  rw metric.eventually_nhds_iff_ball at *,
  simp at p, simp,
  cases p with d q,
  cases q with q q',
  use d,
  split,
  { exact q, },
  {
    intros y m,
    have m₁ := h' y,
    have m₂ := h' x,
    rw [← m₁, ← m₂],
    have := q' y m,
    ring_nf at this,
    ring_nf,
    assumption,
  },
end

theorem deriv_of_functions_eq_except_at_const (x x' f' : ℝ) (h : x ≠ x')
  (f g : ℝ → ℝ) (h' : ∀ (y : ℝ), (y ≠ x') → f y = g y) :
  has_deriv_at f f' x → has_deriv_at g f' x :=
begin
  intro p,
  rw [has_deriv_at, has_deriv_at_filter, has_fderiv_at_filter,
    asymptotics.is_o_iff] at *,
  intros c r,
  specialize p r,
  rw metric.eventually_nhds_iff_ball at *,
  simp at p, simp,
  cases p with d q,
  cases q with q q',
  use min d (|x - x'| / 2),
  split,
  { rw [lt_min_iff],
    split,
    { exact q, },
    {
      have := abs_nonneg (x - x'),
      rw ne_zero_iff_sub_ne_zero at h,
      rw ← abs_pos at h,
      have : 0 < |x - x'| / 2, by linarith,
      exact this,
    },
  },
  {
    intros y m,
    rw lt_min_iff at m,
    specialize q' y m.1,
    have m' := m.2,
    rw abs_sub_comm at m',
    have := h' y (half_bound x y m' h),
    rw ← this,
    have := h' x h,
    rw ← this,
    exact q',
  },
end

theorem deriv_of_functions_eq_except_at_const_add_const (x x' f' : ℝ) {c : ℝ} (h : x ≠ x')
  (f g : ℝ → ℝ) (h' : ∀ (y : ℝ), (y ≠ x') → f y + c = g y) :
  has_deriv_at f f' x → has_deriv_at g f' x :=
begin
  intro p,
  rw [has_deriv_at, has_deriv_at_filter, has_fderiv_at_filter,
    asymptotics.is_o_iff] at *,
  intros c r,
  specialize p r,
  rw metric.eventually_nhds_iff_ball at *,
  simp at p, simp,
  cases p with d q,
  cases q with q q',
  use min d (|x - x'| / 2),
  split,
  { rw [lt_min_iff],
    split,
    { exact q, },
    {
      have := abs_nonneg (x - x'),
      rw ne_zero_iff_sub_ne_zero at h,
      rw ← abs_pos at h,
      have : 0 < |x - x'| / 2, by linarith,
      exact this,
    },
  },
  {
    intros y m,
    rw lt_min_iff at m,
    specialize q' y m.1,
    have m' := m.2,
    rw abs_sub_comm at m',
    have := h' y (half_bound x y m' h),
    rw ← this,
    have := h' x h,
    rw ← this,
    ring_nf,
    ring_nf at q',
    exact q',
  },
end

lemma first_deriv_geom_offset_eq_add_const (n : ℕ) (x : ℝ) :
  ∑ (k : ℕ) in finset.range n, (↑k + 2) * x ^ (k + 1) + 1 =
  (∑ (k : ℕ) in finset.range (n + 1), (↑k + 1) * x ^ k) :=
begin
  rw finset.sum_range_succ',
  simp,
  apply finset.sum_congr rfl,
  intros k p,
  ring_nf,
end

theorem second_derivative_uniqueness_geometric_2 (n : ℕ) (x : ℝ) :
  has_deriv_at (λ (y : ℝ), ∑ (k : ℕ) in finset.range n, (↑k + 2) * y ^ (k + 1))
    (∑ (k : ℕ) in finset.range n, (↑k + 2) * ((↑k + 1) * x ^ k)) x → 
  has_deriv_at (λ (y : ℝ), ∑ (k : ℕ) in finset.range (n + 1), (↑k + 1) * y ^ k)
    (∑ (k : ℕ) in finset.range n, (↑k + 2) * ((↑k + 1) * x ^ k)) x :=
begin
  intro p,
  have := deriv_of_functions_eq_add_const x (∑ (k : ℕ) in finset.range n, (↑k + 2) * ((↑k + 1) * x ^ k))
    (λ (y : ℝ), ∑ (k : ℕ) in finset.range n, (↑k + 2) * y ^ (k + 1))
    (λ (y : ℝ), ∑ (k : ℕ) in finset.range (n + 1), (↑k + 1) * y ^ k)
    (first_deriv_geom_offset_eq_add_const n),
  exact this p,
end

lemma deriv_sub_geom_eq_sum (n : ℕ) (q : ℝ) :
  ∑ (k : ℕ) in finset.range n, (↑k + 1) * q ^ k - ∑ (k : ℕ) in finset.range n, q ^ k
  = ∑ (k : ℕ) in finset.range n, k * q ^ k :=
begin
  rw deriv_sum_eq_sum_sum n q,
  ring_nf,
end

lemma deriv_arith_geom_numerator_1 (n : ℕ) (q : ℝ) :
  has_deriv_at (λ (x : ℝ), (x ^ (n + 1) - 1)) ((↑n + 1) * q ^ n) q :=
begin
  have := power_rule.deriv_of_power (n + 1) q,
  have := has_deriv_at.sub_const this 1,
  rw [power_rule.x_to_n, power_rule.x_to_n'] at this,
  assumption,
end

lemma deriv_arith_geom_denominator_1 (n : ℕ) (q : ℝ) :
  has_deriv_at (λ (x : ℝ), (x - 1)) (1 : ℝ) q :=
begin
  have := power_rule.deriv_of_power 1 q,
  have := has_deriv_at.sub_const this 1,
  rw [power_rule.x_to_n, power_rule.x_to_n'] at this,
  simp at this,
  exact this,
end

lemma deriv_geom_at_ne_one (n : ℕ) (q : ℝ) (h : q ≠ 1) :
  has_deriv_at (λ (y : ℝ), (y ^ (n + 1) - 1) / (y - 1)) 
    (((↑n + 1) * q ^ n * (q - 1) - (q ^ (n + 1) - 1)) / (q - 1) ^ 2) q :=
begin
  have a := deriv_arith_geom_numerator_1 n q,
  have b := deriv_arith_geom_denominator_1 n q,
  rw ne_zero_iff_sub_ne_zero at h,
  have c := has_deriv_at.div a b h,
  simp at c,
  rename_var x y,
  assumption,
end

lemma cancel_power (q : ℝ) (h : q ≠ 0) (n : ℕ) : q / q ^ (n + 1) = 1 / q ^ n :=
begin
  induction n with n ih,
  {
    simp,
    exact div_self h,
  },
  {
    rw [pow_succ, nat.succ_eq_add_one, ← div_div, div_self h],
  },
end

lemma left_linearity_first_of_three_sum {n : ℕ} {a : ℝ} {b c : ℕ → ℝ} :
  ∑ (k : ℕ) in finset.range n, a * (b k) * (c k) = a * ∑ (k : ℕ) in finset.range n, b k * c k :=
begin
  rw finset.mul_sum,
  apply finset.sum_congr rfl,
  intros a b,
  rw mul_assoc,
end

lemma linearity_second_of_three_sum {n : ℕ} {a b : ℝ} {c : ℕ → ℝ} :
  ∑ (k : ℕ) in finset.range n, a * b * (c k) = b * ∑ (k : ℕ) in finset.range n, a * (c k) :=
begin
  rw finset.mul_sum,
  apply finset.sum_congr rfl,
  intros a b,
  ring_nf,
end

lemma summand_comm {n : ℕ} {a : ℝ} {c : ℕ → ℝ} :
  ∑ (k : ℕ) in finset.range n, c k * a = ∑ (k : ℕ) in finset.range n, a * c k :=
begin
  apply finset.sum_congr rfl,
  intros p q,
  ring_nf,
end

lemma mul_right_cancel_iff_ne_zero {a b c : ℝ} (h : b ≠ 0) : a * b = c * b ↔ a = c :=
begin
  rw ne_iff_lt_or_gt at h,
  cases h,
  {
    split,
    {
      intro p,
      have : 0 < -b, by linarith,
      rw [← neg_neg b, mul_neg, mul_neg c, ← neg_mul, ← neg_mul] at p,
      rw (mul_right_cancel_iff_of_pos this) at p,
      rw neg_eq_iff_neg_eq at p,
      rw neg_neg at p,
      symmetry,
      exact p,
    },
    {
      intro p,
      rw p,
    },
  },
  {
    split,
    {
      intro p,
      have : 0 < b, by linarith,
      rw (mul_right_cancel_iff_of_pos this) at p,
      exact p,
    },
    {
      intro p,
      rw p,
    },
  }
end

lemma multiply_both_sides_by_ne_zero {a b c : ℝ} (h : b ≠ 0) : (a = c) → a * b = c * b :=
begin
  intros p,
  rw mul_right_cancel_iff_ne_zero h,
  exact p,
end

lemma mul_consecutive_nats_even (n : ℕ) : 2 ∣ n * (n + 1) :=
begin
  have := nat.even_mul_succ_self n,
  exact (even_iff_two_dvd.mp) this,
end
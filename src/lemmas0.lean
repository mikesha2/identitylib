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

lemma sub_ne_zero_iff_sub_ne_zero (a b : ℝ) : a - b ≠ 0 ↔ b - a ≠ 0 :=
begin
  split;
  intro h₁;
  by_contra;
  apply h₁;
  linarith,
end

lemma mul_self_eq_square (a : ℝ) : a * a = a ^ 2 := begin ring_nf, end
import data.polynomial.basic
import data.polynomial.eval
import data.real.basic

noncomputable theory
open finset
open_locale big_operators polynomial
universes u v
variables {R : Type} {a b : R} {m n : ℕ} [comm_ring R]

namespace umbral_calculus

  -- Describe binomial polynomial sequences
  class binomial_polynomial_sequence (ps : ℕ → R[X]) :=
    (to_poly : ℕ → R[X])
    (degree_matches : ∀ (n : ℕ), ↑n = (to_poly n).degree)
    (is_binomial : ∀ (n : ℕ) (x y : R), (ps n).eval (x + y) = 
      ∑ (k : ℕ) in range (n + 1), ((ps k).eval x) * ((ps (n - k)).eval y) * n.choose k)
  
  -- Define the shift operator
  def shift_operator (ps : R[X]) : R[X] :=
    polynomial.comp ps (polynomial.X + polynomial.C 1)

  def shift_a_operator (a : R) (ps : R[X]) : R[X] :=
    polynomial.comp ps (polynomial.X + polynomial.C a)

  @[simp] lemma shift_x_by_a {a : R} :
    shift_a_operator a polynomial.X = polynomial.X + polynomial.C a := 
      by rw [shift_a_operator, polynomial.X_comp]

  @[simp] lemma shift_monomial_by_a {a : R} :
    shift_a_operator a ((polynomial.X) ^ n) = (polynomial.X + polynomial.C a) ^ n := 
    by rw [shift_a_operator, polynomial.X_pow_comp]
  
  def shift_one_op_eq_shift_op :
    (shift_operator : R[X] → R[X]) = shift_a_operator 1 :=
  begin
    ext,
    rw [shift_operator, shift_a_operator],
  end

  theorem shift_ab_operator_add (a b : R) (p : R[X]) : 
    (shift_a_operator a) ((shift_a_operator b) p) = shift_a_operator (a + b) p :=
  begin
    repeat {rw shift_a_operator},
    ext,
    rw [polynomial.comp_assoc, polynomial.add_comp],
    simp,
    rw add_assoc,
  end

  def shift_ring_hom (a : R) : ring_hom R[X] R[X] :=
  {
    to_fun := shift_a_operator a,
    map_one' := by rw [shift_a_operator, polynomial.one_comp],
    map_mul' := begin
      intros a b,
      repeat {rw shift_a_operator},
      simp,
    end,
    map_zero' := by rw [shift_a_operator, polynomial.zero_comp],
    map_add' := begin
      intros a b,
      repeat {rw shift_a_operator},
      simp,
    end,
  }

  def shift_linear_map (a : R) : linear_map (shift_ring_hom a) R[X] R[X] :=
  {
    to_fun := shift_a_operator a,
    map_add' := begin
      intros x y,
      repeat {rw shift_a_operator},
      rw polynomial.add_comp,
    end,
    map_smul' := begin
      intros x y,
      repeat {rw shift_a_operator},
      simp,
      refl,
    end,
  }

  -- Show that the single variable monomials indexed by power are a binomial polynomial sequence
  instance monomial_is_bps : binomial_polynomial_sequence (λ (n : ℕ), polynomial.monomial n (1 : ℝ)) :=
  {
    to_poly := (λ (n : ℕ), polynomial.monomial n (1 : ℝ)),
    degree_matches := begin
      intro n,
      simp,
    end,
    is_binomial := begin
      intros n x y,
      simp,
      exact add_pow x y n,
    end
  }

  class shift_invariant_op {a : R} (b : R) (op : R[X] →ₗ[R] R[X]) :=
    (is_shift_invariant : ∀ (p : R[X]), op (shift_linear_map b p) = (shift_linear_map b) (op p))
/-
  -- The shift operators are shift invariant
  instance shift_a_operator_is_shift_invariant_op {a : R} : 
    shift_invariant_op (shift_linear_map a) :=
  {
    is_shift_invariant := begin
      intros k p,
      repeat {rw shift_a_operator},
      rw polynomial.comp_assoc,
    end,
  }
  
  class is_delta_op (op : R[X] → R[X]) extends is_shift_invariant_op op :=
    (is_delta : ∃ (c : R), op polynomial.X = polynomial.C c ∧ c ≠ 0)
  
  /- This lemma specifically requires a ring structure on R 
     so that we can use the additive group property add_right_inj.
     The previous theorems only require a semiring.
  -/
  lemma delta_constant_is_zero (op : R[X] → R[X]) [is_delta_op op] :
    ∀ (a : R), op (polynomial.C a) = 0 :=
  begin
    intro a,
    have q₁ := _inst_2.is_shift_invariant a polynomial.X,
    have q₂ := _inst_2.is_delta,
    cases q₂ with c q₃,
    rw q₃.1 at q₁,
    rw [shift_a_operator, polynomial.X_comp,
      _inst_2.map_add polynomial.X (polynomial.C a), q₃.1,
      shift_a_operator, polynomial.C_comp] at q₁,
    nth_rewrite_rhs 0 ← add_zero (polynomial.C c) at q₁,
    rw add_right_inj at q₁,
    exact q₁,
  end

  variables (delta_op : R[X] → R[X]) [is_delta_op delta_op]

  lemma delta_decreases_degree (p : R[X]) : (delta_op (polynomial.X ^ (n + 1))).degree = n :=
  begin
    have q₁ := _inst_2.is_delta,
    cases q₁ with a q₁,
    have := add_pow polynomial.X (polynomial.C a) n,
    have q₂ : delta_op ((polynomial.X + polynomial.C a) ^ n) = delta_op (∑ (m : ℕ) in range (n + 1), polynomial.X ^ m * polynomial.C a ^ (n - m) * ↑(n.choose m)), by rw this,
    clear this,
    rw linear_map.map_sum,
  end
-/
end umbral_calculus
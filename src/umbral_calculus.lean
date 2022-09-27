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

  theorem shift_is_linear_map (a : R) : is_linear_map R (shift_a_operator a) :=
  {
    map_add := begin
      intros x y,
      rw [shift_a_operator, shift_a_operator, shift_a_operator, 
        polynomial.add_comp],
    end,
    map_smul := begin
      intros c x,
      rw [shift_a_operator, shift_a_operator, polynomial.smul_comp],
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

  class is_shift_invariant_op (op : R[X] → R[X]) extends is_linear_map R op :=
    (is_shift_invariant : ∀ (a : R) (p : R[X]), op (shift_a_operator a p) = (shift_a_operator a) (op p))

  -- The shift operators are shift invariant
  instance shift_n_operator_is_shift_invariant_op (a : R): 
    is_shift_invariant_op (shift_a_operator a : R[X] → R[X]) :=
  {
    map_add := begin
      intros x y,
      rw [shift_a_operator, shift_a_operator, shift_a_operator, 
        polynomial.add_comp],
    end,
    map_smul := begin
      intros c x,
      rw [shift_a_operator, shift_a_operator, polynomial.smul_comp],
    end,
    is_shift_invariant := begin
      intros k p,
      repeat {rw shift_ab_operator_add},
      rw add_comm,
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
    
  end
  
end umbral_calculus
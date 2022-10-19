import data.polynomial.basic
import data.polynomial.eval
import data.real.basic
import ring_theory.derivation

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

  def shift_linear_map (a : R) : linear_map (shift_ring_hom a : R[X] →+* R[X]) R[X] R[X] :=
  {
    to_fun := shift_ring_hom a,
    map_add' := begin
      intros x y,
      repeat {rw shift_a_operator},
      have := (shift_ring_hom a).map_add' x y,
      simp,
    end,
    map_smul' := begin
      intros x y,
      repeat {rw shift_a_operator},
      have := (shift_ring_hom a).map_mul' x y,
      simp,
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

  class shift_invariant_op (op : R[X] →+* R[X]) :=
    (is_shift_invariant : ∀ (a : R), ring_hom.comp 
      op (shift_ring_hom a) = ring_hom.comp (shift_ring_hom a) op)

  -- The shift operators are shift invariant
  instance shift_a_operator_is_shift_invariant_op (a : R) : 
    shift_invariant_op (shift_ring_hom a) :=
  {
    is_shift_invariant := begin
      intros b,
      repeat {rw shift_ring_hom},
      repeat {rw ring_hom.comp},
      simp,
      repeat {rw function.comp},
      ext,
      repeat {rw shift_a_operator},
      repeat {rw polynomial.comp_assoc},
      repeat {rw polynomial.add_comp},
      simp,
      rw [add_assoc, add_comm (polynomial.C a), ← add_assoc],
    end,
  }

  class delta_op (op : R[X] →+* R[X]) extends shift_invariant_op op :=
    (is_delta : ∃ (c : R), op polynomial.X = polynomial.C c ∧ c ≠ 0)

  /- This lemma specifically requires a ring structure on R 
     so that we can use the additive group property add_right_inj.
     The previous theorems only require a semiring.
  -/
  lemma delta_constant_is_zero (op : R[X] →+* R[X]) [delta_op op] :
    ∀ (a : R), op (polynomial.C a) = 0 :=
  begin
    intro a,
    have q₁ := _inst_2.is_shift_invariant a,
    have q₂ := _inst_2.is_delta,
    cases q₂ with c q₃,
    repeat {rw ring_hom.comp at q₁},
    simp at q₁,
    repeat {rw function.comp at q₁},
    replace q₁ : (λ (x : R[X]), op ((shift_ring_hom a) x)) (polynomial.X) = 
      (λ (x : R[X]), (shift_ring_hom a) (op x)) (polynomial.X) := by rw q₁,
    simp at q₁,
    repeat {rw shift_ring_hom at q₁},
    simp at q₁,
    repeat {rw shift_a_operator at q₁},
    rw q₃.1 at q₁,
    rw polynomial.C_comp at q₁,
    nth_rewrite_rhs 0 ← add_zero (polynomial.C c) at q₁,
    rw add_right_inj at q₁,
    exact q₁,
  end

  lemma delta_op_comm_shift_pow {R : Type} (n : ℕ)
    [comm_ring R]
    (op : R[X] →+* R[X])
    [delta_op op]
    (a : R) :
    op ((polynomial.X + polynomial.C a) ^ (n + 1)) =
      shift_a_operator a (op polynomial.X ^ (n + 1)) :=
  begin
    have q' := _inst_3.is_shift_invariant a,
    repeat {rw ring_hom.comp at q'},
    simp at q',
    repeat {rw function.comp at q'},
    replace q' : (λ (x : R[X]), op ((shift_ring_hom a) x)) (polynomial.X ^ (n + 1)) = 
      (λ (x : R[X]), (shift_ring_hom a) (op x)) (polynomial.X ^ (n + 1)) := by rw q',
    dsimp at q',
    rw ← shift_monomial_by_a,
    repeat {rw shift_ring_hom at q'},
    simp at q',
    simp,
    exact q',
  end

  lemma delta_op_is_linear_map (op : R[X] →+* R[X]) [delta_op op] :
    linear_map op R[X] R[X] :=
  {
    to_fun := op,
    map_add' := begin
      intros x y,
      simp,
    end,
    map_smul' := begin
      intros r x,
      simp,
    end,
  }

  instance delta_op.has_smul (op : R[X] →+* R[X]) [delta_op op] : has_smul R R[X] :=
  {
    smul := (λ (r: R) (x : R[X]), polynomial.C r * op x),
  }

  lemma delta_decreases_degree (n : ℕ) (op : R[X] →+* R[X]) [delta_op op] 
    : (op (polynomial.X ^ (n + 1))).degree = ↑n :=
  begin
/-    induction n with n ih,
    {
      simp,
      have q₁ := _inst_2.is_delta,
      cases q₁ with a q₁,
      have q₂ := q₁.1,
      have := congr_arg polynomial.degree q₂,
      rw polynomial.degree_C q₁.2 at this,
      exact this,
    },
    {
      
    },
-/
    have q₁ := _inst_2.is_delta,
    cases q₁ with a q₁,
    have := add_pow polynomial.X (polynomial.C a) (n + 1),
    have q₂ : op ((polynomial.X + polynomial.C a) ^ (n + 1)) = op (∑ (m : ℕ) in range (n + 1 + 1), polynomial.X ^ m * polynomial.C a ^ (n + 1 - m) * ↑((n + 1).choose m)), by rw this,
    clear this,
    -- linearity of ring homomorphisms
    rw ring_hom.map_sum at q₂,
    simp at q₂,
    have q₃ : ((op polynomial.X + op (polynomial.C a)) ^ (n + 1)).eval 0 = (∑ (x : ℕ) in range (n + 1 + 1), op polynomial.X ^ x * op (polynomial.C a) ^ (n + 1 - x) * ↑((n + 1).choose x)).eval 0, by rw q₂,
    simp at q₃,
    rw [q₁.1, polynomial.eval_C, delta_constant_is_zero, polynomial.eval_zero, add_zero] at q₃,
/-
    rw delta_constant_is_zero at q₂,
    simp at q₂,
-/
/-
    have := add_pow polynomial.X (polynomial.C a) (n + 1),
    have q₂ : op ((polynomial.X + polynomial.C a) ^ (n + 1)) = op (∑ (m : ℕ) in range (n + 1 + 1), polynomial.X ^ m * polynomial.C a ^ (n + 1 - m) * ↑((n + 1).choose m)), by rw this,
    clear this,
    -- linearity of ring homomorphisms
    rw ring_hom.map_sum at q₂,
    simp at q₂,
    rw delta_constant_is_zero at q₂,
    simp at q₂,

    have q₃ := delta_op_comm_shift_pow n op a,
    have q₄ : (0 : R[X]) ^ 0 = 1, by norm_num,
-/
  end

end umbral_calculus
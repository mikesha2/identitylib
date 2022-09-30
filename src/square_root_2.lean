import algebra.parity

theorem even_times_self_is_even {n : ℕ} : -- n is a natural number
  (even n) → even (n ^ 2) := -- if n is even, then n ^ 2 is even
begin
  intro p, 
  -- assume that n is even


  rw even at *,
  -- rewrite the definition of "even"


  cases p with r h,
  -- since p is a hypothesis,
  --assume such a number r exists



  use (r ^ 2 + r ^ 2),
  -- we need to find a number m
  -- such that n ^ 2 = m + m
  -- (definition of "even")
  -- let's use 2 r ^ 2



  rw h,
  -- replace n by r + r



  ring, -- simplify algebra
end




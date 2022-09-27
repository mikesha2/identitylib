import algebra.parity

theorem even_times_self_is_even {n : ℕ} :
  (even n) → even (n ^ 2) :=
begin
  intro p,



  rw even at *,



  cases p with r h,




  use (r ^ 2 + r ^ 2),







  rw h,




  ring,
end




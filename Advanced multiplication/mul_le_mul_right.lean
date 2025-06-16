induction t with d hd
repeat rw [mul_zero]
apply le_refl
repeat rw [succ_eq_add_one]
repeat rw [mul_add]
cases hd
rw [h_1]
cases h
rw [mul_one,  mul_one, h_2, add_assoc]
nth_rewrite 3 [add_comm]
repeat rw [← add_assoc]
use (w_1 + w)
simp_add

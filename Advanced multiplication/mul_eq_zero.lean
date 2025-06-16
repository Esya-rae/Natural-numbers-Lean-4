cases b
tauto
cases a
tauto
repeat rw [succ_eq_add_one] at h
rw [mul_add, add_mul, add_mul, ←add_assoc, one_mul, mul_one, mul_one, ←succ_eq_add_one] at h
apply succ_ne_zero at h
tauto

induction b with d hd generalizing c
rw [mul_zero] at h
symm at h
apply mul_eq_zero at h
tauto
cases c with e
rw [mul_zero] at h
apply mul_eq_zero at h
tauto
repeat rw [succ_eq_add_one] at h
repeat rw [mul_add] at h
apply add_right_cancel (a * d) (a * e) (a * 1) at h
apply hd at h
repeat rw [succ_eq_add_one]
rw [h]
trivial

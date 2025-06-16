apply eq_succ_of_ne_zero at ha
cases ha with n hn
rw [hn, one_eq_succ_zero]
repeat rw [succ_eq_add_one]
rw [zero_add]
use n
simp_add

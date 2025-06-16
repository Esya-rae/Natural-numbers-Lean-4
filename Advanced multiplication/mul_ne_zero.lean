apply eq_succ_of_ne_zero at ha
apply eq_succ_of_ne_zero at hb
cases ha
cases hb
rw [h, h_1]
repeat rw [succ_eq_add_one]
rw [add_mul]
repeat rw [mul_add]
repeat rw [mul_one, one_mul]
rw [← add_assoc]
rw [mul_one]
rw [← succ_eq_add_one]
apply succ_ne_zero

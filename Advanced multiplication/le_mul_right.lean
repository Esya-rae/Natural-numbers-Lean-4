apply mul_left_ne_zero at h
apply one_le_of_ne_zero at h
nth_rewrite 1 [← one_mul a]
nth_rewrite 2 [mul_comm]
apply mul_le_mul_right
exact h

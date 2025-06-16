cases x with y
left
trivial
right
cases hx
rw [succ_eq_add_one] at h
nth_rewrite 2 [add_comm] at h
rw [add_assoc] at h
symm at h
apply add_right_eq_self at h
apply add_right_eq_zero at h
rw [h]
exact one_eq_succ_zero

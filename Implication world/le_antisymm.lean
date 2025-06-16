cases hxy
cases hyx
rw [h_1] at h
symm at h
rw [add_assoc] at h
apply add_right_eq_self at h
apply add_right_eq_zero at h
rw [h] at h_1
rw [add_zero] at h_1
exact h_1

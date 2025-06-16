cases hx
cases w
rw [add_zero] at h
right
right
symm at h
exact h
cases a with b
rw [two_eq_succ_one, succ_eq_add_one, succ_eq_add_one, ← add_assoc, add_zero] at h
apply add_right_cancel at h
symm at h
right
left
exact h
rw [two_eq_succ_one] at h
repeat rw [succ_eq_add_one] at h
rw [← add_assoc, ← add_assoc] at h
apply add_right_cancel at h
symm at h
apply add_left_eq_self at h
apply add_right_eq_zero at h
left
exact h

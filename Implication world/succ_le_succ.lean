cases hx
repeat rw [succ_eq_add_one] at h
rw [add_comm] at h
nth_rewrite 3 [add_comm] at h
rw [add_assoc] at h
apply add_left_cancel at h
rw [h]
use w
trivial

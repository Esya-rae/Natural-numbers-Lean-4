have h2: x * y ≠ 0
rw [h]
tauto
apply le_mul_right at h2
rw [h] at h2
apply le_one at h2
cases h2
rw [h_1, zero_mul] at h
tauto
exact h_1

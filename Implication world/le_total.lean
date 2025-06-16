induction y with d hd
right
apply zero_le
cases hd with h1 h2
left
apply le_trans x d (succ d)
exact h1
apply le_succ_self
cases h2 with e he
rw [he]
cases e with b
left
rw [add_zero]
apply le_succ_self
right
rw [add_succ]
rw [←succ_add]
use b
trivial
